#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RAR5 口令恢复工具（找回自己文件的口令）
================================================
用途：对 RAR5（WinRAR 5.x/6.x/7.x）加密压缩包做「口令猜测试验」。
     不修改、不破坏原文件，只在内存中验证口令是否正确。

原理（与 UnRAR / hashcat 完全一致，已用 hashcat 官方测试向量自检）：
    dk       = PBKDF2-HMAC-SHA256( password_utf8 , salt , 2^Lg2 + 32 , 32字节 )
    pswcheck = dk[0..7] ^ dk[8..15] ^ dk[16..23] ^ dk[24..31]   (按字节折叠)
    若 pswcheck 与压缩包加密头里的 8 字节校验值相同 => 口令正确

用法示例：
    python rar5_recover.py --selftest                       # 算法自检
    python rar5_recover.py "文件.rar" --info                # 只看加密头信息
    python rar5_recover.py "文件.rar" -w 字典.txt           # 字典攻击
    python rar5_recover.py "文件.rar" --builtin             # 内置常见弱口令
    python rar5_recover.py "文件.rar" --mask "?d?d?d?d?d?d" # 6位纯数字爆破
"""

import argparse
import hashlib
import itertools
import multiprocessing as mp
import os
import sys
import time

BATCH = 64                      # 每个任务批处理的候选口令数
CHARSETS = {
    "?d": "0123456789",
    "?l": "abcdefghijklmnopqrstuvwxyz",
    "?u": "ABCDEFGHIJKLMNOPQRSTUVWXYZ",
    "?s": "!@#$%^&*-_=+",
    "?a": "0123456789abcdefghijklmnopqrstuvwxyz",
    "?A": "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ",
}

# 内置常见弱口令（通用，不含任何针对性猜测；想试别的请用 -w 字典文件）
BUILTIN = [
    "123456", "123456789", "12345678", "1234567890", "111111", "000000",
    "123123", "123321", "666666", "888888", "88888888", "5201314", "520520",
    "abc123", "qwerty", "qwerty123", "password", "password123", "admin",
    "admin123", "root", "letmein", "a123456", "a12345678", "1qaz2wsx",
    "qazwsx", "zxcvbnm", "asdfgh", "woaini", "woaini1314", "iloveyou",
    "666888", "168168", "1314520", "100200", "000000000", "111111111",
    "1234", "12345", "1234567", "1", "12", "112233", "121212", "654321",
]


# --------------------------------------------------------------------------- #
# 加密头解析
# --------------------------------------------------------------------------- #
def read_vint(buf, i):
    v = 0
    sh = 0
    while True:
        b = buf[i]
        i += 1
        v |= (b & 0x7F) << sh
        if not (b & 0x80):
            break
        sh += 7
    return v, i


def parse_crypt_header(path):
    with open(path, "rb") as f:
        d = f.read(128)
    if d[:8] != b"Rar!\x1a\x07\x01\x00":
        raise SystemExit("不是 RAR5 格式的文件（签名不匹配）")
    i = 8
    i += 4                                   # HeadCRC
    head_size, i = read_vint(d, i)
    htype, i = read_vint(d, i)
    hflags, i = read_vint(d, i)
    if htype != 4:
        raise SystemExit(
            "第一个头不是加密头(HEAD_CRYPT, type=%d)。\n"
            "说明该包可能只加密了文件数据、未加密文件名，本工具需配合 unrar/WinRAR 使用。" % htype
        )
    if hflags & 0x0001:                      # 有 extra area
        extra, i = read_vint(d, i)
        extra_start = i
        i = extra_start + extra
    if hflags & 0x0002:                      # 有 data area
        data_size, i = read_vint(d, i)
        i += data_size

    enc_version, i = read_vint(d, i)
    flags, i = read_vint(d, i)
    lg2, i = read_vint(d, i)
    salt = d[i:i + 16]; i += 16
    if not (flags & 0x0001):
        raise SystemExit("该包没有写入口令校验值(pswcheck)，无法离线快速验证口令。")
    pswcheck = d[i:i + 8]; i += 8
    csum = d[i:i + 4]; i += 4

    valid = hashlib.sha256(pswcheck).digest()[:4] == csum
    return {
        "enc_version": enc_version, "flags": flags, "lg2": lg2,
        "salt": salt, "pswcheck": pswcheck, "csum": csum, "header_ok": valid,
        "iters": (1 << lg2) + 32, "head_size": head_size,
    }


# --------------------------------------------------------------------------- #
# 口令校验
# --------------------------------------------------------------------------- #
_G = {}


def _init_worker(salt, pswcheck, iters):
    _G["salt"] = salt
    _G["pswcheck"] = pswcheck
    _G["iters"] = iters


def derive_pswcheck(pwd: bytes, salt: bytes, iters: int) -> bytes:
    dk = hashlib.pbkdf2_hmac("sha256", pwd, salt, iters, 32)
    return bytes((dk[j] ^ dk[j + 8] ^ dk[j + 16] ^ dk[j + 24]) for j in range(8))


def _check_batch(batch):
    for cand in batch:
        if derive_pswcheck(cand, _G["salt"], _G["iters"]) == _G["pswcheck"]:
            return cand
    return None


# --------------------------------------------------------------------------- #
# 候选口令生成
# --------------------------------------------------------------------------- #
def variants(line: bytes):
    """口令编码变体：原样字节 + GBK->UTF-8（WinRAR 内部按 UTF-8 取密码）"""
    out = [line]
    for enc in ("utf-8", "gbk"):
        try:
            s = line.decode(enc)
        except UnicodeDecodeError:
            continue
        u = s.encode("utf-8")
        if u not in out:
            out.append(u)
    return out


def gen_from_wordlist(path):
    with open(path, "rb") as f:
        for raw in f:
            raw = raw.rstrip(b"\r\n")
            if not raw:
                continue
            for v in variants(raw):
                yield v


def gen_from_builtin():
    for w in BUILTIN:
        yield w.encode("utf-8")


def gen_from_mask(mask):
    pos = []
    k = 0
    while k < len(mask):
        if mask[k] == "?":
            key = mask[k:k + 2]
            if key not in CHARSETS:
                raise SystemExit("未知的掩码字符: %s" % key)
            pos.append(CHARSETS[key])
            k += 2
        else:
            pos.append(mask[k])
            k += 1
    for combo in itertools.product(*pos):
        yield "".join(combo).encode("utf-8")


# --------------------------------------------------------------------------- #
# 攻击主循环
# --------------------------------------------------------------------------- #
def run_attack(cands, salt, pswcheck, iters, total=None, workers=None):
    workers = workers or (os.cpu_count() or 4)
    t0 = time.time()
    done = 0
    last = t0

    def batches():
        it = iter(cands)
        while True:
            b = list(itertools.islice(it, BATCH))
            if not b:
                return
            yield b

    with mp.Pool(workers, initializer=_init_worker,
                 initargs=(salt, pswcheck, iters)) as pool:
        for res in pool.imap_unordered(_check_batch, batches(), chunksize=1):
            done += BATCH
            now = time.time()
            if now - last >= 1.0:
                spd = done / (now - t0)
                eta = (" 剩余约 %.0f 秒" % ((total - done) / spd)) if total else ""
                sys.stderr.write("\r已尝试 %d 个口令 (%.0f 个/秒)%s   "
                                 % (done, spd, eta))
                sys.stderr.flush()
                last = now
            if res is not None:
                pool.terminate()
                sys.stderr.write("\n")
                return res
    sys.stderr.write("\n")
    return None


# --------------------------------------------------------------------------- #
def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="RAR5 口令恢复工具")
    ap.add_argument("archive", nargs="?", help="RAR5 加密压缩包路径")
    ap.add_argument("-w", "--wordlist", help="口令字典文件（每行一个）")
    ap.add_argument("--builtin", action="store_true", help="使用内置常见弱口令")
    ap.add_argument("--mask", help='掩码爆破, 如 "?d?d?d?d?d?d" 或 "abc?d?d"')
    ap.add_argument("--info", action="store_true", help="只显示加密头信息")
    ap.add_argument("--selftest", action="store_true", help="算法自检（hashcat 官方向量）")
    ap.add_argument("-j", "--workers", type=int, default=None, help="并行进程数")
    args = ap.parse_args()

    if args.selftest:
        salt = bytes.fromhex("38466361001011015181344360681307")
        expect = bytes.fromhex("cc7a30583e62676a")
        got = derive_pswcheck(b"hashcat", salt, (1 << 15) + 32)
        print("自检: 期望 %s / 实际 %s -> %s"
              % (expect.hex(), got.hex(), "通过" if got == expect else "失败"))
        t0 = time.time()
        for _ in range(10):
            derive_pswcheck(b"hashcat", salt, (1 << 15) + 32)
        one = (time.time() - t0) / 10
        n = os.cpu_count() or 4
        print("单核速度: %.1f ms/个 -> 约 %.0f 个/秒（%d 核并行约 %.0f 个/秒）"
              % (one * 1000, 1 / one, n, n / one))
        return

    if not args.archive:
        ap.print_help()
        return

    info = parse_crypt_header(args.archive)
    print("文件      : %s" % args.archive)
    print("加密方式  : RAR5 + AES-256，头部全加密（WinRAR 的 -hp 模式）")
    print("KDF       : PBKDF2-HMAC-SHA256, 迭代 2^%d = %d 次（校验值用 %d 次）"
          % (info["lg2"], 1 << info["lg2"], info["iters"]))
    print("Salt      : %s" % info["salt"].hex())
    print("校验值    : %s" % info["pswcheck"].hex())
    print("头完整性  : %s (sha256(校验值)[:4] = %s)"
          % ("有效(已核实)" if info["header_ok"] else "异常", info["csum"].hex()))
    if args.info or not (args.wordlist or args.builtin or args.mask):
        return

    import math
    if args.wordlist:
        cands, total, label = gen_from_wordlist(args.wordlist), None, "字典"
    elif args.builtin:
        cands, total, label = gen_from_builtin(), len(BUILTIN), "内置弱口令"
    else:
        parts = []
        k = 0
        while k < len(args.mask):
            if args.mask[k] == "?":
                parts.append(len(CHARSETS[args.mask[k:k + 2]])); k += 2
            else:
                parts.append(1); k += 1
        total = math.prod(parts)
        cands, label = gen_from_mask(args.mask), "掩码 %s" % args.mask

    if not args.wordlist:
        size = os.path.getsize(args.archive)
        print("待尝试    : %s，约 %s 个候选口令" % (label, format(total, ",")))
    print("开始尝试...（Ctrl+C 可中断）\n")

    found = run_attack(cands, info["salt"], info["pswcheck"], info["iters"],
                       total=total, workers=args.workers)
    if found is None:
        print("× 没有命中：候选口令全部试完仍未找到正确口令。")
    else:
        for enc in ("utf-8", "gbk"):
            try:
                text = found.decode(enc)
                break
            except UnicodeDecodeError:
                text = None
        print("★ 找到口令了！")
        print("  字节: %s" % found.hex())
        print("  文本: %s" % (text if text is not None else "(非文本，见上方字节)"))
        print("\n用 WinRAR / 7-Zip 打开该文件，输入上面的口令即可解压。")


if __name__ == "__main__":
    mp.freeze_support()
    main()
