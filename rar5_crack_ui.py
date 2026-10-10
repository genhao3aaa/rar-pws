#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RAR5 口令恢复工具 · 图形界面版（仅用于找回你自己文件的口令）
================================================================
功能：
  · 字典攻击：自选字典文件，支持大小写/数字后缀等变形规则
  · 暴力枚举：自选「密码位数区间」+「字符类型」（数字/小写/大写/符号/自定义）
              可加固定前缀、后缀
  · 内置弱口令：一键快速检查常见弱口令
  · 多进程并行、实时速度与剩余时间、随时暂停/继续/停止
  · 断点续跑：停止或关闭后再次运行，可从中断处继续
  · 找到口令后自动写入文件并可一键复制

算法（与 UnRAR / hashcat 完全一致，内置官方向量自检）：
    dk       = PBKDF2-HMAC-SHA256(password_utf8, salt, 2^Lg2 + 32, 32)
    pswcheck = dk[0..7] ^ dk[8..15] ^ dk[16..23] ^ dk[24..31]

命令行（不开界面）：
    python rar5_crack_ui.py --selftest                  # 算法自检 + 测速
    python rar5_crack_ui.py --engine-test 文件.rar      # 无界面跑一次内置弱口令
"""

import argparse
import hashlib
import itertools
import json
import math
import multiprocessing as mp
import os
import queue
import sys
import threading
import time
import tkinter as tk
from collections import deque
from tkinter import filedialog, messagebox, ttk

# --------------------------------------------------------------------------- #
# 一、口令校验后端（优先使用 OpenSSL 版 PBKDF2，快 2 倍以上）
# --------------------------------------------------------------------------- #
try:
    from cryptography.hazmat.primitives import hashes as _hashes
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC as _PBKDF2

    def pbkdf2_32(pwd: bytes, salt: bytes, iters: int) -> bytes:
        return _PBKDF2(algorithm=_hashes.SHA256(), length=32,
                       salt=salt, iterations=iters).derive(pwd)

    BACKEND = "cryptography / OpenSSL"
except Exception:                                     # pragma: no cover
    def pbkdf2_32(pwd: bytes, salt: bytes, iters: int) -> bytes:
        return hashlib.pbkdf2_hmac("sha256", pwd, salt, iters, 32)

    BACKEND = "hashlib (stdlib)"

MS_PER_CANDIDATE = 4.4      # 单核单候选大约耗时（毫秒），用于剩余时间预估

# 字符集定义
CH_DIGIT = "0123456789"
CH_LOWER = "abcdefghijklmnopqrstuvwxyz"
CH_UPPER = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
CH_SYMBOL = "!@#$%^&*()-_=+[]{};:,.<>/?"

BUILTIN_WEAK = [
    "123456", "123456789", "12345678", "1234567890", "111111", "000000",
    "123123", "123321", "666666", "888888", "88888888", "5201314", "520520",
    "abc123", "qwerty", "qwerty123", "password", "password123", "admin",
    "admin123", "root", "letmein", "a123456", "1qaz2wsx", "qazwsx", "zxcvbnm",
    "asdfgh", "woaini", "woaini1314", "iloveyou", "666888", "168168",
    "1314520", "112233", "121212", "654321", "a12345678", "abcd1234",
]


def fold8(dk: bytes) -> bytes:
    """把 32 字节派生结果按字节折叠成 8 字节口令校验值。"""
    return bytes((dk[j] ^ dk[j + 8] ^ dk[j + 16] ^ dk[j + 24]) for j in range(8))


def derive_pswcheck(pwd: bytes, salt: bytes, iters: int) -> bytes:
    return fold8(pbkdf2_32(pwd, salt, iters))


# --------------------------------------------------------------------------- #
# 二、加密头解析（RAR5 HEAD_CRYPT）
# --------------------------------------------------------------------------- #
def read_vint(buf, i):
    v = sh = 0
    while True:
        b = buf[i]
        i += 1
        v |= (b & 0x7F) << sh
        if not (b & 0x80):
            return v, i
        sh += 7


def parse_crypt_header(path):
    with open(path, "rb") as f:
        d = f.read(160)
    if d[:8] != b"Rar!\x1a\x07\x01\x00":
        raise ValueError("不是 RAR5 格式（文件签名不匹配）")
    i = 12                                     # 跳过 8 字节签名 + 4 字节 HeadCRC
    _, i = read_vint(d, i)                     # HeadSize
    htype, i = read_vint(d, i)
    hflags, i = read_vint(d, i)
    if htype != 4:
        raise ValueError("第一个头不是加密头(HEAD_CRYPT)，该包可能未加密文件名")
    if hflags & 0x0001:
        extra, i = read_vint(d, i)
        i += extra
    if hflags & 0x0002:
        dsize, i = read_vint(d, i)
        i += dsize
    enc_ver, i = read_vint(d, i)
    flags, i = read_vint(d, i)
    lg2, i = read_vint(d, i)
    salt = d[i:i + 16]; i += 16
    if not (flags & 0x0001):
        raise ValueError("该包未写入口令校验值(pswcheck)，无法离线校验口令")
    pswcheck = d[i:i + 8]; i += 8
    csum = d[i:i + 4]
    return {
        "enc_version": enc_ver, "flags": flags, "lg2": lg2,
        "salt": salt, "pswcheck": pswcheck, "csum": csum,
        "iters": (1 << lg2) + 32,
        "header_ok": hashlib.sha256(pswcheck).digest()[:4] == csum,
    }


# --------------------------------------------------------------------------- #
# 三、多进程工作进程
# --------------------------------------------------------------------------- #
_W = {}


def _init_worker(salt, pswcheck, iters):
    _W["salt"], _W["pswcheck"], _W["iters"] = salt, pswcheck, iters


def _check_batch(batch):
    """batch = [(序号, 口令bytes), ...]；返回 (起始序号, 本批数量, 命中口令|None)"""
    salt, psw, iters = _W["salt"], _W["pswcheck"], _W["iters"]
    start = batch[0][0]
    for _, cand in batch:
        if fold8(pbkdf2_32(cand, salt, iters)) == psw:
            return start, len(batch), cand
    return start, len(batch), None


# --------------------------------------------------------------------------- #
# 四、攻击引擎（后台线程 + 进程池，可暂停/继续/停止/断点续跑）
# --------------------------------------------------------------------------- #
class AttackEngine(threading.Thread):
    BATCH = 24

    def __init__(self, salt, pswcheck, iters, gen_factory, start_index,
                 total, workers, msgq, tag=""):
        super().__init__(daemon=True)
        self.salt, self.pswcheck, self.iters = salt, pswcheck, iters
        self.gen_factory = gen_factory          # 返回「候选口令生成器」的函数
        self.start_index = start_index
        self.total = total
        self.workers = workers
        self.msgq = msgq
        self.tag = tag
        self._stop = threading.Event()
        self._pause = threading.Event()
        self._pause.set()                       # set = 运行中
        self.safe_done = start_index            # 安全断点（此前的都已试过）
        self.tried = 0
        self.found = None
        self.finished = False
        self.t0 = time.time()
        self.paused_time = 0.0
        self._pool = None

    # --- 控制 --- #
    def pause(self):
        if self._pause.is_set():
            self._pause.clear()
            self._paused_at = time.time()

    def resume(self):
        if not self._pause.is_set():
            self._pause.set()
            self.paused_time += time.time() - self._paused_at

    def stop(self):
        self._stop.set()
        self._pause.set()
        if self._pool is not None:
            try:
                self._pool.terminate()
            except Exception:
                pass

    @property
    def paused(self):
        return not self._pause.is_set()

    def speed(self):
        el = time.time() - self.t0 - self.paused_time
        return self.tried / el if el > 0 else 0.0

    # --- 批次生成（供 imap_unordered 拉取，天然实现背压） --- #
    def _batches(self):
        gen = self.gen_factory()
        idx = self.start_index
        if self.start_index:
            gen = itertools.islice(gen, self.start_index, None)
        while not self._stop.is_set():
            self._pause.wait()
            if self._stop.is_set():
                break
            batch = []
            for _ in range(self.BATCH):
                try:
                    cand = next(gen)
                except StopIteration:
                    break
                batch.append((idx, cand))
                idx += 1
            if not batch:
                break
            self.submitted_upto = idx
            yield batch
        self.submitted_upto = idx

    def run(self):
        ctx = mp.get_context("spawn")
        batch_starts = deque()
        done_starts = set()
        self.submitted_upto = self.start_index

        def wrapped():
            for b in self._batches():
                batch_starts.append(b[0][0])
                yield b

        try:
            self._pool = ctx.Pool(self.workers, initializer=_init_worker,
                                  initargs=(self.salt, self.pswcheck, self.iters))
            for start, size, cand in self._pool.imap_unordered(
                    _check_batch, wrapped(), chunksize=1):
                self.tried += size
                done_starts.add(start)
                while batch_starts and batch_starts[0] in done_starts:
                    done_starts.discard(batch_starts.popleft())
                self.safe_done = batch_starts[0] if batch_starts else self.submitted_upto
                if cand is not None:
                    self.found = cand
                    self.msgq.put(("found", cand, self.tried))
                    self._stop.set()
                    self._pool.terminate()
                    break
            else:
                if not self._stop.is_set():          # 自然跑完
                    self.finished = True
                    self.msgq.put(("done", None, self.tried))
        except Exception as exc:
            if not self._stop.is_set():              # 正常停止不算错误
                self.msgq.put(("error", str(exc), self.tried))
        finally:
            if self._pool is not None:
                try:
                    self._pool.terminate()
                    self._pool.join()
                except Exception:
                    pass
            self.msgq.put(("stopped", None, self.tried))


# --------------------------------------------------------------------------- #
# 五、候选口令生成器
# --------------------------------------------------------------------------- #
def enc_variants(word: bytes, try_gbk=True):
    """WinRAR 内部按 UTF-8 取密码；这里额外兼容 GBK 字典。"""
    out = [word]
    if try_gbk:
        for enc in ("utf-8", "gbk"):
            try:
                u = word.decode(enc).encode("utf-8")
            except UnicodeDecodeError:
                continue
            if u not in out:
                out.append(u)
    return out


def transform_rules(word: bytes, rules):
    """对字典单词生成变形：首字母大写 / 全大写 / 尾部追加数字等。"""
    forms = [word]
    try:
        text = word.decode("utf-8")
    except UnicodeDecodeError:
        try:
            text = word.decode("gbk")
        except UnicodeDecodeError:
            text = None
    if text is not None:
        if "cap" in rules:
            forms.append(text[:1].upper() + text[1:])
        if "upper" in rules:
            forms.append(text.upper())
        if "digit" in rules:
            forms += [text + str(d) for d in range(10)]
        if "digit2" in rules:
            forms += [text + "%02d" % d for d in range(100)]
        if "suffix" in rules:
            forms += [text + s for s in ("!", "@", "#", "123", "1234", "888", "520")]
    out = []
    for f in forms:
        f = f.encode("utf-8") if isinstance(f, str) else f
        out.append(f)
    return out


def gen_wordlist(path, rules, try_gbk=True):
    with open(path, "rb") as f:
        for raw in f:
            raw = raw.rstrip(b"\r\n")
            if not raw:
                continue
            for form in transform_rules(raw, rules):
                for v in enc_variants(form, try_gbk):
                    yield v


def gen_builtin():
    for w in BUILTIN_WEAK:
        yield w.encode("utf-8")


def gen_brute(charset, min_len, max_len, prefix="", suffix=""):
    p, s = prefix.encode("utf-8"), suffix.encode("utf-8")
    for length in range(min_len, max_len + 1):
        for combo in itertools.product(charset, repeat=length):
            yield p + "".join(combo).encode("utf-8") + s


def brute_total(charset_size, min_len, max_len):
    return sum(charset_size ** L for L in range(min_len, max_len + 1))


# --------------------------------------------------------------------------- #
# 六、图形界面
# --------------------------------------------------------------------------- #
C_BG = "#1b1c1f"
C_PANEL = "#26282c"
C_FG = "#e8e8ea"
C_SUB = "#9aa0a6"
C_ACCENT = "#4c8bf5"
C_OK = "#3ddc84"
C_WARN = "#ffb020"

CHECKPOINT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "rar5_progress.json")


def human_num(n):
    return format(int(n), ",")


def human_time(sec):
    if sec < 1:
        return "不到 1 秒"
    if sec < 60:
        return "%.0f 秒" % sec
    if sec < 3600:
        return "%.1f 分钟" % (sec / 60)
    if sec < 86400:
        return "%.1f 小时" % (sec / 3600)
    if sec < 86400 * 30:
        return "%.1f 天" % (sec / 86400)
    return "%.1f 年" % (sec / 86400 / 365)


class App:
    def __init__(self, root):
        self.root = root
        self.engine = None
        self.msgq = queue.Queue()
        self.info = None
        self.archive = tk.StringVar()
        self.mode = tk.StringVar(value="dict")
        self.workers = tk.IntVar(value=max(1, min(24, os.cpu_count() or 4)))
        self.status = tk.StringVar(value="请选择要恢复口令的压缩包")
        self.stat_line = tk.StringVar(value="")
        self.cur_cand = tk.StringVar(value="")
        self.result_text = tk.StringVar(value="")
        # 字典模式
        self.dict_path = tk.StringVar()
        self.try_gbk = tk.BooleanVar(value=True)
        self.rule_vars = {k: tk.BooleanVar(value=False) for k in
                          ("cap", "upper", "digit", "digit2", "suffix")}
        # 暴力模式
        self.use_digit = tk.BooleanVar(value=True)
        self.use_lower = tk.BooleanVar(value=False)
        self.use_upper = tk.BooleanVar(value=False)
        self.use_symbol = tk.BooleanVar(value=False)
        self.custom_chars = tk.StringVar()
        self.min_len = tk.IntVar(value=6)
        self.max_len = tk.IntVar(value=6)
        self.prefix = tk.StringVar()
        self.suffix = tk.StringVar()
        self.est_line = tk.StringVar(value="")
        self._build()
        self._poll()

    # ---------------- 样式 ---------------- #
    def _style(self):
        st = ttk.Style()
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure(".", background=C_BG, foreground=C_FG, fieldbackground=C_PANEL)
        st.configure("TFrame", background=C_BG)
        st.configure("Panel.TFrame", background=C_PANEL, relief="flat")
        st.configure("TLabel", background=C_BG, foreground=C_FG, font=("Microsoft YaHei UI", 10))
        st.configure("Sub.TLabel", background=C_BG, foreground=C_SUB, font=("Microsoft YaHei UI", 9))
        st.configure("Panel.TLabel", background=C_PANEL, foreground=C_FG,
                     font=("Microsoft YaHei UI", 10))
        st.configure("H1.TLabel", background=C_BG, foreground=C_FG,
                     font=("Microsoft YaHei UI", 15, "bold"))
        st.configure("Big.TLabel", background=C_BG, foreground=C_OK,
                     font=("Consolas", 16, "bold"))
        st.configure("TCheckbutton", background=C_BG, foreground=C_FG,
                     font=("Microsoft YaHei UI", 10))
        st.map("TCheckbutton", background=[("active", C_BG)])
        st.configure("TRadiobutton", background=C_BG, foreground=C_FG,
                     font=("Microsoft YaHei UI", 10))
        st.map("TRadiobutton", background=[("active", C_BG)])
        st.configure("TNotebook", background=C_BG, borderwidth=0)
        st.configure("TNotebook.Tab", background=C_PANEL, foreground=C_SUB,
                     padding=(16, 8), font=("Microsoft YaHei UI", 10))
        st.map("TNotebook.Tab", background=[("selected", C_BG)], foreground=[("selected", C_ACCENT)])
        st.configure("TEntry", fieldbackground=C_PANEL, foreground=C_FG,
                     insertcolor=C_FG, bordercolor="#3a3d42")
        st.configure("TSpinbox", fieldbackground=C_PANEL, foreground=C_FG,
                     insertcolor=C_FG, arrowcolor=C_FG)
        st.configure("TCombobox", fieldbackground=C_PANEL, foreground=C_FG,
                     background=C_PANEL, arrowcolor=C_FG)
        st.configure("Accent.TButton", background=C_ACCENT, foreground="#ffffff",
                     font=("Microsoft YaHei UI", 10, "bold"), padding=(14, 7), borderwidth=0)
        st.map("Accent.TButton", background=[("active", "#3d78d8"), ("disabled", "#3a3d42")])
        st.configure("TButton", background=C_PANEL, foreground=C_FG,
                     font=("Microsoft YaHei UI", 10), padding=(12, 7), borderwidth=0)
        st.map("TButton", background=[("active", "#33363b")])
        st.configure("TProgressbar", background=C_ACCENT, troughcolor=C_PANEL,
                     bordercolor=C_PANEL, lightcolor=C_ACCENT, darkcolor=C_ACCENT)

    # ---------------- 界面 ---------------- #
    def _build(self):
        self.root.title("RAR5 口令恢复工具 · 图形界面版")
        self.root.geometry("980x760")
        self.root.minsize(900, 700)
        self.root.configure(bg=C_BG)
        self._style()

        pad = dict(padx=16, pady=6)

        # 标题
        head = ttk.Frame(self.root)
        head.pack(fill="x", **pad)
        ttk.Label(head, text="RAR5 口令恢复工具", style="H1.TLabel").pack(side="left")
        ttk.Label(head, text="  仅用于找回你自己文件的口令；算法与 UnRAR / hashcat 一致",
                  style="Sub.TLabel").pack(side="left", pady=(6, 0))

        # 文件选择
        fbox = ttk.Frame(self.root)
        fbox.pack(fill="x", **pad)
        ttk.Label(fbox, text="目标文件").pack(side="left")
        ttk.Entry(fbox, textvariable=self.archive).pack(side="left", fill="x", expand=True, padx=8)
        ttk.Button(fbox, text="选择文件…", command=self.pick_file).pack(side="left")
        ttk.Button(fbox, text="解析加密头", command=self.load_info).pack(side="left", padx=6)

        # 加密头信息
        self.info_lbl = ttk.Label(self.root, text="尚未解析", style="Sub.TLabel",
                                  justify="left")
        self.info_lbl.pack(fill="x", padx=16)

        # 模式页签
        nb = ttk.Notebook(self.root)
        nb.pack(fill="both", expand=True, **pad)
        self.nb = nb
        self._tab_dict(nb)
        self._tab_brute(nb)
        self._tab_quick(nb)
        nb.bind("<<NotebookTabChanged>>", self.on_tab)

        # 运行控制
        ctl = ttk.Frame(self.root)
        ctl.pack(fill="x", **pad)
        self.btn_start = ttk.Button(ctl, text="▶ 开始", style="Accent.TButton",
                                    command=self.start)
        self.btn_start.pack(side="left")
        self.btn_pause = ttk.Button(ctl, text="⏸ 暂停", command=self.toggle_pause,
                                    state="disabled")
        self.btn_pause.pack(side="left", padx=6)
        self.btn_stop = ttk.Button(ctl, text="■ 停止", command=self.stop, state="disabled")
        self.btn_stop.pack(side="left")
        ttk.Label(ctl, text="并行进程").pack(side="left", padx=(24, 6))
        ttk.Spinbox(ctl, from_=1, to=max(2, os.cpu_count() or 4), width=4,
                    textvariable=self.workers, command=self.update_estimate).pack(side="left")
        ttk.Label(ctl, text="（本机 %d 线程）" % (os.cpu_count() or 1), style="Sub.TLabel").pack(side="left")

        # 进度
        prog = ttk.Frame(self.root)
        prog.pack(fill="x", **pad)
        self.pbar = ttk.Progressbar(prog, mode="determinate", maximum=1000)
        self.pbar.pack(fill="x")
        ttk.Label(prog, textvariable=self.stat_line).pack(anchor="w", pady=(6, 0))
        ttk.Label(prog, textvariable=self.cur_cand, style="Sub.TLabel").pack(anchor="w")

        # 结果
        res = ttk.Frame(self.root)
        res.pack(fill="x", **pad)
        ttk.Label(res, text="结果：").pack(side="left")
        ttk.Label(res, textvariable=self.result_text, style="Big.TLabel").pack(side="left")
        ttk.Button(res, text="复制口令", command=self.copy_result).pack(side="left", padx=10)

        # 日志
        self.log = tk.Text(self.root, height=8, bg=C_PANEL, fg=C_SUB,
                           insertbackground=C_FG, relief="flat",
                           font=("Consolas", 9), wrap="word")
        self.log.pack(fill="both", expand=True, padx=16, pady=(0, 12))
        self.log.configure(state="disabled")
        self.say("就绪。后端：%s" % BACKEND)
        self.say("提示：暴力枚举请先看清「预计耗时」，长时间任务可随时暂停/停止，进度会保存。")

    def _tab_dict(self, nb):
        f = ttk.Frame(nb)
        nb.add(f, text=" 字典攻击 ")
        row = ttk.Frame(f); row.pack(fill="x", padx=14, pady=(14, 6))
        ttk.Label(row, text="字典文件").pack(side="left")
        ttk.Entry(row, textvariable=self.dict_path).pack(side="left", fill="x",
                                                         expand=True, padx=8)
        ttk.Button(row, text="选择…", command=self.pick_dict).pack(side="left")
        ttk.Label(f, text="变形规则（可多选，逐条叠加）", style="Sub.TLabel").pack(anchor="w", padx=14, pady=(10, 2))
        g = ttk.Frame(f); g.pack(fill="x", padx=14)
        for key, label in (("cap", "首字母大写"), ("upper", "全部大写"),
                           ("digit", "尾部追加 0-9"), ("digit2", "尾部追加 00-99"),
                           ("suffix", "尾部追加 123/888/520/!")):
            ttk.Checkbutton(g, text=label, variable=self.rule_vars[key]).pack(side="left", padx=(0, 14))
        ttk.Checkbutton(f, text="额外把 GBK 词条按 UTF-8 再试一遍（中文口令建议勾选）",
                        variable=self.try_gbk).pack(anchor="w", padx=14, pady=10)
        ttk.Label(f, text="说明：字典里请一行一个候选口令；先用小字典试，再逐步换大字典。",
                  style="Sub.TLabel").pack(anchor="w", padx=14, pady=4)

    def _tab_brute(self, nb):
        f = ttk.Frame(nb)
        nb.add(f, text=" 暴力枚举 ")
        ttk.Label(f, text="字符类型（可多选）", style="Sub.TLabel").pack(anchor="w", padx=14, pady=(14, 2))
        g = ttk.Frame(f); g.pack(fill="x", padx=14)
        items = (("数字 0-9", self.use_digit), ("小写 a-z", self.use_lower),
                 ("大写 A-Z", self.use_upper), ("符号 !@#$…", self.use_symbol))
        for label, var in items:
            ttk.Checkbutton(g, text=label, variable=var,
                            command=self.update_estimate).pack(side="left", padx=(0, 14))
        r = ttk.Frame(f); r.pack(fill="x", padx=14, pady=8)
        ttk.Label(r, text="自定义字符").pack(side="left")
        e = ttk.Entry(r, textvariable=self.custom_chars, width=30)
        e.pack(side="left", padx=8)
        e.bind("<KeyRelease>", lambda _e: self.update_estimate())

        lr = ttk.Frame(f); lr.pack(fill="x", padx=14, pady=6)
        ttk.Label(lr, text="密码位数：从").pack(side="left")
        ttk.Spinbox(lr, from_=1, to=20, width=5, textvariable=self.min_len,
                    command=self.update_estimate).pack(side="left", padx=6)
        ttk.Label(lr, text="到").pack(side="left")
        ttk.Spinbox(lr, from_=1, to=20, width=5, textvariable=self.max_len,
                    command=self.update_estimate).pack(side="left", padx=6)
        ttk.Label(lr, text="位").pack(side="left")
        ttk.Label(lr, text="   固定前缀").pack(side="left", padx=(20, 4))
        ttk.Entry(lr, textvariable=self.prefix, width=12).pack(side="left")
        ttk.Label(lr, text="固定后缀").pack(side="left", padx=(12, 4))
        ttk.Entry(lr, textvariable=self.suffix, width=12).pack(side="left")

        pr = ttk.Frame(f); pr.pack(fill="x", padx=14, pady=8)
        ttk.Label(pr, text="常用预设").pack(side="left")
        self.preset = ttk.Combobox(pr, state="readonly", width=22, values=[
            "6 位纯数字", "1-6 位纯数字", "4-8 位纯数字",
            "1-5 位小写字母", "1-6 位小写+数字", "1-4 位全字符", "1-6 位全字符",
        ])
        self.preset.pack(side="left", padx=8)
        self.preset.bind("<<ComboboxSelected>>", self.apply_preset)
        ttk.Button(pr, text="重新预估", command=self.update_estimate).pack(side="left")
        ttk.Label(f, textvariable=self.est_line, style="Sub.TLabel",
                  justify="left").pack(anchor="w", padx=14, pady=(6, 10))
        self.update_estimate()

    def _tab_quick(self, nb):
        f = ttk.Frame(nb)
        nb.add(f, text=" 内置弱口令 ")
        ttk.Label(f, text="先跑一遍最常见的弱口令（约 %d 条，几秒内完成）。" % len(BUILTIN_WEAK),
                  style="Sub.TLabel").pack(anchor="w", padx=14, pady=14)
        ttk.Label(f, text="包含 123456 / 888888 / 5201314 / 1qaz2wsx 这类常见口令。\n"
                          "如果没有命中，请改用字典攻击或暴力枚举。",
                  style="Sub.TLabel", justify="left").pack(anchor="w", padx=14)

    # ---------------- 交互 ---------------- #
    def on_tab(self, *_):
        try:
            idx = self.nb.index(self.nb.select())
        except Exception:
            return
        self.mode.set(("dict", "brute", "quick")[idx])

    def say(self, msg):
        stamp = time.strftime("%H:%M:%S")
        self.log.configure(state="normal")
        self.log.insert("end", "[%s] %s\n" % (stamp, msg))
        self.log.see("end")
        self.log.configure(state="disabled")

    def pick_file(self):
        p = filedialog.askopenfilename(
            title="选择 RAR5 加密包",
            filetypes=[("RAR / 伪装文件", "*.rar *.txt *.zip *.bin *.*"), ("所有文件", "*.*")])
        if p:
            self.archive.set(p)
            self.load_info()

    def pick_dict(self):
        p = filedialog.askopenfilename(title="选择字典文件",
                                       filetypes=[("文本字典", "*.txt *.dic *.lst *.*")])
        if p:
            self.dict_path.set(p)
            try:
                with open(p, "rb") as fh:
                    n = sum(1 for _ in fh)
                self.say("字典已载入：%s（%s 行）" % (os.path.basename(p), human_num(n)))
            except Exception as exc:
                self.say("读取字典失败：%s" % exc)

    def load_info(self):
        path = self.archive.get().strip()
        if not path or not os.path.exists(path):
            messagebox.showwarning("提示", "请先选择存在的文件")
            return
        try:
            self.info = parse_crypt_header(path)
        except Exception as exc:
            self.info = None
            self.info_lbl.configure(text="解析失败：%s" % exc, foreground=C_WARN)
            return
        i = self.info
        self.info_lbl.configure(
            foreground=C_SUB,
            text=("加密头：RAR5 全加密(-hp) | PBKDF2-HMAC-SHA256 迭代 %s 次 | 头完整性 %s\n"
                  "Salt = %s\n校验值 = %s")
                 % (human_num(1 << i["lg2"]),
                    "有效" if i["header_ok"] else "异常",
                    i["salt"].hex(), i["pswcheck"].hex()))
        self.say("已解析加密头：迭代 2^%d = %s 次，Salt=%s"
                 % (i["lg2"], human_num(1 << i["lg2"]), i["salt"].hex()))

    def charset(self):
        cs = ""
        if self.use_digit.get():
            cs += CH_DIGIT
        if self.use_lower.get():
            cs += CH_LOWER
        if self.use_upper.get():
            cs += CH_UPPER
        if self.use_symbol.get():
            cs += CH_SYMBOL
        cs += self.custom_chars.get()
        # 去重保序
        seen, out = set(), ""
        for c in cs:
            if c not in seen:
                seen.add(c); out += c
        return out

    def update_estimate(self, *_):
        cs = self.charset()
        try:
            mn, mx = int(self.min_len.get()), int(self.max_len.get())
        except Exception:
            return
        if not cs or mn > mx:
            self.est_line.set("请选择字符类型，并保证「位数」区间合法。")
            return
        total = brute_total(len(cs), mn, mx)
        w = max(1, int(self.workers.get()))
        sec = total * MS_PER_CANDIDATE / 1000.0 / w
        txt = ("字符集 %d 个：%s\n候选总数 ≈ %s 个 | 按 %d 进程预估耗时 ≈ %s"
               % (len(cs), cs if len(cs) <= 48 else cs[:48] + "…",
                  human_num(total), w, human_time(sec)))
        if total > 2 * 10 ** 12:
            txt += "\n⚠ 空间过大，实际上无法穷尽，请缩小位数或字符类型。"
            self.est_line.set(txt)
            return
        self.est_line.set(txt)

    def apply_preset(self, *_):
        name = self.preset.get()
        presets = {
            "6 位纯数字": (True, False, False, False, 6, 6),
            "1-6 位纯数字": (True, False, False, False, 1, 6),
            "4-8 位纯数字": (True, False, False, False, 4, 8),
            "1-5 位小写字母": (False, True, False, False, 1, 5),
            "1-6 位小写+数字": (True, True, False, False, 1, 6),
            "1-4 位全字符": (True, True, True, True, 1, 4),
            "1-6 位全字符": (True, True, True, True, 1, 6),
        }
        if name not in presets:
            return
        d, l, u, s, mn, mx = presets[name]
        self.use_digit.set(d); self.use_lower.set(l)
        self.use_upper.set(u); self.use_symbol.set(s)
        self.min_len.set(mn); self.max_len.set(mx)
        self.update_estimate()

    # ---------------- 断点续跑 ---------------- #
    def sig(self):
        if self.mode.get() == "brute":
            return {"m": "brute", "cs": self.charset(), "min": int(self.min_len.get()),
                    "max": int(self.max_len.get()), "pre": self.prefix.get(),
                    "suf": self.suffix.get()}
        if self.mode.get() == "dict":
            return {"m": "dict", "path": self.dict_path.get(),
                    "rules": sorted(k for k, v in self.rule_vars.items() if v.get())}
        return {"m": "quick"}

    def load_checkpoint(self, sig):
        try:
            with open(CHECKPOINT, "r", encoding="utf-8") as fh:
                data = json.load(fh)
        except Exception:
            return None
        if data.get("archive") == self.archive.get() and data.get("sig") == sig:
            return int(data.get("done", 0))
        return None

    def save_checkpoint(self, done, sig):
        try:
            with open(CHECKPOINT, "w", encoding="utf-8") as fh:
                json.dump({"archive": self.archive.get(), "sig": sig,
                           "done": int(done), "time": time.strftime("%Y-%m-%d %H:%M:%S")}, fh)
        except Exception:
            pass

    # ---------------- 运行控制 ---------------- #
    def start(self):
        if self.engine and self.engine.is_alive():
            return
        path = self.archive.get().strip()
        if not path or not os.path.exists(path):
            messagebox.showwarning("提示", "请先选择压缩包文件")
            return
        if self.info is None or not self.info.get("header_ok"):
            self.load_info()
            if self.info is None:
                return
        if self.mode.get() == "dict" and not os.path.exists(self.dict_path.get() or ""):
            messagebox.showwarning("提示", "请选择字典文件")
            return
        if self.mode.get() == "brute":
            if not self.charset():
                messagebox.showwarning("提示", "请至少选择一种字符类型")
                return
            if int(self.min_len.get()) > int(self.max_len.get()):
                messagebox.showwarning("提示", "位数区间不合法")
                return

        sig = self.sig()
        mn, mx = int(self.min_len.get()), int(self.max_len.get())
        if self.mode.get() == "brute":
            total = brute_total(len(self.charset()), mn, mx)
            factory = lambda: gen_brute(self.charset(), mn, mx,
                                        self.prefix.get(), self.suffix.get())
        elif self.mode.get() == "dict":
            rules = {k for k, v in self.rule_vars.items() if v.get()}
            gbk = self.try_gbk.get()
            factory = lambda: gen_wordlist(self.dict_path.get(), rules, gbk)
            total = None
        else:
            total = len(BUILTIN_WEAK)
            factory = gen_builtin

        start_index = 0
        ck = self.load_checkpoint(sig)
        if ck:
            if messagebox.askyesno("发现进度",
                                   "检测到上次未跑完的进度（已试 %s 个）。\n要从断点继续吗？\n"
                                   "选「否」将从 0 重新开始。" % human_num(ck)):
                start_index = ck
            else:
                start_index = 0
                self.save_checkpoint(0, sig)

        self.result_text.set("")
        self.engine = AttackEngine(self.info["salt"], self.info["pswcheck"],
                                   self.info["iters"], factory, start_index,
                                   total, max(1, int(self.workers.get())), self.msgq)
        self.engine_sig = sig
        self.engine.start()
        self.btn_start.configure(state="disabled")
        self.btn_pause.configure(state="normal", text="⏸ 暂停")
        self.btn_stop.configure(state="normal")
        self.say("开始：模式=%s，起始序号=%s" % (self.mode.get(), human_num(start_index)))
        self.root.after(20000, self._autosave)
        if total:
            self.pbar.configure(mode="determinate")
            self.pbar["value"] = (start_index / total * 1000) if total else 0
        else:
            self.pbar.configure(mode="indeterminate")
            self.pbar.start(40)

    def toggle_pause(self):
        if not (self.engine and self.engine.is_alive()):
            return
        if self.engine.paused:
            self.engine.resume()
            self.btn_pause.configure(text="⏸ 暂停")
            self.root.after(20000, self._autosave)
            self.say("已继续。")
        else:
            self.engine.pause()
            self.btn_pause.configure(text="▶ 继续")
            self.save_checkpoint(self.engine.safe_done, self.engine_sig)
            self.say("已暂停，进度已保存（序号 %s）。" % human_num(self.engine.safe_done))

    def _autosave(self):
        if self.engine and self.engine.is_alive() and not self.engine.paused:
            self.save_checkpoint(self.engine.safe_done, self.engine_sig)
            self.root.after(20000, self._autosave)

    def stop(self):
        if self.engine and self.engine.is_alive():
            self.engine.stop()
            self.save_checkpoint(self.engine.safe_done, self.engine_sig)
            self.say("已停止，进度已保存（序号 %s）。下次「开始」可继续。"
                     % human_num(self.engine.safe_done))
        self._reset_buttons()

    def _reset_buttons(self):
        self.btn_start.configure(state="normal")
        self.btn_pause.configure(state="disabled", text="⏸ 暂停")
        self.btn_stop.configure(state="disabled")
        try:
            self.pbar.stop()
        except Exception:
            pass

    def copy_result(self):
        txt = self.result_text.get().strip()
        if not txt:
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(txt)
        self.say("口令已复制到剪贴板。")

    # ---------------- 事件轮询 ---------------- #
    def _poll(self):
        updated = False
        try:
            while True:
                kind, payload, tried = self.msgq.get_nowait()
                updated = True
                if kind == "found":
                    self.result_text.set(payload.decode("utf-8", "replace"))
                    self.say("★ 找到口令：%s" % payload.decode("utf-8", "replace"))
                    out = os.path.splitext(self.archive.get())[0] + ".password.txt"
                    try:
                        with open(out, "w", encoding="utf-8") as fh:
                            fh.write(self.result_text.get() + "\n")
                        self.say("已写入 %s" % out)
                    except Exception:
                        pass
                    self.save_checkpoint(0, self.engine_sig)
                    self._reset_buttons()
                    messagebox.showinfo("成功", "找到口令：%s\n\n已写入 %s"
                                        % (self.result_text.get(), out))
                elif kind == "done":
                    self.say("候选空间已穷尽，未找到口令。建议扩大范围或更换字典。")
                    self.pbar["value"] = 1000
                    self._reset_buttons()
                elif kind == "error":
                    self.say("出错：%s" % payload)
                    self._reset_buttons()
                elif kind == "stopped":
                    self._reset_buttons()
        except queue.Empty:
            pass

        if self.engine and self.engine.is_alive():
            e = self.engine
            spd = e.speed()
            el = time.time() - e.t0 - e.paused_time
            left = ""
            if e.total:
                pct = min(1.0, (e.start_index + e.tried) / e.total)
                self.pbar["value"] = int(pct * 1000)
                if spd > 0:
                    left = " | 进度 %.4f%% | 剩余约 %s"
                    left = left % (pct * 100, human_time((1 - pct) * e.total / spd))
            else:
                left = " | 已试 %s 个" % human_num(e.tried)
            self.stat_line.set("已试 %s 个 | 速度 %.0f 个/秒 | 已用 %s%s%s"
                               % (human_num(e.tried), spd, human_time(el), left,
                                  " | ⏸ 已暂停" if e.paused else ""))
        self.root.after(120, self._poll)

    def on_close(self):
        if self.engine and self.engine.is_alive():
            self.engine.stop()
            self.save_checkpoint(self.engine.safe_done, self.engine_sig)
        self.root.destroy()


# --------------------------------------------------------------------------- #
# 七、命令行自检 / 无界面引擎测试
# --------------------------------------------------------------------------- #
def cli_selftest():
    salt = bytes.fromhex("38466361001011015181344360681307")
    expect = bytes.fromhex("cc7a30583e62676a")
    got = derive_pswcheck(b"hashcat", salt, (1 << 15) + 32)
    print("后端       : %s" % BACKEND)
    print("自检       : 期望 %s / 实际 %s -> %s"
          % (expect.hex(), got.hex(), "通过" if got == expect else "失败"))
    t0 = time.perf_counter()
    for _ in range(5):
        derive_pswcheck(b"hashcat", salt, (1 << 15) + 32)
    one = (time.perf_counter() - t0) / 5
    n = os.cpu_count() or 4
    print("单核速度   : %.2f ms/个 -> 约 %.0f 个/秒（%d 线程并行约 %.0f 个/秒）"
          % (one * 1000, 1 / one, n, n / one))


def cli_engine_test(path):
    info = parse_crypt_header(path)
    print("加密头: 迭代 2^%d, Salt=%s, 校验值=%s, 完整性=%s"
          % (info["lg2"], info["salt"].hex(), info["pswcheck"].hex(),
             "有效" if info["header_ok"] else "异常"))
    q = queue.Queue()
    eng = AttackEngine(info["salt"], info["pswcheck"], info["iters"],
                       gen_builtin, 0, len(BUILTIN_WEAK),
                       max(1, min(8, os.cpu_count() or 4)), q, tag="engine-test")
    eng.start()
    eng.join()
    while not q.empty():
        print("事件:", q.get())
    print("引擎跑通：已试 %d 个，速度 %.0f 个/秒" % (eng.tried, eng.speed()))


def main():
    ap = argparse.ArgumentParser(description="RAR5 口令恢复工具（图形界面）")
    ap.add_argument("--selftest", action="store_true", help="算法自检 + 测速")
    ap.add_argument("--engine-test", metavar="ARCHIVE", help="无界面跑一次内置弱口令")
    args = ap.parse_args()
    mp.freeze_support()
    if args.selftest:
        cli_selftest()
        return
    if args.engine_test:
        cli_engine_test(args.engine_test)
        return
    root = tk.Tk()
    app = App(root)
    root.protocol("WM_DELETE_WINDOW", app.on_close)
    root.mainloop()


if __name__ == "__main__":
    main()
