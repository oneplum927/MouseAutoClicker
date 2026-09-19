"""
MouseAutoClicker —— Windows 鼠标连点器 (v1.1)

技术栈: Python 3 + tkinter(界面) + pynput(键鼠) / pyautogui(备用点击后端)
定位  : 合法授权场景下的桌面自动化工具（自动化测试、重复性办公操作等）
边界  : 不做驱动级模拟、不隐藏进程、不绕过安全软件、不注入其他进程。

热键  : F6 开始/停止   F7 记录坐标/添加序列点   F8 退出程序
        热键优先使用 Win32 RegisterHotKey（系统消息机制，兼容性优于
        低级键盘钩子），失败时回退 pynput GlobalHotKeys，状态栏如实显示。

v1.1 相对 v1.0 的变化:
  - 热键重构为 RegisterHotKey 主机制（修复部分环境下全局热键静默失效）
  - 新增四角急停保护：光标贴近屏幕四角自动停止（可开关，默认开）
  - 新增配置持久化：参数自动保存/加载（%APPDATA%\\MouseAutoClicker\\config.json）
  - 新增坐标序列模式：多个位置按顺序循环点击
  - 新增运行统计：实际 CPS 与运行时长
  - 修复：上一次任务未结束时按开始静默无反馈；pyautogui 坐标重复读取
"""
from __future__ import annotations

import argparse
import ctypes
import json
import os
import random
import sys
import threading
import time
import tkinter as tk
from tkinter import messagebox, ttk

APP_NAME = "鼠标连点器"
VERSION = "1.1"

# Win32 热键
WM_HOTKEY = 0x0312
WM_QUIT = 0x0012
MOD_NOREPEAT = 0x4000
VK_F6, VK_F7, VK_F8 = 0x75, 0x76, 0x77

# 四角急停判定边距（物理像素）
CORNER_MARGIN = 5

BACKEND = None
_mouse_controller = None
_pynput_mouse = None
_pynput_keyboard = None
pyautogui = None

CONFIG_DIR = os.path.join(
    os.environ.get("APPDATA", os.path.expanduser("~")), "MouseAutoClicker"
)
CONFIG_FILE = os.path.join(CONFIG_DIR, "config.json")


def init_backend() -> bool:
    """初始化点击后端，返回是否成功。重复调用安全。"""
    global BACKEND, _mouse_controller, _pynput_mouse, _pynput_keyboard, pyautogui
    if BACKEND is not None:
        return True
    try:
        from pynput import keyboard, mouse

        _pynput_mouse = mouse
        _pynput_keyboard = keyboard
        _mouse_controller = mouse.Controller()
        BACKEND = "pynput"
        return True
    except Exception:
        pass
    try:
        import pyautogui as _pg

        _pg.FAILSAFE = False
        _pg.PAUSE = 0
        pyautogui = _pg
        BACKEND = "pyautogui"
        return True
    except Exception:
        return False


BTN_ITEMS = [("左键", "left"), ("右键", "right"), ("中键", "middle")]
TYPE_ITEMS = [("单击", "single"), ("双击", "double")]
POS_ITEMS = [
    ("跟随鼠标当前位置", "follow"),
    ("锁定启动时的位置", "locked"),
    ("使用固定坐标", "fixed"),
    ("坐标序列（按顺序循环）", "seq"),
]


def resolve_button(name: str):
    """把 'left'/'right'/'middle' 转成当前后端认识的按键对象。

    pynput 的 Controller.press() 只接受 Button 枚举，传字符串会直接抛
    AttributeError: 'str' object has no attribute 'value'。
    """
    if BACKEND == "pynput" and _pynput_mouse is not None:
        return getattr(_pynput_mouse.Button, name)
    return name


def _dpi_aware() -> None:
    """声明 DPI 感知，保证界面清晰且与物理像素坐标一致。"""
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


def screen_size() -> tuple[int, int]:
    """物理像素屏幕尺寸（进程已声明 DPI 感知）。"""
    try:
        u = ctypes.windll.user32
        return int(u.GetSystemMetrics(0)), int(u.GetSystemMetrics(1))
    except Exception:
        return (1920, 1080)


class AutoClickerApp:
    """主界面 + 点击线程调度。"""

    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.cfg: dict = {}
        self.done = 0
        self.running = False
        self.last_err: str | None = None
        self.stop_reason = ""
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._hotkey_tid = 0
        self._hotkey_listener = None
        self._last_shown = -1
        self.seq_points: list[list[int]] = []
        self._samples: list[tuple[float, int]] = []
        self._t0 = 0.0

        root.title(f"{APP_NAME} v{VERSION}")
        root.resizable(True, True)
        root.minsize(640, 480)
        root.protocol("WM_DELETE_WINDOW", self.on_close)

        self._build_ui()
        self._load_config()
        self._sync_states()
        self._setup_hotkeys()
        root.columnconfigure(0, weight=1)
        root.rowconfigure(4, weight=1)
        root.after(80, self._tick)

    # ------------------------------------------------------------------ UI
    def _build_ui(self) -> None:
        pad = {"padx": 6, "pady": 3}

        f_speed = ttk.LabelFrame(self.root, text="点击速度")
        f_speed.grid(row=0, column=0, sticky="ew", padx=8, pady=(8, 4))

        self.v_speed_mode = tk.StringVar(value="interval")
        ttk.Radiobutton(
            f_speed, text="固定间隔 (毫秒)", value="interval",
            variable=self.v_speed_mode, command=self._sync_states,
        ).grid(row=0, column=0, sticky="w", **pad)
        self.v_interval = tk.StringVar(value="100")
        self.e_interval = ttk.Entry(f_speed, textvariable=self.v_interval, width=8)
        self.e_interval.grid(row=0, column=1, **pad)
        ttk.Label(f_speed, text="± 抖动(ms)").grid(
            row=0, column=2, sticky="e", **pad)
        self.v_jitter = tk.StringVar(value="0")
        self.e_jitter = ttk.Entry(f_speed, textvariable=self.v_jitter, width=8)
        self.e_jitter.grid(row=0, column=3, **pad)

        ttk.Radiobutton(
            f_speed, text="随机 CPS (每秒点击次数，区间内随机)", value="cps",
            variable=self.v_speed_mode, command=self._sync_states,
        ).grid(row=1, column=0, columnspan=2, sticky="w", **pad)
        self.v_cps_min = tk.StringVar(value="8")
        self.v_cps_max = tk.StringVar(value="12")
        self.e_cps_min = ttk.Entry(f_speed, textvariable=self.v_cps_min, width=8)
        self.e_cps_min.grid(row=1, column=2, **pad)
        self.e_cps_max = ttk.Entry(f_speed, textvariable=self.v_cps_max, width=8)
        self.e_cps_max.grid(row=1, column=3, **pad)
        ttk.Label(f_speed, text="最小 / 最大").grid(row=1, column=4, sticky="w", **pad)

        f_cnt = ttk.LabelFrame(self.root, text="点击次数")
        f_cnt.grid(row=1, column=0, sticky="ew", padx=8, pady=4)
        ttk.Label(f_cnt, text="目标次数 (0 = 无限)").grid(row=0, column=0, sticky="w", **pad)
        self.v_target = tk.StringVar(value="0")
        ttk.Entry(f_cnt, textvariable=self.v_target, width=10).grid(row=0, column=1, **pad)
        ttk.Label(f_cnt, text="启动延迟 (ms)").grid(row=0, column=2, sticky="e", **pad)
        self.v_delay = tk.StringVar(value="1000")
        ttk.Entry(f_cnt, textvariable=self.v_delay, width=10).grid(row=0, column=3, **pad)

        f_btn = ttk.LabelFrame(self.root, text="鼠标按键与点击类型")
        f_btn.grid(row=2, column=0, sticky="ew", padx=8, pady=4)
        ttk.Label(f_btn, text="按键").grid(row=0, column=0, sticky="w", **pad)
        self.v_button = tk.StringVar(value="左键")
        ttk.Combobox(
            f_btn, textvariable=self.v_button, state="readonly", width=6,
            values=[n for n, _ in BTN_ITEMS],
        ).grid(row=0, column=1, **pad)
        ttk.Label(f_btn, text="类型").grid(row=0, column=2, sticky="e", **pad)
        self.v_type = tk.StringVar(value="单击")
        self.cb_type = ttk.Combobox(
            f_btn, textvariable=self.v_type, state="readonly", width=6,
            values=list(TYPE_ITEMS),
        )
        self.cb_type.grid(row=0, column=3, **pad)
        self.cb_type.bind("<<ComboboxSelected>>", lambda _e: self._sync_states())
        ttk.Label(f_btn, text="双击间隔 (ms)").grid(row=0, column=4, sticky="e", **pad)
        self.v_dbl = tk.StringVar(value="80")
        self.e_dbl = ttk.Entry(f_btn, textvariable=self.v_dbl, width=8)
        self.e_dbl.grid(row=0, column=5, **pad)

        f_pos = ttk.LabelFrame(self.root, text="点击位置")
        f_pos.grid(row=3, column=0, sticky="ew", padx=8, pady=4)
        self.v_pos_mode = tk.StringVar(value="follow")
        for i, (label, value) in enumerate(POS_ITEMS):
            ttk.Radiobutton(
                f_pos, text=label, value=value,
                variable=self.v_pos_mode, command=self._sync_states,
            ).grid(row=i, column=0, sticky="w", **pad)
        ttk.Label(f_pos, text="X").grid(row=0, column=1, sticky="e", **pad)
        self.v_x = tk.StringVar(value="0")
        self.e_x = ttk.Entry(f_pos, textvariable=self.v_x, width=8)
        self.e_x.grid(row=0, column=2, **pad)
        ttk.Label(f_pos, text="Y").grid(row=1, column=1, sticky="e", **pad)
        self.v_y = tk.StringVar(value="0")
        self.e_y = ttk.Entry(f_pos, textvariable=self.v_y, width=8)
        self.e_y.grid(row=1, column=2, **pad)
        self.btn_rec = ttk.Button(
            f_pos, text="记录当前坐标 (F7)", command=self.record_position)
        self.btn_rec.grid(row=2, column=1, columnspan=2, sticky="ew", **pad)

        f_seq = ttk.LabelFrame(self.root, text="坐标序列（按顺序循环点击）")
        f_seq.grid(row=4, column=0, sticky="ewsn", padx=8, pady=4)
        self.lb_seq = tk.Listbox(f_seq, height=5, activestyle="dotbox")
        self.lb_seq.grid(row=0, column=0, columnspan=3, sticky="ewsn", **pad)
        sb = ttk.Scrollbar(f_seq, orient="vertical", command=self.lb_seq.yview)
        sb.grid(row=0, column=3, sticky="ns", **pad)
        self.lb_seq.configure(yscrollcommand=sb.set)
        self.btn_seq_add = ttk.Button(
            f_seq, text="添加当前坐标 (F7)", command=self.record_position)
        self.btn_seq_add.grid(row=1, column=0, sticky="ew", **pad)
        self.btn_seq_del = ttk.Button(
            f_seq, text="删除选中", command=self._seq_delete)
        self.btn_seq_del.grid(row=1, column=1, sticky="ew", **pad)
        self.btn_seq_clr = ttk.Button(f_seq, text="清空", command=self._seq_clear)
        self.btn_seq_clr.grid(row=1, column=2, sticky="ew", **pad)
        f_seq.columnconfigure(0, weight=1)
        f_seq.columnconfigure(1, weight=1)
        f_seq.columnconfigure(2, weight=1)
        f_seq.rowconfigure(0, weight=1)

        f_st = ttk.LabelFrame(self.root, text="状态")
        f_st.grid(row=5, column=0, sticky="ew", padx=8, pady=4)
        self.v_status = tk.StringVar(value="已停止")
        ttk.Label(
            f_st, textvariable=self.v_status,
            font=("Microsoft YaHei UI", 12, "bold"), foreground="#b00020",
        ).grid(row=0, column=0, sticky="w", **pad)
        self.v_count = tk.StringVar(value="已执行: 0 次")
        ttk.Label(f_st, textvariable=self.v_count, font=("Consolas", 11)).grid(
            row=0, column=1, sticky="e", padx=20, pady=3)
        self.v_backend = tk.StringVar(value="")
        ttk.Label(f_st, textvariable=self.v_backend, foreground="#666").grid(
            row=1, column=0, columnspan=2, sticky="w", **pad)
        self.v_hint = tk.StringVar(value="")
        ttk.Label(f_st, textvariable=self.v_hint, foreground="#0a7a3d").grid(
            row=2, column=0, columnspan=2, sticky="w", **pad)

        f_act = ttk.Frame(self.root)
        f_act.grid(row=6, column=0, sticky="ew", padx=8, pady=(4, 8))
        self.btn_start = ttk.Button(f_act, text="开始 (F6)", command=self.toggle)
        self.btn_start.grid(row=0, column=0, sticky="ew", padx=(0, 4))
        self.btn_reset = ttk.Button(f_act, text="重置计数", command=self.reset_count)
        self.btn_reset.grid(row=0, column=1, sticky="ew", padx=4)
        self.v_top = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            f_act, text="窗口置顶", variable=self.v_top,
            command=self._apply_topmost,
        ).grid(row=0, column=2, padx=8)
        self.v_corner = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            f_act, text="四角急停（光标移到屏幕四角自动停止）",
            variable=self.v_corner,
        ).grid(row=0, column=3, padx=8)
        f_act.columnconfigure(0, weight=1)
        f_act.columnconfigure(1, weight=1)

        ttk.Label(
            self.root, foreground="#666",
            text="F6 开始/停止    F7 记录坐标/加点    F8 退出    急停: 光标移到屏幕任意一角",
        ).grid(row=7, column=0, pady=(0, 8))

        self._apply_topmost()

    # ------------------------------------------------------- 序列列表管理
    def _seq_refresh(self) -> None:
        self.lb_seq.delete(0, "end")
        for i, (x, y) in enumerate(self.seq_points, 1):
            self.lb_seq.insert("end", f"{i}.  ({x}, {y})")

    def _seq_delete(self) -> None:
        sel = list(self.lb_seq.curselection())
        for idx in reversed(sel):
            del self.seq_points[idx]
        self._seq_refresh()

    def _seq_clear(self) -> None:
        self.seq_points.clear()
        self._seq_refresh()

    # -------------------------------------------------------------- 配置
    def _save_config(self) -> None:
        data = {
            "version": VERSION,
            "speed_mode": self.v_speed_mode.get(),
            "interval": self.v_interval.get(),
            "jitter": self.v_jitter.get(),
            "cps_min": self.v_cps_min.get(),
            "cps_max": self.v_cps_max.get(),
            "target": self.v_target.get(),
            "delay": self.v_delay.get(),
            "button": self.v_button.get(),
            "type": self.v_type.get(),
            "dbl": self.v_dbl.get(),
            "pos_mode": self.v_pos_mode.get(),
            "x": self.v_x.get(),
            "y": self.v_y.get(),
            "seq": [list(map(int, p)) for p in self.seq_points],
            "top": bool(self.v_top.get()),
            "corner": bool(self.v_corner.get()),
        }
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            with open(CONFIG_FILE, "w", encoding="utf-8") as fh:
                json.dump(data, fh, ensure_ascii=False, indent=1)
        except Exception:
            pass

    def _load_config(self) -> None:
        try:
            with open(CONFIG_FILE, encoding="utf-8") as fh:
                data = json.load(fh)
        except Exception:
            return
        if not isinstance(data, dict):
            return
        mapping = {
            "speed_mode": self.v_speed_mode, "interval": self.v_interval,
            "jitter": self.v_jitter, "cps_min": self.v_cps_min,
            "cps_max": self.v_cps_max, "target": self.v_target,
            "delay": self.v_delay, "button": self.v_button,
            "type": self.v_type, "dbl": self.v_dbl,
            "pos_mode": self.v_pos_mode, "x": self.v_x, "y": self.v_y,
        }
        for key, var in mapping.items():
            val = data.get(key)
            if isinstance(val, (str, int, float)):
                try:
                    var.set(str(val))
                except Exception:
                    pass
        seq = data.get("seq")
        if isinstance(seq, list):
            self.seq_points = [
                [int(p[0]), int(p[1])] for p in seq
                if isinstance(p, (list, tuple)) and len(p) == 2
            ]
            self._seq_refresh()
        for key, var in (("top", self.v_top), ("corner", self.v_corner)):
            if key in data:
                var.set(bool(data[key]))
        self._apply_topmost()

    # -------------------------------------------------------------- 状态
    def _apply_topmost(self) -> None:
        try:
            self.root.attributes("-topmost", bool(self.v_top.get()))
        except Exception:
            pass

    def _sync_states(self) -> None:
        """按当前选择启用/禁用无关输入框。"""
        mode = self.v_speed_mode.get()
        for w in (self.e_interval, self.e_jitter):
            w.state(["!disabled"] if mode == "interval" else ["disabled"])
        for w in (self.e_cps_min, self.e_cps_max):
            w.state(["!disabled"] if mode == "cps" else ["disabled"])
        self.e_dbl.state(
            ["!disabled"] if self.v_type.get() == "双击" else ["disabled"])
        pos_mode = self.v_pos_mode.get()
        fixed = pos_mode == "fixed"
        for w in (self.e_x, self.e_y, self.btn_rec):
            w.state(["!disabled"] if fixed else ["disabled"])
        seq_on = pos_mode == "seq"
        for w in (self.lb_seq, self.btn_seq_add, self.btn_seq_del, self.btn_seq_clr):
            try:
                w.state(["!disabled"] if seq_on else ["disabled"])
            except Exception:
                w.configure(state="normal" if seq_on else "disabled")

    # -------------------------------------------------------------- 热键
    def _setup_hotkeys(self) -> None:
        init_backend()
        if sys.platform == "win32":
            self._setup_hotkeys_win32()
        else:
            self._setup_hotkeys_pynput()

    def _setup_hotkeys_win32(self) -> None:
        """RegisterHotKey 热键线程：系统消息机制，不依赖低级键盘钩子。"""
        result = {"ok": [], "fail": [], "tid": 0}
        started = threading.Event()

        def run() -> None:
            import ctypes.wintypes

            user32 = ctypes.windll.user32
            kernel32 = ctypes.windll.kernel32
            result["tid"] = kernel32.GetCurrentThreadId()
            hotkeys = {1: VK_F6, 2: VK_F7, 3: VK_F8}
            for hid, vk in hotkeys.items():
                if user32.RegisterHotKey(None, hid, MOD_NOREPEAT, vk):
                    result["ok"].append(hid)
                else:
                    result["fail"].append(hid)
            started.set()
            msg = ctypes.wintypes.MSG()
            while user32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
                if msg.message == WM_HOTKEY:
                    cb = {
                        1: self.toggle,
                        2: self.record_position,
                        3: self.on_close,
                    }.get(msg.wParam)
                    if cb:
                        self.root.after(0, cb)
            for hid in result["ok"]:
                user32.UnregisterHotKey(None, hid)

        threading.Thread(target=run, name="hotkey-win32", daemon=True).start()
        started.wait(2.0)
        self._hotkey_tid = result["tid"]
        backend_txt = f"点击后端: {BACKEND or '不可用'}"
        if not result["ok"]:
            self.v_backend.set(
                f"{backend_txt}    ⚠ Win32 热键注册全部失败，尝试 pynput 后备")
            self._setup_hotkeys_pynput()
            return
        fail_txt = ""
        if result["fail"]:
            names = {1: "F6", 2: "F7", 3: "F8"}
            fail_txt = (
                "（" + "/".join(names[i] for i in result["fail"])
                + " 被其他程序占用）")
        self.v_backend.set(
            f"{backend_txt}    热键: Win32 F6/F7/F8 已注册{fail_txt}")

    def _setup_hotkeys_pynput(self) -> None:
        if BACKEND != "pynput" or _pynput_keyboard is None:
            self.v_backend.set(
                f"点击后端: {BACKEND or '不可用'}"
                "    ⚠ 热键不可用，请使用界面按钮")
            return
        try:
            self._hotkey_listener = _pynput_keyboard.GlobalHotKeys({
                "<f6>": lambda: self.root.after(0, self.toggle),
                "<f7>": lambda: self.root.after(0, self.record_position),
                "<f8>": lambda: self.root.after(0, self.on_close),
            })
            self._hotkey_listener.daemon = True
            self._hotkey_listener.start()
            self.v_backend.set(
                f"点击后端: {BACKEND}    热键: pynput F6/F7/F8 已注册")
        except Exception as exc:
            self.v_backend.set(f"点击后端: {BACKEND}    ⚠ 热键注册失败: {exc}")

    # -------------------------------------------------------------- 配置项
    def read_config(self) -> dict:
        def num(var, name, lo, hi, cast=float):
            raw = (var.get() or "").strip()
            try:
                val = cast(float(raw))
            except Exception:
                raise ValueError(f"「{name}」需要填数字，当前是：{raw!r}")
            if not (lo <= val <= hi):
                raise ValueError(
                    f"「{name}」超出范围 [{lo:g}, {hi:g}]：{val:g}")
            return val

        speed_mode = self.v_speed_mode.get()
        cfg = {
            "speed_mode": speed_mode,
            "button": dict(BTN_ITEMS)[self.v_button.get()],
            "type": dict(TYPE_ITEMS)[self.v_type.get()],
            "pos_mode": self.v_pos_mode.get(),
            "target": int(num(self.v_target, "目标次数", 0, 1_000_000_000, int)),
            "delay_ms": num(self.v_delay, "启动延迟", 0, 600000),
            "dbl_ms": num(self.v_dbl, "双击间隔", 0, 500),
            "interval_ms": 0.0,
            "jitter_ms": 0.0,
            "cps_min": 0.0,
            "cps_max": 0.0,
            "fix_x": 0,
            "fix_y": 0,
            "lock_x": 0,
            "lock_y": 0,
            "seq_x": 0,
            "seq_y": 0,
            "seq": [],
        }
        if speed_mode == "interval":
            cfg["interval_ms"] = num(self.v_interval, "固定间隔", 1, 3600000)
            cfg["jitter_ms"] = num(self.v_jitter, "抖动", 0, 3600000)
        else:
            cfg["cps_min"] = num(self.v_cps_min, "最小 CPS", 0.1, 1000)
            cfg["cps_max"] = num(self.v_cps_max, "最大 CPS", 0.1, 1000)
        if cfg["pos_mode"] == "fixed":
            cfg["fix_x"] = int(num(self.v_x, "固定坐标 X", -32768, 32767, int))
            cfg["fix_y"] = int(num(self.v_y, "固定坐标 Y", -32768, 32767, int))
        elif cfg["pos_mode"] == "seq":
            cfg["seq"] = [tuple(p) for p in self.seq_points]
            if not cfg["seq"]:
                raise ValueError(
                    "坐标序列为空，请先『添加当前坐标 (F7)』或手动记录")
        if cfg["speed_mode"] == "interval" and cfg["interval_ms"] < 1:
            raise ValueError("固定间隔不能小于 1 毫秒")
        return cfg

    # -------------------------------------------------------------- 坐标
    def get_position(self):
        try:
            if BACKEND == "pynput":
                x, y = _mouse_controller.position
                return int(x), int(y)
            pos = pyautogui.position()
            return int(pos[0]), int(pos[1])
        except Exception:
            return None

    def record_position(self) -> None:
        pos = self.get_position()
        if pos is None:
            messagebox.showwarning(
                APP_NAME, "读取鼠标坐标失败，请检查后端是否可用。")
            return
        if self.v_pos_mode.get() == "seq":
            self.seq_points.append([pos[0], pos[1]])
            self._seq_refresh()
            self.v_hint.set(
                f"已添加序列点 ({pos[0]}, {pos[1]})，共 {len(self.seq_points)} 个")
        else:
            self.v_x.set(str(pos[0]))
            self.v_y.set(str(pos[1]))
            self.v_hint.set(f"已记录坐标 ({pos[0]}, {pos[1]})")

    def _corner_failsafe(self, w: int, h: int) -> bool:
        """四角急停：光标贴近屏幕四角时返回 True。"""
        if not self.v_corner.get():
            return False
        pos = self.get_position()
        if pos is None:
            return False
        x, y = pos
        m = CORNER_MARGIN
        return x <= m or y <= m or x >= w - 1 - m or y >= h - 1 - m

    # -------------------------------------------------------------- 启停
    def reset_count(self) -> None:
        with self._lock:
            busy = self.running
        if busy:
            messagebox.showinfo(APP_NAME, "请先停止再重置计数。")
            return
        with self._lock:
            self.done = 0
        self._last_shown = -1

    def toggle(self) -> None:
        if self.running:
            self.stop()
        else:
            self.start()

    def start(self) -> None:
        if self._thread is not None and self._thread.is_alive():
            self._thread.join(0.3)
        if self._thread is not None and self._thread.is_alive():
            self.v_hint.set("上一次任务尚未完全结束，请稍候再按开始")
            return
        if not init_backend():
            messagebox.showerror(
                APP_NAME, "未找到可用的点击后端。\n请先执行：pip install pynput pyautogui")
            return
        try:
            cfg = self.read_config()
        except ValueError as exc:
            messagebox.showerror(APP_NAME, str(exc))
            return
        self.cfg = cfg
        with self._lock:
            self.done = 0
            self.running = True
            self.last_err = None
        self.stop_reason = ""
        self._last_shown = -1
        self._samples = [(time.time(), 0)]
        self._t0 = time.time()
        self.v_hint.set("")
        self._save_config()
        self._stop.clear()
        self._thread = threading.Thread(
            target=self._worker, args=(cfg,), name="autoclicker", daemon=True)
        self._thread.start()

    def stop(self) -> None:
        self._stop.set()

    def on_close(self) -> None:
        self._stop.set()
        self._save_config()
        t = self._thread
        if t is not None and t.is_alive():
            t.join(timeout=1.0)
        if self._hotkey_tid:
            try:
                ctypes.windll.kernel32.PostThreadMessageW(
                    self._hotkey_tid, WM_QUIT, 0, 0)
            except Exception:
                pass
        if self._hotkey_listener is not None:
            try:
                self._hotkey_listener.stop()
            except Exception:
                pass
        try:
            self.root.destroy()
        except Exception:
            pass

    # -------------------------------------------------------------- 引擎
    @staticmethod
    def _next_interval(cfg: dict) -> float:
        """返回本次点击后的等待秒数。"""
        if cfg["speed_mode"] == "cps":
            lo, hi = cfg["cps_min"], cfg["cps_max"]
            if lo > hi:
                lo, hi = hi, lo
            return 1.0 / max(random.uniform(lo, hi), 0.1)
        ms = cfg["interval_ms"]
        if cfg["jitter_ms"] > 0:
            ms += random.uniform(-cfg["jitter_ms"], cfg["jitter_ms"])
        return max(ms, 1.0) / 1000.0

    def _press_release(self, btn) -> None:
        """一次按下+抬起。release 放在 finally，避免异常导致鼠标键卡在按下状态。"""
        if BACKEND == "pynput":
            c = _mouse_controller
            try:
                c.press(btn)
            finally:
                try:
                    c.release(btn)
                except Exception:
                    pass
        else:
            pyautogui.mouseDown(button=btn)
            pyautogui.mouseUp(button=btn)

    def _do_action(self, cfg: dict) -> None:
        x = y = None
        if cfg["pos_mode"] == "fixed":
            x, y = cfg["fix_x"], cfg["fix_y"]
        elif cfg["pos_mode"] == "locked":
            x, y = cfg["lock_x"], cfg["lock_y"]
        elif cfg["pos_mode"] == "seq":
            x, y = cfg["seq_x"], cfg["seq_y"]
        if x is not None:
            if BACKEND == "pynput":
                _mouse_controller.position = (int(x), int(y))
            else:
                pyautogui.moveTo(int(x), int(y), duration=0)
        btn = resolve_button(cfg["button"])
        self._press_release(btn)
        if cfg["type"] == "double":
            gap = cfg["dbl_ms"] / 1000.0
            if gap > 0:
                time.sleep(gap)
            self._press_release(btn)

    def _worker(self, cfg: dict) -> None:
        err = None
        reason = ""
        try:
            if cfg["delay_ms"] > 0 and self._stop.wait(cfg["delay_ms"] / 1000.0):
                return
            if cfg["pos_mode"] == "locked":
                pos = self.get_position()
                if pos is None:
                    raise RuntimeError("无法读取当前鼠标坐标，『锁定启动位置』不可用")
                cfg["lock_x"], cfg["lock_y"] = pos
            w, h = screen_size()
            seq = cfg.get("seq") or []
            seq_i = 0
            while not self._stop.is_set():
                if self._corner_failsafe(w, h):
                    reason = "corner"
                    break
                if cfg["pos_mode"] == "seq":
                    if not seq:
                        raise RuntimeError("坐标序列为空")
                    cfg["seq_x"], cfg["seq_y"] = seq[seq_i % len(seq)]
                    seq_i += 1
                self._do_action(cfg)
                with self._lock:
                    self.done += 1
                    done = self.done
                if cfg["target"] and done >= cfg["target"]:
                    break
                deadline = time.perf_counter() + self._next_interval(cfg)
                while not self._stop.is_set():
                    # 急停检查放进等待循环：固定/序列模式下点击本身会把光标
                    # 拉离角落，只在点击前检查会与移动抢跑，50ms 内必能发现。
                    if self._corner_failsafe(w, h):
                        reason = "corner"
                        break
                    remain = deadline - time.perf_counter()
                    if remain <= 0:
                        break
                    self._stop.wait(min(remain, 0.05))
                if reason:
                    break
        except Exception as exc:
            err = f"{type(exc).__name__}: {exc}"
        finally:
            with self._lock:
                self.running = False
                self.last_err = err
                self.stop_reason = reason
            self._stop.set()

    def _tick(self) -> None:
        with self._lock:
            running, done, err = self.running, self.done, self.last_err
        if running:
            self.v_status.set("● 运行中")
            self.btn_start.configure(text="停止 (F6)")
            now = time.time()
            self._samples.append((now, done))
            while self._samples and now - self._samples[0][0] > 2.5:
                self._samples.pop(0)
            cps = 0.0
            if len(self._samples) >= 2:
                dt = self._samples[-1][0] - self._samples[0][0]
                dc = self._samples[-1][1] - self._samples[0][1]
                if dt > 0:
                    cps = dc / dt
            elapsed = int(now - self._t0)
            self.v_count.set(
                f"已执行: {done} 次   实际 {cps:4.1f} CPS   "
                f"{elapsed // 60:02d}:{elapsed % 60:02d}")
        else:
            self.v_status.set("已停止")
            self.btn_start.configure(text="开始 (F6)")
            if done != self._last_shown:
                self._last_shown = done
                self.v_count.set(f"已执行: {done} 次")
            self._samples.clear()
            if err:
                with self._lock:
                    self.last_err = None
                messagebox.showerror(APP_NAME, f"点击线程已中止：\n{err}")
            elif self.stop_reason == "corner":
                self.stop_reason = ""
                self.v_hint.set("⚠ 光标进入屏幕四角，已自动急停")
        try:
            self.root.after(80, self._tick)
        except tk.TclError:
            return


def selftest() -> int:
    """自检：验证后端、热键、tkinter 与间隔计算，不产生任何真实点击。

    --windowed 打包后没有控制台，所以结果同时写入 CWD 下的 selftest_report.txt。
    """
    report: list[str] = []

    def say(msg: str) -> None:
        report.append(msg)
        print(msg, flush=True)

    ok = init_backend()
    say(f"backend      : {BACKEND} (init_ok={ok})")
    if not ok:
        _write_report(report)
        return 1

    # Win32 RegisterHotKey 探测
    if sys.platform == "win32":
        import ctypes.wintypes

        u = ctypes.windll.user32
        reg = bool(u.RegisterHotKey(None, 0x5F6, MOD_NOREPEAT, VK_F6))
        if reg:
            u.UnregisterHotKey(None, 0x5F6)
        say(f"hotkeys(win32): RegisterHotKey F6 "
            f"{'OK' if reg else 'FAIL (可能被占用)'}")
    else:
        say("hotkeys(win32): N/A (非 Windows)")

    if _pynput_keyboard is not None:
        try:
            kl = _pynput_keyboard.GlobalHotKeys({"<f6>": lambda: None})
            kl.daemon = True
            kl.start()
            kl.stop()
            say("hotkeys(pynput): F6/F7/F8 注册 OK")
        except Exception as exc:
            say(f"hotkeys(pynput): FAIL {type(exc).__name__}: {exc}")
    else:
        say("hotkeys(pynput): N/A (非 pynput 后端)")

    try:
        _tk = __import__("tkinter")
        _r = _tk.Tk()
        _r.withdraw()
        say(f"tkinter      : OK (tcl {_tk.TclVersion})")
        _r.destroy()
    except Exception as exc:
        say(f"tkinter      : FAIL {type(exc).__name__}: {exc}")

    for lo, hi in ((8, 12), (1, 1)):
        cfg = {"speed_mode": "cps", "cps_min": lo, "cps_max": hi}
        samples = [AutoClickerApp._next_interval(cfg) for _ in range(5)]
        say(f"cps {lo}-{hi:<3}   : "
            + ", ".join(f"{s * 1000:6.2f}ms" for s in samples))
    cfg = {"speed_mode": "interval", "interval_ms": 100, "jitter_ms": 20}
    samples = [AutoClickerApp._next_interval(cfg) for _ in range(5)]
    say("100ms±20ms   : "
        + ", ".join(f"{s * 1000:6.2f}ms" for s in samples))

    try:
        if BACKEND == "pynput":
            pos = tuple(int(v) for v in _mouse_controller.position)
        else:
            p = pyautogui.position()
            pos = (int(p[0]), int(p[1]))
        say(f"mouse pos    : {pos}")
    except Exception as exc:
        say(f"mouse pos    : FAIL {exc}")

    say("config file  : " + CONFIG_FILE)
    say("SELFTEST OK")
    _write_report(report)
    return 0


def _write_report(report: list[str]) -> None:
    import os

    path = os.path.join(os.getcwd(), "selftest_report.txt")
    try:
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("\n".join(report) + "\n")
    except Exception:
        pass


def main() -> int:
    parser = argparse.ArgumentParser(description=f"{APP_NAME} v{VERSION}")
    parser.add_argument("--selftest", action="store_true", help="无界面自检后退出")
    args = parser.parse_args()
    if args.selftest:
        return selftest()

    _dpi_aware()
    backend_ok = init_backend()
    root = tk.Tk()
    try:
        ttk.Style().theme_use("vista")
    except Exception:
        pass
    AutoClickerApp(root)
    if not backend_ok:
        messagebox.showerror(
            APP_NAME,
            "未检测到 pynput / pyautogui，程序无法点击。\n"
            "请先执行：pip install pynput pyautogui")
    root.mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main())
