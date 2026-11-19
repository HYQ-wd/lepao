#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
步道乐跑 + FakeLocation 全自动打卡 (MuMu 实例 1)

顺序(关键): 先开 FakeLocation 启动路线模拟, 再开步道乐跑起跑.
乐跑进入跑步页时会去拿一次定位, 那时必须已经有 mock 坐标在输出,
否则会停在「获取当前位置失败」. 反过来先起跑再开模拟, 轨迹会断头.

流程:
    boot  -> 启动 MuMu 安卓设备1, 连 adb, 等开机
    fl    -> FakeLocation: 抽屉 -> 路线模拟 -> 设速度 -> 启动模拟
    lp    -> 步道乐跑: 打开 -> 乐跑 -> 开始乐跑 -> 进入乐跑 -> before_run -> 起跑
    state -> 读当前 里程/打卡数/打卡点 (screencap + OCR)
    stop  -> 停止跑步 + 上传成绩
    full  -> 全流程, 满足 >=1.5km 且 >=2 个打卡点后自动结束上传

用法:
    python lepao_auto.py full
    python lepao_auto.py full --km 1.5 --points 2

要点:
    * 跑步中地图每秒重绘, uiautomator dump 必然报 "could not get idle state",
      所以运行态一律 screencap + WinRT OCR 读屏.
    * FakeLocation 全程 rid 驱动, 零 OCR —— 加固版的界面文字 OCR 极不稳.
    * 底部 tv_start_pause_continue_run 是「开始<->暂停」同一个开关,
      盲长按会把在跑的状态按成暂停, 所以起跑前必须先判相位.
"""

import glob
import json
import math
import os
import re
import subprocess
import sys
import time
import xml.etree.ElementTree as ET

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ocr as OCR

# ------------------------------------------------------------------ 配置
# 全部可被环境变量覆盖, 换电脑不用改代码:
#   LEPAO_MUMU_HOME  MuMu 安装根目录(含 nx_main\MuMuManager.exe)
#   LEPAO_INDEX      要操作的实例序号
#   LEPAO_SERIAL     直接指定 adb serial(如 127.0.0.1:16416), 跳过自动探测
#   LEPAO_KM / LEPAO_POINTS  目标里程 / 打卡点
PKG_FAKE = "com.lerist.fakelocation"     # 默认候选, 运行时由 resolve_pkgs() 覆盖
PKG_RUN = "com.lptiyu.tanke"

# App 包名自动识别: 换台电脑装的版本可能不同, 先精确候选, 再关键字模糊
_FAKE_CANDIDATES = ["com.lerist.fakelocation", "com.lerist.fakelocationv2"]
_RUN_CANDIDATES = ["com.lptiyu.tanke", "com.lptiyu.tanke.run", "com.lptiyu.pao"]
_FAKE_KEYS = ("fakelocation", "lerist")
_RUN_KEYS = ("lptiyu", "tanke", "lepao")

POLL_SEC = 30
MAX_MINUTES = 50
SHOT = "/sdcard/_lp_shot.png"
SHOT_LOCAL = os.path.join(HERE, "_probe", "_state.png")

LOG = lambda *a: print(*a, flush=True)


def _force_utf8_stdout():
    """中文 Windows 控制台默认 GBK, 直接 print 中文在某些终端会抛
    UnicodeEncodeError. 这里把 stdout 尽量切成 utf-8, 切不动就降级替换."""
    try:
        if hasattr(sys.stdout, "reconfigure"):
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")
            return
    except Exception:
        pass
    try:
        import io
        sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8",
                                      errors="replace", line_buffering=True)
        sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding="utf-8",
                                      errors="replace", line_buffering=True)
    except Exception:
        pass


_force_utf8_stdout()


def _env_int(name, default):
    try:
        return int(os.environ.get(name, default))
    except (TypeError, ValueError):
        return default


def _env_float(name, default):
    try:
        return float(os.environ.get(name, default))
    except (TypeError, ValueError):
        return default


TARGET_KM = _env_float("LEPAO_KM", 1.5)
TARGET_POINTS = _env_int("LEPAO_POINTS", 2)
# -1 = 自动挑实例(装齐乐跑+FakeLocation 的优先). 显式给了 LEPAO_INDEX 就按给的来.
INDEX = _env_int("LEPAO_INDEX", -1)


# ------------------------------------------------------------------ MuMu 路径自动探测

# 常见安装位置: 官方默认装在 C 盘, 但很多人改到 D/E 盘
_MUMU_CANDIDATES = [
    r"C:\Program Files\Netease\MuMuPlayer-12.0",
    r"C:\Program Files\Netease\MuMuPlayerGlobal-12.0",
    r"C:\Program Files\Netease\MuMu Player 12",
    r"D:\Program Files\Netease\MuMuPlayer-12.0",
    r"C:\Program Files\MuMuPlayer-12.0",
    r"E:\MuMuPlayer-12.0",
    r"D:\MuMuPlayer-12.0",
]


def _mumu_root_from_home(home):
    """把各种输入统一解析成 MuMu 安装根目录.

    可接受: 根目录 / nx_main 目录 / MuMuManager.exe 全路径.
    找不到则返回 None.
    """
    if not home:
        return None
    home = os.path.abspath(home)

    # 传进来是 exe 文件, 先退到所在目录
    if os.path.isfile(home) or home.lower().endswith((".exe", ".dll")):
        home = os.path.dirname(home)

    # 最多向上找 3 层, 覆盖 root / root\nx_main 两种
    for _ in range(4):
        if os.path.exists(os.path.join(home, "nx_main", "MuMuManager.exe")):
            return home
        parent = os.path.dirname(home)
        if parent == home:
            break
        home = parent
    return None


def _mumu_root_from_registry():
    """MuMu 12 会在注册表留 InstallDir; 读不到就返回 None"""
    try:
        import winreg
    except ImportError:
        return None
    keys = [
        (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Netease\MuMuPlayer-12.0"),
        (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Netease\MuMuPlayer-12.0"),
        (winreg.HKEY_CURRENT_USER, r"SOFTWARE\Netease\MuMuPlayer-12.0"),
        (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Netease\MuMuPlayerGlobal-12.0"),
    ]
    for root, path in keys:
        try:
            with winreg.OpenKey(root, path) as k:
                for name in ("InstallDir", "installDir", "InstallPath", "Path"):
                    try:
                        val, _ = winreg.QueryValueEx(k, name)
                    except OSError:
                        continue
                    if val and _mumu_root_from_home(val):
                        return _mumu_root_from_home(val)
        except OSError:
            continue
    return None


def _mumu_root_from_running():
    """已经开着模拟器时, 从进程路径反推安装目录"""
    try:
        out = sh(["powershell", "-NoProfile", "-Command",
                  "(Get-Process MuMuPlayer,MuMuManager,MuMuNxDevice -ErrorAction "
                  "SilentlyContinue | Select-Object -First 1).Path"], check=False)
    except Exception:
        return None
    p = (out or "").strip()
    return _mumu_root_from_home(p) if p else None


def _all_drives():
    """枚举本机所有盘符. glob 不支持 *:\\ 这种写法, 必须自己列"""
    drives = []
    try:
        import string
        for ch in string.ascii_uppercase:
            root = "%s:\\" % ch
            if os.path.exists(root):
                drives.append(root)
    except Exception:
        pass
    return drives


def _mumu_root_from_drives():
    """兜底: 扫各盘的常见目录层级.

    Python 的 glob 不认 *:\\ 这种盘符通配, 所以先枚举盘符再匹配.
    覆盖: 盘根\\MuMuPlayer*、盘根\\*\\MuMuPlayer*、盘根\\*\\*\\MuMuPlayer*,
    以及目录名里带 MuMu 的各种变体.
    """
    sub_patterns = [
        "MuMuPlayer*\\nx_main\\MuMuManager.exe",
        "*MuMu*\\nx_main\\MuMuManager.exe",
        "*\\MuMuPlayer*\\nx_main\\MuMuManager.exe",
        "*\\*MuMu*\\nx_main\\MuMuManager.exe",
        "*\\*\\MuMuPlayer*\\nx_main\\MuMuManager.exe",
        "*\\*\\*MuMu*\\nx_main\\MuMuManager.exe",
        "*\\Netease\\MuMuPlayer*\\nx_main\\MuMuManager.exe",
    ]
    for drive in _all_drives():
        for sub in sub_patterns:
            try:
                hits = glob.glob(os.path.join(drive, sub))
            except Exception:
                continue
            for hit in hits:
                root = _mumu_root_from_home(hit)
                if root:
                    return root
    return None


def find_mumu_root():
    """按 环境变量 -> 常见路径 -> 注册表 -> 运行中进程 -> 全盘扫描 的顺序定位"""
    env = os.environ.get("LEPAO_MUMU_HOME")
    if env:
        root = _mumu_root_from_home(env)
        if root:
            return root
        raise RuntimeError(
            "LEPAO_MUMU_HOME=%s 下没找到 nx_main\\MuMuManager.exe" % env)

    for cand in _MUMU_CANDIDATES:
        root = _mumu_root_from_home(cand)
        if root:
            return root

    for fn in (_mumu_root_from_registry, _mumu_root_from_running, _mumu_root_from_drives):
        root = fn()
        if root:
            return root

    raise RuntimeError(
        "没找到 MuMu 模拟器 12.\n"
        "  请先安装 MuMu 模拟器 12, 或设置环境变量指向安装目录:\n"
        '    set LEPAO_MUMU_HOME=C:\\Program Files\\Netease\\MuMuPlayer-12.0')


class MuMu(object):
    """MuMu 安装信息的懒加载容器"""

    def __init__(self):
        self._root = None

    @property
    def root(self):
        if self._root is None:
            self._root = find_mumu_root()
        return self._root

    @property
    def manager(self):
        return os.path.join(self.root, "nx_main", "MuMuManager.exe")

    @property
    def adb(self):
        return os.path.join(self.root, "nx_main", "adb.exe")

    @property
    def vms(self):
        return os.path.join(self.root, "vms")


MUMU = MuMu()

# 允许用环境变量直接指定 adb.exe, 适合 MuMu 装得很偏或想用 platform-tools 的 adb
_ADB_OVERRIDE = os.environ.get("LEPAO_ADB", "").strip()


def adb_exe():
    if _ADB_OVERRIDE and os.path.exists(_ADB_OVERRIDE):
        return _ADB_OVERRIDE
    if _ADB_OVERRIDE:
        LOG("[!] LEPAO_ADB=%s 不存在, 改用 MuMu 自带 adb" % _ADB_OVERRIDE)
    return MUMU.adb


def shot_path(name):
    p = os.path.join(HERE, "_probe", name)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    return p


# ------------------------------------------------------------------ adb

def sh(cmd, timeout=120, check=True):
    p = subprocess.run(cmd, capture_output=True, timeout=timeout,
                       encoding="utf-8", errors="ignore")
    if check and p.returncode != 0:
        raise RuntimeError("cmd failed: %s\n%s\n%s" % (cmd, p.stdout, p.stderr))
    return p.stdout


def adb_port(index=None):
    """从实例 vm_config.json 读 adb 端口.

    MuMu 12 的 `MuMuManager info` 不返回端口, 只能读配置文件.
    实例目录名形如 MuMuPlayer-12.0-1 / MuMuPlayer-15.0-0, 以 -<index> 结尾.
    """
    index = INDEX if index is None else index
    vms = MUMU.vms
    if not os.path.isdir(vms):
        raise RuntimeError("MuMu vms 目录不存在: %s" % vms)
    for name in os.listdir(vms):
        if not name.endswith("-%d" % index):
            continue
        cfg = os.path.join(vms, name, "configs", "vm_config.json")
        if not os.path.exists(cfg):
            continue
        try:
            with open(cfg, encoding="utf-8") as f:
                data = json.load(f)
            return int(data["vm"]["nat"]["port_forward"]["adb"]["host_port"])
        except (KeyError, TypeError, ValueError):
            continue
    raise RuntimeError(
        "实例 %d 找不到 adb 端口配置.\n  可用实例: %s\n  目录: %s"
        % (index, list_instances(), vms))


def list_instances():
    """列出 (index, dir_name, adb_port), 方便报错时提示用户"""
    out = []
    vms = MUMU.vms
    if not os.path.isdir(vms):
        return out
    for name in os.listdir(vms):
        m = re.search(r"-(\d+)$", name)
        cfg = os.path.join(vms, name, "configs", "vm_config.json")
        if not m or not os.path.exists(cfg):
            continue
        port = None
        try:
            with open(cfg, encoding="utf-8") as f:
                port = int(json.load(f)["vm"]["nat"]["port_forward"]["adb"]["host_port"])
        except Exception:
            pass
        out.append((int(m.group(1)), name, port))
    return sorted(out)


SERIAL = None


# 上次成功定位到的实例号. 多开器里有一堆没装 App 的空实例时,
# 记住一个能少启动一堆模拟器 —— 换电脑第一次仍然会全扫一遍.
_LAST_INDEX_FILE = os.path.join(HERE, "_last_index.txt")


def _read_last_index():
    try:
        with open(_LAST_INDEX_FILE, encoding="utf-8") as f:
            return int(f.read().strip())
    except (OSError, ValueError):
        return None


def _write_last_index(idx):
    try:
        with open(_LAST_INDEX_FILE, "w", encoding="utf-8") as f:
            f.write(str(idx))
    except OSError:
        pass


def _pkgs_on(port, timeout=12):
    """直接对某个实例的 adb 端口跑 pm list packages(绕过全局 serial 缓存).
    连不上返回 None, 连上但没装东西返回 set()."""
    s = "127.0.0.1:%d" % port
    try:
        sh([adb_exe(), "connect", s], check=False, timeout=timeout)
        p = subprocess.run([adb_exe(), "-s", s, "shell", "pm", "list", "packages"],
                           capture_output=True, timeout=timeout,
                           encoding="utf-8", errors="ignore")
    except Exception:
        return None
    out = p.stdout or ""
    if "package:" not in out:
        return None
    return set(x[len("package:"):].strip()
               for x in out.splitlines() if x.startswith("package:"))


def _match_in(pkgs, cands, keys):
    """在包名集合里找目标包. 先精确候选, 再关键字模糊(取最短, 排除子进程包)"""
    for c in cands:
        if c in pkgs:
            return c
    best = None
    for p in sorted(pkgs):
        low = p.lower()
        if any(k in low for k in keys):
            if best is None or len(p) < len(best):
                best = p
    return best


def pick_index(insts=None):
    """自动挑实例: 装齐了乐跑和 FakeLocation 的优先, 其次进程在跑的, 再次第一个.

    换台电脑实例号不一定是 1(有人只有实例 0, 有人开了多开), 所以默认走这里.
    """
    insts = list_instances() if insts is None else insts
    if not insts:
        return None
    best = None
    for idx, _name, port in insts:
        if not port:
            continue
        pkgs = _pkgs_on(port)
        if pkgs is None:          # 该实例没开/adb 连不上
            continue
        fake = _match_in(pkgs, _FAKE_CANDIDATES, _FAKE_KEYS)
        run = _match_in(pkgs, _RUN_CANDIDATES, _RUN_KEYS)
        missing = (fake is None) + (run is None)
        score = (missing, 0 if idx == INDEX else 1, idx)
        LOG("[=] 实例 %d (端口 %d): 乐跑=%s FakeLocation=%s"
            % (idx, port, run or "缺", fake or "缺"))
        if best is None or score < best[0]:
            best = (score, idx)
    if best is None:
        return None
    return best[1]


def resolve_index():
    """把 INDEX 定下来. -1/不存在 时自动挑, 结果写回全局."""
    global INDEX
    insts = list_instances()
    if not insts:
        raise RuntimeError(
            "MuMu 里没有可用实例.\n  请在 MuMu 多开器里新建一个安卓设备, 或设置 "
            "LEPAO_SERIAL=127.0.0.1:端口")

    indices = [i for i, _, _ in insts]
    if INDEX in indices:
        return INDEX

    if INDEX >= 0:
        LOG("[!] 实例 %d 不存在, 可用: %s" % (INDEX, indices))

    picked = pick_index(insts)
    if picked is None:
        # 全都没开: 用第一个, boot 会负责启动它
        picked = indices[0]
        LOG("[=] 没有已启动的实例, 先按实例 %d 处理(会自动启动)" % picked)
    else:
        LOG("[+] 自动选中实例 %d" % picked)
    INDEX = picked
    return INDEX


def locate_target_index(tries_each=40):
    """换电脑时的真正入口: 找出装了乐跑+FakeLocation 的那个实例, 没有就启动再找.

    先扫所有已开实例; 都找不到就逐个 launch 一遍, 起来一个查一个.
    返回 (index, fake_pkg, run_pkg), 找不到返回 (index, None, None).
    """
    global INDEX, SERIAL, _PKG_FAKE, _PKG_RUN
    insts = list_instances()
    if not insts:
        raise RuntimeError(
            "MuMu 里没有可用实例.\n  请在 MuMu 多开器里新建安卓设备后重试")

    # 用户显式指定了实例就只用它, 不要乱启动别的
    if INDEX >= 0 and INDEX in [i for i, _, _ in insts]:
        wanted = [x for x in insts if x[0] == INDEX]
    else:
        wanted = list(insts)

    # 0) 上次成功过的实例先试. 有多个实例时不用每次把别的也点起来
    last = _read_last_index()
    if INDEX < 0 and last is not None:
        hit = [x for x in wanted if x[0] == last]
        if hit:
            wanted = hit + [x for x in wanted if x[0] != last]
            LOG("[=] 上次用的是实例 %d, 先试它" % last)

    def _pick(idx, fake, run, s):
        global INDEX, SERIAL, _PKG_FAKE, _PKG_RUN
        INDEX, SERIAL = idx, s
        _PKG_FAKE, _PKG_RUN = fake, run
        _write_last_index(idx)
        return idx, fake, run

    # 1) 已经开着的实例里找
    for idx, name, port in wanted:
        if not port:
            continue
        pkgs = _pkgs_on(port)
        if pkgs is None:
            continue
        fake = _match_in(pkgs, _FAKE_CANDIDATES, _FAKE_KEYS)
        run = _match_in(pkgs, _RUN_CANDIDATES, _RUN_KEYS)
        LOG("[=] 实例 %d 已在运行: 乐跑=%s FakeLocation=%s"
            % (idx, run or "缺", fake or "缺"))
        if fake and run:
            LOG("[+] 选定实例 %d (端口 %d)" % (idx, port))
            return _pick(idx, fake, run, "127.0.0.1:%d" % port)

    # 2) 没有现成的就逐个启动
    for idx, name, port in wanted:
        if not port:
            continue
        LOG("[=] 启动实例 %d 看看里面有没有装好..." % idx)
        try:
            sh([MUMU.manager, "control", "-v", str(idx), "launch"],
               check=False, timeout=120)
        except Exception as e:
            LOG("[!] 实例 %d 启动失败: %s" % (idx, e))
            continue

        s = "127.0.0.1:%d" % port
        online = False
        for _ in range(tries_each):
            sh([adb_exe(), "connect", s], check=False, timeout=20)
            p = subprocess.run([adb_exe(), "-s", s, "get-state"],
                               capture_output=True, timeout=20,
                               encoding="utf-8", errors="ignore")
            if (p.stdout or "").strip() == "device":
                online = True
                break
            time.sleep(2)
        if not online:
            LOG("[!] 实例 %d 起来了但 adb 连不上, 换下一个" % idx)
            continue

        # 等系统真正就绪再查包
        for _ in range(60):
            p = subprocess.run([adb_exe(), "-s", s, "shell", "getprop",
                                "sys.boot_completed"], capture_output=True,
                               timeout=20, encoding="utf-8", errors="ignore")
            if (p.stdout or "").strip() == "1":
                break
            time.sleep(2)

        pkgs = _pkgs_on(port)
        if pkgs is None:
            continue
        fake = _match_in(pkgs, _FAKE_CANDIDATES, _FAKE_KEYS)
        run = _match_in(pkgs, _RUN_CANDIDATES, _RUN_KEYS)
        LOG("[=] 实例 %d: 乐跑=%s FakeLocation=%s" % (idx, run or "缺", fake or "缺"))
        if fake and run:
            LOG("[+] 选定实例 %d (端口 %d)" % (idx, port))
            return _pick(idx, fake, run, s)

    # 3) 都没装齐: 至少定一个能连上的, 让调用方报准确错误
    for idx, name, port in wanted:
        if port and _pkgs_on(port) is not None:
            INDEX, SERIAL = idx, "127.0.0.1:%d" % port
            return idx, None, None
    INDEX = wanted[0][0]
    SERIAL = None
    return INDEX, None, None


def serial():
    """adb serial. LEPAO_SERIAL 可直连; 否则自动挑实例再定位端口"""
    global SERIAL
    if SERIAL is not None:
        return SERIAL

    env = os.environ.get("LEPAO_SERIAL", "").strip()
    if env:
        SERIAL = env
        return SERIAL

    resolve_index()
    SERIAL = "127.0.0.1:%d" % adb_port(INDEX)
    return SERIAL


def d(*args, timeout=90, check=True):
    """执行 adb 命令. 连接掉了会自动 connect 一次再重试, 避免长时间轮询中途断线.

    ★★★ 绝对不能把「stdout 为空」当成断线信号 ★★★
      实测: `adb shell input tap X Y` 成功时 returncode=0, 且 stdout / stderr
      **都是空字符串** —— input 这类命令本来就没有输出. 老版本把
      `not (p.stdout or "").strip()` 也算进"疑似断线", 于是每次 tap 都被判为
      连接异常, 自动 connect 之后**再执行一次同样的命令**.

      后果: 每个点击都变成"点两下". 在 FakeLocation 路线页上这是灾难:
        点「启动模拟」两下 = 启动 -> 立刻暂停  (第二个落脚点正好在暂停键范围)
        点「继续」两下     = 继续  -> 立刻暂停
      用户看到的"脚本总是在点暂停" / "点了继续还是不动" 全是这一个 bug 造成的.

      修复: 只有 returncode != 0, 或 stderr 里明确出现连接类错误时才重试.
      空输出是正常现象, 不构成重试理由.
    """
    cmd = [adb_exe(), "-s", serial()] + list(args)
    p = subprocess.run(cmd, capture_output=True, timeout=timeout,
                       encoding="utf-8", errors="ignore")
    if p.returncode != 0:
        # 判断是不是连接掉了: 只在**真的失败**时看错误文本
        err = ((p.stdout or "") + (p.stderr or "")).lower()
        if ("not found" in err or "offline" in err or "no devices" in err
                or "device '" in err or "cannot connect" in err
                or "connection refused" in err or "closed" in err):
            try:
                sh([adb_exe(), "connect", serial()], check=False, timeout=30)
                time.sleep(1)
                p = subprocess.run(cmd, capture_output=True, timeout=timeout,
                                   encoding="utf-8", errors="ignore")
            except Exception:
                pass
    if check and p.returncode != 0:
        raise RuntimeError("adb 命令失败: %s\n%s\n%s"
                           % (" ".join(cmd), p.stdout, p.stderr))
    return p.stdout


def vm_running(index=None):
    """MuMu 的 is_android_started 会在进程退出后仍是缓存值 true, 不可靠.
    这里再确认底层进程真的在, 才算运行中."""
    index = INDEX if index is None else index
    if index < 0:                      # 直连 LEPAO_SERIAL 时没有实例号, 取第一个
        insts = list_instances()
        if not insts:
            return False
        index = insts[0][0]
    try:
        info = json.loads(sh([MUMU.manager, "info", "-v", str(index)],
                             check=False))
    except Exception:
        return False
    if not info.get("is_android_started", False):
        return False

    # 再验一次真实进程: MuMu 崩了/被关掉时 info 仍可能返回 true
    try:
        out = sh(["powershell", "-NoProfile", "-Command",
                  "@(Get-Process MuMuPlayer,MuMuNxDevice,MuMuManager "
                  "-ErrorAction SilentlyContinue).Count"], check=False, timeout=30)
        if out.strip().isdigit() and int(out.strip()) == 0:
            return False
    except Exception:
        pass
    return True


def adb_online(timeout=20):
    """adb 是否真的能连上. 用 connect + get-state 双确认"""
    s = serial()
    try:
        sh([adb_exe(), "connect", s], check=False, timeout=timeout)
        return d("get-state", check=False, timeout=timeout).strip() == "device"
    except Exception:
        return False


def boot():
    # 先看 adb 能不能直接连上 —— 已经跑起来就直接用, 省一次重启
    if adb_online(timeout=8):
        LOG("[=] 实例 %d 已在运行且 adb 可连" % INDEX)
        return _wait_bootdone()

    if vm_running():
        LOG("[=] 实例 %d 进程在, 但 adb 连不上, 重新拉起" % INDEX)
    else:
        LOG("[=] 实例 %d 未运行, 开始启动" % INDEX)

    if INDEX >= 0:
        out = sh([MUMU.manager, "control", "-v", str(INDEX), "launch"], check=False)
        if out and '"errcode"' in out:
            try:
                if json.loads(out).get("errcode", 0) != 0:
                    raise RuntimeError(
                        "MuMu 启动失败: %s\n  请手动打开 MuMu 确认实例 %d 能正常启动"
                        % (out.strip(), INDEX))
            except ValueError:
                pass
        LOG("[+] 已下发启动指令")

    s = serial()
    ok = False
    for _ in range(120):                      # 最多等 4 分钟
        sh([adb_exe(), "connect", s], check=False, timeout=20)
        if d("get-state", check=False, timeout=20).strip() == "device":
            ok = True
            break
        time.sleep(2)
    if not ok:
        raise RuntimeError(
            "adb 连不上 %s\n"
            "  排查顺序:\n"
            "   1) 模拟器是否已启动到桌面\n"
            "   2) MuMu 设置 -> 其他 -> 是否开启 ADB 调试\n"
            "   3) 手动试: \"%s\" connect %s" % (s, adb_exe(), s))
    LOG("[+] adb 已连 %s" % s)
    return _wait_bootdone()


def _wait_bootdone():
    """等 sys.boot_completed, 并把 adb 从 root 收回 shell"""
    s = serial()
    t0 = time.time()
    while time.time() - t0 < 300:
        if d("shell", "getprop", "sys.boot_completed", check=False).strip() == "1":
            time.sleep(4)
            # adb root 会让 adbd 变 uid0, input 注入被 INJECT_EVENTS 拦, 必须保持 shell
            try:
                d("unroot", check=False, timeout=30)
            except Exception:
                pass
            time.sleep(3)
            sh([adb_exe(), "connect", s], check=False)
            time.sleep(2)
            LOG("[+] 开机完成 %.0fs" % (time.time() - t0))
            return
        time.sleep(2)
    raise TimeoutError("开机超时: 模拟器起来了但系统没就绪, 请手动看一眼")


# ------------------------------------------------------------------ 输入 / 截图

def tap(x, y, wait=0.6):
    d("shell", "input", "tap", str(int(x)), str(int(y)))
    time.sleep(wait)


def long_press(x, y, ms=2200):
    d("shell", "input", "swipe", str(int(x)), str(int(y)),
      str(int(x)), str(int(y)), str(int(ms)))
    time.sleep(0.6)


def swipe(x1, y1, x2, y2, ms=300):
    d("shell", "input", "swipe", str(x1), str(y1), str(x2), str(y2), str(ms))
    time.sleep(0.6)


def launch(pkg, settle=2.5):
    sh([adb_exe(), "-s", serial(), "shell", "monkey", "-p", pkg, "-c",
        "android.intent.category.LAUNCHER", "1"], check=False, timeout=60)
    time.sleep(settle)


# ------------------------------------------------------------------ App 包名自动识别
# 换台电脑 App 版本可能不同(乐跑有 com.lptiyu.tanke 等变体), 所以不硬编码,
# 先按候选精确匹配, 再按关键字模糊找. 候选表见文件头配置区.

_PKG_FAKE = None
_PKG_RUN = None


def installed_packages():
    out = d("shell", "pm", "list", "packages", check=False)
    return set(x[len("package:"):].strip()
               for x in out.splitlines() if x.startswith("package:"))


def _match(pkgs, cands, keys, label):
    best = _match_in(pkgs, cands, keys)
    if best:
        LOG("[=] %s 包名识别为 %s" % (label, best))
    return best


def resolve_pkgs(strict=True):
    """返回 (fake_pkg, run_pkg), 任一没找到则 None.
    结果缓存到模块变量, launch/fl_* 都用解析后的包名."""
    global _PKG_FAKE, _PKG_RUN
    if _PKG_FAKE and _PKG_RUN:
        return _PKG_FAKE, _PKG_RUN

    pkgs = installed_packages()
    if not pkgs:
        if strict:
            raise RuntimeError(
                "读不到模拟器里的应用列表(pm list packages 为空)\n"
                "  先手动确认: \"%s\" -s %s shell pm list packages"
                % (adb_exe(), serial()))
        return None, None

    fake = _match(pkgs, _FAKE_CANDIDATES, _FAKE_KEYS, "FakeLocation")
    run = _match(pkgs, _RUN_CANDIDATES, _RUN_KEYS, "步道乐跑")

    missing = []
    if fake is None:
        missing.append("FakeLocation (关键字: FakeLocation)")
    if run is None:
        missing.append("步道乐跑 (关键字: lptiyu / tanke)")
    if missing:
        if strict:
            raise RuntimeError(
                "模拟器里没找到: %s\n"
                "  已安装的包共 %d 个, 前 20 个:\n    %s"
                % (", ".join(missing), len(pkgs),
                   "\n    ".join(sorted(pkgs)[:20])))
        return fake, run

    _PKG_FAKE, _PKG_RUN = fake, run
    return fake, run


def pkg_fake():
    return _PKG_FAKE or resolve_pkgs()[0]


def pkg_run():
    return _PKG_RUN or resolve_pkgs()[1]


def current_app():
    out = d("shell", "dumpsys", "window", check=False)
    m = re.findall(r"mCurrentFocus=Window\{\S+ \S+ ([\w.]+)/", out)
    return m[-1] if m else "?"


def screencap(local=None):
    local = local or SHOT_LOCAL
    if os.path.exists(local):
        try:
            os.remove(local)
        except OSError:
            pass
    d("shell", "screencap", "-p", SHOT, check=False, timeout=60)
    sh([adb_exe(), "-s", serial(), "pull", SHOT, local], check=False, timeout=60)
    return local if os.path.exists(local) and os.path.getsize(local) > 2000 else None


def read_screen(local=None):
    img = screencap(local)
    return OCR.ocr(img) if img else []


# ------------------------------------------------------------------ 屏幕尺寸自适应
# 所有写死的像素坐标都按 1080x1920 记录. 换一台电脑 MuMu 分辨率可能不同,
# 这里统一按比例换算, 调用方仍然可以写原始坐标.

BASE_W, BASE_H = 1080.0, 1920.0
_SCREEN = None


def screen_size():
    """返回 (w, h). 从 screencap 的 PNG 头直接读, 不依赖 dumpsys"""
    global _SCREEN
    if _SCREEN is not None:
        return _SCREEN

    out = d("shell", "wm", "size", check=False)
    m = re.findall(r"(\d+)\s*x\s*(\d+)", out or "")
    if m:
        w, h = int(m[-1][0]), int(m[-1][1])
        if w > h:                      # 统一成竖屏
            w, h = h, w
        _SCREEN = (w, h)
        return _SCREEN

    _SCREEN = (int(BASE_W), int(BASE_H))
    return _SCREEN


def sx(x):
    return int(round(float(x) * screen_size()[0] / BASE_W))


def sy(y):
    return int(round(float(y) * screen_size()[1] / BASE_H))


def texts(rows):
    return [r[0] for r in rows]


def tap_row(rows, keys, wait=2.5, exact=False):
    for key in keys:
        for txt, x1, y1, x2, y2 in rows:
            if ((txt == key) if exact else (key in txt)) is False:
                continue
            cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
            tap(cx, cy, wait)
            LOG("[+] 点『%s』@(%d,%d)" % (txt, cx, cy))
            return True
    return False


# ------------------------------------------------------------------ 静态界面 (uiautomator)

BOUNDS = re.compile(r"\[(\d+),(\d+)\]\[(\d+),(\d+)\]")


def dump_xml(retries=5, wait=1.0):
    for _ in range(retries):
        out = sh([adb_exe(), "-s", serial(), "shell", "uiautomator", "dump",
                  "/sdcard/ui.xml"], check=False, timeout=45)
        if "dumped" in out:
            xml = sh([adb_exe(), "-s", serial(), "exec-out", "cat", "/sdcard/ui.xml"],
                     check=False, timeout=45)
            i = xml.find("<?xml")
            if i >= 0:
                try:
                    return ET.fromstring(xml[i:])
                except ET.ParseError:
                    pass
        time.sleep(wait)
    return None


def nodes(root):
    return [] if root is None else list(root.iter("node"))


def rect_of(n):
    if n is None:
        return None
    m = BOUNDS.search(n.get("bounds") or "")
    return tuple(map(int, m.groups())) if m else None


def rid(n):
    return (n.get("resource-id") or "").rsplit("/", 1)[-1]


def pmap(root):
    p = {}
    for par in root.iter():
        for ch in par:
            p[ch] = par
    return p


def find(root, rid_=None, text=None):
    for n in nodes(root):
        if rid_ is not None and rid(n) == rid_:
            return n
        if text is not None and text in (n.get("text") or ""):
            return n
    return None


def tap_node(root, n, wait=2.0):
    p = pmap(root)
    cur = n
    while cur is not None and cur.get("clickable") != "true":
        cur = p.get(cur)
    tgt = cur if cur is not None else n
    rc = rect_of(tgt)
    tap((rc[0] + rc[2]) // 2, (rc[1] + rc[3]) // 2, wait)


def chrono_secs(rows=None):
    """从 OCR 行里解析 用时 秒数. 起跑的可靠判据: 计时器在走"""
    rows = rows if rows is not None else lp_state_raw()
    for txt, x1, y1, x2, y2 in rows:
        m = re.search(r"(\d{1,2})\s*[:：]\s*(\d{2})\s*[:：]\s*(\d{2})", txt)
        if not m:
            continue
        cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
        if _in_box(cx, cy, 300, 300, 760, 500):      # 顶部计时器区域
            return int(m.group(1)) * 3600 + int(m.group(2)) * 60 + int(m.group(3))
    return None


def lp_state_raw():
    if not current_app().startswith(pkg_run()):
        launch(pkg_run(), 1.5)
    return read_screen(shot_path("_state.png"))


def run_state():
    """running / idle / paused / home / None.

    坑: 底部 tv_start_pause_continue_run 是「开始 <-> 暂停」同一个开关.
    盲长按会把已经在跑的按成暂停, 所以必须先判当前相位再动作.
    跑步页地图每秒重绘, uiautomator dump 拿不到 idle state, 只能 OCR.
    """
    rows = read_screen(shot_path("_phase.png"))

    # 底部控制条: 只看 y>1650 的行, 避免顶部「平均配速」之类误命中
    labels = set()
    for txt, x1, y1, x2, y2 in rows:
        if (y1 + y2) // 2 < 1650:
            continue
        labels.add(txt)

    joined = " ".join(labels)
    if "结束" in joined and "继续" in joined:
        return "paused"
    if "暂停" in joined:
        return "running"
    if "开始乐跑" in joined:
        return "home"

    t = " ".join(x for x, *_ in rows)
    if "已打卡" in t and ("距你" in t or "未打卡" in t):
        return "idle"
    if "开始乐跑" in t:
        return "home"
    return None


def _timer_advancing(gap=4.0):
    """计时器在走 = 真的在跑. 比任何文字判据都硬"""
    a = chrono_secs()
    if a is None:
        return False
    time.sleep(gap)
    b = chrono_secs()
    return b is not None and b > a


def lp_start_checked():
    """把「跑步页 未起跑 / 暂停」推到「真的在跑」. 幂等, 已在跑直接返回.

    老版本自己又实现了一套 run_state()/长按逻辑, 和 lp_start() 打架:
    run_state() 在 dump 失败时返回 None, 被当成 idle 又长按一遍.
    现在统一交给 lp_start(), 相位判据只有 lp_bottom_btn() 一个来源.
    """
    return lp_start()


# ------------------------------------------------------------------ GPS 轨迹积分

def gps():
    """取当前 mock 定位 (FakeLocation 注入的那条).

    dumpsys location 里同一个坐标会挂在多个 provider 下 (network/gps/fused) 各出现一次,
    还可能有历史残留的真实定位. 只认带 'mock' 标记的; 多条 mock 时取 et 最大(最新)的.
    """
    out = d("shell", "dumpsys", "location", check=False, timeout=60)
    best = None          # (et_seconds, lat, lng)
    for line in out.splitlines():
        if "Location[" not in line or "mock" not in line:
            continue
        m = re.search(r"Location\[\w+ (-?\d+\.\d+),(-?\d+\.\d+)", line)
        if not m:
            continue
        et = 0.0
        me = re.search(r"\bet=\+(\d+)m([\d.]+)s", line)
        if me:
            et = int(me.group(1)) * 60 + float(me.group(2))
        pt = (float(m.group(1)), float(m.group(2)))
        if best is None or et >= best[0]:
            best = (et, pt[0], pt[1])
    if best is None:
        return None
    return (best[1], best[2])


def haversine(a, b):
    R = 6371000.0
    p1, p2 = math.radians(a[0]), math.radians(b[0])
    dp = p2 - p1
    dl = math.radians(b[1] - a[1])
    h = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * R * math.asin(math.sqrt(h))


class Track:
    """GPS 逐点累加, 与乐跑自身里程口径一致.

    采样越稀越不准: FakeLocation 每 ~0.5s 输出一个点, 30s 采一次等于把
    一整段折线压成一条弦, 里程会偏小; 而点太密时 GPS 抖动又会虚增.
    这里折中: 每个 poll 内高频采若干次, 用 haversine 累加, 单步 >200m 视为跳点丢弃.
    """

    def __init__(self):
        self.m = 0.0
        self.last = None
        self.samples = 0

    def reset(self):
        self.m = 0.0
        self.samples = 0
        self.last = gps()
        return self.last

    def step(self, n=8, gap=1.2):
        for _ in range(n):
            cur = gps()
            if cur is not None:
                if self.last is None:
                    self.last = cur
                else:
                    dist = haversine(self.last, cur)
                    if 0.0 < dist < 200.0:
                        self.m += dist
                        self.last = cur
                    elif dist >= 200.0:
                        LOG("[!] 跳点 %.0fm, 丢弃" % dist)
                        self.last = cur
                self.samples += 1
            time.sleep(gap)
        return self.m

    @property
    def km(self):
        return self.m / 1000.0


# ------------------------------------------------------------------ 步道乐跑

def lp_skip_popups(rows, rounds=4):
    """开屏广告 / 未完成记录恢复 / 定位失败提示.

    恢复弹窗的文字会被 OCR 拆成多行(「是否恢复跑步？」被切成两行),
    所以这里用资源 id + 固定坐标双保险, 不依赖整句匹配.
    """
    for _ in range(rounds):
        t = " ".join(texts(rows))

        # 未完成记录: 选【放弃】(左边那个)
        if "未完成" in t or "是否恢复跑步" in t or "是否复跑步" in t:
            LOG("[=] 有未完成记录, 选 放弃")
            root = dump_xml()
            n = find(root, rid_="dialog_cancel") if root is not None else None
            if n is not None:
                tap_node(root, n, 2.5)
            else:
                tap(sx(344), sy(1130), 2.5)        # 实测【放弃】位置
            rows = read_screen(shot_path("_lp.png"))
            continue

        # 定位失败: 点【重新获取】; 仍失败则先把模拟拉起来
        if "获取当前位置失败" in t:
            if tap_row(rows, ("重新获取",), wait=3):
                LOG("[=] 点 重新获取 定位")
                rows = read_screen(shot_path("_lp.png"))
                if "获取当前位置失败" in " ".join(texts(rows)):
                    LOG("[!] 仍无定位, 去启动路线模拟")
                    try:
                        fl_ensure_simulating()
                    except Exception as e:
                        LOG("[!] 启动模拟失败: %s" % e)
                    launch(pkg_run(), 2.0)
                rows = read_screen(shot_path("_lp.png"))
                continue
            if tap_row(rows, ("取消",), wait=2, exact=True):
                rows = read_screen(shot_path("_lp.png"))
                continue

        hit = False
        for key in ("跳过", "以后再说", "暂不", "关闭"):
            for txt, x1, y1, x2, y2 in rows:
                if txt.strip() == key:
                    tap((x1 + x2) // 2, (y1 + y2) // 2, 2.5)
                    LOG("[+] 关闭弹层『%s』" % key)
                    hit = True
                    break
            if hit:
                break
        if not hit:
            return rows
        rows = read_screen(shot_path("_lp.png"))
    return rows


def lp_enter_run(max_rounds=6):
    """进跑步页面并长按起跑.

    首页会先出现「正在获取当前位置」/未完成记录恢复/开屏广告等中间态,
    单次点击常常落空, 所以整条点击链包成状态机重试: 每轮重新截图判断在哪一步.
    """
    launch(pkg_run())

    for rnd in range(max_rounds):
        rows = lp_skip_popups(read_screen(shot_path("_lp.png")))
        t = texts(rows)
        LOG("[=] 第%d轮界面: %s" % (rnd + 1, t[:12]))

        if run_state() == "running" and _timer_advancing(gap=2.0):
            LOG("[=] 已在跑步中")
            return True

        # 跑步页: 有已打卡/打卡点列表
        if any("已打卡" in x for x in t) or any("距你" in x for x in t):
            break

        # 加载态 / 未完成弹窗还在: 等或交给下一轮 popups
        if any("正在获取当前位置" in x for x in t):
            LOG("[=] 等待定位/加载")
            time.sleep(4)
            continue
        if "未完成" in " ".join(t):
            time.sleep(2)
            continue

        root = dump_xml()
        # 开始乐跑
        n = find(root, rid_="tv_enterRun") if root is not None else None
        if n is not None:
            tap_node(root, n, 3.5)
            LOG("[+] 已点 开始乐跑")
            continue
        # 安全提示
        n = find(root, rid_="tv_sure") if root is not None else None
        if n is not None:
            tap_node(root, n, 4.5)
            LOG("[+] 已点 进入乐跑")
            continue
        # before_run
        n = find(root, text="进入跑步") if root is not None else None
        btn = find(root, rid_="button1") if root is not None else None
        if n is not None and btn is not None:
            tap_node(root, btn, 4.5)
            LOG("[+] 已通过 before_run 弹窗")
            continue
        # 不在乐跑 tab
        n = find(root, rid_="rl_run") if root is not None else None
        if n is not None:
            tap_node(root, n, 2.5)
            LOG("[+] 已点 乐跑 tab")
            continue

        time.sleep(2)

    if run_state() == "running" and _timer_advancing(gap=2.0):
        return True

    rows = read_screen(shot_path("_lp.png"))
    if not any("已打卡" in x for x in texts(rows)):
        raise RuntimeError("没进到跑步页面: %s" % texts(rows)[:14])

    LOG("[=] 在跑步页面, 起跑")
    return lp_start_checked()


# 跑步页 uiautomator 拿不到 idle state(地图每秒重绘), 所以「是不是已经到首页/跑步页」
# 只能靠这几个 rid 判. 这些都是静态控件, 不受动画影响, dump 就算超时也能拿到部分树.
LP_HOME_IDS = ("rl_run", "tv_enterRun")
LP_RUN_IDS = ("tv_start_pause_continue_run", "chronometer",
              "tv_distance_value", "tv_log_num_value")


def lp_ids():
    """dump 一次, 返回当前页面上所有 resource-id 的集合. 拿不到返回空集"""
    root = dump_xml(retries=2)
    if root is None:
        return set()
    return set(i for i in (rid(n) for n in nodes(root)) if i)


def lp_is_open():
    """乐跑是不是已经在前台了(不区分首页/跑步页)"""
    return current_app().startswith(pkg_run())


def lp_wait_ready(seconds=25):
    """打开乐跑后等它加载到出控件为止.

    刚 monkey 起来会有开屏广告 / 「正在获取当前位置」, 这段时间 rid 树是空的.
    这里只看 dump 里有没有出现任意一个乐跑控件, 不做文字判断 —— 换电脑没装
    中文 OCR 语言包也能用.
    """
    t0 = time.time()
    while time.time() - t0 < seconds:
        ids = lp_ids()
        if ids & set(LP_HOME_IDS + LP_RUN_IDS):
            return True
        time.sleep(2)
    return False


def lp_running():
    """乐跑是不是正在跑(不管在前台还是后台).

    跑步页 uiautomator dump 一定失败(地图每秒重绘), 所以不能靠 rid.
    这里看 activity 栈里有没有乐跑的 MapRunActivity —— 有就是跑步任务还在.
    注意: 前台可能是别的 App(比如 FakeLocation), 乐跑在后台照样计时,
    所以这里只判「有没有在跑」, 前台的事交给 lp_open 处理.
    """
    out = d("shell", "dumpsys", "activity", "activities", check=False, timeout=60)
    if pkg_run() not in (out or ""):
        return False
    return "MapRunActivity" in out


def lp_foreground():
    """乐跑是不是在前台."""
    out = d("shell", "dumpsys", "window", check=False, timeout=60)
    for line in (out or "").splitlines():
        if "mCurrentFocus" in line and pkg_run() in line:
            return True
    return False


def lp_open(pkg=None):
    """把步道乐跑拉起来并推进到「乐跑」tab 的跑步页. 纯 rid 驱动, 零 OCR.

    FakeLocation 已经启动路线模拟的前提下才会走到这里 —— 首页要拿一次定位,
    没有 mock 点会卡在「获取当前位置失败」.
    返回 True 表示已经停在可起跑的页面上.
    """
    pkg = pkg or pkg_run()

    # 已在跑步页就别再 monkey 一次, 会把当前状态顶掉
    ids = lp_ids()
    if ids & set(LP_RUN_IDS):
        LOG("[=] 已经在跑步页")
        return True

    # ★ 跑步中 uiautomator dump 必然失败(地图每秒重绘, 见 6.2), 上面 lp_ids() 拿不到东西.
    #   所以先用 activity 栈判断乐跑是不是已经在跑 —— 跑步任务在, 就只把它切到前台,
    #   绝不再点一遍(会把状态顶掉, 也可能被误判成「打不开乐跑」).
    if lp_running():
        if lp_foreground():
            LOG("[=] 步道乐跑在跑步中且已在前台, 不用再操作")
        else:
            LOG("[=] 步道乐跑在后台跑着, 切到前台")
            launch(pkg, 3.0)
            if lp_foreground():
                LOG("[+] 已切到前台")
            else:
                LOG("[!] 没切到前台, 手动在模拟器里切一下也行, 跑步没停")
        return True

    if not lp_is_open():
        LOG("[=] 启动步道乐跑")
        launch(pkg, 4.0)
    else:
        LOG("[=] 步道乐跑已在前台")

    if not lp_wait_ready():
        LOG("[!] 等了 25s 没看到乐跑控件, 可能卡在开屏广告或定位失败; 继续尝试点击")

    # ★ 关键: dump 连续失败本身就是「已经进跑步页」的强信号 ——
    #   跑步页地图每秒重绘, uiautomator 永远拿不到 idle state (见 6.2).
    #   所以这里数连续失败次数, 攒够 3 次就用 OCR 确认一次, 而不是死等 8 轮后报错.
    dump_fail = 0
    for rnd in range(12):
        root = dump_xml(retries=2)
        if root is None:
            dump_fail += 1
            LOG("[=] 乐跑第%d轮: dump 失败(%d/3)" % (rnd + 1, dump_fail))
            if dump_fail >= 3:
                # 用截图 OCR 判: 底部出现「长按暂停」/「长按开始」= 到跑步页了
                btn = lp_bottom_btn()
                if btn in ("running", "paused", "idle"):
                    LOG("[+] 已到跑步页 (dump 全失败 + 底部按钮=%s)" % btn)
                    return True
                # 也看看 activity 是不是 MapRunActivity
                if lp_running():
                    LOG("[+] 已到跑步页 (activity 是 MapRunActivity)")
                    return True
            time.sleep(3)
            continue
        dump_fail = 0
        ids = set(i for i in (rid(n) for n in nodes(root)) if i)
        LOG("[=] 乐跑第%d轮: %s" % (rnd + 1, sorted(ids)[:8]))

        # 1) 已经在跑步页
        if ids & set(LP_RUN_IDS):
            LOG("[+] 已到跑步页")
            return True

        # 2) 「未完成」恢复弹窗 —— 放弃上一段, 否则进不去新的
        if "dialog_cancel" in ids:
            n = find(root, rid_="dialog_cancel")
            if n is not None:
                tap_node(root, n, 2.5)
                LOG("[=] 放弃未完成记录")
                continue

        # 2.5) 成绩规则页(activity_school_run_rules) —— 点右上角 close_t 关掉.
        #      这一页会一直挡着, 不关永远到不了跑步页.
        if "activity_school_run_rules" in ids or "close_t" in ids:
            n = find(root, rid_="close_t")
            if n is None:
                d("shell", "input", "keyevent", "KEYCODE_BACK", check=False)
                LOG("[=] 成绩规则页: 按返回")
            else:
                tap_node(root, n, 2.5)
                LOG("[=] 关掉成绩规则页")
            continue

        # 3) 各种确认弹窗(权限/辅助功能/重新获取定位)
        hit = False
        for r in ("dialog_confirm", "tv_sure", "button1", "tv_but2", "tv_button"):
            if r not in ids:
                continue
            n = find(root, rid_=r)
            if n is not None:
                tap_node(root, n, 3.0)
                LOG("[=] 关掉弹窗 %s" % r)
                hit = True
                break
        if hit:
            continue

        # 4) 首页「开始乐跑」
        if "tv_enterRun" in ids:
            n = find(root, rid_="tv_enterRun")
            if n is not None:
                tap_node(root, n, 3.5)
                LOG("[+] 已点 开始乐跑")
                continue

        # 5) 不在乐跑 tab —— 切过去
        if "rl_run" in ids:
            n = find(root, rid_="rl_run")
            if n is not None:
                tap_node(root, n, 2.5)
                LOG("[+] 已点 乐跑 tab")
                continue

        # 6) 什么都没有: 可能还在加载, 再等一轮
        time.sleep(3)

    root = dump_xml(retries=2)
    if root is None:
        # dump 全失败: 基本可以断定在跑步页了
        if lp_running() or lp_bottom_btn() in ("running", "paused", "idle"):
            LOG("[+] 已到跑步页 (dump 全失败, 但确认是跑步页)")
            return True
    ids = set(i for i in (rid(n) for n in nodes(root)) if i) if root is not None else set()
    if ids & set(LP_RUN_IDS):
        LOG("[+] 已到跑步页")
        return True
    raise RuntimeError(
        "没能打开步道乐跑到跑步页 (最后一轮控件: %s)\n"
        "  最常见原因: FakeLocation 的 mock 定位没生效, 首页卡在「获取当前位置失败」."
        % sorted(ids)[:10])


def lp_chrono():
    """读顶部计时器文字(rid=chronometer). 拿不到返回 None.

    不用 OCR —— chronometer 是控件自己的 text 属性, dump 直接读, 换电脑也能用.
    """
    root = dump_xml(retries=2)
    if root is None:
        return None
    n = find(root, rid_="chronometer")
    return (n.get("text") or "").strip() if n is not None else None


def lp_bottom_btn():
    """OCR 读底部控制条, 判断当前相位. 返回 'running' / 'paused' / 'idle' / None.

    ★ 为什么不能只靠 chronometer: 跑步中 uiautomator dump 必然失败(地图每秒重绘),
      lp_chrono() 于是返回 None, 早期版本把 None 当成「还没起跑」,
      于是盲长按 —— 结果把正跑着的计时器按成暂停, 里程停在那儿.

    底部实测三种形态:
      运行中 -> 中间一个大按钮「长按暂停」
      已暂停 -> 左「继续」(x≈288) + 右「结束」(x≈792)
      未起跑 -> 中间一个大按钮「长按开始」

    ★ 早期裁剪框是 300..780, 正好把 x≈288 的「继续」和 x≈792 的「结束」切掉了,
      于是「已暂停」这个相位根本读不出来, 被当成 None 往下走. 这里放宽到 150..930.
    """
    try:
        rows = read_screen()
    except Exception:
        return None
    if not rows:
        return None
    hit = set()
    for txt, x1, y1, x2, y2 in rows:
        cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
        if not _in_box(cx, cy, 150, 1690, 930, 1900):
            continue
        if "暂停" in txt:
            hit.add("running")
        elif "继续" in txt:
            hit.add("paused")
        elif "开始" in txt:
            hit.add("idle")
    for k in ("running", "paused", "idle"):
        if k in hit:
            return k
    return None


def lp_continue_btn():
    """暂停态下点左下『继续』(实测 x≈288, y≈1812). 点完确认计时在走."""
    w, h = screen_size()
    tap(int(288 * w / BASE_W), int(1812 * h / BASE_H), 2.5)
    LOG("[+] 点底部『继续』恢复计时")
    for _ in range(4):
        time.sleep(1.5)
        if lp_bottom_btn() == "running":
            return True
        if _timer_advancing(gap=2.0):
            return True
    return lp_bottom_btn() == "running"


def lp_start(max_press=3):
    """在跑步页把状态推到「真的在跑」. 幂等.

    ★ 用户定的规矩: 起跑阶段**绝不点暂停**. 整个流程只有「起跑」和「继续」两种动作,
      暂停只在收尾(结束并上传)时才可能需要.
      底部 tv_start_pause_continue_run 是一个开关, 盲长按会把正在跑的按成暂停,
      所以先判相位再动手:
        running -> 什么都不做
        paused  -> 点左边『继续』(不是长按!)
        idle    -> 长按中间按钮起跑
    """
    btn = lp_bottom_btn()
    cur = lp_chrono()
    LOG("[=] 起跑前: 按钮=%s 计时器=%s" % (btn, cur))

    if btn == "running":
        LOG("[=] 底部按钮已经是「长按暂停」, 正在跑, 不重复长按")
        return True
    if cur and cur != "00:00:00":
        LOG("[=] 已经在跑, 不重复长按")
        return True
    if btn == "paused":
        LOG("[=] 底部是【继续】【结束】, 处于暂停态 -> 点继续")
        return lp_continue_btn()

    if btn is None and cur is None:
        # 两个信号都读不到. 可能是: (a) 乐跑不在前台, OCR 看到的是别的 App;
        # (b) 正在地图重绘. 先确认前台, 再看一次.
        if not lp_foreground():
            LOG("[=] 乐跑不在前台, 切过去再看")
            launch(pkg_run(), 3.0)
            btn = lp_bottom_btn()
            cur = lp_chrono()
            LOG("[=] 复检: 按钮=%s 计时器=%s" % (btn, cur))
        if btn == "running" or (cur and cur != "00:00:00"):
            LOG("[=] 已经在跑, 不重复长按")
            return True
        if btn == "paused":
            return lp_continue_btn()
        if btn is None and cur is None:
            # 还在跑的任务说明计时在走, 长按的风险是把它按暂停, 比不起跑更糟
            if lp_running():
                LOG("[!] 相位读不到但跑步任务在, 保守判定已在跑, 不乱长按")
                return True
            LOG("[!] 相位读不到, 也不在跑步中; 先不动, 手动看一眼")
            return True

    for ms in (2200, 3000, 4000)[:max_press]:
        long_press(sx(559), sy(1812), ms)
        time.sleep(3.0)

        # 长按后用 OCR 看按钮有没有切成「长按暂停」—— 这个判据不受 dump 失败影响
        btn = lp_bottom_btn()
        if btn == "running":
            LOG("[+] 已起跑 (长按 %dms)" % ms)
            return True
        now = lp_chrono()
        if now and now != "00:00:00":
            LOG("[+] 已起跑 (长按 %dms, 计时器 %s)" % (ms, now))
            return True

        # ★ 相位读不到时绝不能盲目再长按: 底部按钮是开关, 第二下就是把刚起跑的
        #   任务按成暂停 (用户实测踩到的就是这一下). 只有明确读到 idle 才允许再按.
        if btn is None:
            time.sleep(2.0)
            btn = lp_bottom_btn()
            LOG("[=] 长按 %dms 后复检: 按钮=%s 计时器=%s" % (ms, btn, now))
            if btn in ("running", "paused"):
                break
            if btn is None:
                if lp_running():
                    LOG("[=] 相位读不到但 activity 是 MapRunActivity, 就当起跑了, 不再长按")
                    return True
                LOG("[!] 相位彻底读不到, 停止重试, 避免误按暂停")
                break

        if btn == "paused":
            # 长按出来【继续】【结束】= 当前是暂停态, 点继续
            return lp_continue_btn()

        LOG("[=] 长按 %dms -> 按钮=%s 计时器=%s, 仍是未起跑, 再试" % (ms, btn, now))

    btn = lp_bottom_btn()
    if btn in ("running", "paused") or (lp_chrono() or "00:00:00") != "00:00:00":
        return True
    raise RuntimeError("多次长按都没起跑 (按钮=%s), 手动看一眼跑步页" % btn)


DIST_RE = re.compile(r"(\d{1,2})\s*[.．。,·，]\s*(\d{1,3})")


NUM_ONLY = re.compile(r"^(\d{1,2})\s*[.．。,·，]\s*(\d{1,3})$")


def _in_box(cx, cy, x1, y1, x2, y2):
    """按 1080x1920 基准框判断, 内部换成实际屏幕比例"""
    w, h = screen_size()
    return (x1 * w / BASE_W <= cx <= x2 * w / BASE_W
            and y1 * h / BASE_H <= cy <= y2 * h / BASE_H)


def parse_km(rows):
    """屏幕橙色公里数 —— 仅供参考, 不参与判定.

    OCR 把这串大号橙字认得很烂(实测 "2.6" 会出来 "圓6"), 所以:
      * 只接受能无歧义解析的读数;
      * "5.0" 这种 1 位整数 + 1 位小数, 无法区分 0.50 / 5.0, 直接丢弃返回 None.
    真正的里程判定走 Track —— 对 FakeLocation 注入的 mock 坐标做 haversine 积分,
    那是实测真值, 不受 OCR 影响.
    """
    for txt, x1, y1, x2, y2 in rows:
        cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
        if not _in_box(cx, cy, 30, 100, 400, 330):
            continue
        s = txt.strip()
        m = NUM_ONLY.match(s)
        if not m:
            continue
        whole, frac = m.group(1), m.group(2)
        if len(whole) == 1 and len(frac) == 1:
            # 0.26 vs 2.6 分不清, 宁可不给
            LOG("[!] 里程读数歧义 (%r), 忽略" % s)
            return None
        return float("%s.%s" % (whole, frac))
    return None


def lp_state(tries=4):
    """读 距离/打卡数/用时/打卡点. 纯 screencap + OCR, OCR 偶发漏字所以重试"""
    if not current_app().startswith(pkg_run()):
        launch(pkg_run(), 1.5)

    rows = []
    for i in range(tries):
        rows = read_screen(shot_path("_state.png"))
        if parse_km(rows) is not None and chrono_secs(rows) is not None:
            break
        if i < tries - 1:
            time.sleep(1.5)

    st = {"km": parse_km(rows), "points": None, "time": chrono_secs(rows),
          "detail": [], "rows": rows}

    for txt, x1, y1, x2, y2 in rows:
        cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
        if _in_box(cx, cy, 820, 320, 1000, 450):
            m = re.search(r"(\d+)", txt)
            if m:
                st["points"] = int(m.group(1))
                break

    names = [r[0] for r in rows
             if _in_box((r[1] + r[3]) // 2, (r[2] + r[4]) // 2, 0, 1500, 1080, 1920)
             and ("距你" in r[0] or "米" in r[0])]
    flags = [r[0] for r in rows
             if _in_box((r[1] + r[3]) // 2, (r[2] + r[4]) // 2, 0, 1500, 1080, 1920)
             and ("已打卡" in r[0] or "未打卡" in r[0])]
    st["detail"] = list(zip(names, flags))
    if flags and st["points"] is None:
        st["points"] = sum(1 for f in flags if "未" not in f)

    LOG("[=] 屏幕=%s km  打卡=%s  用时=%s" % (st["km"], st["points"], st["time"]))
    for n, f in st["detail"]:
        LOG("      %s -> %s" % (n, f))
    return st


# 底部控制条 / 弹窗的裁剪区 (基准 1080x1920), 运行时按实际分辨率换算
BOTTOM_BOX = (0, 1690, 1080, 1920)
DIALOG_BOX = (0, 820, 1080, 1300)
CROP_SCALE = 3


def _crop(box, scale=CROP_SCALE):
    """把基准框换算成实际像素的 (x, y, w, h, scale)"""
    w, h = screen_size()
    x1 = int(box[0] * w / BASE_W)
    y1 = int(box[1] * h / BASE_H)
    x2 = int(box[2] * w / BASE_W)
    y2 = int(box[3] * h / BASE_H)
    return (x1, y1, max(1, x2 - x1), max(1, y2 - y1), scale)


def _unscale(rows, box, scale=CROP_SCALE):
    """把裁剪区 OCR 坐标还原成全屏坐标"""
    w, h = screen_size()
    ox = int(box[0] * w / BASE_W)
    oy = int(box[1] * h / BASE_H)
    out = []
    for txt, x1, y1, x2, y2 in rows:
        out.append((txt,
                    ox + x1 // scale, oy + y1 // scale,
                    ox + x2 // scale, oy + y2 // scale))
    return out


def bottom_rows():
    """放大只 OCR 底部控制区 —— 全图 OCR 认不出底部按钮"""
    img = screencap(shot_path("_bottom.png"))
    if not img:
        return []
    return _unscale(OCR.ocr(img, crop=_crop(BOTTOM_BOX)), BOTTOM_BOX)


def tap_bottom(keys, wait=2.5):
    rows = bottom_rows()
    LOG("[=] 底部按钮: %s" % [(r[0], (r[1] + r[3]) // 2, (r[2] + r[4]) // 2) for r in rows])
    for key in keys:
        for txt, x1, y1, x2, y2 in rows:
            if key not in txt:
                continue
            cx = (x1 + x2) // 2
            cy = (y1 + y2) // 2
            tap(cx, cy, wait)
            LOG("[+] 点底部『%s』@(%d,%d)" % (txt, cx, cy))
            return True
    return False


def dialog_rows():
    """放大 OCR 弹窗区, 避免把提示正文当成按钮"""
    img = screencap(shot_path("_dlg.png"))
    if not img:
        return []
    return _unscale(OCR.ocr(img, crop=_crop(DIALOG_BOX, 2)), DIALOG_BOX, 2)


def tap_dialog(keys, wait=3.0):
    """只在弹窗区里找短文本按钮 (长度<=6), 排除提示正文"""
    rows = dialog_rows()
    LOG("[=] 弹窗: %s" % [r[0] for r in rows])
    for key in keys:
        for txt, x1, y1, x2, y2 in rows:
            s = txt.strip()
            if key not in s or len(s) > 6:
                continue
            cx = (x1 + x2) // 2
            cy = (y1 + y2) // 2
            tap(cx, cy, wait)
            LOG("[+] 点弹窗『%s』@(%d,%d)" % (s, cx, cy))
            return True
    return False


def lp_stop_and_upload():
    """停止并上传. 实测交互链:
        长按底部按钮暂停 -> 底部出现【继续】【结束】
        -> 点【结束】 -> 弹窗「确定结束跑步并保存上传记录吗？」点【结束】
        -> 「结束跑步·上传预览」页(显示距离/有效定位点/配速区间)
        -> 点右下【上传】 -> 页面出现「上传成功」/『完成一次跑步!』

    ★ 两个实测要点:
      1) 底部【结束】按钮得点两下才进弹窗(第一次只是切换选中态), 中间隔 2s 再点;
      2) 上传成功后先弹「完成一次跑步!」广告弹窗, 再后是轨迹详情页.
         看到『完成一次跑步』就已经算上传成功, 不必等「上传成功」四个字.
    """
    if not current_app().startswith(pkg_run()):
        launch(pkg_run(), 1.5)

    # 已经在跑步页但不确定相位: 先看底部有没有【继续】【结束】, 没有才长按
    for attempt in range(3):
        rows = bottom_rows()
        line = texts(rows)
        if any("继续" in x for x in line) and any("结束" in x for x in line):
            LOG("[=] 底部已是【继续】【结束】, 处于暂停态")
            break
        if any("长按暂停" in x for x in line):
            LOG("[=] 长按底部按钮暂停")
            long_press(sx(559), sy(1812), 2200)
            time.sleep(2.5)
            continue
        # 都不是, 可能在别的页面
        LOG("[=] 第%d次: 底部没找到暂停/继续, 当前: %s" % (attempt + 1, line[:8]))
        if attempt == 0:
            lp_enter_run()
        time.sleep(2.0)
    else:
        LOG("[!] 没能确认暂停态, 继续尝试往下走")

    # 点【结束】—— 实测要连点两次, 第一次可能只切换状态没弹窗
    for i in range(3):
        if not tap_bottom(("结束",), wait=2.5):
            LOG("[!] 底部没找到『结束』, 固定坐标兜底")
            tap(sx(792), sy(1812), 2.5)
        time.sleep(2.0)
        rows = read_screen(shot_path("_stop_chk%d.png" % (i + 1)))
        line = texts(rows)
        if any("确定结束" in x for x in line) or any("上传预览" in x for x in line):
            break
        LOG("[=] 点结束第%d次, 未见弹窗, 当前: %s" % (i + 1, line[:10]))

    for i in range(10):
        rows = read_screen(shot_path("_stop%d.png" % (i + 1)))
        line = texts(rows)
        LOG("[=] 第%d层: %s" % (i + 1, line[:14]))

        # 上传成功: 「完成一次跑步!」/「上传成功」都算
        if any(k in x for x in line
               for k in ("上传成功", "成绩已上传", "已上传", "上传完成",
                         "完成一次跑步", "恭喜你")):
            LOG("[+] 成绩已上传")
            return True

        # 上传预览页: 底部 左【丢弃】 右【上传】
        if any("上传预览" in x for x in line):
            w, h = screen_size()
            if tap_row([r for r in rows if (r[2] + r[4]) // 2 > h * 1400 // BASE_H],
                       ("上传",), wait=4, exact=True):
                continue
            tap(sx(859), sy(1495), 4)          # 实测坐标兜底
            continue

        # 确认弹窗「确定结束跑步并保存上传记录吗?」—— 取消 / 结束
        if "确定结束跑步" in " ".join(line):
            # 弹窗里两个按钮都在 x>600 区域的是【结束】; 先精确找
            dlg = [r for r in rows if _in_box((r[1] + r[3]) // 2,
                                              (r[2] + r[4]) // 2,
                                              400, 1000, 1000, 1200)]
            if tap_row(dlg, ("结束",), wait=3.5, exact=True):
                continue
            tap(sx(734), sy(1092), 3.5)        # 实测坐标兜底
            continue

        if not tap_dialog(("上传成绩", "上传", "确定", "确认", "提交", "保存"), wait=3.5):
            if not tap_row(rows, ("上传成绩", "上传", "确定", "确认", "提交"), wait=3.5):
                break

    rows = read_screen(shot_path("_stop_end.png"))
    LOG("[=] 最终界面: %s" % texts(rows)[:18])
    ok = any(k in x for x in texts(rows)
             for k in ("上传成功", "完成一次跑步", "恭喜你"))
    LOG("[+] 上传成功" if ok else "[!] 未见『上传成功』, 请人工确认")
    return ok


# ------------------------------------------------------------------ FakeLocation
#
# 全 rid 驱动, 不依赖 OCR. FakeLocation 的路线模拟页结构(实测 v1 加固版):
#   未运行: f_route_btn_service_switch + f_route_tv_service_switch='启动模拟'
#   运行中: f_route_tv_service_pause (='暂停') + f_route_tv_service_switch='停止模拟'
#   速度:   f_route_btn_set_speed —— 但被可点父容器 f_route_ll_target_route
#           ([72,732][1008,1151]) 包住, 触摸会被截走跳『选择路线』页, 面板打不开.
#           实测默认速度配速 10'15"/km (1.71 m/s), 本就是正常步行速度, 不改也过.
#
# 抽屉菜单坐标(实测): 位置模拟 684-828 / 路线模拟 828-972 / WIFI 972-1116 /
#                      独立模拟 1116-1260 / 反检测 1260-1404 / ROOT隐藏 1404-1548

FL_PKG = None      # 运行时取 pkg_fake()
FL_SPEED_DEFAULT = 2.5
FL_DRAWER_ROUTE = (420, 900)      # 抽屉里「路线模拟」的中心


def fl_state_ocr():
    """dump 失败时的兜底: 截图 OCR 读路线模拟页那两个按钮.

    按钮实测位置(1080x1920 基准):
      暂停/继续   [72,1067][252,1151]  中心 (162,1109)
      启动/停止   [276,1067][540,1151] 中心 (408,1108)
    返回同 fl_state(): 'running' / 'paused' / 'stopped' / None
    """
    try:
        rows = read_screen()
    except Exception:
        return None
    if not rows:
        return None
    pause_txt = ""
    switch_txt = ""
    for txt, x1, y1, x2, y2 in rows:
        cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
        if not _in_box(cx, cy, 40, 1030, 560, 1190):
            continue
        if cx < 270:
            pause_txt += txt
        else:
            switch_txt += txt
    if "继续" in pause_txt:
        return "paused"
    if "暂停" in pause_txt:
        return "running"
    if "停止" in switch_txt:
        return "running"
    if "启动" in switch_txt:
        return "stopped"
    return None


def fl_state():
    """返回 'running' / 'paused' / 'stopped' / None(不在路线模拟页).

    以 rid + 文字判定, 不用 OCR —— 加固版 FakeLocation 的界面文字 OCR 极不稳.

    ★ 关键: f_route_tv_service_pause 这个节点在「暂停」和「继续」两种状态下**都存在**,
      只有文字不同. 早期版本只判 rid 是否存在, 于是暂停被误判成 running,
      fl_start() 直接返回「已在运行」, 结果 mock 坐标一动不动, 乐跑里程永远是 0.
      这里必须读文字:
        文字含「继续」 -> paused (已启动但暂停, 点它 = 继续跑)
        文字含「暂停」 -> running

    ★ 第二关键: dump 读不到时**必须返回 None 而不是猜**. 早期 fl_start() 把 None
      当「没启动」去点 f_route_btn_service_switch, 而那个位置在运行态写的是
      「停止模拟」—— 一点就把模拟停了. 就是用户说的「你为什么要点击暂停」.
      dump 失败时这里退到 OCR 兜底, 两个都拿不到才返回 None.
    """
    root = dump_xml(retries=2)
    if root is None:
        return fl_state_ocr()
    n = find(root, rid_="f_route_tv_service_pause")
    if n is not None:
        t = (n.get("text") or "").strip()
        if "继续" in t:
            return "paused"
        return "running"          # 「暂停」或空文字都按运行中算
    sw = find(root, rid_="f_route_tv_service_switch")
    if sw is not None:
        t = (sw.get("text") or "").strip()
        if "停止" in t:
            return "running"
        return "stopped"
    if find(root, rid_="f_route_btn_service_switch") is not None:
        return "stopped"
    return fl_state_ocr()


def _fl_close_popups():
    """FakeLocation 冷启动可能弹: 无障碍服务提示 / ROOT 授权 / 免责声明.
    有就点掉, 没有就立刻返回."""
    for _ in range(3):
        root = dump_xml(retries=2)
        if root is None:
            return
        ids = [i for i in (rid(n) for n in nodes(root)) if i]
        hit = False
        # 假定位的通用确认按钮只有这两个 id 比较稳
        for r in ("dialog_confirm", "md_buttonDefaultPositive", "button1"):
            if r in ids:
                n = find(root, rid_=r)
                if n is not None:
                    tap_node(root, n, 2.0)
                    LOG("[=] 关掉 FakeLocation 弹窗(%s)" % r)
                    hit = True
                    break
        if hit:
            continue
        # 文字兜底: 同意 / 确定 / 我知道了
        txts = [(n.get("text") or "").strip() for n in nodes(root)]
        for want in ("同意", "确定", "我知道了", "允许"):
            if want in txts:
                n = find(root, text=want)
                if n is not None:
                    tap_node(root, n, 2.0)
                    LOG("[=] 关掉 FakeLocation 弹窗(%s)" % want)
                    hit = True
                    break
        if not hit:
            return


def _fl_open_drawer():
    """打开左侧抽屉. 多策略: 无障碍描述 -> 左边缘滑出 -> 固定坐标."""
    root = dump_xml(retries=2)
    if root is not None:
        for n in nodes(root):
            dsc = n.get("content-desc") or ""
            if dsc.startswith("Open navigation") or dsc.startswith("打开导航"):
                tap_node(root, n, 2.0)
                return True
    # 从最左边缘往右滑, 抽屉一定能拉出来
    swipe(sx(1), sy(900), sx(900), sy(900), 300)
    time.sleep(1.5)
    root = dump_xml(retries=2)
    if root is not None:
        for n in nodes(root):
            if (n.get("text") or "").strip() == "路线模拟":
                return True
    # 再兜一次: 汉堡按钮的常见位置
    tap(sx(60), sy(150), 2.0)
    return False


def _fl_finish_route_select():
    """『路线模拟』菜单项会先进到 选择路线 页(a_select_route_*), 点右下角
    『完成』(a_select_route_btn_done) 才落到真正的路线模拟页(f_route_*).
    这是实测的必经中间页, 不是异常."""
    root = dump_xml(retries=2)
    if root is None:
        return False
    ids = set(i for i in (rid(n) for n in nodes(root)) if i)
    if not any(i.startswith("a_select_route") for i in ids):
        return False
    done = find(root, rid_="a_select_route_btn_done")
    if done is None:
        return False
    tap_node(root, done, 3.0)
    LOG("[=] 过了『选择路线』页")
    return True


def fl_open_route(retries=3):
    """打开 FakeLocation 并进到 路线模拟 页. 已在则直接返回.

    实测路径(加固版):
      冷启动 -> 位置模拟(f_fakeloc_*) -> 汉堡抽屉 -> 点『路线模拟』
             -> 选择路线页(a_select_route_*) -> 点『完成』 -> 路线模拟页(f_route_*)
    """
    if fl_state():
        return
    launch(pkg_fake(), 3.5)
    if fl_state():
        return

    last = None
    for attempt in range(retries):
        _fl_close_popups()
        # 冷启动 / 上一步残留可能已经在选择路线页, 先过掉
        if _fl_finish_route_select() and fl_state():
            LOG("[+] 已进入路线模拟页")
            return
        if fl_state():
            LOG("[+] 已进入路线模拟页")
            return

        _fl_open_drawer()

        # 抽屉里点『路线模拟』: 先按文字, 再按固定坐标
        root = dump_xml(retries=2)
        tapped = False
        if root is not None:
            for n in nodes(root):
                if (n.get("text") or "").strip() == "路线模拟":
                    tap_node(root, n, 3.0)
                    tapped = True
                    break
        if not tapped:
            tap(sx(FL_DRAWER_ROUTE[0]), sy(FL_DRAWER_ROUTE[1]), 3.0)

        _fl_finish_route_select()
        if fl_state():
            LOG("[+] 已进入路线模拟页")
            return

        last = "attempt %d: 点『路线模拟』后仍未到路线模拟页" % (attempt + 1)
        LOG("[!] " + last)
        d("shell", "input", "keyevent", "KEYCODE_BACK", check=False)
        time.sleep(1.5)

    raise RuntimeError(
        "没进到 FakeLocation 路线模拟页 (%s)\n"
        "  确认: 1) FakeLocation 已装并授权 2) LSPosed 模块已启用 3) 抽屉里能看到『路线模拟』\n"
        "  手动跑一次: \"%s\" -s %s shell monkey -p %s 1"
        % (last or "unknown", adb_exe(), serial(), pkg_fake()))


def fl_loop_on():
    """只读判断『循环』开关状态. 返回 True/False/None(读不到).

    ★ 不点它. 循环开关 f_route_sv_set_repeat [868,1068][1008,1149] 和暂停键、
      启动开关一起被可点父容器 f_route_ll_target_route [72,732][1008,1151] 包住,
      点下去触摸会被父容器截走跳到『选择路线』页. 只在确实关闭时才点, 且点完必须复检.
    """
    root = dump_xml(retries=2)
    if root is None:
        return None
    sw = find(root, rid_="f_route_sv_set_repeat")
    if sw is None:
        return None
    return (sw.get("text") or "").strip() == "开启"


def fl_ensure_loop():
    """路线模拟页的『循环』开关, 必须开. 已开就什么都不做.

    校内循环路线跑完一圈会自动从头再来, 里程才会一直涨到目标;
    不开的话跑完一圈就停在终点, 打卡点也就只能拿到那几个.
    """
    st = fl_loop_on()
    if st is True:
        LOG("[=] 循环已开启")
        return True
    if st is None:
        LOG("[!] 读不到循环开关, 跳过(默认就是开的)")
        return False

    root = dump_xml(retries=2)
    sw = find(root, rid_="f_route_sv_set_repeat") if root is not None else None
    if sw is None:
        return False
    tap_node(root, sw, 2.0)
    if fl_loop_on() is True:
        LOG("[+] 循环已开启")
        return True
    LOG("[!] 循环开关没打开, 里程可能只跑到一圈")
    return False


def fl_set_speed(mps=FL_SPEED_DEFAULT):
    """调运动速度. 尽力而为, 失败不阻塞主流程.

    坑: f_route_btn_set_speed 被可点的父容器 f_route_ll_target_route
    ([72,732][1008,1151]) 包着, 触摸会被父容器截走跳到『选择路线』页,
    面板根本出不来. 实测默认速度跑出来的配速是 10'15"/km (1.71 m/s),
    本来就是正常步行速度, 不改也没问题 —— 所以这里只试一次, 拿不到就算了.
    """
    root = dump_xml(retries=2)
    btn = find(root, rid_="f_route_btn_set_speed") if root is not None else None
    if btn is None:
        return False
    tap_node(root, btn, 2.0)

    root = dump_xml(retries=2)
    et = find(root, rid_="d_settings_speed_et_value") if root is not None else None
    if et is None:
        LOG("[=] 速度面板打不开(父容器截触摸), 用默认速度, 不影响打卡")
        # 如果被带到了选择路线页, 点「完成」退回
        back = find(root, rid_="a_select_route_btn_done") if root is not None else None
        if back is not None:
            tap_node(root, back, 2.5)
        return False

    rc = rect_of(et)
    tap((rc[0] + rc[2]) // 2, (rc[1] + rc[3]) // 2, 1.0)
    d("shell", "input", "keyevent", "KEYCODE_MOVE_END", check=False)
    for _ in range(6):
        d("shell", "input", "keyevent", "KEYCODE_DEL", check=False)
    d("shell", "input", "text", str(mps), check=False)
    time.sleep(1.0)

    root = dump_xml(retries=2)
    cur = (find(root, rid_="d_settings_speed_et_value") or {}).get("text") if root is not None else None
    LOG("[=] 速度设为 %s m/s (面板显示 %s)" % (mps, cur))
    tap(sx(540), sy(800), 1.0)
    return True


def fl_resume():
    """【已废弃, 不要再用】无条件点「继续」恢复路线模拟.

    ★ 为什么不该有这个函数:
      ① 它**不看状态就点**. 已经在跑的时候点「继续」就是把它按停, 下一次读到
         又是「继续」, 于是无限反复 —— 用户看到的「不断地点击继续然后暂停」.
      ② 验收规则 (CODEX_TEST_REPORT.md) 明确要求自动流程里删掉「继续」点击:
         "已经运行、显示「继续」或状态不明时, 不点击任何 FakeLocation 控件."

    ★ 至于"点完『启动模拟』会落到暂停态, 必须再点一次「继续」"这个说法 ——
      **那是假的**. 它是 `d()` 重复执行点击那个 bug (见 d() 的 docstring) 造成的
      假象: 点「启动模拟」被执行两遍 = 启动后立刻暂停, 看起来就像"启动后需要继续".
      bug 修掉之后实测: 冷启动点一次「启动模拟」直接进运行态, 坐标连续移动 30 秒
      不停, 根本不需要「继续」. 用户从一开始说的就是对的.

      真正正确的做法统一在 fl_start(): 先看坐标在不在动, 动了就一个按钮都不碰;
      没动且确认是「启动模拟」才点一次, 点完就收手.
    """
    raise RuntimeError(
        "fl_resume() 已废弃: 它不看状态就无脑点「继续」, 会把正在跑的按停. "
        "统一改用 fl_start()")


def fl_mock_moves(timeout=15.0, gap=1.5):
    """等 mock 坐标出现位移就立刻返回 True.

    ★ 这是判断「路线模拟到底在不在跑」的唯一真判据. 坐标不会骗人:
      暂停态的 FakeLocation 仍在持续上报坐标(et 时间戳一直在跳),
      但经纬度完全不变. 实测暂停态连续 20 次采样都是
      `31.049425,112.188812` 一动不动, 只有 et 在涨.
      恢复后立刻变成 31.049039 -> 31.049117 -> 31.049172 -> 31.049218.

    ★ 用途限定: 只用来**观察**状态, 绝不能拿它的结果去触发再点击一次按钮.
      点一次就够, 点第二次会踩到漂移后的暂停键 (见 fl_start() 的说明).
    """
    t0 = time.time()
    last = fl_mock_loc()
    while time.time() - t0 < timeout:
        time.sleep(gap)
        p = fl_mock_loc()
        if p is None:
            continue
        if last is not None and p != last:
            return True
        last = p
    return False


def fl_start():
    """启动路线模拟. ★★ 只点一次『启动模拟』, 点完立刻收手, 没有第二步 ★★

    ★ 用户定的规矩 (从头到尾都是对的, 老代码一直没做到):
        路线模拟只要点『启动模拟』即可, 不需要任何后续动作.
        不要点暂停.

    ★ CODEX 验收要求 (CODEX_TEST_REPORT.md):
        "FakeLocation 路线页只在明确看到「启动模拟」时点一次; 点击后立刻切到乐跑.
         已经运行、显示「继续」或状态不明时, 不点击任何 FakeLocation 控件.
         从自动流程删除「继续」点击和启动后自动重试;
         坐标只能用于日志观察, 不能作为再点击按钮的触发条件."

    ★★★ 老版本为什么"总是在点暂停" —— 真正原因不是坐标漂移, 是点击被执行了两次 ★★★
      `d()` 曾经把"stdout 为空"也当成 adb 断线的信号 (`input tap` 成功时 stdout
      本来就是空的), 于是判定连接异常 -> `adb connect` -> **再把同一条 tap 命令
      重跑一遍**. 每个点击都变成点两下:
        点「启动模拟」两下 = 启动 -> 立刻暂停
        点「继续」两下     = 继续 -> 立刻暂停
      再叠加按钮坐标漂移 (冷启动「启动模拟」中心 204,1109; 一旦跑起来,
      204 落进了暂停键 72~252 的范围), 第二下就精准踩在暂停上.
      这个 bug 已在 `d()` 里修掉 (只有 returncode != 0 才重试), 所以现在
      **一次点击就是一次点击**, 用户说的"点一次就够"完全成立.

      ★ 实测证据 (修掉双重点击之后): force-stop 冷启动 -> 进路线页 ->
        点一次 (204,1109) -> 坐标连续移动 30 秒不停, 按钮稳定显示「暂停」.
        一次点击, 直接进入运行态, 不需要「继续」.

    ★ 所以本函数的全部逻辑就是:
        ① 已经在跑    -> 一个按钮都不碰
        ② 确认是「启动模拟」 -> 点**一次**, 结束
        ③ 其它任何状态 -> 不点, 报错交给人
      没有任何重试、没有任何事后复查点击、没有「继续」分支.
    """
    fl_open_route()

    # ① 已经在跑就别碰 (只用于判断, 不触发任何点击)
    if fl_mock_moves(timeout=5.0):
        LOG("[+] mock 坐标在动, 路线模拟已在跑, 一个按钮都不碰")
        return True

    root = dump_xml(retries=3)
    if root is None:
        LOG("[!] 读不到路线模拟页, 不点任何按钮. 到模拟器里看一眼")
        return False

    sw_lbl = find(root, rid_="f_route_tv_service_switch")
    sw_txt = ((sw_lbl.get("text") if sw_lbl is not None else "") or "").strip()
    ps = find(root, rid_="f_route_tv_service_pause")
    ps_txt = ((ps.get("text") if ps is not None else "") or "").strip()
    LOG("[=] 当前: 启动键=[%s] 暂停键=[%s]" % (sw_txt, ps_txt))

    # ② 已经在跑: 暂停键写着「暂停」-> 一个按钮都不碰
    #    ★ 判据只看暂停键. 启动键在"暂停态"和"运行中"都是「停止模拟」, 不能用来判断.
    if "暂停" in ps_txt:
        LOG("[+] 已在运行中 (暂停键=「暂停」), 一个按钮都不碰")
        return True

    # ③ 冷启动: 确认循环开着, 然后点唯一一次『启动模拟』
    if "启动" in sw_txt:
        fl_ensure_loop()          # 已开则只读不动手, 见 fl_loop_on()
        time.sleep(1.2)           # 万一开了循环会重绘按钮栏, 等它稳定
        root = dump_xml(retries=3)
        if root is None:
            LOG("[!] 读不到页面, 不点. 到模拟器里看一眼")
            return False
        # ★ 点之前重新读一遍文字, 绝不沿用旧快照
        sw_lbl = find(root, rid_="f_route_tv_service_switch")
        sw_txt = ((sw_lbl.get("text") if sw_lbl is not None else "") or "").strip()
        ps = find(root, rid_="f_route_tv_service_pause")
        ps_txt = ((ps.get("text") if ps is not None else "") or "").strip()
        if "暂停" in ps_txt:
            LOG("[+] 页面已变成运行中, 不点")
            return True
        if "启动" not in sw_txt:
            LOG("[!] 启动键变成[%s] 暂停键=[%s], 不认识, 不点" % (sw_txt, ps_txt))
            return False
        btn = find(root, rid_="f_route_btn_service_switch")
        if btn is None:
            LOG("[!] 找不到『启动模拟』的点击节点, 不点. 到模拟器里看一眼")
            return False
        tap_node(root, btn, 3.0)
        LOG("[+] 点了『启动模拟』(全程仅此一次点击). 到此为止, 不再点任何按钮")
        return True

    # ④ 其它状态 (典型: 暂停键=「继续」) -> 按 CODEX 规则**不点**
    if "继续" in ps_txt:
        LOG("[!] 当前是暂停态 (暂停键=「继续」). 规则: 脚本只点「启动模拟」, "
            "不自动点「继续」")
        LOG("    到模拟器里点一下左边那个「继续」, 然后重跑 run.bat")
        return False

    LOG("[!] 状态看不懂 (启动键=[%s] 暂停键=[%s]), 不点任何按钮. "
        "到模拟器里手动确认一下" % (sw_txt, ps_txt))
    return False


def fl_pause():
    """把路线模拟停下来. ★ 只给收尾显式调用, 启动流程里任何地方都不许调它.

    ★ 有 `停止模拟` 就点 `停止模拟`, 不是点左边那个暂停键. 点完必须复检.
    """
    st = fl_state()
    if st == "stopped":
        LOG("[=] 路线模拟本来就是停的")
        return True

    root = dump_xml(retries=2)
    if root is None:
        return False
    btn = find(root, rid_="f_route_btn_service_switch")
    if btn is None:
        return False
    txt = find(root, rid_="f_route_tv_service_switch")
    label = ((txt.get("text") if txt is not None else "") or "").strip()
    if "启动" in label:
        LOG("[=] 路线模拟本来就是停的")
        return True
    tap_node(root, btn, 3.0)
    for _ in range(6):
        time.sleep(1.2)
        if fl_state() == "stopped":
            LOG("[=] 路线模拟已停止")
            return True
    return False


def fl_mock_loc():
    """读当前 mock 坐标 (FakeLocation 注入的). 取不到返回 None.

    ★ 直接复用 gps(): 它已经处理了「同一个坐标挂在多个 provider 下各出现一次」
      和「第一条是残留真实定位」两个坑. 老版本这里自己写了一套只认
      `last location` 行的解析, 实测匹配不到, 于是永远返回 None —— 上层
      于是以为"没在跑", 又去点按钮, 把正在跑的按成暂停.
    """
    return gps()


def mock_moving(samples=3, gap=2.0):
    """采几次 mock 坐标, 判断它到底动没动.

    暂停态的 FakeLocation 仍会持续上报坐标(时间戳在跳), 但经纬度**完全不变**.
    乐跑按坐标位移算里程, 坐标不动 -> 里程永远 0.00, 这是最容易看漏的故障.
    用「经纬度是否变化」判定, 不看时间戳.
    """
    seen = []
    for _ in range(samples):
        p = fl_mock_loc()
        if p is not None:
            seen.append(p)
        if len(seen) >= 2 and seen[-1] != seen[0]:
            return True
        time.sleep(gap)
    if len(seen) < 2:
        return False
    return seen[-1] != seen[0]


# 兼容旧调用名
fl_ensure_simulating = fl_start


# ------------------------------------------------------------------ 子命令

def cmd_go(upload=False, wait_min=0):
    """别人电脑上的唯一入口.

    三件事: FakeLocation 开路线模拟 -> 打开步道乐跑到跑步页 -> 长按起跑.
    upload=True 时再接着「等够时间 -> 停止 -> 上传」走完全套.
    wait_min 是起跑后要跑多少分钟; 0 表示不等, 起跑就收工.
    """
    LOG("========== 1/3 定位 MuMu ==========")
    root = MUMU.root
    LOG("    安装目录: %s" % root)
    for label, p in (("MuMuManager.exe", MUMU.manager), ("adb.exe", MUMU.adb)):
        if not os.path.exists(p):
            raise RuntimeError(
                "%s 不存在: %s\n"
                "  MuMu 装得不完整, 或者装在别处. 手动指定:\n"
                '    set LEPAO_MUMU_HOME=<MuMu 安装根目录>' % (label, p))

    idx, fake, run = locate_target_index()
    if not (fake and run):
        missing = []
        if not fake:
            missing.append("FakeLocation")
        if not run:
            missing.append("步道乐跑")
        raise RuntimeError(
            "实例 %d 里没找到: %s\n"
            "  先把这两个 App 装进 MuMu 的那个实例里, 再重跑.\n"
            "  想指定别的实例: set LEPAO_INDEX=<实例号>" % (idx, " / ".join(missing)))

    boot()
    LOG("    实例 %d / adb %s" % (INDEX, serial()))
    LOG("    FakeLocation: %s" % fake)
    LOG("    步道乐跑    : %s" % run)

    LOG("\n========== 2/3 路线模拟: 开循环 + 启动 ==========")
    ok = fl_start()
    loc = gps()
    LOG("[+] 当前 mock 坐标: %s" % (loc,))
    if loc is None:
        LOG("[!] 没读到 mock 坐标, LSPosed 模块可能没生效; 但模拟已经启动, 观察一下")

    LOG("\n========== 3/3 打开步道乐跑 ==========")
    lp_open(run)

    LOG("\n========== 起跑 ==========")
    try:
        lp_start()
        LOG("[+] 已起跑, 计时器在走")
    except Exception as e:
        # 起跑失败不代表前面的活白干 —— 乐跑已经开在跑步页了, 手动长按一下就行
        LOG("[!] 自动起跑没成功: %s" % e)
        LOG("    乐跑已经打开在跑步页, 手动长按底部绿色按钮起跑即可")

    if not upload:
        LOG("\n[+] 搞定. FakeLocation 在跑, 步道乐跑已在跑步页.")
        return ok

    # ---- 可选: 等够时间后停止 + 上传 ----
    if wait_min > 0:
        LOG("\n========== 跑 %d 分钟 ==========" % wait_min)
        target = time.time() + wait_min * 60
        last = 0
        while time.time() < target:
            left = int(target - time.time())
            if left // 60 != last:
                last = left // 60
                LOG("    还剩 %d 分钟" % (left // 60 + 1))
            time.sleep(5)

    LOG("\n========== 停止 + 上传 ==========")
    try:
        up = lp_stop_and_upload()
    except Exception as e:
        LOG("[!] 停止/上传出错: %s" % e)
        LOG("    乐跑已经在跑步页, 手动长按底部按钮 -> 结束 -> 上传")
        return False

    LOG("\n[+] 全套完成. 上传%s." % ("成功" if up else "结果需人工确认"))
    return up


def cmd_boot():
    boot()


def cmd_lp():
    lp_enter_run()


def cmd_fl():
    boot()
    fl_ensure_simulating()


def cmd_state():
    lp_state()


def cmd_stop():
    lp_stop_and_upload()


def cmd_full(km, points):
    boot()
    t0 = time.time()

    # 先让 FakeLocation 注入定位, 乐跑首页「获取当前位置」才能成功
    LOG("\n########## 1/4 FakeLocation 路线模拟 ##########")
    fl_ensure_simulating()

    LOG("\n########## 2/4 步道乐跑 起跑 ##########")
    lp_enter_run()

    LOG("\n########## 3/4 轨迹积分 + 打卡轮询 ##########")
    tr = Track()
    LOG("[=] 起点 GPS: %s" % (tr.reset(),))
    screen_km = None

    while True:
        tr.step(n=POLL_SEC // 2, gap=1.0)      # 小步高频, 折线不会被压成弦
        el = time.time() - t0
        st = lp_state()

        # 屏幕读数只做旁证: OCR 认大号橙字极不稳, 有就用, 离谱就丢
        scr = st["km"]
        if scr is not None:
            if tr.km > 0.1 and abs(scr - tr.km) > max(0.5, tr.km * 0.5):
                LOG("[!] 屏幕 %.2f 与轨迹 %.2f 偏差过大, 判为 OCR 误读, 忽略"
                    % (scr, tr.km))
            else:
                screen_km = scr

        LOG("[=] 进度 轨迹=%.2f km 屏幕=%s 打卡=%s 用时=%s (%.1f 分钟)"
            % (tr.km, ("%.2f" % screen_km) if screen_km is not None else "-",
               st["points"], st["time"], el / 60))

        # 里程以 mock 轨迹为准; 屏幕读数超过目标也算数(乐跑自己认的里程更硬)
        ok_km = tr.km >= km or (screen_km is not None and screen_km >= km)
        ok_pt = (st["points"] or 0) >= points
        if ok_km and ok_pt:
            LOG("[+] 达成: 轨迹 %.2f km, %d 个打卡点" % (tr.km, st["points"]))
            break
        if el > MAX_MINUTES * 60:
            LOG("[!] 超时 %.0f 分钟, 结束" % (el / 60))
            break

    LOG("\n########## 4/4 结束并上传 ##########")
    ok = lp_stop_and_upload()
    LOG("\n[+] 全部完成" if ok else "\n[!] 请人工确认上传结果")


# ------------------------------------------------------------------ 环境自检
# 换电脑最容易踩的坑都在这里一次性检查掉, 报错信息直接告诉用户怎么办.

def preflight(strict=True):
    """返回 True 表示环境可用. strict=True 时有问题直接抛异常"""
    problems = []
    notes = []

    # 1) Python 版本
    if sys.version_info < (3, 6):
        problems.append("Python 版本过低 (%s), 需要 3.6+"
                        % sys.version.split()[0])
    else:
        notes.append("Python %s" % sys.version.split()[0])

    # 2) 平台
    if os.name != "nt":
        problems.append("只支持 Windows (当前系统: %s)" % os.name)

    # 3) PowerShell (可选, 只有 state/stop 的 OCR 判读才需要)
    try:
        notes.append("PowerShell: %s" % OCR.POWERSHELL)
        ok, detail = OCR.ocr_available()
        if ok:
            notes.append("OCR 引擎: %s" % detail)
        else:
            notes.append("OCR 引擎不可用 (%s) —— 只影响 state/stop 读屏, "
                         "go/full 的起跑判定走 uiautomator, 不阻塞" % detail)
    except Exception as e:
        notes.append("PowerShell 检测跳过: %s" % e)

    # 4) MuMu
    try:
        root = MUMU.root
        notes.append("MuMu: %s" % root)
        if not os.path.exists(MUMU.manager):
            problems.append("MuMuManager.exe 不存在: %s" % MUMU.manager)
        if not os.path.exists(MUMU.adb):
            problems.append("adb.exe 不存在: %s" % MUMU.adb)
        insts = list_instances()
        if insts:
            notes.append("实例: %s" % ", ".join(
                "%d(%s)" % (i, p) for i, _, p in insts))
        else:
            problems.append("MuMu 里没有可用实例, 请先在多开器里新建安卓设备")
    except Exception as e:
        problems.append(str(e))

    # 5) 两个 App 是否装了 (模拟器没开时无法判断, 跳过)
    try:
        # 先主动 connect, 否则没有已建立的连接时 get-state 永远是空
        try:
            sh([adb_exe(), "connect", serial()], check=False, timeout=30)
        except Exception:
            pass
        if d("get-state", check=False).strip() == "device":
            pm = d("shell", "pm", "list", "packages", check=False)
            if "package:" in pm:          # 确认拿到了真实列表再判断
                pkgs = set(x[len("package:"):].strip()
                           for x in pm.splitlines() if x.startswith("package:"))
                fake = _match_in(pkgs, _FAKE_CANDIDATES, _FAKE_KEYS)
                run = _match_in(pkgs, _RUN_CANDIDATES, _RUN_KEYS)
                if fake:
                    notes.append("FakeLocation: %s" % fake)
                else:
                    problems.append(
                        "模拟器里没装 FakeLocation\n"
                        "    请先在该实例里装好这个 App 并授权")
                if run:
                    notes.append("步道乐跑: %s" % run)
                else:
                    problems.append(
                        "模拟器里没装 步道乐跑\n"
                        "    请先在该实例里装好这个 App 并登录")
            else:
                notes.append("App 检查: 跳过 (读取包列表失败)")
        else:
            notes.append("App 检查: 跳过 (模拟器未启动, full 流程会自动启动)")
    except Exception:
        notes.append("App 检查: 跳过")

    for n in notes:
        LOG("  " + n)
    if problems:
        LOG("")
        for p in problems:
            LOG("[X] " + p)
        if strict:
            raise RuntimeError("环境自检未通过, 请按上面提示处理后重试")
        return False
    LOG("[+] 环境自检通过\n")
    return True


def cmd_check():
    try:
        ok = preflight(strict=False)
    except Exception as e:
        LOG(str(e))
        ok = False
    if not ok:
        sys.exit(1)


if __name__ == "__main__":
    args = sys.argv[1:]
    action = args[0] if args else "go"
    km, pts = TARGET_KM, TARGET_POINTS
    do_upload = "--upload" in args
    wait_min = 0
    for i, a in enumerate(args):
        if a == "--km" and i + 1 < len(args):
            km = float(args[i + 1])
        if a == "--points" and i + 1 < len(args):
            pts = int(args[i + 1])
        if a == "--wait" and i + 1 < len(args):
            wait_min = float(args[i + 1])

    cmds = {
        "go": lambda: cmd_go(do_upload, wait_min),   # 别人电脑上的主入口
        "boot": cmd_boot,
        "lp": cmd_lp,
        "fl": cmd_fl,
        "state": cmd_state,
        "stop": cmd_stop,
        "check": cmd_check,
        "full": lambda: cmd_full(km, pts),
    }
    if action not in cmds:
        LOG("用法: python lepao_auto.py [go|stop|check|boot|lp|fl|state|full] [选项]")
        LOG("")
        LOG("  go                 定位 MuMu + 开路线模拟 + 打开乐跑并起跑 (换电脑就用这个)")
        LOG("  go --upload        上面全做, 再停止并上传")
        LOG("  go --upload --wait 30   先跑 30 分钟, 再停止并上传")
        LOG("  stop               只做「停止 + 上传」(跑步已经在进行时用)")
        LOG("  check              只做环境自检, 不操作模拟器")
        LOG("  state              读一次乐跑当前数据")
        sys.exit(2)

    # go / check 自己管定位, 不能先跑通用自检 —— preflight 里的 serial()
    # 会把 INDEX 钉在某个实例上, 后面的 locate_target_index 就没法扫别的实例了
    if action not in ("check", "go"):
        LOG("=== 环境自检 ===")
        preflight(strict=True)

    try:
        cmds[action]()
    except KeyboardInterrupt:
        LOG("\n[!] 用户中断")
        sys.exit(130)
    except Exception as e:
        LOG("\n[X] %s" % e)
        sys.exit(1)
