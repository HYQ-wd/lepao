# -*- coding: utf-8 -*-
"""WinRT OCR 工具: 截图 -> (可选裁剪+放大) -> 中文 OCR

用法:
    python ocr.py <png>                       # 全图
    python ocr.py <png> x1 y1 x2 y2 [scale]   # 只识别指定矩形, 默认放大 3 倍
"""
import os
import shutil
import subprocess
import sys
import tempfile

PS_TEMPLATE = r'''
$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Add-Type -AssemblyName System.Drawing
Add-Type -AssemblyName System.Runtime.WindowsRuntime

# ---- 可选: 裁剪 + 放大, 提高小字识别率
$src = $env:LEPAO_OCR_IMG
$work = $src
if ($env:LEPAO_OCR_CROP) {
    $v = $env:LEPAO_OCR_CROP -split ','
    $x = [int]$v[0]; $y = [int]$v[1]; $w = [int]$v[2]; $h = [int]$v[3]
    $scale = [double]$v[4]
    $img = [System.Drawing.Image]::FromFile($src)
    $bmp = New-Object System.Drawing.Bitmap ([int]($w * $scale)), ([int]($h * $scale))
    $g = [System.Drawing.Graphics]::FromImage($bmp)
    $g.InterpolationMode = [System.Drawing.Drawing2D.InterpolationMode]::HighQualityBicubic
    $g.DrawImage($img, (New-Object System.Drawing.Rectangle 0, 0, $bmp.Width, $bmp.Height),
                 (New-Object System.Drawing.Rectangle $x, $y, $w, $h),
                 [System.Drawing.GraphicsUnit]::Pixel)
    $g.Dispose()
    $work = Join-Path $env:TEMP 'dsh_ocr_crop.png'
    $bmp.Save($work, [System.Drawing.Imaging.ImageFormat]::Png)
    $bmp.Dispose(); $img.Dispose()

    # 灰度 + 强制二值化: 橙色大数字 OCR 识别率低, 拉成纯黑白后稳定很多
    if ($env:LEPAO_OCR_BW -eq '1') {
        $s = [System.Drawing.Image]::FromFile($work)
        $b2 = New-Object System.Drawing.Bitmap $s.Width, $s.Height
        $g2 = [System.Drawing.Graphics]::FromImage($b2)
        $ia = New-Object System.Drawing.Imaging.ImageAttributes
        $cm = New-Object System.Drawing.Imaging.ColorMatrix
        $cm.Matrix00 = 0.299; $cm.Matrix01 = 0.299; $cm.Matrix02 = 0.299
        $cm.Matrix10 = 0.587; $cm.Matrix11 = 0.587; $cm.Matrix12 = 0.587
        $cm.Matrix20 = 0.114; $cm.Matrix21 = 0.114; $cm.Matrix22 = 0.114
        $cm.Matrix33 = 1.0; $cm.Matrix40 = 0; $cm.Matrix41 = 0; $cm.Matrix42 = 0
        $ia.SetColorMatrix($cm)
        $g2.DrawImage($s, (New-Object System.Drawing.Rectangle 0, 0, $b2.Width, $b2.Height),
                      0, 0, $s.Width, $s.Height, [System.Drawing.GraphicsUnit]::Pixel, $ia)
        $g2.Dispose()
        # 阈值二值化, 让笔画纯黑背景纯白
        $thr = [int]$env:LEPAO_OCR_THR
        for ($yy = 0; $yy -lt $b2.Height; $yy++) {
            for ($xx = 0; $xx -lt $b2.Width; $xx++) {
                $c = $b2.GetPixel($xx, $yy)
                if ($c.R -lt $thr) { $b2.SetPixel($xx, $yy, [System.Drawing.Color]::Black) }
                else { $b2.SetPixel($xx, $yy, [System.Drawing.Color]::White) }
            }
        }
        $b2.Save($work, [System.Drawing.Imaging.ImageFormat]::Png)
        $b2.Dispose(); $s.Dispose()
    }
}

$asTask = ([System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {
    $_.Name -eq 'AsTask' -and $_.GetParameters().Count -eq 1 -and
    $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1' })[0]
function Await($op, $type) {
    $t = $asTask.MakeGenericMethod($type).Invoke($null, @($op))
    $t.Wait(-1) | Out-Null
    $t.Result
}
$OcrEngine = [Windows.Media.Ocr.OcrEngine, Windows.Media.Ocr, ContentType = WindowsRuntime]
$lang = [Windows.Globalization.Language, Windows.Globalization, ContentType = WindowsRuntime]::new('zh-Hans-CN')
$engine = $OcrEngine::TryCreateFromLanguage($lang)
if ($engine -eq $null) { $engine = $OcrEngine::TryCreateFromUserProfileLanguages() }

$SF = [Windows.Storage.StorageFile, Windows.Storage, ContentType = WindowsRuntime]
$file = Await ($SF::GetFileFromPathAsync($work)) ([Windows.Storage.StorageFile])
$stream = Await ($file.OpenAsync([Windows.Storage.FileAccessMode]::Read)) ([Windows.Storage.Streams.IRandomAccessStream])
$BD = [Windows.Graphics.Imaging.BitmapDecoder, Windows.Graphics.Imaging, ContentType = WindowsRuntime]
$decoder = Await ($BD::CreateAsync($stream)) ([Windows.Graphics.Imaging.BitmapDecoder])
$bitmap = Await ($decoder.GetSoftwareBitmapAsync()) ([Windows.Graphics.Imaging.SoftwareBitmap])
$result = Await ($engine.RecognizeAsync($bitmap)) ([Windows.Media.Ocr.OcrResult])

foreach ($line in $result.Lines) {
    $x1 = [double]::MaxValue; $y1 = [double]::MaxValue; $x2 = 0.0; $y2 = 0.0
    foreach ($w in $line.Words) {
        $r = $w.BoundingRect
        if ($r.X -lt $x1) { $x1 = $r.X }
        if ($r.Y -lt $y1) { $y1 = $r.Y }
        if (($r.X + $r.Width) -gt $x2) { $x2 = $r.X + $r.Width }
        if (($r.Y + $r.Height) -gt $y2) { $y2 = $r.Y + $r.Height }
    }
    "{0}`t{1}`t{2}`t{3}`t{4}" -f $line.Text, [int]$x1, [int]$y1, [int]$x2, [int]$y2
}
'''

def _find_powershell():
    """定位 powershell.exe. 不写死 C 盘 —— 系统盘不一定是 C, 也可能被精简掉"""
    env = os.environ.get("LEPAO_POWERSHELL", "").strip()
    if env and os.path.exists(env):
        return env

    cands = []
    sysroot = os.environ.get("SystemRoot") or os.environ.get("windir") or r"C:\Windows"
    cands.append(os.path.join(sysroot, "System32", "WindowsPowerShell", "v1.0",
                              "powershell.exe"))
    # 64 位系统上 32 位进程会看 SysWOW64
    cands.append(os.path.join(sysroot, "SysWOW64", "WindowsPowerShell", "v1.0",
                              "powershell.exe"))
    for c in cands:
        if os.path.exists(c):
            return c

    found = shutil.which("powershell") or shutil.which("pwsh")
    if found:
        return found
    raise RuntimeError(
        "找不到 powershell.exe, 脚本依赖它调用系统 OCR.\n"
        "  可设置环境变量 LEPAO_POWERSHELL 指向 powershell.exe")


POWERSHELL = _find_powershell()

# OCR 引擎是否可用 (Windows.Media.Ocr 需要 Win10 及以上)
_ENGINE_OK = None


def ocr_available():
    """检查系统 OCR 引擎能否创建, 返回 (ok, 说明)"""
    global _ENGINE_OK
    if _ENGINE_OK is not None:
        return _ENGINE_OK

    probe = (
        "$ErrorActionPreference='Stop';"
        "try{"
        "  $t=[Windows.Media.Ocr.OcrEngine, Windows.Media.Ocr, ContentType=WindowsRuntime];"
        "  $l=[Windows.Globalization.Language, Windows.Globalization, ContentType=WindowsRuntime]::new('zh-Hans-CN');"
        "  $e=$t::TryCreateFromLanguage($l);"
        "  if($e -eq $null){$e=$t::TryCreateFromUserProfileLanguages()};"
        "  if($e -eq $null){'NO_ENGINE'}else{'OK ' + $e.RecognizerLanguage.LanguageTag}"
        "}catch{'ERR ' + $_.Exception.Message}"
    )
    try:
        p = subprocess.run([POWERSHELL, "-NoProfile", "-ExecutionPolicy", "Bypass",
                            "-Command", probe],
                           capture_output=True, encoding="utf-8", errors="ignore")
        out = (p.stdout or "").strip()
    except Exception as e:
        out = "ERR %s" % e

    if out.startswith("OK"):
        _ENGINE_OK = (True, out)
    else:
        _ENGINE_OK = (False, out or "OCR 引擎不可用")
    return _ENGINE_OK


def _script_path():
    p = os.path.join(tempfile.gettempdir(), "lepao_ocr.ps1")
    with open(p, "w", encoding="utf-8-sig") as f:
        f.write(PS_TEMPLATE)
    return p


_PS1 = None


def _ps1():
    global _PS1
    if _PS1 is None:
        _PS1 = _script_path()
    return _PS1


def ocr(img_path, crop=None, bw=False, thr=140):
    """crop=(x, y, w, h, scale) 或 None; bw=True 灰度二值化"""
    env = dict(os.environ)
    env["LEPAO_OCR_IMG"] = os.path.abspath(img_path)
    env.pop("LEPAO_OCR_CROP", None)
    env.pop("LEPAO_OCR_BW", None)
    env["LEPAO_OCR_THR"] = str(thr)
    if crop:
        env["LEPAO_OCR_CROP"] = ",".join(str(v) for v in crop)
        if bw:
            env["LEPAO_OCR_BW"] = "1"
    p = subprocess.run([POWERSHELL, "-NoProfile", "-ExecutionPolicy", "Bypass",
                        "-File", _ps1()],
                       capture_output=True, encoding="utf-8", errors="ignore",
                       env=env)
    rows = []
    for line in (p.stdout or "").splitlines():
        parts = line.split("\t")
        if len(parts) != 5:
            continue
        txt, x1, y1, x2, y2 = parts
        try:
            rows.append((txt.replace(" ", ""), int(x1), int(y1), int(x2), int(y2)))
        except ValueError:
            pass
    return rows


if __name__ == "__main__":
    a = sys.argv[1:]
    crop = None
    if len(a) >= 5:
        x, y, w, h = (int(v) for v in a[1:5])
        scale = float(a[5]) if len(a) >= 6 else 3.0
        crop = (x, y, w, h, scale)
    for r in ocr(a[0], crop):
        print("%-34s (%4d,%4d)-(%4d,%4d)" % r)
