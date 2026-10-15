# PyInstaller tarifi: tek klasörde iki program üretir, kütüphaneleri ortak kullanırlar.
#   AkademikIndirici.exe      → pencereli uygulama
#   AkademikKutuphaneMCP.exe  → Claude masaüstü bağlantısı (konsol; Claude arka planda çalıştırır)
import base64
import re
from PyInstaller.utils.hooks import collect_data_files

# Uygulama simgesi akademik_indirici.py içinde saklanır; exe'ye gömülmek üzere buradan çıkarılır.
_src = open("akademik_indirici.py", encoding="utf-8").read()
_b64 = "".join(re.findall(r'"([A-Za-z0-9+/=]+)"', re.search(r"APP_ICON_ICO_B64 = \((.*?)\)", _src, re.S).group(1)))
with open("uygulama.ico", "wb") as _fh:
    _fh.write(base64.b64decode(_b64))

# Güncellenen kod sonradan yeni standart modüller kullanabilsin diye yaygın olanlar da pakete girer.
STDLIB = ["uuid", "platform", "importlib.util", "difflib", "statistics", "textwrap", "calendar", "secrets",
          "hmac", "base64", "gzip", "bz2", "lzma", "tarfile", "glob", "fnmatch", "configparser", "logging",
          "tempfile", "string", "pprint", "decimal", "fractions", "itertools", "functools", "collections",
          "dataclasses", "enum", "typing", "copy", "bisect", "heapq", "random", "math", "struct", "codecs",
          "html.parser", "http.client", "http.cookiejar", "urllib.request", "email", "email.utils",
          "xml.dom.minidom", "concurrent.futures", "socket", "ssl", "locale", "plistlib", "colorsys",
          "tkinter.font", "tkinter.ttk", "tkinter.simpledialog", "tkinter.colorchooser", "sqlite3", "ctypes",
          "ctypes.wintypes", "winreg", "msvcrt", "pypdf", "requests", "customtkinter"]
a = Analysis(["akademik_indirici.py"], datas=collect_data_files("customtkinter"), hiddenimports=STDLIB)
pyz = PYZ(a.pure)

gui = EXE(pyz, a.scripts, [], exclude_binaries=True, name="AkademikIndirici", console=False, icon="uygulama.ico")
mcp = EXE(pyz, a.scripts, [], exclude_binaries=True, name="AkademikKutuphaneMCP", console=True, icon="uygulama.ico")

coll = COLLECT(gui, mcp, a.binaries, a.datas, name="AkademikIndirici")
