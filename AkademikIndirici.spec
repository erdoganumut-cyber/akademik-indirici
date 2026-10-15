# PyInstaller tarifi: tek klasörde iki program üretir, kütüphaneleri ortak kullanırlar.
#   AkademikIndirici.exe      → pencereli uygulama
#   AkademikKutuphaneMCP.exe  → Claude masaüstü bağlantısı (konsol; Claude arka planda çalıştırır)
from PyInstaller.utils.hooks import collect_data_files

a = Analysis(["akademik_indirici.py"], datas=collect_data_files("customtkinter"))
pyz = PYZ(a.pure)

gui = EXE(pyz, a.scripts, [], exclude_binaries=True, name="AkademikIndirici", console=False)
mcp = EXE(pyz, a.scripts, [], exclude_binaries=True, name="AkademikKutuphaneMCP", console=True)

coll = COLLECT(gui, mcp, a.binaries, a.datas, name="AkademikIndirici")
