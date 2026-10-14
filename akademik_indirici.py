# -*- coding: utf-8 -*-
"""
Akademik Kaynak İndirici
========================
Karışık metinlerden ve akademik kaynakçalardan (APA, MLA, Chicago...) linkleri
ayıklar ve seçilen klasöre indirir.

Öne çıkanlar
- http/https linklerini ve (isteğe bağlı) çıplak DOI'leri (doi:10.xxxx/...) bulur;
  sonlarında kalan nokta, virgül, kapanmamış parantez gibi artıkları temizler.
- requests ile parça parça (stream=True) indirir, DOI yönlendirmelerini izler
  (allow_redirects=True), geçici sunucu hatalarında otomatik yeniden dener.
- Link bir makale sayfasına açılırsa sayfadaki Google Scholar etiketinden
  (citation_pdf_url) PDF'i bulup indirir ve dosyayı "Yazar (Yıl) - Başlık.pdf"
  olarak adlandırır.
- İndirme ayrı bir iş parçacığında (thread) çalışır; arayüz donmaz.
- Bitince hedef klasöre Excel'de açılabilen bir indirme raporu (CSV) yazar.

Gereksinimler:  pip install customtkinter requests
"""

import csv
import html
import mimetypes
import os
import queue
import re
import subprocess
import sys
import threading
import time
from datetime import datetime
from pathlib import Path
from urllib.parse import unquote, urljoin, urlparse

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

import customtkinter as ctk
from tkinter import filedialog, messagebox

# PyInstaller --windowed ile derlenen exe'de konsol olmadığı için stdout/stderr
# boş gelir; bir kütüphane yine de yazmaya çalışırsa uygulama çökmesin.
if sys.stdout is None:
    sys.stdout = open(os.devnull, "w", encoding="utf-8")
if sys.stderr is None:
    sys.stderr = open(os.devnull, "w", encoding="utf-8")


APP_NAME = "Akademik Kaynak İndirici"
APP_VERSION = "1.0"

CHUNK_SIZE = 64 * 1024              # parça parça indirme boyutu (64 KB)
HTML_READ_LIMIT = 5 * 1024 * 1024   # PDF etiketi aramak için okunacak en fazla HTML
TIMEOUT = (15, 60)                  # (bağlanma, okuma) saniye
PAUSE_BETWEEN = 0.5                 # sunucuları yormamak için dosyalar arası bekleme

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/130.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/pdf;q=0.9,*/*;q=0.8",
    "Accept-Language": "tr-TR,tr;q=0.9,en;q=0.8",
}


# ════════════════════════════════════════════════════════════════════════════
#  1) LİNK AYIKLAMA (REGEX)
# ════════════════════════════════════════════════════════════════════════════

# PDF'ten / Word'den kopyalanan metinlerdeki görünmez karakterler
_INVISIBLE = dict.fromkeys(map(ord, "​‌‍⁠﻿­"), None)

# Link içinde bulunamayacak karakterler: boşluk, tırnaklar, açılı/köşeli parantez...
_URL_STOP = r"\s<>\"'`{}|\\^\[\]“”‘’«»"
URL_RE = re.compile(rf"https?://[^{_URL_STOP}]+", re.IGNORECASE)

# Çıplak DOI: "doi:10.1037/abc", "doi.org/10.1037/abc" ya da sadece "10.1037/abc"
DOI_RE = re.compile(
    rf"(?<![\w.])(?:(?:dx\.)?doi\.org/|doi:\s*)?(10\.\d{{4,9}}/[^{_URL_STOP}]+)",
    re.IGNORECASE,
)

# Linkin sonunda kalırsa atılacak noktalama işaretleri
_TRAILING_PUNCT = ".,;:!?'\"*`“”‘’«»>"
_BRACKET_PAIRS = {")": "(", "]": "[", "}": "{"}


def clean_url(url: str) -> str:
    """Linkin sonundaki nokta, virgül ve eşi olmayan kapanış parantezini temizler.

    Linkin kendisine ait parantezler korunur, ör.
    https://doi.org/10.1016/S0140-6736(20)30183-5  →  değişmez
    (https://ornek.org/makale).                    →  https://ornek.org/makale
    """
    while url:
        last = url[-1]
        if last in _TRAILING_PUNCT:
            url = url[:-1]
        elif last in _BRACKET_PAIRS and url.count(last) > url.count(_BRACKET_PAIRS[last]):
            url = url[:-1]
        else:
            break
    return url


def _looks_valid(url: str) -> bool:
    try:
        host = urlparse(url).hostname or ""
    except ValueError:
        return False
    return bool(host) and ("." in host or host == "localhost")


def _dedupe_key(url: str):
    """http/https, dx.doi.org/doi.org ve sondaki / farkını yok sayan anahtar."""
    p = urlparse(url)
    host = (p.hostname or "").lower()
    if host in ("dx.doi.org", "www.doi.org"):
        host = "doi.org"
    path = p.path.rstrip("/")
    if host == "doi.org":
        path = path.lower()  # DOI'ler büyük/küçük harf duyarsızdır
    return host, path, p.query


def extract_links(text: str, include_doi: bool = True) -> list:
    """Metindeki linkleri metindeki sırasıyla, tekrarsız olarak döndürür."""
    text = text.translate(_INVISIBLE)
    found = []  # (metindeki konum, link)

    for m in URL_RE.finditer(text):
        url = clean_url(m.group(0))
        if _looks_valid(url):
            found.append((m.start(), url))

    if include_doi:
        # Linkleri aynı uzunlukta boşlukla maskele ki içlerindeki DOI'ler
        # ikinci kez yakalanmasın ve konumlar kaymasın.
        masked = URL_RE.sub(lambda m: " " * len(m.group(0)), text)
        for m in DOI_RE.finditer(masked):
            doi = clean_url(m.group(1))
            if doi.split("/", 1)[1:] and doi.split("/", 1)[1]:
                found.append((m.start(), "https://doi.org/" + doi))

    found.sort(key=lambda item: item[0])
    seen, links = set(), []
    for _, url in found:
        key = _dedupe_key(url)
        if key not in seen:
            seen.add(key)
            links.append(url)
    return links


# ════════════════════════════════════════════════════════════════════════════
#  2) DOSYA ADI YARDIMCILARI
# ════════════════════════════════════════════════════════════════════════════

_WIN_RESERVED = {"CON", "PRN", "AUX", "NUL",
                 *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10))}

_KNOWN_EXT = {
    ".pdf", ".epub", ".djvu", ".ps", ".doc", ".docx", ".odt", ".ods", ".odp", ".rtf",
    ".txt", ".md", ".tex",
    ".bib", ".ris", ".ppt", ".pptx", ".xls", ".xlsx", ".csv", ".json", ".xml", ".html",
    ".htm", ".zip", ".rar", ".7z", ".gz", ".tar", ".png", ".jpg", ".jpeg", ".gif",
    ".svg", ".tif", ".tiff", ".webp", ".mp3", ".wav", ".mp4", ".mov", ".avi", ".mkv",
}

_EXT_BY_TYPE = {
    "application/pdf": ".pdf",
    "text/html": ".html",
    "application/xhtml+xml": ".html",
    "text/plain": ".txt",
    "text/csv": ".csv",
    "application/json": ".json",
    "application/xml": ".xml",
    "text/xml": ".xml",
    "application/zip": ".zip",
    "application/epub+zip": ".epub",
    "application/msword": ".doc",
    "application/vnd.openxmlformats-officedocument.wordprocessingml.document": ".docx",
    "application/vnd.openxmlformats-officedocument.presentationml.presentation": ".pptx",
    "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet": ".xlsx",
    "image/jpeg": ".jpg",
    "image/png": ".png",
}

# Bilgi vermeyen, dosya adı olarak kullanılmayacak URL sonları
_GENERIC_NAMES = {
    "", "download", "downloads", "pdf", "epdf", "pdfdirect", "view", "viewer", "content",
    "fulltext", "full", "file", "files", "index", "article", "abstract", "getpdf",
    "render", "servlet", "viewcontent.cgi", "reader", "document", "stamp",
}


def split_ext(name: str):
    """Yalnızca bilinen bir uzantı varsa (gövde, uzantı) olarak ayırır.
    '2101.00001' veya 'doi_10.1037_abc' gibi adlar bölünmez."""
    stem, ext = os.path.splitext(name)
    if ext.lower() in _KNOWN_EXT:
        return stem, ext.lower()
    return name, ""


def sanitize_filename(name: str, max_len: int = 150) -> str:
    """Windows'ta geçerli, makul uzunlukta bir dosya adı üretir."""
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", name)
    name = re.sub(r"\s+", " ", name).strip(" .")
    stem, ext = split_ext(name)
    stem = stem[: max(1, max_len - len(ext))].rstrip(" .") or "dosya"
    if stem.split(".")[0].upper() in _WIN_RESERVED:
        stem = "_" + stem
    return stem + ext


def filename_from_content_disposition(value):
    """Content-Disposition başlığındaki dosya adını (UTF-8 dahil) çözer."""
    if not value:
        return None
    m = re.search(r"filename\*\s*=\s*([\w-]*)'[^']*'([^;]+)", value, re.IGNORECASE)
    if m:
        raw = m.group(2).strip().strip('"')
        try:
            return unquote(raw, encoding=m.group(1) or "utf-8", errors="replace")
        except LookupError:
            return unquote(raw)
    m = (re.search(r'filename\s*=\s*"([^"]*)"', value, re.IGNORECASE)
         or re.search(r"filename\s*=\s*([^;]+)", value, re.IGNORECASE))
    if not m:
        return None
    name = m.group(1).strip()
    try:  # HTTP başlıkları latin-1 okunur; UTF-8 Türkçe karakterleri düzelt
        name = name.encode("latin-1").decode("utf-8")
    except (UnicodeEncodeError, UnicodeDecodeError):
        pass
    if "%" in name:
        name = unquote(name)
    return os.path.basename(name.replace("\\", "/"))


def content_type(resp) -> str:
    return resp.headers.get("Content-Type", "").split(";")[0].strip().lower()


def is_html(ctype: str) -> bool:
    return ctype in ("text/html", "application/xhtml+xml")


def guess_ext(ctype: str) -> str:
    if ctype in _EXT_BY_TYPE:
        return _EXT_BY_TYPE[ctype]
    if not ctype or ctype == "application/octet-stream":
        return ""
    ext = mimetypes.guess_extension(ctype) or ""
    return ext if ext.lower() in _KNOWN_EXT else ""


def url_basename(url: str) -> str:
    try:
        return unquote(os.path.basename(urlparse(url).path.rstrip("/")))
    except ValueError:
        return ""


def doi_from_url(url: str):
    try:
        host = (urlparse(url).hostname or "").lower()
    except ValueError:
        return None
    m = re.search(r"(10\.\d{4,9}/[^?#\s]+)", unquote(url))
    if m and host.endswith("doi.org"):
        return m.group(1).rstrip("/")
    return None


def name_from_meta(meta: dict):
    """Makale sayfasındaki etiketlerden 'Soyad (Yıl) - Başlık' üretir."""
    if not meta:
        return None
    title = meta.get("citation_title") or meta.get("dc.title")
    if not title:
        return None
    title = re.sub(r"\s+", " ", title).strip()
    if len(title) > 110:
        title = title[:110].rsplit(" ", 1)[0] + "…"

    author = (meta.get("citation_author") or meta.get("dc.creator") or "").strip()
    if "," in author:
        surname = author.split(",")[0].strip()
    else:
        surname = author.split()[-1] if author.split() else ""

    date = " ".join(meta.get(k, "") for k in (
        "citation_publication_date", "citation_date", "citation_online_date",
        "citation_year", "dc.date"))
    year = re.search(r"\b(1[5-9]\d\d|20\d\d)\b", date)

    prefix = " ".join(p for p in (surname, f"({year.group(1)})" if year else "") if p)
    return f"{prefix} - {title}" if prefix else title


def make_filename(resp, original_url, index, meta=None, first_bytes=b"", force_ext=None):
    """İndirilen içerik için anlamlı bir dosya adı seçer.

    Öncelik: makale etiketleri → Content-Disposition → DOI → URL'nin son parçası.
    """
    ctype = content_type(resp)
    looks_pdf = b"%PDF-" in first_bytes[:1024] or ctype == "application/pdf"
    host = (urlparse(original_url).hostname or "kaynak").removeprefix("www.")

    stem, ext = None, ""
    title_name = name_from_meta(meta)
    if title_name:
        stem = title_name
    else:
        candidates = [filename_from_content_disposition(resp.headers.get("Content-Disposition"))]
        doi = doi_from_url(original_url)
        if doi:
            candidates.append("doi_" + doi.replace("/", "_"))
        candidates += [url_basename(resp.url), url_basename(original_url)]
        for cand in candidates:
            cand = (cand or "").strip()
            if not cand or split_ext(cand)[0].lower() in _GENERIC_NAMES:
                continue
            if cand.isdigit():  # ör. .../article-file/123456
                cand = f"{host}_{cand}"
            stem, ext = split_ext(cand)
            break
        if not stem:
            stem = f"kaynak_{index:03d}_{host}"

    if force_ext:
        ext = force_ext
    elif looks_pdf:
        ext = ".pdf"
    elif not ext:
        ext = guess_ext(ctype)
    return sanitize_filename(stem + ext)


def unique_path(folder: Path, filename: str) -> Path:
    """Aynı adlı dosya varsa üzerine yazmamak için 'ad (2).pdf' üretir."""
    stem, ext = split_ext(filename)
    candidate = folder / filename
    n = 2
    while candidate.exists() or candidate.with_name(candidate.name + ".part").exists():
        candidate = folder / f"{stem} ({n}){ext}"
        n += 1
    return candidate


def format_bytes(n) -> str:
    n = float(n or 0)
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024


def shorten(text: str, limit: int = 48) -> str:
    if len(text) <= limit:
        return text
    half = (limit - 1) // 2
    return text[:half] + "…" + text[-half:]


# ════════════════════════════════════════════════════════════════════════════
#  3) MAKALE SAYFASINDAN PDF BULMA
# ════════════════════════════════════════════════════════════════════════════

_META_TAG_RE = re.compile(r"<meta\b[^>]*>", re.IGNORECASE)
_ATTR_RE = re.compile(r"""([\w:.-]+)\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'>]+))""")
_WANTED_META = {
    "citation_pdf_url", "citation_title", "citation_author", "citation_publication_date",
    "citation_date", "citation_online_date", "citation_year",
    "dc.title", "dc.creator", "dc.date",
}


def parse_citation_meta(page: str) -> dict:
    """Google Scholar / Dublin Core <meta> etiketlerini okur (ilk değer geçerli)."""
    meta = {}
    for tag in _META_TAG_RE.findall(page):
        attrs = {}
        for m in _ATTR_RE.finditer(tag):
            value = next(v for v in m.groups()[1:] if v is not None)
            attrs[m.group(1).lower()] = html.unescape(value).strip()
        key = (attrs.get("name") or attrs.get("property") or "").lower()
        if key in _WANTED_META and attrs.get("content") and key not in meta:
            meta[key] = attrs["content"]
    return meta


def decode_html(raw: bytes, resp) -> str:
    enc = None
    m = re.search(r"charset=\s*[\"']?([\w-]+)", resp.headers.get("Content-Type", ""), re.I)
    if m:
        enc = m.group(1)
    else:
        m = re.search(rb"<meta[^>]+charset=\s*[\"']?([\w-]+)", raw[:4096], re.I)
        if m:
            enc = m.group(1).decode("ascii", "ignore")
    try:
        return raw.decode(enc or "utf-8", errors="replace")
    except LookupError:
        return raw.decode("utf-8", errors="replace")


# ════════════════════════════════════════════════════════════════════════════
#  4) İNDİRME MOTORU (ayrı iş parçacığında çalışır)
# ════════════════════════════════════════════════════════════════════════════

class Cancelled(Exception):
    """Kullanıcı 'Durdur'a bastı."""


class DownloadError(Exception):
    """Kullanıcıya gösterilecek, açıklaması hazır indirme hatası."""


def make_session() -> requests.Session:
    session = requests.Session()
    session.headers.update(HEADERS)
    retry = Retry(
        total=3, connect=3, read=2, backoff_factor=1.0,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=frozenset({"GET", "HEAD"}),
        raise_on_status=False, respect_retry_after_header=False,
    )
    adapter = HTTPAdapter(max_retries=retry)
    session.mount("http://", adapter)
    session.mount("https://", adapter)
    return session


def describe_status(code: int) -> str:
    tips = {
        401: "giriş ya da abonelik gerekiyor",
        403: "erişim engellendi (yayıncı otomatik indirmeye izin vermiyor ya da abonelik gerekiyor)",
        404: "sayfa bulunamadı (link hatalı ya da kaldırılmış olabilir)",
        410: "kaynak kalıcı olarak kaldırılmış",
        429: "çok fazla istek gönderildi, bir süre sonra tekrar deneyin",
        451: "yasal nedenlerle erişilemiyor",
    }
    reason = tips.get(code) or ("sunucu hatası" if code >= 500 else "istek reddedildi")
    return f"HTTP {code} – {reason}"


def describe_error(exc: Exception) -> str:
    exc_mod = requests.exceptions
    if isinstance(exc, DownloadError):
        return str(exc)
    if isinstance(exc, exc_mod.HTTPError) and exc.response is not None:
        return describe_status(exc.response.status_code)
    if isinstance(exc, exc_mod.SSLError):
        return "Güvenli bağlantı (SSL) kurulamadı"
    if isinstance(exc, exc_mod.Timeout):
        return "Zaman aşımı – sunucu yanıt vermedi"
    if isinstance(exc, exc_mod.TooManyRedirects):
        return "Çok fazla yönlendirme"
    if isinstance(exc, exc_mod.ChunkedEncodingError):
        return "Bağlantı indirme sırasında koptu"
    if isinstance(exc, exc_mod.ConnectionError):
        return "Bağlantı kurulamadı – internet bağlantınızı ya da adresi kontrol edin"
    if isinstance(exc, (exc_mod.InvalidURL, exc_mod.MissingSchema, exc_mod.InvalidSchema)):
        return "Geçersiz link"
    if isinstance(exc, OSError):
        return f"Dosya kaydedilemedi: {exc.strerror or exc}"
    return f"{type(exc).__name__}: {exc}"


STATUS_LABELS = {
    "ok": "İndirildi",
    "html": "Web sayfası kaydedildi",
    "skipped": "Atlandı",
    "error": "Hata",
}


class DownloadWorker(threading.Thread):
    """Linkleri sırayla indirir; arayüze yalnızca kuyruk üzerinden mesaj yollar.

    (Tkinter thread-safe olmadığı için bu sınıf arayüz nesnelerine hiç dokunmaz.)
    Mesajlar:
        ("log", seviye, metin)
        ("overall", tamamlanan, toplam)
        ("file", dosya_adı, inen_bayt, toplam_bayt | None)
        ("done", sayaçlar, durduruldu_mu, rapor_yolu | None)
    """

    def __init__(self, links, folder, options, events, cancel_event):
        super().__init__(daemon=True)
        self.links = list(links)
        self.folder = Path(folder)
        self.options = options
        self.events = events
        self.cancel = cancel_event

    # --- arayüze mesaj ---------------------------------------------------------
    def emit(self, *message):
        self.events.put(message)

    def log(self, level, text):
        self.emit("log", level, text)

    # --- ana döngü -------------------------------------------------------------
    def run(self):
        total = len(self.links)
        counts = {"ok": 0, "html": 0, "skipped": 0, "error": 0}
        results = []
        stopped = False
        session = make_session()
        try:
            for i, url in enumerate(self.links, start=1):
                if self.cancel.is_set():
                    stopped = True
                    break
                self.emit("overall", i - 1, total)
                self.log("info", f"[{i}/{total}] {url}")
                try:
                    status, filename, note = self._download_one(session, url, i)
                except Cancelled:
                    stopped = True
                    results.append((i, url, "Durduruldu", "", "Kullanıcı durdurdu"))
                    break
                except Exception as exc:  # her türlü hatayı loga yaz, sonrakine geç
                    status, filename, note = "error", "", describe_error(exc)

                counts[status] += 1
                results.append((i, url, STATUS_LABELS[status], filename, note))
                if status == "ok":
                    self.log("success", f"   ✓ Kaydedildi: {filename}  ({note})")
                elif status == "html":
                    self.log("warn", f"   ⚠ {note}: {filename}")
                elif status == "skipped":
                    self.log("warn", f"   ⚠ Atlandı: {note}")
                else:
                    self.log("error", f"   ✗ Hata: {note}")
                self.emit("overall", i, total)

                if i < total:
                    self.cancel.wait(PAUSE_BETWEEN)
        except Exception as exc:
            self.log("error", f"Beklenmeyen hata: {describe_error(exc)}")
        finally:
            session.close()
            stopped = stopped or self.cancel.is_set()
            report = self._write_report(results)
            self.emit("done", counts, stopped, report)

    # --- tek link ---------------------------------------------------------------
    def _download_one(self, session, url, index):
        resp = session.get(url, stream=True, allow_redirects=True, timeout=TIMEOUT)
        with resp:
            resp.raise_for_status()
            if resp.history:
                self.log("muted", f"   ↪ Yönlendirildi → {resp.url}")

            if is_html(content_type(resp)):
                return self._handle_page(session, resp, url, index)

            path, size = self._stream_to_file(
                resp, lambda first: make_filename(resp, url, index, first_bytes=first))
            return "ok", path.name, format_bytes(size)

    def _handle_page(self, session, resp, url, index):
        """Link bir web sayfasına açıldıysa: içindeki PDF etiketini dene."""
        raw = self._read_limited(resp)
        meta = parse_citation_meta(decode_html(raw, resp)) if self.options["find_pdf"] else {}
        pdf_url = meta.get("citation_pdf_url")

        if pdf_url:
            pdf_url = urljoin(resp.url, pdf_url)
            self.log("muted", f"   → Sayfada PDF bağlantısı bulundu: {pdf_url}")
            try:
                pdf_resp = session.get(pdf_url, stream=True, allow_redirects=True,
                                       timeout=TIMEOUT, headers={"Referer": resp.url})
            except requests.RequestException as exc:
                self.log("warn", f"   ⚠ PDF bağlantısı açılamadı: {describe_error(exc)}")
            else:
                with pdf_resp:
                    if pdf_resp.ok and not is_html(content_type(pdf_resp)):
                        path, size = self._stream_to_file(
                            pdf_resp,
                            lambda first: make_filename(pdf_resp, url, index, meta=meta,
                                                        first_bytes=first))
                        return "ok", path.name, f"{format_bytes(size)}, makale sayfasındaki PDF bağlantısından"
                    if pdf_resp.ok:
                        self.log("warn", "   ⚠ PDF yerine yine bir web sayfası geldi "
                                         "(abonelik ya da giriş gerekiyor olabilir).")
                    else:
                        self.log("warn", f"   ⚠ PDF indirilemedi: {describe_status(pdf_resp.status_code)}")
        elif self.options["find_pdf"]:
            self.log("muted", "   · Sayfada PDF bağlantısı etiketi bulunamadı.")

        if self.options["save_html"]:
            filename = make_filename(resp, url, index, meta=meta, force_ext=".html")
            path = self._write_bytes(raw, filename)
            return "html", path.name, "PDF bulunamadı, web sayfası kaydedildi"
        return "skipped", "", "link bir web sayfasına açılıyor ve PDF bulunamadı"

    # --- dosyaya yazma ---------------------------------------------------------
    def _stream_to_file(self, resp, name_for_first_chunk):
        """stream=True yanıtı parça parça .part dosyasına yazar, bitince adlandırır."""
        encoded = resp.headers.get("Content-Encoding", "").lower() not in ("", "identity")
        try:
            total = None if encoded else int(resp.headers.get("Content-Length", ""))
        except ValueError:
            total = None

        chunks = resp.iter_content(chunk_size=CHUNK_SIZE)
        first = b""
        for chunk in chunks:
            if self.cancel.is_set():
                raise Cancelled()
            if chunk:
                first = chunk
                break
        if not first:
            raise DownloadError("Sunucu boş yanıt döndürdü")

        # Dosya adını ilk parçaya bakarak seç (ör. '%PDF' imzası → .pdf)
        path = unique_path(self.folder, name_for_first_chunk(first))
        tmp = path.with_name(path.name + ".part")
        received = len(first)
        self.emit("file", path.name, received, total)
        last_update = time.monotonic()
        try:
            with open(tmp, "wb") as fh:
                fh.write(first)
                for chunk in chunks:
                    if self.cancel.is_set():
                        raise Cancelled()
                    if not chunk:
                        continue
                    fh.write(chunk)
                    received += len(chunk)
                    now = time.monotonic()
                    if now - last_update >= 0.1:   # arayüzü mesaja boğma
                        self.emit("file", path.name, received, total)
                        last_update = now
            if total and received < total:
                raise DownloadError(
                    f"Bağlantı yarıda kesildi ({format_bytes(received)} / {format_bytes(total)})")
            os.replace(tmp, path)
        except BaseException:
            try:
                tmp.unlink()
            except OSError:
                pass
            raise
        self.emit("file", path.name, received, received)
        return path, received

    def _read_limited(self, resp) -> bytes:
        buf = bytearray()
        for chunk in resp.iter_content(chunk_size=CHUNK_SIZE):
            if self.cancel.is_set():
                raise Cancelled()
            buf += chunk
            if len(buf) >= HTML_READ_LIMIT:
                break
        return bytes(buf)

    def _write_bytes(self, data: bytes, filename: str) -> Path:
        path = unique_path(self.folder, filename)
        path.write_bytes(data)
        self.emit("file", path.name, len(data), len(data))
        return path

    def _write_report(self, results):
        if not results:
            return None
        path = self.folder / f"indirme_raporu_{datetime.now():%Y%m%d_%H%M%S}.csv"
        try:
            # utf-8-sig + ';' → Türkçe Excel'de çift tıklayınca düzgün açılır
            with open(path, "w", newline="", encoding="utf-8-sig") as fh:
                writer = csv.writer(fh, delimiter=";")
                writer.writerow(["Sıra", "Link", "Durum", "Dosya", "Açıklama"])
                writer.writerows(results)
            return path
        except OSError as exc:
            self.log("error", f"Rapor yazılamadı: {describe_error(exc)}")
            return None


# ════════════════════════════════════════════════════════════════════════════
#  5) ARAYÜZ (CustomTkinter)
# ════════════════════════════════════════════════════════════════════════════

TEXT = ("gray10", "gray92")
MUTED = ("gray40", "gray62")
LOG_COLORS = {
    "success": "#2FA36B",
    "error": "#E5484D",
    "warn": "#D98E04",
    "muted": "#8B919A",
}
STATUS_COLORS = {"success": LOG_COLORS["success"], "error": LOG_COLORS["error"],
                 "warn": LOG_COLORS["warn"], "info": TEXT}


def default_download_dir() -> Path:
    home = Path.home()
    downloads = home / "Downloads"
    return (downloads if downloads.is_dir() else home) / "Akademik Kaynaklar"


def open_in_file_manager(path: Path):
    if sys.platform.startswith("win"):
        os.startfile(str(path))  # type: ignore[attr-defined]
    elif sys.platform == "darwin":
        subprocess.Popen(["open", str(path)])
    else:
        subprocess.Popen(["xdg-open", str(path)])


class App(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title(f"{APP_NAME}  v{APP_VERSION}")
        self.geometry("1180x740")
        self.minsize(980, 640)

        self.events = queue.Queue()
        self.cancel_event = threading.Event()
        self.worker = None
        self._file_bar_spinning = False

        self.folder_var = ctk.StringVar(value=str(default_download_dir()))
        self.opt_doi = ctk.BooleanVar(value=True)
        self.opt_find_pdf = ctk.BooleanVar(value=True)
        self.opt_save_html = ctk.BooleanVar(value=True)

        if sys.platform.startswith("win"):
            mono = "Consolas"
        elif sys.platform == "darwin":
            mono = "Menlo"
        else:
            mono = "DejaVu Sans Mono"
        self.font_title = ctk.CTkFont(size=22, weight="bold")
        self.font_section = ctk.CTkFont(size=15, weight="bold")
        self.font_small = ctk.CTkFont(size=12)
        self.font_log = ctk.CTkFont(family=mono, size=12)

        self.grid_columnconfigure(0, weight=3, uniform="col")
        self.grid_columnconfigure(1, weight=2, uniform="col")
        self.grid_rowconfigure(1, weight=1)

        self._build_header()
        self._build_left_panel()
        self._build_right_panel()

        self._log("info", "Hazır. Metni yapıştırın, klasörü seçin ve 'İndirmeyi Başlat'a basın.")
        self.after(80, self._poll_events)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ── yerleşim ────────────────────────────────────────────────────────────────
    def _section(self, parent, text, row, pady=(16, 2)):
        ctk.CTkLabel(parent, text=text, font=self.font_section, anchor="w").grid(
            row=row, column=0, sticky="ew", padx=18, pady=pady)

    def _build_header(self):
        header = ctk.CTkFrame(self, fg_color="transparent")
        header.grid(row=0, column=0, columnspan=2, sticky="ew", padx=22, pady=(18, 8))
        header.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(header, text=APP_NAME, font=self.font_title).grid(row=0, column=0, sticky="w")
        ctk.CTkLabel(
            header, font=self.font_small, text_color=MUTED,
            text="Kaynakçayı ya da linkli metni yapıştırın; linkler ayıklanır, dosyalar klasörünüze iner.",
        ).grid(row=1, column=0, sticky="w")
        self.theme_switch = ctk.CTkSwitch(header, text="Koyu tema", command=self._toggle_theme)
        self.theme_switch.grid(row=0, column=1, rowspan=2, sticky="e")
        if ctk.get_appearance_mode().lower() == "dark":
            self.theme_switch.select()

    def _build_left_panel(self):
        card = ctk.CTkFrame(self, corner_radius=14)
        card.grid(row=1, column=0, sticky="nsew", padx=(22, 10), pady=(4, 22))
        card.grid_columnconfigure(0, weight=1)
        card.grid_rowconfigure(2, weight=1)

        # 1 — metin
        self._section(card, "1   Kaynak metni", row=0)
        ctk.CTkLabel(
            card, font=self.font_small, text_color=MUTED, anchor="w", justify="left",
            wraplength=520,
            text="Kaynakça, e-posta ya da karışık metin: http/https linkleri ve DOI'ler otomatik bulunur.",
        ).grid(row=1, column=0, sticky="ew", padx=18)

        self.input_box = ctk.CTkTextbox(card, wrap="word", font=ctk.CTkFont(size=13),
                                        border_width=1, corner_radius=10)
        self.input_box.grid(row=2, column=0, sticky="nsew", padx=18, pady=(8, 8))
        self.input_box.bind("<Control-a>", self._select_all_input)
        self.input_box.bind("<Control-A>", self._select_all_input)

        bar = ctk.CTkFrame(card, fg_color="transparent")
        bar.grid(row=3, column=0, sticky="ew", padx=18)
        bar.grid_columnconfigure(2, weight=1)
        self.paste_btn = ctk.CTkButton(bar, text="Panodan Yapıştır", width=130,
                                       fg_color="transparent", border_width=1,
                                       text_color=TEXT, command=self._paste)
        self.paste_btn.grid(row=0, column=0, padx=(0, 8))
        self.clear_btn = ctk.CTkButton(bar, text="Temizle", width=80,
                                       fg_color="transparent", border_width=1,
                                       text_color=TEXT, command=self._clear_input)
        self.clear_btn.grid(row=0, column=1)
        self.count_label = ctk.CTkLabel(bar, text="Henüz link ayıklanmadı",
                                        font=self.font_small, text_color=MUTED)
        self.count_label.grid(row=0, column=2, sticky="e", padx=10)
        self.extract_btn = ctk.CTkButton(bar, text="Linkleri Ayıkla", width=140,
                                         command=self._on_extract)
        self.extract_btn.grid(row=0, column=3, sticky="e")

        # 2 — klasör
        self._section(card, "2   İndirme klasörü", row=4, pady=(20, 6))
        folder_row = ctk.CTkFrame(card, fg_color="transparent")
        folder_row.grid(row=5, column=0, sticky="ew", padx=18)
        folder_row.grid_columnconfigure(0, weight=1)
        self.folder_entry = ctk.CTkEntry(folder_row, textvariable=self.folder_var, height=34)
        self.folder_entry.grid(row=0, column=0, sticky="ew", padx=(0, 8))
        self.folder_btn = ctk.CTkButton(folder_row, text="İndirme Klasörü Seç", width=160,
                                        height=34, command=self._choose_folder)
        self.folder_btn.grid(row=0, column=1)

        # seçenekler
        self._section(card, "Seçenekler", row=6, pady=(20, 4))
        opts = ctk.CTkFrame(card, fg_color="transparent")
        opts.grid(row=7, column=0, sticky="ew", padx=18, pady=(0, 18))
        self.option_boxes = []
        for i, (text, var) in enumerate([
            ("Çıplak DOI'leri de yakala  (doi:10.xxxx/…  →  https://doi.org/…)", self.opt_doi),
            ("Link bir makale sayfasına açılırsa sayfadaki PDF'i bulup indir", self.opt_find_pdf),
            ("PDF bulunamazsa web sayfasını .html olarak kaydet", self.opt_save_html),
        ]):
            box = ctk.CTkCheckBox(opts, text=text, variable=var, font=self.font_small,
                                  checkbox_width=20, checkbox_height=20)
            box.grid(row=i, column=0, sticky="w", pady=3)
            self.option_boxes.append(box)

    def _build_right_panel(self):
        card = ctk.CTkFrame(self, corner_radius=14)
        card.grid(row=1, column=1, sticky="nsew", padx=(10, 22), pady=(4, 22))
        card.grid_columnconfigure(0, weight=1)
        card.grid_rowconfigure(8, weight=1)

        # 3 — başlat / durdur
        self._section(card, "3   İndir", row=0)
        btns = ctk.CTkFrame(card, fg_color="transparent")
        btns.grid(row=1, column=0, sticky="ew", padx=18, pady=(6, 10))
        btns.grid_columnconfigure(0, weight=1)
        self.start_btn = ctk.CTkButton(
            btns, text="İndirmeyi Başlat", height=42,
            font=ctk.CTkFont(size=15, weight="bold"),
            fg_color="#1F8F4E", hover_color="#18723E", command=self._start)
        self.start_btn.grid(row=0, column=0, sticky="ew")
        self.stop_btn = ctk.CTkButton(
            btns, text="Durdur", width=84, height=42,
            fg_color="#C9353A", hover_color="#A42A2E", state="disabled", command=self._stop)
        self.stop_btn.grid(row=0, column=1, padx=(8, 0))
        self.open_btn = ctk.CTkButton(
            btns, text="Klasörü Aç", width=96, height=42, fg_color="transparent",
            border_width=1, text_color=TEXT, command=self._open_folder)
        self.open_btn.grid(row=0, column=2, padx=(8, 0))

        # ilerleme
        head1 = ctk.CTkFrame(card, fg_color="transparent")
        head1.grid(row=2, column=0, sticky="ew", padx=18)
        head1.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(head1, text="Genel ilerleme", font=self.font_small).grid(row=0, column=0, sticky="w")
        self.overall_label = ctk.CTkLabel(head1, text="0 / 0", font=self.font_small, text_color=MUTED)
        self.overall_label.grid(row=0, column=1, sticky="e")
        self.overall_bar = ctk.CTkProgressBar(card, height=12)
        self.overall_bar.grid(row=3, column=0, sticky="ew", padx=18, pady=(2, 10))
        self.overall_bar.set(0)

        head2 = ctk.CTkFrame(card, fg_color="transparent")
        head2.grid(row=4, column=0, sticky="ew", padx=18)
        head2.grid_columnconfigure(0, weight=1)
        self.file_name_label = ctk.CTkLabel(head2, text="Şu anki dosya: —", font=self.font_small, anchor="w")
        self.file_name_label.grid(row=0, column=0, sticky="w")
        self.file_size_label = ctk.CTkLabel(head2, text="", font=self.font_small, text_color=MUTED)
        self.file_size_label.grid(row=0, column=1, sticky="e")
        self.file_bar = ctk.CTkProgressBar(card, height=8)
        self.file_bar.grid(row=5, column=0, sticky="ew", padx=18, pady=(2, 8))
        self.file_bar.set(0)

        self.status_label = ctk.CTkLabel(card, text="Bekliyor", font=ctk.CTkFont(size=13, weight="bold"),
                                         anchor="w", justify="left", wraplength=400)
        self.status_label.grid(row=6, column=0, sticky="ew", padx=18, pady=(0, 4))

        # log
        head3 = ctk.CTkFrame(card, fg_color="transparent")
        head3.grid(row=7, column=0, sticky="ew", padx=18, pady=(8, 0))
        head3.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(head3, text="İşlem Geçmişi", font=self.font_section).grid(row=0, column=0, sticky="w")
        ctk.CTkButton(head3, text="Logu Temizle", width=96, height=26, fg_color="transparent",
                      border_width=1, text_color=TEXT, command=self._clear_log).grid(row=0, column=1, sticky="e")
        self.log_box = ctk.CTkTextbox(card, wrap="word", font=self.font_log, border_width=1,
                                      corner_radius=10, state="disabled")
        self.log_box.grid(row=8, column=0, sticky="nsew", padx=18, pady=(6, 18))
        for tag, color in LOG_COLORS.items():
            self.log_box.tag_config(tag, foreground=color)

    # ── küçük yardımcılar ────────────────────────────────────────────────────────
    def _log(self, level, text):
        stamp = datetime.now().strftime("%H:%M:%S")
        self.log_box.configure(state="normal")
        self.log_box.insert("end", f"{stamp}  ", ("muted",))
        self.log_box.insert("end", text + "\n", (level,) if level in LOG_COLORS else None)
        self.log_box.configure(state="disabled")
        self.log_box.see("end")

    def _clear_log(self):
        self.log_box.configure(state="normal")
        self.log_box.delete("1.0", "end")
        self.log_box.configure(state="disabled")

    def _set_status(self, text, level="info"):
        self.status_label.configure(text=text, text_color=STATUS_COLORS.get(level, TEXT))

    def _select_all_input(self, _event=None):
        self.input_box.tag_add("sel", "1.0", "end-1c")
        return "break"

    def _toggle_theme(self):
        ctk.set_appearance_mode("dark" if self.theme_switch.get() else "light")

    def _set_running(self, running: bool):
        idle = "disabled" if running else "normal"
        self.start_btn.configure(state="disabled" if running else "normal",
                                 text="İndiriliyor…" if running else "İndirmeyi Başlat")
        self.stop_btn.configure(state="normal" if running else "disabled")
        for widget in (self.extract_btn, self.folder_btn, self.folder_entry,
                       self.paste_btn, self.clear_btn, *self.option_boxes):
            widget.configure(state=idle)

    def _reset_file_progress(self):
        if self._file_bar_spinning:
            self.file_bar.stop()
            self.file_bar.configure(mode="determinate")
            self._file_bar_spinning = False
        self.file_bar.set(0)
        self.file_name_label.configure(text="Şu anki dosya: —")
        self.file_size_label.configure(text="")

    def _update_file_progress(self, name, received, total):
        self.file_name_label.configure(text=shorten(name, 46))
        if total:
            if self._file_bar_spinning:
                self.file_bar.stop()
                self.file_bar.configure(mode="determinate")
                self._file_bar_spinning = False
            self.file_bar.set(min(received / total, 1.0))
            self.file_size_label.configure(text=f"{format_bytes(received)} / {format_bytes(total)}")
        else:  # sunucu boyut bildirmediyse kayan çubuk
            if not self._file_bar_spinning:
                self.file_bar.configure(mode="indeterminate")
                self.file_bar.start()
                self._file_bar_spinning = True
            self.file_size_label.configure(text=format_bytes(received))

    def _extract_links(self):
        text = self.input_box.get("1.0", "end")
        links = extract_links(text, include_doi=self.opt_doi.get())
        self.count_label.configure(text=f"{len(links)} link bulundu" if links else "Link bulunamadı")
        return links

    # ── buton olayları ───────────────────────────────────────────────────────────
    def _paste(self):
        try:
            text = self.clipboard_get()
        except Exception:
            text = ""
        if not text.strip():
            self._log("warn", "Panoda yapıştırılacak metin yok.")
            return
        self.input_box.insert("insert", text)

    def _clear_input(self):
        self.input_box.delete("1.0", "end")
        self.count_label.configure(text="Henüz link ayıklanmadı")

    def _on_extract(self):
        links = self._extract_links()
        if not links:
            self._log("warn", "Metinde link bulunamadı.")
            return
        self._log("info", f"{len(links)} link bulundu:")
        for i, link in enumerate(links, start=1):
            self._log("muted", f"  {i:>3}. {link}")

    def _choose_folder(self):
        initial = self.folder_var.get()
        if not os.path.isdir(initial):
            initial = str(Path.home())
        path = filedialog.askdirectory(parent=self, initialdir=initial,
                                       title="İndirme klasörünü seçin")
        if path:
            self.folder_var.set(os.path.normpath(path))
            self._log("info", f"İndirme klasörü: {self.folder_var.get()}")

    def _open_folder(self):
        folder = Path(self.folder_var.get().strip() or ".").expanduser()
        if not folder.is_dir():
            messagebox.showinfo(APP_NAME, "Klasör henüz yok; ilk indirmede otomatik oluşturulacak.",
                                parent=self)
            return
        try:
            open_in_file_manager(folder)
        except Exception as exc:
            self._log("error", f"Klasör açılamadı: {exc}")

    def _start(self):
        if self.worker and self.worker.is_alive():
            return
        links = self._extract_links()
        if not links:
            messagebox.showwarning(APP_NAME, "Metinde indirilecek link bulunamadı.\n"
                                             "Önce kaynakçayı ya da linkli metni yapıştırın.",
                                   parent=self)
            return
        folder_text = self.folder_var.get().strip()
        if not folder_text:
            messagebox.showwarning(APP_NAME, "Lütfen bir indirme klasörü seçin.", parent=self)
            return
        folder = Path(folder_text).expanduser()
        try:
            folder.mkdir(parents=True, exist_ok=True)
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"Klasör oluşturulamadı:\n{folder}\n\n{exc}", parent=self)
            return

        self.cancel_event = threading.Event()
        options = {"find_pdf": self.opt_find_pdf.get(), "save_html": self.opt_save_html.get()}
        self._set_running(True)
        self.overall_bar.set(0)
        self.overall_label.configure(text=f"0 / {len(links)}")
        self._reset_file_progress()
        self._set_status("İndiriliyor…")
        self._log("info", f"İndirme başladı: {len(links)} link → {folder}")
        self.worker = DownloadWorker(links, folder, options, self.events, self.cancel_event)
        self.worker.start()

    def _stop(self):
        if self.worker and self.worker.is_alive():
            self.cancel_event.set()
            self.stop_btn.configure(state="disabled")
            self._set_status("Durduruluyor…", "warn")
            self._log("warn", "Durdurma isteği alındı; yarım kalan dosya silinecek.")

    def _finish(self, counts, stopped, report):
        self._set_running(False)
        self._reset_file_progress()
        parts = [f"{counts['ok']} dosya indirildi"]
        if counts["html"]:
            parts.append(f"{counts['html']} web sayfası kaydedildi")
        if counts["skipped"]:
            parts.append(f"{counts['skipped']} atlandı")
        if counts["error"]:
            parts.append(f"{counts['error']} hata")
        summary = " · ".join(parts)
        title = "Durduruldu" if stopped else "Tamamlandı"
        level = "warn" if (stopped or counts["error"]) else "success"
        if not stopped:
            self.overall_bar.set(1)
        self._set_status(f"{title}: {summary}", level)
        self._log(level, f"{title}: {summary}")
        if report:
            self._log("muted", f"Rapor: {report}")

    # ── iş parçacığından gelen mesajlar ─────────────────────────────────────────
    def _poll_events(self):
        try:
            for _ in range(500):
                try:
                    message = self.events.get_nowait()
                except queue.Empty:
                    break
                self._handle_event(message)
        finally:
            self.after(80, self._poll_events)

    def _handle_event(self, message):
        kind = message[0]
        if kind == "log":
            self._log(message[1], message[2])
        elif kind == "overall":
            done, total = message[1], message[2]
            self.overall_bar.set(done / total if total else 0)
            self.overall_label.configure(text=f"{done} / {total}")
        elif kind == "file":
            self._update_file_progress(*message[1:])
        elif kind == "done":
            self._finish(*message[1:])

    def _on_close(self):
        if self.worker and self.worker.is_alive():
            if not messagebox.askyesno(APP_NAME, "İndirme devam ediyor. Durdurup çıkmak istiyor musunuz?",
                                       parent=self):
                return
            self.cancel_event.set()
            self.worker.join(timeout=3)
        self.destroy()


def main():
    ctk.set_appearance_mode("system")
    ctk.set_default_color_theme("blue")
    app = App()
    app.mainloop()


if __name__ == "__main__":
    main()
