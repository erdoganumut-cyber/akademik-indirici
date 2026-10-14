# -*- coding: utf-8 -*-
"""
Akademik Kaynak İndirici  v1.1
==============================
Karışık metinlerden ve akademik kaynakçalardan (APA, MLA, Chicago...) linkleri
ayıklar ve seçilen klasöre indirir.

Öne çıkanlar
- http/https linklerini ve (isteğe bağlı) çıplak DOI'leri (doi:10.xxxx/...) bulur;
  sonlarında kalan nokta, virgül, kapanmamış parantez gibi artıkları temizler.
- requests ile parça parça (stream=True) indirir, DOI yönlendirmelerini izler
  (allow_redirects=True), geçici sunucu hatalarında otomatik yeniden dener.
- Link bir makale sayfasına açılırsa PDF'i şu sırayla arar:
    1. sayfadaki Google Scholar etiketi (citation_pdf_url)
    2. sayfadaki "PDF / Tam Metin / İndir" bağlantıları (OJS dergileri dahil)
    3. DSpace 7 kurum arşivleri (hdl.handle.net linkleri) için arşivin kendi API'si
    4. Unpaywall: DOI'nin yasal açık erişim kopyaları (e-posta girilirse)
- Aynı dosya ikinci kez inerse (aynı makalenin DOI'si ve DergiPark linki gibi)
  kopyayı silip "zaten vardı" der; listeyi tekrar çalıştırmak çift dosya üretmez.
- İnmeyen linkleri tek tıkla tarayıcıda açar (kurum girişinizle indirebilmeniz için).
- Word (.docx), TXT ve PDF dosyalarından da link okur (Word'de bir yazının
  arkasına gizlenmiş köprüler ve dipnotlar dahil).
- Klasörde daha önce indirilmiş kaynakları (eski raporlara bakarak) tekrar indirmez.
- İndirme ayrı bir iş parçacığında (thread) çalışır; arayüz donmaz.
- Bitince hedef klasöre Excel'de açılabilen bir indirme raporu (CSV) yazar.

Gereksinimler:  pip install customtkinter requests pypdf
"""

import csv
import hashlib
import html
import json
import mimetypes
import os
import queue
import re
import subprocess
import sys
import threading
import time
import webbrowser
import zipfile
from datetime import datetime
from pathlib import Path
from urllib.parse import quote, unquote, urljoin, urlparse

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
APP_VERSION = "1.1"

CHUNK_SIZE = 64 * 1024              # parça parça indirme boyutu (64 KB)
HTML_READ_LIMIT = 5 * 1024 * 1024   # PDF bağlantısı aramak için okunacak en fazla HTML
TIMEOUT = (10, 40)                  # (bağlanma, okuma) saniye
API_TIMEOUT = (10, 25)
PAUSE_BETWEEN = 0.5                 # sunucuları yormamak için dosyalar arası bekleme
MAX_CANDIDATES = 4                  # bir sayfada denenecek en fazla PDF adayı

UNPAYWALL_API = "https://api.unpaywall.org/v2/"
EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")

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

    # PDF'lerde satır sonunda bölünen linkin yarım kalan ilk parçasını at
    # (ör. ".../konservatoryum/" + tam hâli ".../konservatoryum/issue/82862/1264925")
    return [u for u in links
            if not (u.endswith(("/", "-", "_"))
                    and any(o != u and o.startswith(u) for o in links))]


# ── Dosyadan metin okuma (Word, TXT, PDF...) ────────────────────────────────

SUPPORTED_FILES = (
    ("Desteklenen dosyalar", "*.docx *.txt *.pdf *.md *.rtf *.csv *.html *.htm"),
    ("Word belgesi", "*.docx"),
    ("Metin dosyası", "*.txt *.md *.csv"),
    ("PDF", "*.pdf"),
    ("Tüm dosyalar", "*.*"),
)

_DOCX_TOKEN_RE = re.compile(
    r"<w:hyperlink\b([^>]*)>|</w:hyperlink>|<w:t(?:\s[^>]*)?>(.*?)</w:t>|"
    r"<w:instrText(?:\s[^>]*)?>(.*?)</w:instrText>|<w:tab/>|<w:br\b[^>]*/>|</w:p>",
    re.S,
)
_REL_RE = re.compile(r"<Relationship\b[^>]*>")


def _docx_part_text(zf: zipfile.ZipFile, part: str) -> str:
    """Bir Word XML parçasının metnini çıkarır; köprülerin (hyperlink) adresini de
    görünen metnin yanına ekler — Word'de linkler çoğu zaman bir yazının arkasına
    gizlenir."""
    xml = zf.read(part).decode("utf-8", errors="replace")
    targets = {}
    rels_name = part.replace("word/", "word/_rels/", 1) + ".rels"
    if rels_name in zf.namelist():
        for tag in _REL_RE.findall(zf.read(rels_name).decode("utf-8", errors="replace")):
            attrs = parse_attrs(tag)
            if attrs.get("targetmode", "").lower() == "external" and attrs.get("id"):
                targets[attrs["id"]] = attrs.get("target", "")

    out, link_stack = [], []
    for m in _DOCX_TOKEN_RE.finditer(xml):
        token = m.group(0)
        if token.startswith("<w:hyperlink"):
            rid = parse_attrs(m.group(1)).get("r:id")
            link_stack.append(targets.get(rid, ""))
        elif token == "</w:hyperlink>":
            target = link_stack.pop() if link_stack else ""
            if target.lower().startswith(("http://", "https://")):
                out.append(f" {target} ")
        elif m.group(2) is not None:
            out.append(html.unescape(m.group(2)))
        elif m.group(3) is not None:
            out.append(" " + html.unescape(m.group(3)) + " ")   # HYPERLINK "..." alanları
        elif token == "<w:tab/>":
            out.append("\t")
        else:
            out.append("\n")
    return "".join(out)


def read_docx(path: Path) -> str:
    with zipfile.ZipFile(path) as zf:
        names = zf.namelist()
        parts = ["word/document.xml", "word/footnotes.xml", "word/endnotes.xml"]
        return "\n".join(_docx_part_text(zf, p) for p in parts if p in names)


def read_pdf(path: Path) -> str:
    try:
        from pypdf import PdfReader
    except ImportError:
        raise ValueError("PDF okumak için 'pypdf' kütüphanesi gerekli.")
    reader = PdfReader(str(path))
    chunks = []
    for page in reader.pages:
        try:
            chunks.append(page.extract_text() or "")
        except Exception:
            pass
        # Tıklanabilir linkler (metinde satır sonunda bölünmüş olsalar bile tam hâlleri)
        try:
            for annot in page.get("/Annots") or []:
                uri = (annot.get_object().get("/A") or {}).get("/URI")
                if uri:
                    chunks.append(f" {uri} ")
        except Exception:
            pass
    return "\n".join(chunks)


def read_plain(path: Path) -> str:
    raw = path.read_bytes()
    encodings = ["utf-8-sig", "cp1254"]       # cp1254: eski Türkçe Windows dosyaları
    if raw[:2] in (b"\xff\xfe", b"\xfe\xff"):
        encodings.insert(0, "utf-16")
    for enc in encodings:
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            pass
    return raw.decode("utf-8", errors="replace")


def read_text_from_file(path) -> str:
    path = Path(path)
    ext = path.suffix.lower()
    if ext == ".docx":
        return read_docx(path)
    if ext == ".pdf":
        return read_pdf(path)
    if ext == ".doc":
        raise ValueError("Eski .doc biçimi okunamıyor. Word'de 'Farklı Kaydet → Word Belgesi (.docx)' "
                         "ile kaydedip tekrar deneyin.")
    return read_plain(path)


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


def is_doi_host(url: str) -> bool:
    try:
        return (urlparse(url).hostname or "").lower().endswith("doi.org")
    except ValueError:
        return False


def doi_from_url(url: str):
    if not is_doi_host(url):
        return None
    m = re.search(r"(10\.\d{4,9}/[^?#\s]+)", unquote(url))
    return m.group(1).rstrip("/") if m else None


def normalize_doi(value):
    """'doi:10.1/x', 'https://doi.org/10.1/x' gibi yazımlardan çıplak DOI'yi alır."""
    if not value:
        return None
    m = re.search(r"(10\.\d{4,9}/\S+)", unquote(value))
    return m.group(1).rstrip("/.") if m else None


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
    "citation_date", "citation_online_date", "citation_year", "citation_doi",
    "dc.title", "dc.creator", "dc.date", "dc.identifier",
}


def parse_attrs(tag: str) -> dict:
    attrs = {}
    for m in _ATTR_RE.finditer(tag):
        value = next(v for v in m.groups()[1:] if v is not None)
        attrs.setdefault(m.group(1).lower(), html.unescape(value).strip())
    return attrs


def parse_citation_meta(page: str) -> dict:
    """Google Scholar / Dublin Core <meta> etiketlerini okur (ilk değer geçerli)."""
    meta = {}
    for tag in _META_TAG_RE.findall(page):
        attrs = parse_attrs(tag)
        key = (attrs.get("name") or attrs.get("property") or "").lower()
        if key == "dc.identifier" and not normalize_doi(attrs.get("content")):
            continue  # yalnızca DOI olan dc.identifier işimize yarar
        if key in _WANTED_META and attrs.get("content") and key not in meta:
            meta[key] = attrs["content"]
    return meta


def meta_doi(meta: dict):
    return normalize_doi(meta.get("citation_doi")) or normalize_doi(meta.get("dc.identifier"))


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


_TITLE_RE = re.compile(r"<title[^>]*>(.*?)</title>", re.I | re.S)
_BOT_RE = re.compile(
    r"just a moment|attention required|access denied|captcha|are you a (?:robot|human)|"
    r"verify(?:ing)? (?:that )?you are (?:a )?human|security check|bot (?:check|protection)|"
    r"doğrulama|dogrulama|güvenlik kontrol|robot musunuz|one more step|please wait",
    re.I,
)


def page_title(page: str) -> str:
    m = _TITLE_RE.search(page)
    return re.sub(r"\s+", " ", html.unescape(m.group(1))).strip() if m else ""


def looks_like_bot_check(page: str, final_url: str = "") -> bool:
    """Cloudflare vb. 'insan mısınız' doğrulama sayfası mı?"""
    if "cf-challenge" in page or "challenge-platform" in page or "cf_chl_" in page:
        return True
    if re.search(r"/(?:dogrulama|verify|captcha|challenge)\b", final_url, re.I):
        return True
    return bool(_BOT_RE.search(page_title(page)))


def site_key(url: str) -> str:
    """'dergipark.org.tr', 'sakarya.edu.tr', 'mdpi.com' gibi kayıtlı alan adı."""
    host = (urlparse(url).hostname or "").lower()
    labels = host.split(".")
    if (len(labels) >= 3 and len(labels[-1]) == 2
            and labels[-2] in {"edu", "ac", "org", "com", "gov", "net", "gen", "bel", "k12", "co"}):
        return ".".join(labels[-3:])
    return ".".join(labels[-2:])


def ojs_download_url(url: str) -> str:
    """OJS dergilerinde PDF görüntüleyici sayfasını doğrudan indirme linkine çevirir."""
    return re.sub(r"/article/view/(\d+)/(\d+)/?$", r"/article/download/\1/\2", url)


_A_RE = re.compile(r"<a\b([^>]*)>(.*?)</a\s*>", re.I | re.S)
_EMBED_RE = re.compile(r"<(?:link|iframe|embed|object)\b[^>]*>", re.I)
_TAG_STRIP = re.compile(r"<[^>]+>")
_PDF_TEXT = re.compile(r"\bpdf\b|tam\s*metin|full[\s-]*text|\bdownload\b|i̇ndir|\bindir", re.I)
_JUNK = re.compile(
    r"guide|rehber|template|şablon|sablon|yaz[ıi]m[-_ ]?kural|telif|copyright|"
    r"[-_ /]policy|politika|instruction|for[-_ ]?authors|author[-_ ]?guide|"
    r"\bform\b|formu|kapak|cover|poster|flyer|broşür|brosur|"
    r"cit(?:e|ation)|\bris\b|bibtex|endnote|zotero|mendeley|refworks|"
    r"statistic|istatistik|licen[cs]e|lisans|privacy|gizlilik|cookie|çerez",
    re.I,
)


def find_pdf_candidates(page: str, base_url: str, meta: dict) -> list:
    """Bir makale sayfasındaki olası PDF linklerini en güvenilirden başlayarak döndürür."""
    candidates = []

    def add(raw_url):
        raw_url = (raw_url or "").strip()
        if not raw_url or raw_url.startswith(("#", "javascript:", "mailto:", "tel:")):
            return
        full = ojs_download_url(urljoin(base_url, raw_url))
        if full != base_url and full not in candidates and full.startswith("http"):
            candidates.append(full)

    # 1) Google Scholar etiketi
    add(meta.get("citation_pdf_url"))

    # 2) <link type="application/pdf">, <iframe src="...pdf">, <embed>, <object>
    for tag in _EMBED_RE.findall(page):
        name = tag[1:].split(None, 1)[0].lower()
        attrs = parse_attrs(tag)
        if name == "link":
            if "pdf" in attrs.get("type", "").lower():
                add(attrs.get("href"))
        else:
            src = attrs.get("src") or attrs.get("data") or ""
            if re.search(r"\.pdf\b|/download/|/pdf/|pdf\?", src, re.I):
                add(src)

    # 3) "PDF", "Tam Metin", "İndir" gibi bağlantılar (puanlanarak)
    base_site = site_key(base_url)
    scored = []
    for order, m in enumerate(_A_RE.finditer(page)):
        attrs = parse_attrs("<a " + m.group(1) + ">")
        href = attrs.get("href", "")
        if not href or href.startswith(("#", "javascript:", "mailto:")):
            continue
        text = re.sub(r"\s+", " ", html.unescape(_TAG_STRIP.sub(" ", m.group(2)))).strip()
        hints = " ".join(attrs.get(k, "") for k in ("class", "title", "aria-label", "type"))
        full = urljoin(base_url, href)
        path = urlparse(full).path.lower()
        if _JUNK.search(unquote(path) + " " + text):
            continue
        score = 0
        if path.endswith(".pdf"):
            score += 3
        if "pdf" in hints.lower():
            score += 2
        if _PDF_TEXT.search(text) or _PDF_TEXT.search(hints):
            score += 2
        if re.search(r"/download|/bitstream|/pdf\b|/files/|/galley|/article-file/", path):
            score += 1
        if site_key(full) != base_site:
            score -= 1
        if score >= 3 and len(text) <= 120:
            scored.append((-score, order, full))
    for _, _, url in sorted(scored)[:3]:
        add(url)

    return candidates[:MAX_CANDIDATES]


_DSPACE7_RE = re.compile(
    r"^(https?://[^/]+(?:/[^?#]*?)?)/(?:items|entities/[\w-]+)/"
    r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})(?:[/?#]|$)",
    re.I,
)


def dspace7_item(url: str):
    """DSpace 7 öğe sayfası ise (sitenin kökü, öğe kimliği) döndürür."""
    m = _DSPACE7_RE.match(url or "")
    return (m.group(1), m.group(2)) if m else None


# ════════════════════════════════════════════════════════════════════════════
#  4) İNDİRME MOTORU (ayrı iş parçacığında çalışır)
# ════════════════════════════════════════════════════════════════════════════

class Cancelled(Exception):
    """Kullanıcı 'Durdur'a bastı."""


class DownloadError(Exception):
    """Kullanıcıya gösterilecek, açıklaması hazır indirme hatası."""


class NotPdf(Exception):
    """Aday link PDF yerine başka bir şey döndürdü."""


def make_session() -> requests.Session:
    session = requests.Session()
    session.headers.update(HEADERS)
    retry = Retry(
        total=2, connect=1, read=1, backoff_factor=1.0,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=frozenset({"GET", "HEAD"}),
        raise_on_status=False, respect_retry_after_header=False,
    )
    adapter = HTTPAdapter(max_retries=retry)
    session.mount("http://", adapter)
    session.mount("https://", adapter)
    return session


def is_cloudflare(resp) -> bool:
    headers = resp.headers if resp is not None else {}
    return ("cf-ray" in headers or "cf-mitigated" in headers
            or headers.get("Server", "").lower() == "cloudflare")


def describe_status(code: int, resp=None) -> str:
    if code in (403, 429, 503) and resp is not None and is_cloudflare(resp):
        return f"HTTP {code} – site bot korumasıyla (Cloudflare) otomatik indirmeyi engelliyor"
    tips = {
        401: "giriş ya da abonelik gerekiyor",
        403: "erişim engellendi (site otomatik indirmeye izin vermiyor ya da abonelik gerekiyor)",
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
        return describe_status(exc.response.status_code, exc.response)
    if isinstance(exc, exc_mod.SSLError):
        return "Güvenli bağlantı (SSL) kurulamadı"
    if isinstance(exc, exc_mod.Timeout):
        return "Zaman aşımı – sunucu yanıt vermedi"
    if isinstance(exc, exc_mod.TooManyRedirects):
        return "Çok fazla yönlendirme"
    if isinstance(exc, exc_mod.ChunkedEncodingError):
        return "Bağlantı indirme sırasında koptu"
    if isinstance(exc, exc_mod.RetryError):
        return "Sunucu tekrar tekrar hata verdi"
    if isinstance(exc, exc_mod.ConnectionError):
        return "Bağlantı kurulamadı – site kapalı olabilir ya da adres hatalı"
    if isinstance(exc, (exc_mod.InvalidURL, exc_mod.MissingSchema, exc_mod.InvalidSchema)):
        return "Geçersiz link"
    if isinstance(exc, OSError):
        return f"Dosya kaydedilemedi: {exc.strerror or exc}"
    return f"{type(exc).__name__}: {exc}"


STATUS_LABELS = {
    "ok": "İndirildi",
    "dup": "Zaten vardı",
    "html": "Web sayfası kaydedildi",
    "nopdf": "PDF bulunamadı",
    "error": "Hata",
}
FAILED_STATUSES = ("html", "nopdf", "error")


REPORT_GLOB = "indirme_raporu_*.csv"


def load_previous_downloads(folder: Path) -> dict:
    """Klasördeki eski indirme raporlarından, dosyası hâlâ duran linkleri okur.
    Dönüş: {link anahtarı: dosya adı}"""
    done = {}
    try:
        reports = sorted(folder.glob(REPORT_GLOB))
    except OSError:
        return done
    for report in reports:
        try:
            with open(report, encoding="utf-8-sig", newline="") as fh:
                rows = list(csv.reader(fh, delimiter=";"))
        except (OSError, csv.Error, UnicodeDecodeError):
            continue
        for row in rows[1:]:
            if len(row) < 4 or not row[1].startswith("http"):
                continue
            if row[2] in (STATUS_LABELS["ok"], STATUS_LABELS["dup"]) and row[3]:
                if (folder / row[3]).is_file():
                    done[_dedupe_key(row[1])] = row[3]
    return done


def file_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for block in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


class DownloadWorker(threading.Thread):
    """Linkleri sırayla indirir; arayüze yalnızca kuyruk üzerinden mesaj yollar.

    (Tkinter thread-safe olmadığı için bu sınıf arayüz nesnelerine hiç dokunmaz.)
    Mesajlar:
        ("log", seviye, metin)
        ("overall", tamamlanan, toplam)
        ("file", dosya_adı, inen_bayt, toplam_bayt | None)
        ("done", sayaçlar, durduruldu_mu, rapor_yolu | None, başarısız_linkler)
    """

    def __init__(self, links, folder, options, events, cancel_event):
        super().__init__(daemon=True)
        self.links = list(links)
        self.folder = Path(folder)
        self.options = options
        self.email = (options.get("email") or "").strip()
        self.events = events
        self.cancel = cancel_event
        self._hash_cache = {}   # yol → (boyut, değişme zamanı, sha256)
        self._tried = set()     # aynı link içinde tekrar denenen adresler

    # --- arayüze mesaj ---------------------------------------------------------
    def emit(self, *message):
        self.events.put(message)

    def log(self, level, text):
        self.emit("log", level, text)

    def check_cancel(self):
        if self.cancel.is_set():
            raise Cancelled()

    # --- ana döngü -------------------------------------------------------------
    def run(self):
        total = len(self.links)
        counts = {key: 0 for key in STATUS_LABELS}
        results, failed = [], []
        stopped = False
        session = make_session()
        previous = {}
        if self.options.get("skip_existing", True):
            previous = load_previous_downloads(self.folder)
            if previous:
                self.log("muted", f"Klasörde daha önce indirilmiş {len(previous)} kaynak var; "
                                  "bunlar tekrar indirilmeyecek.")
        try:
            for i, url in enumerate(self.links, start=1):
                if self.cancel.is_set():
                    stopped = True
                    break
                self.emit("overall", i - 1, total)
                self.log("info", f"[{i}/{total}] {url}")
                self._tried = set()
                key = _dedupe_key(url)
                try:
                    if key in previous:
                        status, filename = "dup", previous[key]
                        note = f"daha önce indirilmiş: {filename}"
                    else:
                        status, filename, note = self._download_one(session, url, i)
                    if status in ("ok", "dup") and filename:
                        previous[key] = filename
                except Cancelled:
                    stopped = True
                    results.append((i, url, "Durduruldu", "", "Kullanıcı durdurdu"))
                    break
                except Exception as exc:  # her türlü hatayı loga yaz, sonrakine geç
                    status, filename, note = "error", "", describe_error(exc)

                counts[status] += 1
                results.append((i, url, STATUS_LABELS[status], filename, note))
                if status in FAILED_STATUSES:
                    failed.append(url)
                if status == "ok":
                    self.log("success", f"   ✓ Kaydedildi: {filename}  ({note})")
                elif status == "dup":
                    self.log("muted", f"   ≡ Zaten var, tekrar indirilmedi: {filename}")
                elif status == "html":
                    self.log("warn", f"   ⚠ {note} → {filename}")
                elif status == "nopdf":
                    self.log("warn", f"   ⚠ PDF bulunamadı: {note}")
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
            self.emit("done", counts, stopped, report, failed)

    # --- tek link ---------------------------------------------------------------
    def _download_one(self, session, url, index):
        find_pdf = self.options.get("find_pdf", True)
        doi = doi_from_url(url)
        meta = {}
        problem = None
        final_url = url
        page_raw = page_resp = None
        reached_page = False

        try:
            resp = session.get(url, stream=True, allow_redirects=True, timeout=TIMEOUT)
        except requests.RequestException as exc:
            problem = describe_error(exc)
        else:
            with resp:
                final_url = resp.url
                if resp.history:
                    self.log("muted", f"   ↪ Yönlendirildi → {final_url}")
                if not resp.ok:
                    problem = describe_status(resp.status_code, resp)
                    if resp.status_code == 404 and is_doi_host(final_url):
                        problem = "HTTP 404 – DOI çözülemedi (DOI kayıtlı değil ya da hatalı yazılmış)"
                elif not is_html(content_type(resp)):
                    return self._save_stream(resp, url, index)
                else:
                    raw = self._read_limited(resp)
                    page = decode_html(raw, resp)
                    meta = parse_citation_meta(page)
                    if looks_like_bot_check(page, final_url):
                        problem = "site bot doğrulaması (\"robot değilim\") istedi"
                    else:
                        reached_page = True
                        page_raw, page_resp = raw, resp
                        if find_pdf:
                            cands = find_pdf_candidates(page, final_url, meta)
                            if cands:
                                self.log("muted", f"   · Sayfada {len(cands)} olası PDF bağlantısı bulundu.")
                            result = self._try_candidates(session, cands, final_url, url, index, meta)
                            if result:
                                return result
                            problem = "sayfada indirilebilir PDF bulunamadı"
                        else:
                            problem = "link bir web sayfasına açılıyor"

        if find_pdf:
            item = dspace7_item(final_url)
            doi = doi or meta_doi(meta)
            if problem and (item or (doi and self.email)):
                self.log("muted", f"   · {problem}; başka kaynaklara bakılıyor…")

            # DSpace 7 kurum arşivi (hdl.handle.net linkleri çoğu zaman buraya açılır)
            if item:
                result = self._try_dspace7(session, item, final_url, url, index, meta)
                if result:
                    return result

            # Unpaywall: DOI'nin yasal açık erişim kopyaları
            if doi and self.email:
                result = self._try_unpaywall(session, doi, url, index, meta)
                if result:
                    return result

        if reached_page and self.options.get("save_html"):
            filename = make_filename(page_resp, url, index, meta=meta, force_ext=".html")
            path = self._write_bytes(page_raw, filename)
            return "html", path.name, "PDF bulunamadı, web sayfası kaydedildi"
        if reached_page:
            return "nopdf", "", problem or "PDF bulunamadı"
        return "error", "", problem or "Bilinmeyen hata"

    # --- PDF adaylarını deneme ------------------------------------------------
    def _try_candidates(self, session, candidates, referer, url, index, meta, note="", depth=0):
        for cand in candidates:
            self.check_cancel()
            if cand in self._tried:
                continue
            self._tried.add(cand)
            self.log("muted", f"   → Deneniyor: {shorten(cand, 96)}")
            headers = {"Referer": referer} if referer else None
            try:
                resp = session.get(cand, stream=True, allow_redirects=True,
                                   timeout=TIMEOUT, headers=headers)
            except requests.RequestException as exc:
                self.log("muted", f"     olmadı: {describe_error(exc)}")
                continue
            with resp:
                if not resp.ok:
                    self.log("muted", f"     olmadı: {describe_status(resp.status_code, resp)}")
                    continue
                if is_html(content_type(resp)):
                    if depth == 0:
                        raw = self._read_limited(resp)
                        page = decode_html(raw, resp)
                        sub_meta = parse_citation_meta(page)
                        if looks_like_bot_check(page, resp.url):
                            self.log("muted", "     olmadı: site bot doğrulaması istedi")
                            continue
                        sub = find_pdf_candidates(page, resp.url, sub_meta)[:2]
                        result = self._try_candidates(session, sub, resp.url, url, index,
                                                      meta or sub_meta, note, depth=1)
                        if result:
                            return result
                    self.log("muted", "     olmadı: PDF yerine web sayfası geldi (giriş/abonelik gerekebilir)")
                    continue
                try:
                    return self._save_stream(resp, url, index, meta=meta, require_pdf=True,
                                             note=note or "makale sayfasındaki PDF bağlantısından")
                except NotPdf:
                    self.log("muted", "     olmadı: gelen dosya PDF değil")
        return None

    def _try_dspace7(self, session, item, page_url, url, index, meta):
        root, uuid = item
        api = f"{root}/server/api/core/items/{uuid}/bundles"
        self.log("muted", "   → DSpace kurum arşivinin dosya listesi soruluyor…")
        if not meta.get("citation_title"):
            meta = self._dspace7_meta(session, root, uuid) or meta
        try:
            r = session.get(api, timeout=API_TIMEOUT, headers={"Accept": "application/json"})
            r.raise_for_status()
            bundles = r.json().get("_embedded", {}).get("bundles", [])
            files = []
            for bundle in bundles:
                if bundle.get("name") != "ORIGINAL":
                    continue
                href = bundle.get("_links", {}).get("bitstreams", {}).get("href")
                if not href:
                    continue
                r2 = session.get(href, timeout=API_TIMEOUT, headers={"Accept": "application/json"})
                r2.raise_for_status()
                files += r2.json().get("_embedded", {}).get("bitstreams", [])
        except (requests.RequestException, ValueError, AttributeError) as exc:
            self.log("muted", f"     olmadı: {describe_error(exc)}")
            return None
        files.sort(key=lambda b: not str(b.get("name", "")).lower().endswith(".pdf"))
        links = [b.get("_links", {}).get("content", {}).get("href") for b in files]
        links = [link for link in links if link][:3]
        if not links:
            self.log("muted", "     olmadı: arşivde herkese açık dosya yok")
            return None
        return self._try_candidates(session, links, page_url, url, index, meta,
                                    note="kurum arşivinden (DSpace)", depth=1)

    @staticmethod
    def _dspace7_meta(session, root, uuid):
        """Dosya adı için başlık, yazar ve yılı arşivin kendisinden alır."""
        try:
            r = session.get(f"{root}/server/api/core/items/{uuid}", timeout=API_TIMEOUT,
                            headers={"Accept": "application/json"})
            r.raise_for_status()
            md = r.json().get("metadata", {})
        except (requests.RequestException, ValueError, AttributeError):
            return None

        def first(*keys):
            for key in keys:
                values = md.get(key) or []
                if values and values[0].get("value"):
                    return values[0]["value"]
            return ""

        title = first("dc.title")
        if not title:
            return None
        return {
            "citation_title": title,
            "citation_author": first("dc.contributor.author", "dc.creator"),
            "citation_publication_date": first("dc.date.issued", "dc.date"),
        }

    def _try_unpaywall(self, session, doi, url, index, meta):
        self.log("muted", f"   → Açık erişim kopyası aranıyor (Unpaywall, DOI {doi})…")
        try:
            r = session.get(UNPAYWALL_API + quote(doi, safe="/:;()._-"),
                            params={"email": self.email}, timeout=API_TIMEOUT,
                            headers={"Accept": "application/json"})
            if r.status_code == 404:
                self.log("muted", "     Unpaywall bu DOI'yi tanımıyor.")
                return None
            if r.status_code == 422:
                self.log("warn", "   ⚠ Unpaywall e-posta adresini kabul etmedi; ayarlardaki adresi kontrol edin.")
                return None
            r.raise_for_status()
            data = r.json()
        except (requests.RequestException, ValueError) as exc:
            self.log("muted", f"     Unpaywall'a ulaşılamadı: {describe_error(exc)}")
            return None

        if not data.get("is_oa"):
            self.log("muted", "     Bu yayının bilinen açık erişim kopyası yok.")
            return None

        if not meta.get("citation_title") and data.get("title"):
            authors = data.get("z_authors") or [{}]
            meta = {
                "citation_title": data["title"],
                "citation_author": (authors[0] or {}).get("family", ""),
                "citation_publication_date": str(data.get("year") or ""),
            }

        locations = [data.get("best_oa_location")] + list(data.get("oa_locations") or [])
        pdfs, landings = [], []
        for loc in locations:
            if not loc:
                continue
            if loc.get("url_for_pdf") and loc["url_for_pdf"] not in pdfs:
                pdfs.append(loc["url_for_pdf"])
            landing = loc.get("url_for_landing_page") or loc.get("url")
            if landing and landing not in landings and not is_doi_host(landing):
                landings.append(landing)
        candidates = (pdfs + [u for u in landings if u not in pdfs])[:5]
        self.log("muted", f"     {len(candidates)} açık erişim konumu bulundu.")
        return self._try_candidates(session, candidates, None, url, index, meta,
                                    note="açık erişim kopyası (Unpaywall)")

    # --- dosyaya yazma ---------------------------------------------------------
    def _save_stream(self, resp, url, index, meta=None, require_pdf=False, note=""):
        def validate(first):
            if require_pdf and b"%PDF-" not in first[:1024]:
                raise NotPdf()

        path, size, digest = self._stream_to_file(
            resp, lambda first: make_filename(resp, url, index, meta=meta, first_bytes=first),
            validate)
        duplicate = self._find_duplicate(path, size, digest)
        if duplicate:
            path.unlink(missing_ok=True)
            return "dup", duplicate.name, f"aynı dosya klasörde zaten var: {duplicate.name}"
        return "ok", path.name, f"{format_bytes(size)}, {note}" if note else format_bytes(size)

    def _stream_to_file(self, resp, name_for_first_chunk, validate=None):
        """stream=True yanıtı parça parça .part dosyasına yazar, bitince adlandırır."""
        encoded = resp.headers.get("Content-Encoding", "").lower() not in ("", "identity")
        try:
            total = None if encoded else int(resp.headers.get("Content-Length", ""))
        except ValueError:
            total = None

        chunks = resp.iter_content(chunk_size=CHUNK_SIZE)
        first = b""
        for chunk in chunks:
            self.check_cancel()
            if chunk:
                first = chunk
                break
        if not first:
            raise DownloadError("Sunucu boş yanıt döndürdü")
        if validate:
            validate(first)

        # Dosya adını ilk parçaya bakarak seç (ör. '%PDF' imzası → .pdf)
        path = unique_path(self.folder, name_for_first_chunk(first))
        tmp = path.with_name(path.name + ".part")
        received = len(first)
        digest = hashlib.sha256(first)
        self.emit("file", path.name, received, total)
        last_update = time.monotonic()
        try:
            with open(tmp, "wb") as fh:
                fh.write(first)
                for chunk in chunks:
                    self.check_cancel()
                    if not chunk:
                        continue
                    fh.write(chunk)
                    digest.update(chunk)
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
        return path, received, digest.hexdigest()

    def _find_duplicate(self, new_path: Path, size: int, digest: str):
        """Klasörde aynı içerikte başka bir dosya varsa onu döndürür."""
        try:
            entries = list(self.folder.iterdir())
        except OSError:
            return None
        for other in entries:
            if other == new_path or other.suffix in (".part", ".csv", ".html"):
                continue
            try:
                st = other.stat()
                if not other.is_file() or st.st_size != size:
                    continue
                cached = self._hash_cache.get(other)
                if not cached or cached[:2] != (st.st_size, st.st_mtime):
                    cached = (st.st_size, st.st_mtime, file_sha256(other))
                    self._hash_cache[other] = cached
                if cached[2] == digest:
                    return other
            except OSError:
                continue
        return None

    def _read_limited(self, resp) -> bytes:
        buf = bytearray()
        for chunk in resp.iter_content(chunk_size=CHUNK_SIZE):
            self.check_cancel()
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
#  5) AYARLAR (klasör, e-posta ve seçenekler bir sonraki açılışta hatırlanır)
# ════════════════════════════════════════════════════════════════════════════

def settings_path() -> Path:
    base = os.environ.get("APPDATA") or str(Path.home())
    return Path(base) / "AkademikIndirici" / "ayarlar.json"


def load_settings() -> dict:
    try:
        with open(settings_path(), encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def save_settings(data: dict):
    try:
        path = settings_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False, indent=2)
    except OSError:
        pass


# ════════════════════════════════════════════════════════════════════════════
#  6) ARAYÜZ (CustomTkinter)
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
        self.geometry("1180x780")
        self.minsize(980, 680)

        self.events = queue.Queue()
        self.cancel_event = threading.Event()
        self.worker = None
        self.failed_links = []
        self._file_bar_spinning = False

        settings = load_settings()
        self.folder_var = ctk.StringVar(value=settings.get("folder") or str(default_download_dir()))
        self.email_var = ctk.StringVar(value=settings.get("email", ""))
        self.opt_doi = ctk.BooleanVar(value=settings.get("doi", True))
        self.opt_find_pdf = ctk.BooleanVar(value=settings.get("find_pdf", True))
        self.opt_save_html = ctk.BooleanVar(value=settings.get("save_html", False))
        self.opt_skip_existing = ctk.BooleanVar(value=settings.get("skip_existing", True))

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
            text="Kaynakçayı yapıştırın ya da Word / TXT / PDF dosyası ekleyin; linkler ayıklanır, dosyalar klasörünüze iner.",
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
            text="Metni yapıştırın ya da Word / TXT / PDF dosyası ekleyin: "
                 "http/https linkleri ve DOI'ler otomatik bulunur.",
        ).grid(row=1, column=0, sticky="ew", padx=18)

        self.input_box = ctk.CTkTextbox(card, wrap="word", font=ctk.CTkFont(size=13),
                                        border_width=1, corner_radius=10)
        self.input_box.grid(row=2, column=0, sticky="nsew", padx=18, pady=(8, 8))
        self.input_box.bind("<Control-a>", self._select_all_input)
        self.input_box.bind("<Control-A>", self._select_all_input)

        bar = ctk.CTkFrame(card, fg_color="transparent")
        bar.grid(row=3, column=0, sticky="ew", padx=18)
        bar.grid_columnconfigure(3, weight=1)
        self.file_btn = ctk.CTkButton(bar, text="Dosyadan Ekle…", width=124,
                                      command=self._add_files)
        self.file_btn.grid(row=0, column=0, padx=(0, 8))
        self.paste_btn = ctk.CTkButton(bar, text="Yapıştır", width=84,
                                       fg_color="transparent", border_width=1,
                                       text_color=TEXT, command=self._paste)
        self.paste_btn.grid(row=0, column=1, padx=(0, 8))
        self.clear_btn = ctk.CTkButton(bar, text="Temizle", width=76,
                                       fg_color="transparent", border_width=1,
                                       text_color=TEXT, command=self._clear_input)
        self.clear_btn.grid(row=0, column=2)
        self.count_label = ctk.CTkLabel(bar, text="", font=self.font_small, text_color=MUTED)
        self.count_label.grid(row=0, column=3, sticky="e", padx=10)
        self.extract_btn = ctk.CTkButton(bar, text="Linkleri Ayıkla", width=124,
                                         fg_color="transparent", border_width=1,
                                         text_color=TEXT, command=self._on_extract)
        self.extract_btn.grid(row=0, column=4, sticky="e")

        # 2 — klasör
        self._section(card, "2   İndirme klasörü", row=4, pady=(18, 6))
        folder_row = ctk.CTkFrame(card, fg_color="transparent")
        folder_row.grid(row=5, column=0, sticky="ew", padx=18)
        folder_row.grid_columnconfigure(0, weight=1)
        self.folder_entry = ctk.CTkEntry(folder_row, textvariable=self.folder_var, height=34)
        self.folder_entry.grid(row=0, column=0, sticky="ew", padx=(0, 8))
        self.folder_btn = ctk.CTkButton(folder_row, text="İndirme Klasörü Seç", width=160,
                                        height=34, command=self._choose_folder)
        self.folder_btn.grid(row=0, column=1)

        # seçenekler
        self._section(card, "Seçenekler", row=6, pady=(18, 4))
        opts = ctk.CTkFrame(card, fg_color="transparent")
        opts.grid(row=7, column=0, sticky="ew", padx=18)
        self.option_boxes = []
        for i, (text, var) in enumerate([
            ("Çıplak DOI'leri de yakala  (doi:10.xxxx/…  →  https://doi.org/…)", self.opt_doi),
            ("Link bir makale sayfasına açılırsa PDF'i bul (sayfa, kurum arşivi, açık erişim)", self.opt_find_pdf),
            ("Klasörde zaten olan kaynakları tekrar indirme", self.opt_skip_existing),
            ("PDF bulunamazsa web sayfasını .html olarak kaydet", self.opt_save_html),
        ]):
            box = ctk.CTkCheckBox(opts, text=text, variable=var, font=self.font_small,
                                  checkbox_width=20, checkbox_height=20)
            box.grid(row=i, column=0, sticky="w", pady=3)
            self.option_boxes.append(box)

        email_row = ctk.CTkFrame(card, fg_color="transparent")
        email_row.grid(row=8, column=0, sticky="ew", padx=18, pady=(8, 0))
        email_row.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(email_row, text="E-posta:", font=self.font_small).grid(row=0, column=0, padx=(0, 8))
        self.email_entry = ctk.CTkEntry(email_row, height=30,
                                        placeholder_text="ad.soyad@universite.edu.tr")
        self.email_entry.grid(row=0, column=1, sticky="ew")
        if self.email_var.get():
            self.email_entry.insert(0, self.email_var.get())
        ctk.CTkLabel(
            card, font=ctk.CTkFont(size=11), text_color=MUTED, anchor="w", justify="left",
            wraplength=540,
            text="İsteğe bağlı. Girerseniz DOI'lerin yasal açık erişim kopyaları Unpaywall'da aranır; "
                 "adres yalnızca Unpaywall'a gönderilir (hizmetin kuralı).",
        ).grid(row=9, column=0, sticky="ew", padx=18, pady=(4, 16))

    def _build_right_panel(self):
        card = ctk.CTkFrame(self, corner_radius=14)
        card.grid(row=1, column=1, sticky="nsew", padx=(10, 22), pady=(4, 22))
        card.grid_columnconfigure(0, weight=1)
        card.grid_rowconfigure(9, weight=1)

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

        self.failed_btn = ctk.CTkButton(
            card, text="İnmeyenleri Tarayıcıda Aç", height=32, fg_color="transparent",
            border_width=1, text_color=TEXT, state="disabled", command=self._open_failed)
        self.failed_btn.grid(row=7, column=0, sticky="ew", padx=18, pady=(4, 0))

        # log
        head3 = ctk.CTkFrame(card, fg_color="transparent")
        head3.grid(row=8, column=0, sticky="ew", padx=18, pady=(12, 0))
        head3.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(head3, text="İşlem Geçmişi", font=self.font_section).grid(row=0, column=0, sticky="w")
        ctk.CTkButton(head3, text="Logu Temizle", width=96, height=26, fg_color="transparent",
                      border_width=1, text_color=TEXT, command=self._clear_log).grid(row=0, column=1, sticky="e")
        self.log_box = ctk.CTkTextbox(card, wrap="word", font=self.font_log, border_width=1,
                                      corner_radius=10, state="disabled")
        self.log_box.grid(row=9, column=0, sticky="nsew", padx=18, pady=(6, 18))
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

    def _save_settings(self):
        save_settings({
            "folder": self.folder_var.get().strip(),
            "email": self.email_entry.get().strip(),
            "doi": self.opt_doi.get(),
            "find_pdf": self.opt_find_pdf.get(),
            "save_html": self.opt_save_html.get(),
            "skip_existing": self.opt_skip_existing.get(),
        })

    def _set_running(self, running: bool):
        idle = "disabled" if running else "normal"
        self.start_btn.configure(state="disabled" if running else "normal",
                                 text="İndiriliyor…" if running else "İndirmeyi Başlat")
        self.stop_btn.configure(state="normal" if running else "disabled")
        for widget in (self.extract_btn, self.folder_btn, self.folder_entry, self.email_entry,
                       self.file_btn, self.paste_btn, self.clear_btn, *self.option_boxes):
            widget.configure(state=idle)
        if running:
            self.failed_btn.configure(state="disabled", text="İnmeyenleri Tarayıcıda Aç")

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

    def _add_files(self):
        paths = filedialog.askopenfilenames(parent=self, title="Kaynak dosyası seçin",
                                            filetypes=SUPPORTED_FILES)
        for path in paths:
            name = os.path.basename(path)
            try:
                text = read_text_from_file(path)
            except Exception as exc:
                reason = str(exc) if isinstance(exc, ValueError) else f"{type(exc).__name__}: {exc}"
                self._log("error", f"{name} okunamadı: {reason}")
                continue
            found = len(extract_links(text, include_doi=self.opt_doi.get()))
            current = self.input_box.get("1.0", "end-1c")
            prefix = "\n\n" if current.strip() else ""
            self.input_box.insert("end", f"{prefix}──── {name} ────\n{text.strip()}\n")
            self.input_box.see("end")
            self._log("success" if found else "warn", f"{name} eklendi: {found} link bulundu.")
        if paths:
            self._extract_links()

    def _clear_input(self):
        self.input_box.delete("1.0", "end")
        self.count_label.configure(text="")

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
            self._save_settings()

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

    def _open_failed(self):
        links = list(self.failed_links)
        if not links:
            return
        if len(links) > 10 and not messagebox.askyesno(
                APP_NAME, f"Tarayıcıda {len(links)} sekme açılacak. Devam edilsin mi?", parent=self):
            return
        self._log("info", f"{len(links)} link tarayıcıda açılıyor…")
        for i, link in enumerate(links):
            self.after(i * 400, lambda u=link: webbrowser.open_new_tab(u))

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
        email = self.email_entry.get().strip()
        if email and not EMAIL_RE.match(email):
            messagebox.showwarning(APP_NAME, "E-posta adresi geçerli görünmüyor.\n"
                                             "Düzeltin ya da kutuyu boş bırakın.", parent=self)
            return
        folder = Path(folder_text).expanduser()
        try:
            folder.mkdir(parents=True, exist_ok=True)
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"Klasör oluşturulamadı:\n{folder}\n\n{exc}", parent=self)
            return

        self._save_settings()
        self.cancel_event = threading.Event()
        self.failed_links = []
        options = {"find_pdf": self.opt_find_pdf.get(), "save_html": self.opt_save_html.get(),
                   "skip_existing": self.opt_skip_existing.get(), "email": email}
        self._set_running(True)
        self.overall_bar.set(0)
        self.overall_label.configure(text=f"0 / {len(links)}")
        self._reset_file_progress()
        self._set_status("İndiriliyor…")
        self._log("info", f"İndirme başladı: {len(links)} link → {folder}")
        if self.opt_find_pdf.get() and not email:
            self._log("muted", "İpucu: Seçeneklere e-posta girerseniz açık erişim kopyaları da aranır.")
        self.worker = DownloadWorker(links, folder, options, self.events, self.cancel_event)
        self.worker.start()

    def _stop(self):
        if self.worker and self.worker.is_alive():
            self.cancel_event.set()
            self.stop_btn.configure(state="disabled")
            self._set_status("Durduruluyor…", "warn")
            self._log("warn", "Durdurma isteği alındı; yarım kalan dosya silinecek.")

    def _finish(self, counts, stopped, report, failed):
        self._set_running(False)
        self._reset_file_progress()
        self.failed_links = list(failed)
        parts = [f"{counts['ok']} dosya indirildi"]
        if counts["dup"]:
            parts.append(f"{counts['dup']} zaten vardı")
        if counts["html"]:
            parts.append(f"{counts['html']} web sayfası kaydedildi")
        if counts["nopdf"]:
            parts.append(f"{counts['nopdf']} PDF bulunamadı")
        if counts["error"]:
            parts.append(f"{counts['error']} hata")
        summary = " · ".join(parts)
        title = "Durduruldu" if stopped else "Tamamlandı"
        level = "warn" if (stopped or self.failed_links) else "success"
        if not stopped:
            self.overall_bar.set(1)
        self._set_status(f"{title}: {summary}", level)
        self._log(level, f"{title}: {summary}")
        if report:
            self._log("muted", f"Rapor: {report}")
        if self.failed_links:
            self.failed_btn.configure(state="normal",
                                      text=f"İnmeyen {len(self.failed_links)} Linki Tarayıcıda Aç")
            self._log("muted", "İnmeyenleri kurum girişinizle indirmek için "
                               "'Tarayıcıda Aç' düğmesini kullanabilirsiniz.")

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
        self._save_settings()
        self.destroy()


def main():
    ctk.set_appearance_mode("system")
    ctk.set_default_color_theme("blue")
    app = App()
    app.mainloop()


if __name__ == "__main__":
    main()
