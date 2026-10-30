# -*- coding: utf-8 -*-
"""
Akademik Kaynak İndirici  v2.0
==============================
Üç sekmeli masaüstü uygulaması:

İNDİR
- Karışık metinlerden, kaynakçalardan ve Word/TXT/PDF dosyalarından linkleri ve DOI'leri
  ayıklar; requests ile parça parça indirir, DOI yönlendirmelerini izler.
- Makale sayfasında PDF'i arar (Google Scholar etiketi, sayfadaki PDF bağlantıları, OJS,
  DSpace kurum arşivleri, Unpaywall açık erişim kopyaları); tahminle bulunan PDF'in
  başlığını doğrular. Daha önce indirdiklerini tekrar indirmez.

KÜTÜPHANEM
- İnen her PDF künyesiyle (Crossref / sayfa etiketleri) kataloğa girer ve tek kütüphane
  klasöründe 'Soyad (Yıl) - Başlık.pdf' adıyla durur. PDF'i olmayanlar ayrıca işaretlenir.
- Arama (PDF içinde de), etiket ve durum filtreleri, künye düzenleme, alıntı kartları
  (atıfla kopyalama), APA 7 kaynakça (Türkçe/İngilizce; panoya ya da Word'e),
  BibTeX/RIS dışa aktarma (Jenni, Zotero), kurum erişimi (VETİS) yönlendirmesi,
  İndirilenler klasörünü izleyip indirilen PDF'i doğru kaynağa bağlama.

TARAMA
- Haftada bir, düzenlenebilir anahtar kelime gruplarıyla DergiPark (OAI-PMH), Crossref, OpenAlex, ERIC ve YÖK Tez'i
  tarar; bulunanları 'yeni' işaretiyle kütüphaneye ekler, açık erişimli PDF'leri indirir
  ve tarayıcıda açılan bir rapor yazar. Windows görev zamanlayıcısıyla uygulama
  kapalıyken de çalışır (exe --tara).

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
import shutil
import sqlite3
import subprocess
import sys
import threading
import time
import unicodedata
import webbrowser
import zipfile
import xml.etree.ElementTree as ET
from xml.sax.saxutils import escape as xml_escape
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qs, quote, unquote, urljoin, urlparse

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
APP_VERSION = "2.42"
# Bu kodu çalıştırabilecek en eski program (exe) sürümü. Yeni bir kütüphane eklenince yükseltilir;
# eski exe bu durumda kendi sürümüyle açılır ve kullanıcıya exe'yi bir kez güncellemesini söyler.
MIN_LAUNCHER = "2.6"

CHUNK_SIZE = 64 * 1024              # parça parça indirme boyutu (64 KB)
HTML_READ_LIMIT = 5 * 1024 * 1024   # PDF bağlantısı aramak için okunacak en fazla HTML
TIMEOUT = (10, 40)                  # (bağlanma, okuma) saniye
API_TIMEOUT = (10, 25)
PAUSE_BETWEEN = 0.5                 # sunucuları yormamak için dosyalar arası bekleme
MAX_CANDIDATES = 4                  # bir sayfada denenecek en fazla PDF adayı

UNPAYWALL_API = "https://api.unpaywall.org/v2/"
OPENALEX_API = "https://api.openalex.org/works"
S2_API = "https://api.semanticscholar.org/graph/v1/paper/"
CORE_API = "https://api.core.ac.uk/v3/search/works"
CORE_KEY_PAGE = "https://core.ac.uk/services/api"
OPENALEX_KEY_PAGE = "https://openalex.org/settings/api"
ERIC_API = "https://api.ies.ed.gov/eric/"
GOOGLE_BOOKS_API = "https://www.googleapis.com/books/v1/volumes"
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
    # kütüphane künyesi için
    "citation_journal_title", "citation_volume", "citation_issue", "citation_firstpage",
    "citation_lastpage", "citation_publisher", "citation_language", "citation_book_title",
    "citation_inbook_title", "citation_conference_title", "citation_dissertation_institution",
    "citation_technical_report_institution", "citation_isbn", "dc.publisher", "dc.language",
    "citation_keywords", "keywords", "dc.subject", "citation_issn", "prism.issn", "prism.eissn",
}


def split_keywords(text) -> list:
    """'a; b, c · d' → ['a', 'b', 'c', 'd'] (tekrarsız, makul uzunlukta)"""
    out, seen = [], set()
    for part in re.split(r"[;,·•|\n]+", str(text or "")):
        word = re.sub(r"\s+", " ", html.unescape(part)).strip(" .:-–—\t")
        key = word.casefold()
        if 2 <= len(word) <= 70 and not re.search(r"@|https?://|\d{4}-\d{3}", word) and key not in seen:
            seen.add(key)
            out.append(word)
    return out


def join_keywords(words) -> str:
    return "; ".join(split_keywords("; ".join(words)))


_KW_LABEL_RE = re.compile(
    r"(?:Anahtar\s*(?:Kelime|Sözcük|Sozcuk)(?:ler)?|Key\s*-?\s*words?|Palabras\s+clave|"
    r"Mots[-\s]cl[ée]s|Schlüsselwörter|Ключов[іы]е?\s+слова)\s*[:：\-–—]?\s*", re.I)
_KW_STOP_RE = re.compile(
    r"\b(?:abstract|öz|özet|resumo|resumen|introduction|giriş|article\s+info|makale\s+bilgi|received|"
    r"geliş|jel|atıf|cite|doi|corresponding|correspondence|sorumlu|orcid|research\s+article|"
    r"araştırma\s+makalesi|copyright|original\s+paper|address|e-?mail|university|üniversitesi|"
    r"faculty|fakültesi|special\s+issue)\b", re.I)
_KW_FOOTNOTE_RE = re.compile(r"\s[A-Za-z]?\d{1,3}\b")        # ' 1 Ege Üniv…', ' S95 Konserv…'


def _keyword_chunk_to_list(chunk: str) -> list:
    chunk = re.sub(r"\s+", " ", chunk)
    stop = _KW_STOP_RE.search(chunk)
    if stop:
        chunk = chunk[:stop.start()]
    chunk = re.split(r"\.\s+(?=[A-ZÇĞİÖŞÜ])|\.$", chunk)[0]          # listeyi bitiren nokta
    foot = _KW_FOOTNOTE_RE.search(chunk)
    if foot:
        chunk = chunk[:foot.start()]
    if "?" in chunk:
        return []
    return [w for w in split_keywords(chunk) if len(w.split()) <= 7]


def extract_keywords_from_text(text: str) -> list:
    """PDF'in ilk sayfalarındaki 'Anahtar Kelimeler / Keywords' satır(lar)ını okur.
    Virgüllü/noktalı virgüllü listeleri ve alt alta yazılmış listeleri tanır."""
    words = []
    for m in _KW_LABEL_RE.finditer(text or ""):
        raw = text[m.end():m.end() + 400]
        first_line = raw.split("\n", 1)[0]
        if "," in first_line or ";" in first_line or "," in raw[:160] or ";" in raw[:160]:
            words.extend(_keyword_chunk_to_list(raw))
        else:
            # alt alta liste: kısa satırları sırayla topla
            for line in raw.split("\n"):
                line = line.strip()
                if not line:
                    if words:
                        break
                    continue
                if len(line.split()) > 6 or _KW_STOP_RE.search(line) or line.endswith((".", ":")) and len(words) > 1:
                    break
                cleaned = _KW_FOOTNOTE_RE.split(line)[0].strip(" .")
                if cleaned:
                    words.append(cleaned)
                if len(words) >= 12:
                    break
        if len(words) >= 20:
            break
    return split_keywords("; ".join(words))[:20]


def parse_attrs(tag: str) -> dict:
    attrs = {}
    for m in _ATTR_RE.finditer(tag):
        value = next(v for v in m.groups()[1:] if v is not None)
        attrs.setdefault(m.group(1).lower(), html.unescape(value).strip())
    return attrs


def parse_citation_meta(page: str) -> dict:
    """Google Scholar / Dublin Core <meta> etiketlerini okur (ilk değer geçerli).
    Tüm yazarlar ayrıca meta["_authors"] listesinde tutulur."""
    meta, authors, keywords, issns = {}, [], [], []
    for tag in _META_TAG_RE.findall(page):
        attrs = parse_attrs(tag)
        key = (attrs.get("name") or attrs.get("property") or "").lower()
        if key == "dc.identifier" and not normalize_doi(attrs.get("content")):
            continue  # yalnızca DOI olan dc.identifier işimize yarar
        if key == "citation_author" and attrs.get("content"):
            authors.append(attrs["content"])
        if key in ("citation_keywords", "dc.subject") and attrs.get("content"):
            keywords.extend(split_keywords(attrs["content"]))
        if key in ("citation_issn", "prism.issn", "prism.eissn") and attrs.get("content"):
            issns.append(attrs["content"])
        if key in _WANTED_META and attrs.get("content") and key not in meta:
            meta[key] = attrs["content"]
    if authors:
        meta["_authors"] = authors
    if keywords:
        meta["_keywords"] = keywords
    if issns:
        meta["_issn"] = issns
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
    r"doğrulama|dogrulama|güvenlik kontrol|robot musunuz|one more step|please wait|"
    r"client challenge|checking your browser|ddos protection|enable javascript and cookies",
    re.I,
)


def page_title(page: str) -> str:
    m = _TITLE_RE.search(page)
    return re.sub(r"\s+", " ", html.unescape(m.group(1))).strip() if m else ""


def looks_like_bot_check(page: str, final_url: str = "") -> bool:
    """Cloudflare vb. 'insan mısınız' doğrulama sayfası mı?"""
    markers = ("cf-challenge", "challenge-platform", "cf_chl_", "/_fs-ch-", "captcha-delivery",
               "px-captcha", "cf-browser-verification", "_incapsula_resource", "awswaf")
    if any(m in page for m in markers):
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


class WrongPdf(Exception):
    """İnen PDF'in başlığı makale sayfasındaki başlıkla uyuşmuyor (başka bir yayın)."""


class RateLimited(DownloadError):
    """Site 'çok fazla istek' (HTTP 429) dedi ve bir süre dinlendiriliyor."""


class HostThrottle:
    """Siteye nazik davranır: aynı siteye art arda istekler arasında en az belli bir süre bırakır,
    'çok fazla istek' (429) gelirse o siteyi istenen süre (Retry-After) ya da giderek artan sürelerle
    dinlendirir. Bütün iş parçacıkları (indirme, tarama, PDF arama) aynı sayacı paylaşır."""

    DEFAULT_GAP = 1.0
    GAPS = {"dergipark.org.tr": 3.0, "tez.yok.gov.tr": 1.5, "doi.org": 0.5, "api.crossref.org": 0.2,
            "api.unpaywall.org": 0.3, "api.openalex.org": 0.2, "scholar.google.com": 15.0,
            "api.semanticscholar.org": 1.5, "api.core.ac.uk": 2.0, "api.ies.ed.gov": 1.0,
            "127.0.0.1": 0.0, "localhost": 0.0}
    MAX_GAP = 20.0
    MAX_BLOCK = 60.0                 # bundan uzun dinlenme gerekiyorsa beklemeden RateLimited verilir

    def __init__(self):
        self.lock = threading.Lock()
        self.next_ok, self.cool_until, self.strikes, self.extra = {}, {}, {}, {}
        self.local = threading.local()

    @staticmethod
    def key(host) -> str:
        host = (host or "").lower()
        host = host[4:] if host.startswith("www.") else host
        for name in HostThrottle.GAPS:
            if host == name or host.endswith("." + name):
                return name
        return host

    def gap(self, key) -> float:
        return min(self.GAPS.get(key, self.DEFAULT_GAP) * self.extra.get(key, 1.0), self.MAX_GAP)

    def cooling(self, host) -> float:
        """Sitenin dinlenmesine kalan süre (sn)."""
        return max(0.0, self.cool_until.get(self.key(host), 0.0) - time.monotonic())

    def wait(self, host):
        key = self.key(host)
        with self.lock:
            now = time.monotonic()
            cool = self.cool_until.get(key, 0.0) - now
            if cool > self.MAX_BLOCK:
                self.local.limited = True
                raise RateLimited(f"{key} 'çok fazla istek' dedi; site yaklaşık {int(cool // 60) + 1} dakika "
                                  "dinlendiriliyor, sonra yeniden deneyin")
            start = max(now, self.next_ok.get(key, 0.0), self.cool_until.get(key, 0.0))
            self.next_ok[key] = start + self.gap(key)
        if start > now:
            time.sleep(start - now)

    def limited(self, host, retry_after=None) -> float:
        key = self.key(host)
        with self.lock:
            strikes = self.strikes.get(key, 0) + 1
            self.strikes[key] = strikes
            pause = retry_after if retry_after else min(20 * 2 ** (strikes - 1), 900)
            pause = min(max(pause, 5), 3600)
            self.cool_until[key] = max(self.cool_until.get(key, 0.0), time.monotonic() + pause)
            self.extra[key] = min(self.extra.get(key, 1.0) * 2, 8.0)      # bundan sonra daha yavaş git
        self.local.limited = True
        diag(f"{key}: çok fazla istek (429) — {pause:.0f} sn dinlendiriliyor, istek aralığı "
             f"{self.gap(key):.1f} sn", throttle=True)
        return pause

    def success(self, host):
        key = self.key(host)
        if self.strikes.get(key):
            with self.lock:
                self.strikes[key] = max(0, self.strikes[key] - 1)

    # iş parçacığı başına 'bu kaynakta istek sınırına takıldık mı?' işareti
    def reset_flag(self):
        self.local.limited = False

    def was_limited(self) -> bool:
        return bool(getattr(self.local, "limited", False))


THROTTLE = HostThrottle()


def parse_retry_after(value):
    if not value:
        return None
    value = value.strip()
    if value.isdigit():
        return float(value)
    try:
        from email.utils import parsedate_to_datetime
        return max(0.0, (parsedate_to_datetime(value) - datetime.now(timezone.utc)).total_seconds())
    except (TypeError, ValueError, IndexError):
        return None


class PoliteAdapter(HTTPAdapter):
    """Her isteği HostThrottle'dan geçirir; 429'da siteyi dinlendirir, kısa bir bekleme yetiyorsa bir kez
    daha dener."""

    def send(self, request, **kwargs):
        host = urlparse(request.url).hostname or ""
        for attempt in range(2):
            THROTTLE.wait(host)
            resp = super().send(request, **kwargs)
            if resp.status_code == 429 or (resp.status_code == 503 and resp.headers.get("Retry-After")):
                pause = THROTTLE.limited(host, parse_retry_after(resp.headers.get("Retry-After")))
                if attempt == 0 and pause <= HostThrottle.MAX_BLOCK:
                    resp.close()
                    continue                                   # wait() dinlenme bitene kadar bekletir
                return resp
            if resp.status_code < 400:
                THROTTLE.success(host)
            return resp
        return resp


def make_session() -> requests.Session:
    session = requests.Session()
    session.headers.update(HEADERS)
    retry = Retry(
        total=2, connect=1, read=1, backoff_factor=1.0,
        status_forcelist=(500, 502, 504),                   # 429/503'ü PoliteAdapter ele alır
        allowed_methods=frozenset({"GET", "HEAD"}),
        raise_on_status=False, respect_retry_after_header=False,
    )
    adapter = PoliteAdapter(max_retries=retry)
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


def history_key(url: str) -> str:
    return "|".join(_dedupe_key(url))


def history_path() -> Path:
    return data_dir() / "indirme_gecmisi.json"


def load_history() -> dict:
    """Bu bilgisayarda bugüne kadar başarıyla indirilen tüm linkler.
    Dönüş: {link anahtarı: {"file": dosya adı, "folder": klasör, "date": tarih}}"""
    try:
        with open(history_path(), encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def save_history(history: dict):
    try:
        path = history_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(".tmp")
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(history, fh, ensure_ascii=False, indent=1)
        os.replace(tmp, path)
    except OSError:
        pass


def load_previous_downloads(folder: Path) -> dict:
    """Klasördeki eski indirme raporlarından başarıyla inmiş linkleri okur
    (dosya sonradan taşınmış ya da silinmiş olsa bile).
    Dönüş: history ile aynı biçimde"""
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
        stamp = report.stem.removeprefix("indirme_raporu_")[:8]
        date = f"{stamp[:4]}-{stamp[4:6]}-{stamp[6:8]}" if stamp.isdigit() else "?"
        for row in rows[1:]:
            if len(row) < 4 or not row[1].startswith("http"):
                continue
            if row[2] in (STATUS_LABELS["ok"], STATUS_LABELS["dup"]) and row[3]:
                done[history_key(row[1])] = {"file": row[3], "folder": str(folder), "date": date}
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
        self._last_saved = None  # son kaydedilen dosya: {"path", "meta", "sha"}
        self.library = options.get("library")
        self.library_folder = options.get("library_folder")
        self.tags = clean_tags(options.get("tags") or [])

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
        history = load_history()
        # Eski sürümün (v1.0) klasöre yazdığı raporlar da geçmişe katılır
        for key, entry in load_previous_downloads(self.folder).items():
            history.setdefault(key, entry)
        skip = self.options.get("skip_existing", True)
        if skip:
            known = sum(1 for url in self.links if history_key(url) in history)
            if known:
                self.log("muted", f"Bu listedeki {known} kaynak daha önce indirilmiş; "
                                  "tekrar indirilmeyecek.")
        today = datetime.now().strftime("%Y-%m-%d")
        try:
            for i, url in enumerate(self.links, start=1):
                if self.cancel.is_set():
                    stopped = True
                    break
                self.emit("overall", i - 1, total)
                self.log("info", f"[{i}/{total}] {url}")
                self._tried = set()
                key = history_key(url)
                try:
                    if skip and key in history:
                        entry = history[key]
                        status, filename = "dup", entry.get("file", "")
                        where = Path(entry.get("folder") or self.folder)
                        if (self.folder / filename).is_file():
                            note = f"klasörde zaten var: {filename}"
                        elif where != self.folder and (where / filename).is_file():
                            note = f"zaten var: {where / filename}"
                        else:
                            note = (f"daha önce indirilmişti ({entry.get('date', '?')}), "
                                    f"dosya taşınmış ya da silinmiş: {filename}")
                    else:
                        self._last_saved = None
                        status, filename, note = self._download_one(session, url, i)
                        saved_folder = self.folder
                        if status == "ok" and self._last_saved:
                            placed = self._catalog(session, url)
                            if placed:
                                filename, saved_folder = placed.name, placed.parent
                        if status in ("ok", "dup") and filename:
                            history[key] = {"file": filename, "folder": str(saved_folder),
                                            "date": today}
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
                    self.log("muted", f"   ≡ Tekrar indirilmedi – {note}")
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
            save_history(history)
            stopped = stopped or self.cancel.is_set()
            report = self._write_report(results)
            self.emit("done", counts, stopped, report, failed)

    def _catalog(self, session, url):
        """İnen dosyayı kütüphaneye ekler; dosyanın yeni adını döndürür."""
        if not self.library:
            return None
        saved = self._last_saved
        try:
            doi = doi_from_url(url) or meta_doi(saved["meta"])
            item_id, _ = catalog_pdf(self.library, session, saved["path"], saved["sha"],
                                     meta=saved["meta"], url=url, doi=doi, tags=self.tags,
                                     log=self.log, library_folder=self.library_folder,
                                     source="indirme", auto_tags=self.options.get("auto_tags"))
            item = self.library.get(item_id)
            if item and item["file_path"]:
                return Path(item["file_path"])
        except Exception as exc:  # kütüphane hatası indirmeyi bozmasın
            self.log("warn", f"   ⚠ Kütüphaneye eklenemedi: {describe_error(exc)}")
        return None

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
    def _try_candidates(self, session, candidates, referer, url, index, meta, note="", depth=0,
                        trusted=()):
        """Adayları sırayla dener. 'trusted' dışındaki adaylardan inen PDF'in başlığı
        sayfadaki başlıkla karşılaştırılır; uyuşmazsa (başka bir yayınsa) reddedilir."""
        trusted = set(trusted)
        if meta.get("citation_pdf_url"):
            trusted.add(ojs_download_url(urljoin(referer or url, meta["citation_pdf_url"])))
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
                        sub_trusted = set()
                        if sub_meta.get("citation_pdf_url"):
                            sub_trusted.add(ojs_download_url(urljoin(resp.url, sub_meta["citation_pdf_url"])))
                        result = self._try_candidates(session, sub, resp.url, url, index,
                                                      meta or sub_meta, note, depth=1,
                                                      trusted=sub_trusted)
                        if result:
                            return result
                    self.log("muted", "     olmadı: PDF yerine web sayfası geldi (giriş/abonelik gerekebilir)")
                    continue
                check_title = (meta.get("citation_title") or "") if cand not in trusted else ""
                try:
                    return self._save_stream(resp, url, index, meta=meta, require_pdf=True,
                                             note=note or "makale sayfasındaki PDF bağlantısından",
                                             check_title=check_title)
                except NotPdf:
                    self.log("muted", "     olmadı: gelen dosya PDF değil")
                except WrongPdf:
                    self.log("muted", "     olmadı: inen PDF başka bir yayına ait (başlık uyuşmuyor), silindi")
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
                                    note="kurum arşivinden (DSpace)", depth=1, trusted=links)

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
                                    note="açık erişim kopyası (Unpaywall)", trusted=pdfs)

    # --- dosyaya yazma ---------------------------------------------------------
    def _save_stream(self, resp, url, index, meta=None, require_pdf=False, note="", check_title=""):
        def validate(first):
            if require_pdf and b"%PDF-" not in first[:1024]:
                raise NotPdf()

        path, size, digest = self._stream_to_file(
            resp, lambda first: make_filename(resp, url, index, meta=meta, first_bytes=first),
            validate)
        if check_title:
            head = pdf_text(path, max_pages=2, max_chars=20_000)
            if head.strip() and not title_matches_text(check_title, head):
                path.unlink(missing_ok=True)
                raise WrongPdf()
        duplicate = self._find_duplicate(path, size, digest)
        if duplicate:
            path.unlink(missing_ok=True)
            return "dup", duplicate.name, f"aynı dosya klasörde zaten var: {duplicate.name}"
        self._last_saved = {"path": path, "meta": meta or {}, "sha": digest}
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
#  5) KÜTÜPHANE: katalog, künye bulma, APA kaynakça
# ════════════════════════════════════════════════════════════════════════════

CROSSREF_API = "https://api.crossref.org/works/"
FULLTEXT_MAX_PAGES = 400
FULLTEXT_MAX_CHARS = 2_000_000

ITEM_TYPES = {
    "article": "Makale",
    "chapter": "Kitap bölümü",
    "book": "Kitap",
    "phd": "Doktora tezi",
    "masters": "Yüksek lisans tezi",
    "conference": "Bildiri",
    "other": "Diğer",
}
TYPE_BY_LABEL = {label: key for key, label in ITEM_TYPES.items()}
RECORD_FIELDS = ("title", "authors", "year", "type", "container", "volume", "issue", "pages",
                 "publisher", "doi", "url", "editors", "institution", "language", "keywords", "issn")

_CROSSREF_TYPES = {
    "journal-article": "article", "book-chapter": "chapter", "book-section": "chapter",
    "book-part": "chapter", "reference-entry": "chapter", "book": "book", "monograph": "book",
    "edited-book": "book", "reference-book": "book", "dissertation": "phd",
    "proceedings-article": "conference",
}


# ── Türkçe duyarlı metin yardımcıları ───────────────────────────────────────

_TR_LOWER = str.maketrans({"I": "ı", "İ": "i"})
_TR_UPPER = str.maketrans({"i": "İ", "ı": "I"})
_TR_ORDER = "aâbcçdefgğhıiîjklmnoöpqrsştuûüvwxyz"
_TR_RANK = {c: i for i, c in enumerate(_TR_ORDER)}


def tr_lower(text: str) -> str:
    return (text or "").translate(_TR_LOWER).lower()


def tr_upper(text: str) -> str:
    return (text or "").translate(_TR_UPPER).upper()


def fold(text: str) -> str:
    """Arama için: büyük/küçük harf, Türkçe karakter ve aksan farkını yok sayar
    ('HALK OYUNLARI' = 'halk oyunları' = 'halk oyunlari')."""
    text = unicodedata.normalize("NFKD", tr_lower(text))
    text = "".join(c for c in text if not unicodedata.combining(c))
    return text.replace("ı", "i")


_ISSN_RE = re.compile(r"(?<![\dXx-])(\d{4})[-\u2010-\u2015 ]?(\d{3}[\dXx])(?![\dXx])")


def issn_valid(code: str) -> bool:
    """8 karakterlik ISSN'in denetim hanesi doğru mu? (yıl aralıklarını ayıklar: 2026-2027)"""
    if not re.fullmatch(r"\d{7}[\dX]", code):
        return False
    total = sum(int(c) * w for c, w in zip(code[:7], range(8, 1, -1)))
    check = (11 - total % 11) % 11
    return code[7] == ("X" if check == 10 else str(check))


def norm_issn(value) -> str:
    """'1234-567x', '1234567X', 123456 (Excel'de baştaki sıfırı düşmüş) → '1234567X' ya da ''"""
    code = re.sub(r"[^0-9Xx]", "", str(value or "")).upper()
    if 4 <= len(code) < 8 and code.isdigit():
        code = code.zfill(8)
    return code if issn_valid(code) else ""


def find_issns(text) -> list:
    if isinstance(text, (list, tuple)):
        text = " ".join(str(t) for t in text)
    out = []
    for a, b in _ISSN_RE.findall(str(text or "")):
        code = norm_issn(a + b)
        if code and code not in out:
            out.append(code)
    return out


def join_issns(values) -> str:
    codes = find_issns(values) if not isinstance(values, str) else find_issns(values)
    return "; ".join(f"{c[:4]}-{c[4:]}" for c in codes)


def tr_sort_key(text: str):
    return [_TR_RANK.get(c, 100 + ord(c)) for c in tr_lower(text)]


def looks_turkish(text: str, language: str = "") -> bool:
    return (language or "").lower().startswith("tr") or bool(re.search(r"[çğıöşüÇĞİÖŞÜ]", text or ""))


_LANG_NAMES = {"tr": "Türkçe", "en": "İngilizce", "de": "Almanca", "fr": "Fransızca", "es": "İspanyolca",
               "it": "İtalyanca", "ru": "Rusça", "bg": "Bulgarca", "el": "Yunanca", "sr": "Sırpça", "cs": "Çekçe",
               "pt": "Portekizce", "ar": "Arapça", "zh": "Çince", "ja": "Japonca"}


def guess_language(item) -> str:
    """Kaynağın dili: kayıtta varsa o, yoksa başlıktan kaba tahmin."""
    lang = (item.get("language") or "").lower()[:2]
    if lang:
        return lang
    title = " " + (item.get("title") or "") + " "
    low = title.lower()
    english = len(re.findall(r" (the|of|and|in|on|for|with|from|to|an?) ", low))
    turkish = len(re.findall(r"[çğıöşüÇĞİÖŞÜ]", title)) + len(re.findall(r" (ve|bir|ile|üzerine|için) ", low))
    if english >= 2 and english > turkish:
        return "en"
    if turkish and not re.search(r"[äßñ]", low):
        return "tr"
    if re.search(r"[\u0400-\u04FF]", title):
        return "bg" if re.search(r"[ъ]", low) else "ru"
    if re.search(r"[\u0370-\u03FF]", title):
        return "el"
    if re.search(r"[ñ¿¡]| (el|los|las|del|y|una|en la) ", low):
        return "es"
    if re.search(r"[äß]| (der|die|das|und|zur|im) ", low):
        return "de"
    if re.search(r"[èêà]| (les|des|du|et|une|la) ", low):
        return "fr"
    if re.search(r"[ěřůčž]", low):
        return "cs"
    return "en"


def is_shouting(text: str) -> bool:
    letters = [c for c in text or "" if c.isalpha()]
    return len(letters) >= 8 and sum(c.isupper() for c in letters) / len(letters) > 0.8


_PROPER_TR = set("""
türk türkiye türkçe türkler türklerin osmanlı anadolu rumeli trakya ege karadeniz akdeniz marmara
balkan balkanlar kafkas kafkasya orta asya avrupa asya cumhuriyet unesco laban benesh mudurnu
adana adıyaman afyonkarahisar afyon ağrı amasya ankara antalya artvin aydın balıkesir bilecik
bingöl bitlis bolu burdur bursa çanakkale çankırı çorum denizli diyarbakır edirne elazığ erzincan
erzurum eskişehir gaziantep antep giresun gümüşhane hakkari hatay ısparta mersin istanbul izmir
kars kastamonu kayseri kırklareli kırşehir kocaeli konya kütahya malatya manisa kahramanmaraş
mardin muğla muş nevşehir niğde rize sakarya samsun siirt sinop sivas tekirdağ tokat trabzon
tunceli şanlıurfa urfa uşak van yozgat zonguldak aksaray bayburt karaman kırıkkale batman şırnak
bartın ardahan ığdır yalova karabük kilis osmaniye düzce kırım azerbaycan kazakistan özbekistan
türkmenistan kırgızistan bulgaristan yunanistan makedonya kosova bosna sırbistan
""".split())
_PROPER_EN = set("""
turkey turkish türkiye ottoman ottomans anatolia anatolian balkan balkans istanbul thrace unesco
laban benesh europe european america american english british asia asian greek greece bulgaria
bulgarian serbia serbian kosovo bosnia macedonia macedonian azerbaijan caucasus caucasian
""".split())


def sentence_case(text: str, turkish: bool) -> str:
    """'SOMUT OLMAYAN KÜLTÜREL MİRAS VE BURSA' → 'Somut olmayan kültürel miras ve Bursa'
    (il, bölge ve alana özgü özel adlar büyük harfle kalır)"""
    low = tr_lower(text) if turkish else text.lower()
    upper = tr_upper if turkish else str.upper
    proper = _PROPER_TR if turkish else _PROPER_EN | _PROPER_TR

    def cap(m):
        return m.group(1) + upper(m.group(2))
    out = re.sub(r"(^\W*|[:?!.]\s+\W*)(\w)", cap, low)

    def proper_noun(m):
        word = m.group(0)
        base = re.split(r"['’]", word)[0]
        if tr_lower(base) in proper:
            return upper(word[:1]) + word[1:]
        return word
    return re.sub(r"\w+(?:['’]\w+)?", proper_noun, out)


def title_case_word(word: str) -> str:
    return tr_upper(word[:1]) + tr_lower(word[1:]) if word else word


def clean_text(value) -> str:
    text = html.unescape(str(value or ""))
    text = re.sub(r"<[^>]+>", "", text)          # Crossref başlıklarındaki <i>, <sub>...
    return re.sub(r"\s+", " ", text).strip()


# ── Kişi adları ─────────────────────────────────────────────────────────────

def parse_person(name: str):
    """'Yılmaz, Ayşe' / 'Ayşe YILMAZ' / 'A. Yılmaz' → {'family': 'Yılmaz', 'given': 'Ayşe'}"""
    name = clean_text(name).strip(",; ")
    if not name:
        return None
    if "," in name:
        family, given = (part.strip() for part in name.split(",", 1))
    else:
        parts = name.split(" ")
        family, given = parts[-1], " ".join(parts[:-1])
    if family.isupper() and len(family) > 1 and given:     # DergiPark: 'Ayşe YILMAZ' (UNESCO değil)
        family = " ".join(title_case_word(w) for w in family.split(" "))
    if given.isupper() and len(given.replace(".", "").replace(" ", "")) > 2:
        given = " ".join(title_case_word(w) for w in given.split(" "))
    return {"family": family, "given": given}


def people_to_text(people) -> str:
    return "; ".join(f"{p.get('family', '')}, {p.get('given', '')}".strip(", ") for p in people or [])


def text_to_people(text: str) -> list:
    return [p for p in (parse_person(part) for part in re.split(r";|\n", text or "")) if p]


def initials(given: str) -> str:
    out = []
    for part in (given or "").replace(".", ". ").split():
        pieces = [p for p in part.split("-") if p and p[0].isalpha()]
        if pieces:
            out.append("-".join(tr_upper(p[0]) + "." for p in pieces))
    return " ".join(out)


def apa_person(p) -> str:
    ini = initials(p.get("given", ""))
    return f"{p.get('family', '')}, {ini}" if ini else p.get("family", "")


def apa_people(people) -> str:
    names = [apa_person(p) for p in people or [] if p.get("family")]
    if not names:
        return ""
    if len(names) == 1:
        return names[0]
    if len(names) <= 20:
        return ", ".join(names[:-1]) + ", & " + names[-1]
    return ", ".join(names[:19]) + ", . . . " + names[-1]


def apa_editors(people) -> str:
    names = [f"{initials(p.get('given', ''))} {p.get('family', '')}".strip() for p in people or []]
    if len(names) <= 2:
        return " & ".join(names)
    return ", ".join(names[:-1]) + ", & " + names[-1]


def first_author_label(rec) -> str:
    people = rec.get("authors") or []
    if not people:
        return ""
    name = people[0].get("family", "")
    return name + (" vd." if len(people) > 2 else f" ve {people[1].get('family', '')}" if len(people) == 2 else "")


# ── Künye kayıtları ─────────────────────────────────────────────────────────

def empty_record() -> dict:
    rec = {field: "" for field in RECORD_FIELDS}
    rec.update(authors=[], editors=[], type="other")
    return rec


def merge_records(primary: dict, fallback: dict) -> dict:
    rec = empty_record()
    for field in RECORD_FIELDS:
        rec[field] = (primary or {}).get(field) or (fallback or {}).get(field) or rec[field]
    if rec["type"] == "other" and (fallback or {}).get("type") not in (None, "", "other"):
        rec["type"] = fallback["type"]
    return rec


def finalize_record(rec: dict) -> dict:
    rec = merge_records(rec, {})
    for field in RECORD_FIELDS:
        if isinstance(rec[field], str):
            rec[field] = clean_text(rec[field])
    turkish = looks_turkish(rec["title"], rec["language"])
    if is_shouting(rec["title"]):
        rec["title"] = sentence_case(rec["title"], turkish)
    rec["title"] = rec["title"].rstrip(" .")
    rec["pages"] = re.sub(r"^(?:pp?\.|ss?\.)\s*", "", rec["pages"]).replace("--", "–").replace("-", "–")
    rec["doi"] = normalize_doi(rec["doi"]) or ""
    rec["issn"] = join_issns(find_issns(rec["issn"]))
    m = re.search(r"\b(1[5-9]\d\d|20\d\d)\b", rec["year"] or "")
    rec["year"] = m.group(1) if m else ""
    if rec["type"] not in ITEM_TYPES:
        rec["type"] = "other"
    return rec


def record_from_crossref(msg: dict) -> dict:
    def people(key):
        out = []
        for a in msg.get(key) or []:
            if a.get("family") or a.get("name"):
                out.append({"family": clean_text(a.get("family") or a.get("name")),
                            "given": clean_text(a.get("given", ""))})
        return out

    year = ""
    for key in ("published-print", "published-online", "issued", "created"):
        parts = (msg.get(key) or {}).get("date-parts") or [[]]
        if parts and parts[0] and parts[0][0]:
            year = str(parts[0][0])
            break
    title = clean_text((msg.get("title") or [""])[0])
    subtitle = clean_text((msg.get("subtitle") or [""])[0])
    if subtitle and subtitle.lower() not in title.lower():
        title = f"{title}: {subtitle}"
    containers = msg.get("container-title") or [""]
    institution = (msg.get("institution") or [{}])[0].get("name", "")
    return {
        "title": title, "authors": people("author"), "editors": people("editor"), "year": year,
        "type": _CROSSREF_TYPES.get(msg.get("type", ""), "other"),
        "container": clean_text(containers[0]), "volume": clean_text(msg.get("volume", "")),
        "issue": clean_text(msg.get("issue", "")), "pages": clean_text(msg.get("page", "")),
        "publisher": clean_text(msg.get("publisher", "")), "doi": msg.get("DOI", ""),
        "institution": clean_text(institution), "language": msg.get("language", ""),
        "issn": join_issns(msg.get("ISSN") or []),
    }


# ── Eksik künye bilgilerini tamamlama (bölüm sayfaları, kitap adı, editörler…) ─────────────

def missing_fields(item) -> list:
    """APA kaynakçası için eksik alanlar (türe göre)."""
    t = item.get("type")
    need = {"chapter": ("pages", "container", "editors", "publisher"),
            "article": ("container", "volume", "pages"),
            "conference": ("container", "pages"),
            "book": ("publisher",)}.get(t, ())
    return [f for f in need if not item.get(f)]


def pdf_page_range(path) -> str:
    """PDF'in kendi sayfa etiketlerinden (yayıncı koyduysa) bölümün sayfa aralığı: '45-67'."""
    if not str(path or "").lower().endswith(".pdf") or not os.path.isfile(path):
        return ""
    try:
        from pypdf import PdfReader
        labels = list(PdfReader(str(path)).page_labels)
    except Exception:
        return ""
    nums = [lab for lab in labels if str(lab).isdigit()]
    if len(nums) >= 2 and int(nums[-1]) > int(nums[0]) > 1:
        return f"{nums[0]}-{nums[-1]}"
    return ""


def crossref_search(session, item):
    """DOI'si olmayan kaynağı Crossref'te başlık+yazar+yılla arar; başlık uyuşursa ham kaydı döner."""
    first = (item.get("authors") or [{}])[0] or {}
    query = " ".join(filter(None, [item.get("title"), first.get("family", ""), str(item.get("year") or "")]))
    try:
        r = session.get(CROSSREF_API.rstrip("/"), params={"query.bibliographic": query, "rows": 5},
                        timeout=API_TIMEOUT, headers={"Accept": "application/json"})
        if not r.ok:
            return None
        for msg in r.json().get("message", {}).get("items", []):
            rec = record_from_crossref(msg)
            if not same_title(item.get("title", ""), rec["title"]):
                continue
            if item.get("year") and rec["year"] and abs(int(item["year"][:4]) - int(rec["year"][:4])) > 1:
                continue
            if first.get("family") and rec["authors"] and \
                    fold(first["family"]) not in {fold(a.get("family", "")) for a in rec["authors"]}:
                continue
            return msg
    except (requests.RequestException, ValueError, AttributeError):
        pass
    return None


def complete_record(session, item) -> dict:
    """Kaynağın BOŞ alanlarını Crossref (DOI ya da başlık araması), üst kitabın künyesi ve PDF sayfa
    etiketleriyle doldurur; dolu alanlara (sizin düzeltmelerinize) dokunmaz. Dönüş: güncellenecek alanlar."""
    msg = None
    doi = normalize_doi(item.get("doi") or "")
    try:
        if doi:
            r = session.get(CROSSREF_API + quote(doi, safe="/:;()._-"), timeout=API_TIMEOUT,
                            headers={"Accept": "application/json"})
            msg = r.json().get("message") if r.ok else None
        else:
            msg = crossref_search(session, item)
    except (requests.RequestException, ValueError):
        msg = None
    found = record_from_crossref(msg) if msg else {}
    # bölümün editörleri çoğu zaman üst kitabın kaydında
    if msg and found.get("type") == "chapter" and not found.get("editors") and not item.get("editors"):
        for isbn in (msg.get("ISBN") or [])[:2]:
            try:
                r = session.get(CROSSREF_API.rstrip("/"), params={"filter": f"isbn:{isbn}", "rows": 3},
                                timeout=API_TIMEOUT, headers={"Accept": "application/json"})
                books = [b for b in (r.json().get("message", {}).get("items", []) if r.ok else [])
                         if b.get("type") in ("book", "edited-book", "monograph", "reference-book")]
            except (requests.RequestException, ValueError):
                books = []
            if books:
                parent = record_from_crossref(books[0])
                found["editors"] = parent.get("editors") or []
                found["container"] = found.get("container") or parent.get("title", "")
                found["publisher"] = found.get("publisher") or parent.get("publisher", "")
                break
    updates = {}
    for field in ("container", "volume", "issue", "pages", "publisher", "editors", "issn", "doi", "year"):
        if not item.get(field) and found.get(field):
            updates[field] = found[field]
    if item.get("type") in ("other", "", None) and found.get("type") not in (None, "other"):
        updates["type"] = found["type"]
    if not item.get("pages") and not updates.get("pages") and \
            (updates.get("type") or item.get("type")) in ("chapter", "article", "conference"):
        pages = pdf_page_range(item.get("file_path"))
        if pages:
            updates["pages"] = pages
    return updates


def crossref_record(session, doi: str, raise_network_errors: bool = False):
    """DOI'nin künyesini Crossref'ten alır (APA için en güvenilir kaynak).
    Kayıt yoksa None; raise_network_errors=True ise bağlantı hataları yükseltilir."""
    try:
        r = session.get(CROSSREF_API + quote(doi, safe="/:;()._-"), timeout=API_TIMEOUT,
                        headers={"Accept": "application/json"})
        if r.status_code != 200:
            return None
        return record_from_crossref(r.json().get("message") or {})
    except requests.RequestException:
        if raise_network_errors:
            raise
        return None
    except (ValueError, AttributeError, IndexError, TypeError):
        return None


def record_from_meta(meta: dict, url: str = "") -> dict:
    meta = meta or {}
    names = meta.get("_authors") or [meta.get("citation_author") or meta.get("dc.creator") or ""]
    first, last = meta.get("citation_firstpage", ""), meta.get("citation_lastpage", "")
    book = meta.get("citation_inbook_title") or meta.get("citation_book_title")
    if meta.get("citation_dissertation_institution"):
        kind = "phd"
    elif meta.get("citation_journal_title"):
        kind = "article"
    elif book:
        kind = "chapter"
    elif meta.get("citation_conference_title"):
        kind = "conference"
    else:
        kind = "other"
    date = " ".join(meta.get(k, "") for k in ("citation_publication_date", "citation_date",
                                              "citation_online_date", "citation_year", "dc.date"))
    return {
        "title": meta.get("citation_title") or meta.get("dc.title") or "",
        "authors": [p for p in (parse_person(n) for n in names) if p],
        "year": date, "type": kind,
        "container": meta.get("citation_journal_title") or book or meta.get("citation_conference_title") or "",
        "volume": meta.get("citation_volume", ""), "issue": meta.get("citation_issue", ""),
        "pages": f"{first}–{last}" if first and last and first != last else first,
        "publisher": meta.get("citation_publisher") or meta.get("dc.publisher") or "",
        "doi": meta_doi(meta) or "", "url": url,
        "institution": meta.get("citation_dissertation_institution")
                       or meta.get("citation_technical_report_institution") or "",
        "language": meta.get("citation_language") or meta.get("dc.language") or "",
        "keywords": join_keywords(meta.get("_keywords") or split_keywords(meta.get("keywords", ""))),
        "issn": join_issns(meta.get("_issn") or []),
    }


_FILENAME_RE = re.compile(r"^(?P<who>[^()]+?)\s*\((?P<year>\d{4})\)\s*-\s*(?P<title>.+?)(?:\s*\(\d+\))?$")


def record_from_filename(stem: str) -> dict:
    """Bu uygulamanın verdiği 'Soyad (Yıl) - Başlık' adlarından künye çıkarır."""
    stem = stem.replace("_", ":") if " - " in stem else stem
    m = _FILENAME_RE.match(stem)
    if not m:
        return {"title": stem.replace(":", " ").strip()}
    who = m.group("who").strip()
    return {"title": m.group("title").rstrip("…").strip(),
            "authors": [{"family": title_case_word(who) if who.isupper() else who, "given": ""}],
            "year": m.group("year")}


# ── PDF içeriği ─────────────────────────────────────────────────────────────

def pdf_text(path, max_pages=FULLTEXT_MAX_PAGES, max_chars=FULLTEXT_MAX_CHARS) -> str:
    if str(path).lower().endswith(".epub"):
        return epub_text(path, max_chars=max_chars)
    try:
        from pypdf import PdfReader
        reader = PdfReader(str(path))
        chunks, size = [], 0
        for page in reader.pages[:max_pages]:
            try:
                text = page.extract_text() or ""
            except Exception:
                continue
            chunks.append(text)
            size += len(text)
            if size >= max_chars:
                break
        return "\n".join(chunks)[:max_chars]
    except Exception:
        return ""


# ── E-kitaplar: EPUB (DRM'siz ya da ödünç alınmış DRM'li), ACSM ödünç biletleri, ISBN ──────────

EBOOK_EXTS = (".epub", ".acsm")
DOC_EXTS = (".pdf",) + EBOOK_EXTS
_FONT_OBFUSCATION = ("http://www.idpf.org/2008/embedding", "http://ns.adobe.com/pdf/enc#RC")


def _xml_local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1].lower()


def _epub_opf(zf):
    container = ET.fromstring(zf.read("META-INF/container.xml"))
    for el in container.iter():
        if _xml_local(el.tag) == "rootfile" and el.get("full-path"):
            return el.get("full-path"), ET.fromstring(zf.read(el.get("full-path")))
    raise ValueError("EPUB içinde OPF yok")


def epub_is_drm(zf) -> bool:
    """Ödünç verilen e-kitaplar (Adobe ADEPT, LCP vb.) içerik dosyalarını şifreler; yalnızca yazı tipi
    gizlemesi DRM sayılmaz."""
    names = set(zf.namelist())
    if "META-INF/rights.xml" in names or "META-INF/license.lcpl" in names:
        return True
    if "META-INF/encryption.xml" not in names:
        return False
    try:
        root = ET.fromstring(zf.read("META-INF/encryption.xml"))
    except ET.ParseError:
        return True
    for data in root.iter():
        if _xml_local(data.tag) != "encrypteddata":
            continue
        algo = next((m.get("Algorithm", "") for m in data.iter() if _xml_local(m.tag) == "encryptionmethod"), "")
        uri = next((c.get("URI", "") for c in data.iter() if _xml_local(c.tag) == "cipherreference"), "")
        if algo not in _FONT_OBFUSCATION and not re.search(r"\.(otf|ttf|woff2?)$", uri, re.I):
            return True
    return False


def epub_info(path) -> dict:
    """EPUB künyesi: başlık, yazarlar, yıl, yayınevi, dil, ISBN; DRM'li mi?"""
    out = {"title": "", "creators": [], "year": "", "publisher": "", "language": "", "isbn": "", "drm": False}
    try:
        with zipfile.ZipFile(path) as zf:
            out["drm"] = epub_is_drm(zf)
            _, opf = _epub_opf(zf)
    except (zipfile.BadZipFile, KeyError, ValueError, ET.ParseError, OSError):
        return out
    for el in opf.iter():
        name, text = _xml_local(el.tag), (el.text or "").strip()
        if not text:
            continue
        if name == "title" and not out["title"]:
            out["title"] = text
        elif name == "creator":
            out["creators"].append(text)
        elif name == "date" and not out["year"]:
            m = re.search(r"\b(1[5-9]\d\d|20\d\d)\b", text)
            out["year"] = m.group(1) if m else ""
        elif name == "publisher" and not out["publisher"]:
            out["publisher"] = text
        elif name == "language" and not out["language"]:
            out["language"] = text[:2].lower()
        elif name == "identifier" and not out["isbn"]:
            out["isbn"] = find_isbn(text)
    return out


def epub_text(path, max_chars=FULLTEXT_MAX_CHARS) -> str:
    """DRM'siz EPUB'un okuma sırasındaki düz metni (tam metin araması için)."""
    try:
        with zipfile.ZipFile(path) as zf:
            if epub_is_drm(zf):
                return ""
            opf_path, opf = _epub_opf(zf)
            base = opf_path.rsplit("/", 1)[0] + "/" if "/" in opf_path else ""
            manifest = {el.get("id"): el.get("href") for el in opf.iter()
                        if _xml_local(el.tag) == "item" and el.get("href")}
            order = [manifest.get(el.get("idref")) for el in opf.iter() if _xml_local(el.tag) == "itemref"]
            chunks, size = [], 0
            for href in order:
                if not href:
                    continue
                try:
                    raw = zf.read(base + unquote(href).split("#")[0]).decode("utf-8", "replace")
                except KeyError:
                    continue
                raw = re.sub(r"(?is)<(script|style|head)\b.*?</\1>", " ", raw)
                text = html.unescape(re.sub(r"<[^>]+>", " ", raw))
                text = re.sub(r"\s+", " ", text).strip()
                if text:
                    chunks.append(text)
                    size += len(text)
                if size >= max_chars:
                    break
            return "\n".join(chunks)[:max_chars]
    except (zipfile.BadZipFile, KeyError, ValueError, ET.ParseError, OSError):
        return ""


def acsm_info(path) -> dict:
    """ACSM (Adobe ödünç bileti) içindeki künye; kitabın kendisi değildir."""
    try:
        text = Path(path).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return {}

    def tag(name):
        return [html.unescape(m.strip()) for m in re.findall(rf"<dc:{name}[^>]*>(.*?)</dc:{name}>", text, re.S)]
    return {"title": (tag("title") or [""])[0], "creators": tag("creator"),
            "publisher": (tag("publisher") or [""])[0], "isbn": next((find_isbn(i) for i in tag("identifier")
                                                                     if find_isbn(i)), ""),
            "language": ((tag("language") or [""])[0])[:2].lower(), "year": ""}


def _isbn_ok(digits: str) -> bool:
    if len(digits) == 13 and digits.isdigit():
        return sum(int(d) * (1 if i % 2 == 0 else 3) for i, d in enumerate(digits)) % 10 == 0
    if len(digits) == 10 and digits[:9].isdigit() and (digits[9].isdigit() or digits[9] in "Xx"):
        total = sum(int(d) * (10 - i) for i, d in enumerate(digits[:9]))
        total += 10 if digits[9] in "Xx" else int(digits[9])
        return total % 11 == 0
    return False


def isbn13(digits: str) -> str:
    if len(digits) == 13:
        return digits
    core = "978" + digits[:9]
    check = (10 - sum(int(d) * (1 if i % 2 == 0 else 3) for i, d in enumerate(core)) % 10) % 10
    return core + str(check)


def find_isbns(text: str) -> list:
    """Metindeki geçerli ISBN'ler (13 haneli biçimde, tekrarsız)."""
    out = []
    for m in re.finditer(r"(?<![\dXx])(97[89][\d\- ]{10,16}|[\d][\d\- ]{8,11}[\dXx])(?![\dXx])", text or ""):
        digits = re.sub(r"[\- ]", "", m.group(1))
        if _isbn_ok(digits):
            code = isbn13(digits.upper())
            if code not in out:
                out.append(code)
    return out


def find_isbn(text: str) -> str:
    found = find_isbns(text)
    return found[0] if found else ""


def book_record_by_isbn(session, isbn: str) -> dict:
    """ISBN'den kitap künyesi: önce Crossref (akademik kitaplar, DOI'siyle), yoksa Google Books."""
    try:
        r = session.get(CROSSREF_API.rstrip("/"), params={"filter": f"isbn:{isbn}", "rows": 3},
                        timeout=API_TIMEOUT, headers={"Accept": "application/json"})
        if r.ok:
            for msg in r.json().get("message", {}).get("items", []):
                if msg.get("type") in ("book", "monograph", "edited-book", "reference-book"):
                    rec = record_from_crossref(msg)
                    if rec.get("title"):
                        rec["type"] = "book"
                        return rec
    except (requests.RequestException, ValueError, AttributeError):
        pass
    try:
        r = session.get(GOOGLE_BOOKS_API, params={"q": f"isbn:{isbn}"},
                        timeout=API_TIMEOUT)
        items = r.json().get("items") or [] if r.ok else []
        if items:
            v = items[0].get("volumeInfo", {})
            title = v.get("title", "")
            if v.get("subtitle"):
                title += ": " + v["subtitle"]
            year = re.match(r"\d{4}", v.get("publishedDate", "") or "")
            return {"type": "book", "title": title, "authors": text_to_people("; ".join(v.get("authors") or [])),
                    "year": year.group(0) if year else "", "publisher": v.get("publisher", ""),
                    "language": (v.get("language") or "")[:2]}
    except (requests.RequestException, ValueError, AttributeError):
        pass
    return {}


# ── Kitap boyutundaki PDF'ler: bildiri kitapları ve ISBN'li kitaplar ───────────────────────

_PROC_RE = re.compile(r"bildiri(ler)?\s+kitab|tam\s+metin(ler)?\s+kitab|ozet(ler)?\s+kitab|bildiri\s+ozetleri|"
                      r"proceedings?|book\s+of\s+(abstracts|papers|full\s+texts)|kongres[i]?\b|congress|"
                      r"sempozyum|symposium|konferans|conference|calistay|workshop")
_PROC_BOOK_RE = re.compile(r"bildiri(ler)?\s+kitab|tam\s+metin(ler)?\s+kitab|ozet(ler)?\s+kitab|bildiri\s+ozetleri|"
                           r"proceedings?|book\s+of\s+(abstracts|papers|full\s+texts)")
_EDITOR_RE = re.compile(r"^(editor(ler)?|editors?|eds?\.|yayina\s+hazirlayan(lar)?|hazirlayan(lar)?|edited\s+by)"
                        r"\s*:?\s*(.*)$")
_ACADEMIC_TITLES = {"prof", "prof.", "doc", "doc.", "dr", "dr.", "ogr", "ogr.", "uyesi", "gor", "gor.", "ars",
                    "ars.", "assoc", "assoc.", "assist", "assist.", "asst", "asst.", "professor", "dr.ogr.",
                    "ogr.gor.", "ars.gor.", "doç.dr.", "prof.dr.", "doc.dr.", "uzm.", "uzm"}
_SMALL_WORDS = {"ve", "ile", "icin", "da", "de", "and", "of", "the", "on", "in", "for", "to", "a", "an", "et", "und"}
_ROMAN_RE = re.compile(r"^[IVXLC]+\.?$")
_PUBLISHER_RE = re.compile(r"(yayinlari|yayinevi|yayincilik|kitabevi|publishing|publications|publishers|press)\s*$")


def heading_case(text: str) -> str:
    """Büyük harfle yazılmış kongre/kitap adını özel ad gibi yazar:
    '8. ULUSLARARASI MÜZİK VE DANS KONGRESİ' → '8. Uluslararası Müzik ve Dans Kongresi'"""
    words = text.split()
    out = []
    for k, w in enumerate(words):
        if _ROMAN_RE.match(w) or any(c.isdigit() for c in w):
            out.append(w)
        elif k and fold(w).strip(".,:;") in _SMALL_WORDS:
            out.append(tr_lower(w))
        elif w.isupper() or w.islower():
            out.append("-".join(title_case_word(part) for part in w.split("-")))
        else:
            out.append(w)
    return " ".join(out)


def _clean_line(line: str) -> str:
    return re.sub(r"\s+", " ", line or "").strip()


def _people_from_line(text: str) -> list:
    """'Prof. Dr. Kürşad GÜLBEYAZ & Doç. Dr. Tarkan YAZICI' → kişiler (unvanlar atılır)."""
    people = []
    text = "".join(c for c in text or "" if c.isprintable() and not ("\ue000" <= c <= "\uf8ff")).replace("*", " ")
    for part in re.split(r"\s*(?:&|;|,|\bve\b|\band\b)\s*", text):
        words = [w for w in part.split() if fold(w) not in _ACADEMIC_TITLES and not re.fullmatch(r"[\W\d]+", w)]
        if 2 <= len(words) <= 5 and not any(c.isdigit() for c in "".join(words)):
            caps = 0
            while caps < len(words) - 1 and words[-1 - caps].isupper() and len(words[-1 - caps]) > 1:
                caps += 1
            if caps >= 2 and not words[0].isupper():            # 'Alev TÜRKAN ÖZCAN': iki soyadlı
                person = parse_person(" ".join(words[-caps:]) + ", " + " ".join(words[:-caps]))
            else:
                person = parse_person(" ".join(words))
            if person and person.get("family"):
                people.append(person)
    return people


def proceedings_record(pages: list, require_repeat=False) -> dict:
    """Bildiri kitabının ilk sayfalarından künye: kongre/kitap adı, editörler, yıl, yayınevi.
    pages: ilk sayfaların metinleri. Bildiri kitabı değilse {}.
    require_repeat: kısa PDF'lerde 'bildiriler kitabı' satırı en az iki sayfada (sayfa başlığı olarak) geçmeli;
    yoksa kaynakçada 'Proceedings of…' geçen sıradan bir makale bildiri sanılmasın."""
    pages = pages[:6]
    per_page = [[_clean_line(line) for line in (page or "").splitlines()] for page in pages]
    book_lines = {}
    for k, page_lines in enumerate(per_page):
        for line in page_lines:
            if line and len(line) < 140 and _PROC_BOOK_RE.search(fold(line)):
                book_lines.setdefault(fold(line), set()).add(k)
    if not book_lines or (require_repeat and max(len(v) for v in book_lines.values()) < 2):
        return {}
    lines = [line for page_lines in per_page for line in page_lines]
    hit = next((k for k, line in enumerate(lines) if line and len(line) < 140 and _PROC_RE.search(fold(line))), None)
    if hit is None:
        return {}

    def stop(line):
        f = fold(line)
        return (not line or len(line) > 120 or "www." in f or "http" in f or "@" in line
                or _EDITOR_RE.match(f) or re.search(r"\b\d{1,2}\s*[-–]\s*\d{1,2}\b", line))
    start = hit
    while start > 0 and not stop(lines[start - 1]):
        start -= 1
    end = hit
    while end + 1 < len(lines) and not stop(lines[end + 1]) and end - start < 5:
        end += 1
    title = " ".join(lines[start:end + 1]).strip(" .")
    if is_shouting(title):
        title = heading_case(title)
    rec = {"type": "book", "title": title[:220]}

    editors = []
    for k, line in enumerate(lines):
        m = _EDITOR_RE.match(fold(line))
        if not m:
            continue
        rest = line[len(line) - len(m.group(4)):] if m.group(4) else ""
        found = _people_from_line(rest) if rest else []
        j = k + 1
        while not found and j < len(lines) and j <= k + 2 and not lines[j]:
            j += 1
        while j < len(lines) and lines[j] and len(lines[j]) <= 80 and len(found) < 8 and not rest:
            more = _people_from_line(lines[j])
            if not more:
                break
            found.extend(more)
            j += 1
        if found:
            editors = found
            break
    if editors:
        rec["editors"] = editors

    text = fold("\n".join(lines))
    m = re.search(r"(?:yayin|basim|baski)\s+tarihi\s*:?\s*[^\n]{0,20}?\b((?:19|20)\d{2})\b", text) or \
        re.search(r"(?:publication\s+date|published)\s*:?\s*[^\n]{0,20}?\b((?:19|20)\d{2})\b", text) or \
        re.search(r"\b((?:19|20)\d{2})\b", "\n".join(fold(x) for x in lines[hit:hit + 40]))
    if m:
        rec["year"] = m.group(1)
    for line in lines:
        f = fold(line).lstrip("© ").strip()
        if line and len(line) < 80 and _PUBLISHER_RE.search(f) and not f.startswith("©"):
            pub = line.lstrip("© ").strip()
            rec["publisher"] = heading_case(pub) if is_shouting(pub) else pub
            break
    rec["keywords"] = "Bildiri kitabı"
    return rec


def pdf_pages_text(path, first=8, last=0) -> tuple:
    """(sayfa sayısı, [ilk sayfaların metni], [son sayfaların metni])"""
    try:
        from pypdf import PdfReader
        reader = PdfReader(str(path))
        n = len(reader.pages)

        def text(k):
            try:
                return reader.pages[k].extract_text() or ""
            except Exception:
                return ""
        head = [text(k) for k in range(min(first, n))]
        tail = [text(k) for k in range(max(min(first, n), n - last), n)] if last else []
        return n, head, tail
    except Exception:
        return 0, [], []


BOOK_MIN_PAGES = 40


def paper_in_proceedings(pages: list) -> dict:
    """Bildiri kitabından ayrılmış tek bildirinin ilk sayfasından başlık ve yazarlar. Her sayfada yinelenen
    sayfa başlığı (kongre adı, tarih, web adresi) ve sayfa numarası atlanır."""
    if len(pages) < 2:
        return {}
    counts = {}
    for page in pages[:6]:
        for line in {fold(_clean_line(x)) for x in (page or "").splitlines()}:
            if line:
                counts[line] = counts.get(line, 0) + 1
    repeated = {line for line, c in counts.items() if c >= 2}
    lines = [_clean_line(x) for x in (pages[0] or "").splitlines()]
    k = 0
    while k < len(lines) and (not lines[k] or fold(lines[k]) in repeated or re.fullmatch(r"[\divxlc]+", fold(lines[k]))):
        k += 1
    block = []
    while k < len(lines) and lines[k] and len(block) < 4:
        block.append(lines[k])
        k += 1
    while k < len(lines) and not lines[k]:
        k += 1
    title = " ".join(block).replace("- ", "-").strip()
    people = _people_from_line(lines[k]) if k < len(lines) else []
    if len(title) < 12 or len(title) > 300 or not people:
        return {}
    return {"title": sentence_case(title, looks_turkish(title, "")) if is_shouting(title) else title,
            "authors": people}


def book_like_record(session, path) -> dict:
    """DOI'si olmayan kitap boyutundaki PDF'in künyesi: bildiri kitabıysa kapak ve künye sayfasından, ISBN
    varsa Crossref/Google Books'tan. Kısa bir bildiri PDF'iyse yalnızca içinde yer aldığı kitabın bilgisi
    (tür 'Bildiri', kitap adı, editörler) döner; başlığa dokunulmaz."""
    if not str(path).lower().endswith(".pdf"):
        return {}
    n, head, tail = pdf_pages_text(path, first=8, last=2)
    if not n:
        return {}
    proc = proceedings_record(head, require_repeat=n < BOOK_MIN_PAGES)
    if n < BOOK_MIN_PAGES:
        if not proc:
            return {}
        out = {"type": "conference", "container": proc.get("title", ""), "editors": proc.get("editors") or [],
               "publisher": proc.get("publisher", ""), "year": proc.get("year", "")}
        out.update(paper_in_proceedings(head))
        return {k: v for k, v in out.items() if v}
    isbns = find_isbns(re.sub(r"https?://\S+", " ", "\n".join(head + tail)))
    looked = {}
    if isbns and session is not None:
        try:
            looked = book_record_by_isbn(session, isbns[0]) or {}
        except Exception:
            looked = {}
    if not proc and not looked:
        return {}
    rec = merge_records(proc, looked) if proc else merge_records(looked, {})
    if proc and not proc.get("editors") and looked.get("authors"):
        rec["editors"], rec["authors"] = looked["authors"], []        # bildiri kitabında yazar değil editör
    rec["type"] = "book"
    if proc:
        rec["keywords"] = rec.get("keywords") or "Bildiri kitabı"
    return {k: v for k, v in rec.items() if v}


ARCHIVE_META_API = "https://archive.org/metadata/"
_LOGIN_RE = re.compile(r"(login|signin|sign-in|shibboleth|/idp/|ezproxy|openathens|/sso|wayf|/auth/|"
                       r"cas/login|myathens|giris)", re.I)
EBOOK_PLATFORMS = {"ebookcentral.proquest.com": "ProQuest Ebook Central", "ebscohost.com": "EBSCO eBooks",
                   "archive.org": "Internet Archive", "books.google": "Google Books", "play.google.com":
                   "Google Play Kitaplar", "jstor.org": "JSTOR", "degruyter.com": "De Gruyter",
                   "taylorfrancis.com": "Taylor & Francis", "cambridge.org": "Cambridge Core",
                   "oapen.org": "OAPEN", "doabooks.org": "DOAB", "link.springer.com": "SpringerLink",
                   "sciencedirect.com": "ScienceDirect", "perlego.com": "Perlego", "scribd.com": "Scribd",
                   "vitalsource.com": "VitalSource", "dergipark.org.tr": "DergiPark", "openedition.org": "OpenEdition",
                   "muse.jhu.edu": "Project MUSE", "bloomsburycollections.com": "Bloomsbury"}


def platform_name(url) -> str:
    host = (urlparse(url).hostname or "").lower()
    return next((v for k, v in EBOOK_PLATFORMS.items() if k in host), host.replace("www.", ""))


def page_plain_text(page: str) -> str:
    page = re.sub(r"(?is)<(script|style|noscript|nav|header|footer|svg)\b.*?</\1>", " ", page)
    text = html.unescape(re.sub(r"<[^>]+>", " ", page))
    return re.sub(r"\s+", " ", text).strip()


def _jsonld_book(page) -> dict:
    for block in re.findall(r'<script[^>]+application/ld\+json[^>]*>(.*?)</script>', page, re.S | re.I):
        try:
            data = json.loads(block.strip())
        except ValueError:
            continue
        for obj in (data if isinstance(data, list) else data.get("@graph", [data]) if isinstance(data, dict) else []):
            if isinstance(obj, dict) and str(obj.get("@type", "")).lower() in ("book", "chapter", "scholarlyarticle"):
                authors = obj.get("author") or []
                authors = authors if isinstance(authors, list) else [authors]
                names = [a.get("name", "") if isinstance(a, dict) else str(a) for a in authors]
                pub = obj.get("publisher") or {}
                return {"title": obj.get("name") or obj.get("headline") or "",
                        "authors": text_to_people("; ".join(n for n in names if n)),
                        "year": str(obj.get("datePublished") or "")[:4],
                        "publisher": pub.get("name", "") if isinstance(pub, dict) else str(pub),
                        "isbn": find_isbn(str(obj.get("isbn") or "")),
                        "type": "chapter" if str(obj.get("@type")).lower() == "chapter" else "book"}
    return {}


def online_book_info(session, url) -> dict:
    """Bağlantıdaki kitabın künyesi ve erişimi. Kurum girişi isteyen sayfalara giriş YAPILMAZ; yalnızca herkese
    açık içerik (açık erişim kitap, kamu malı eser, açık PDF/EPUB) okunur.
    Dönüş: {"record", "isbn", "access": "open"|"restricted", "platform", "files": [...], "text"}"""
    out = {"record": {"type": "book", "url": url}, "isbn": "", "access": "open", "platform": platform_name(url),
           "files": [], "text": ""}
    host = (urlparse(url).hostname or "").lower()
    try:
        if "archive.org" in host and "/details/" in url:
            ident = url.split("/details/", 1)[1].split("/")[0].split("?")[0]
            data = session.get(ARCHIVE_META_API + quote(ident), timeout=API_TIMEOUT).json()
            md = data.get("metadata") or {}

            def first(v):
                return (v[0] if isinstance(v, list) and v else v) or ""
            creators = md.get("creator") or []
            creators = creators if isinstance(creators, list) else [creators]
            out["record"].update(title=first(md.get("title")), authors=text_to_people("; ".join(creators)),
                                 year=str(first(md.get("date")))[:4], publisher=first(md.get("publisher")),
                                 language=str(first(md.get("language")))[:2])
            out["isbn"] = find_isbn(" ".join(map(str, md.get("isbn") or [])) if isinstance(md.get("isbn"), list)
                                    else str(md.get("isbn") or ""))
            restricted = str(md.get("access-restricted-item", "")).lower() == "true" or data.get("is_dark")
            out["access"] = "restricted" if restricted else "open"
            if not restricted:
                for f in data.get("files") or []:
                    name = f.get("name", "")
                    if name.lower().endswith((".pdf", ".epub")) and "_encrypted" not in name and f.get("private") != "true":
                        out["files"].append(f"https://archive.org/download/{ident}/{quote(name)}")
                out["files"].sort(key=lambda u: not u.lower().endswith(".pdf"))
            return out
        if "books.google" in host or ("google." in host and "/books" in url):
            vid = parse_qs(urlparse(url).query).get("id", [""])[0] or \
                (re.search(r"/books/edition/[^/]+/([\w-]+)", url) or [None, ""])[1]
            if vid:
                v = session.get(GOOGLE_BOOKS_API + "/" + quote(vid), timeout=API_TIMEOUT).json()
                info, access = v.get("volumeInfo", {}), v.get("accessInfo", {})
                title = info.get("title", "") + (": " + info["subtitle"] if info.get("subtitle") else "")
                out["record"].update(title=title, authors=text_to_people("; ".join(info.get("authors") or [])),
                                     year=str(info.get("publishedDate") or "")[:4], publisher=info.get("publisher", ""),
                                     language=(info.get("language") or "")[:2])
                out["isbn"] = find_isbn(" ".join(i.get("identifier", "") for i in info.get("industryIdentifiers") or []))
                full = access.get("viewability") == "ALL_PAGES" and access.get("publicDomain")
                out["access"] = "open" if full else "restricted"
                out["preview"] = {"PARTIAL": "sınırlı önizleme", "ALL_PAGES": "tam görünüm",
                                  "NO_PAGES": "önizleme yok"}.get(access.get("viewability"), "")
                for kind in ("pdf", "epub"):
                    link = (access.get(kind) or {}).get("downloadLink")
                    if full and link:
                        out["files"].append(link)
                return out
        r = session.get(url, timeout=TIMEOUT, allow_redirects=True)
        final = r.url
        page = decode_html(r.content[:3_000_000], r) if is_html(content_type(r)) else ""
        if content_type(r).startswith("application/pdf") or r.content[:5] == b"%PDF-":
            out["files"].append(final)
            return out
        meta = parse_citation_meta(page)
        rec = record_from_meta(meta, url) if meta else {}
        ld = _jsonld_book(page)
        title = rec.get("title") or ld.get("title") or page_title(page)
        out["record"].update({k: v for k, v in rec.items() if v})
        out["record"].update({k: v for k, v in ld.items() if v and k not in ("isbn",) and not out["record"].get(k)})
        out["record"]["title"] = title
        if out["record"].get("type") in ("other", "", None):
            out["record"]["type"] = "book"
        out["isbn"] = ld.get("isbn") or find_isbn(meta.get("citation_isbn", "")) or find_isbn(page[:200_000])
        login = _LOGIN_RE.search(urlparse(final).path + " " + (urlparse(final).hostname or "")) or \
            re.search(r'type=["\']password["\']', page, re.I) or r.status_code in (401, 403) or \
            looks_like_bot_check(page, final)
        if login:
            out["access"] = "restricted"
            if not rec.get("title") and not ld.get("title"):
                out["record"]["title"] = ""                    # giriş sayfasının başlığı kitabın adı değil
            return out
        out["files"] = [c for c in find_pdf_candidates(page, final, meta)[:3]]
        text = page_plain_text(page)
        out["text"] = text if len(text) > 3000 else ""
    except (requests.RequestException, ValueError, AttributeError) as exc:
        diag(f"çevrimiçi kitap: {url}: {describe_error(exc)}", throttle=True)
        out["access"] = "restricted"
    return out


ONLINE_RESTRICTED_NOTE = ("Çevrimiçi okunur ({platform}); kurum girişi ya da ödünç alma gerekir. Program ve Claude "
                          "bu içeriği kendisi okumaz: okurken 'Okurken Not Al' penceresiyle alıntılarınızı "
                          "sayfa numarasıyla alıntı kartlarına ekleyin.")
ONLINE_OPEN_NOTE = "Açık çevrimiçi metin bağlantıdan alındı ({platform}); Claude ve metin dizini bunu okuyabilir."
GOOGLE_PREVIEW_NOTE = ("Google Books'ta {preview}: sayfalar yalnızca tarayıcıda görüntülenir; Google otomatik okumaya izin "
                       "vermediği için program ve Claude içeriği okuyamaz. Okurken 'Okurken Not Al' penceresiyle "
                       "alıntılarınızı sayfa numarasıyla alıntı kartlarına ekleyin.")


def try_open_copy(library, session, item_id, rec, library_folder, email="") -> bool:
    """Kitabın/bölümün yasal açık kopyasını (OpenAlex, Semantic Scholar, CORE) arar; PDF bulunursa başlığı
    doğrulanıp bağlanır."""
    copies = find_open_copies(session, rec, email, load_settings().get("core_api_key", ""))
    for link in copies["pdfs"][:4]:
        tmp = Path(library_folder) / f".acik_kopya_{item_id}.pdf"
        try:
            with session.get(link, stream=True, timeout=(15, 180)) as r:
                r.raise_for_status()
                with open(tmp, "wb") as fh:
                    for block in r.iter_content(1 << 16):
                        fh.write(block)
            if b"%PDF-" not in tmp.read_bytes()[:1024]:
                tmp.unlink(missing_ok=True)
                continue
            if link not in copies.get("trusted", []) and \
                    not title_matches_text(rec.get("title", ""), pdf_text(tmp, max_pages=4, max_chars=30_000)):
                tmp.unlink(missing_ok=True)
                continue
            attach_pdf(library, item_id, tmp, library_folder, move=True)
            return True
        except (requests.RequestException, OSError):
            tmp.unlink(missing_ok=True)
    return False


def add_online_book(library, session, url, tags=(), library_folder=None, auto_tags=None, isbn=""):
    """Bağlantıdaki kitabı/bölümü kütüphaneye ekler; bağlantı kayıtta kalır. Açık dosya varsa indirip bağlar,
    açık çevrimiçi metin varsa tam metin olarak saklar. Dönüş: (kimlik, yeni_mi, erişim)"""
    info = online_book_info(session, url)
    info["isbn"] = info["isbn"] or isbn
    rec = dict(info["record"])
    if info["isbn"]:
        looked = book_record_by_isbn(session, info["isbn"])
        if looked:
            rec = merge_records(rec, looked) if rec.get("title") else merge_records(looked, rec)
            rec["url"] = url
    if not rec.get("title"):
        rec["title"] = f"{info['platform']} kitabı (başlığı düzenleyin)"
    existing = library.find_by_url(url) or library.find_by_doi(rec.get("doi")) or library.find_by_title(rec["title"])
    created = not existing
    if existing:
        item_id = existing
        old = library.get(item_id)
        fill = {k: rec[k] for k in RECORD_FIELDS if rec.get(k) and not old.get(k)}
        if fill:
            library.update(item_id, fill)
        library.add_tags(item_id, tags)
    else:
        item_id, _ = library.add(rec, tags=list(tags) + auto_group_tags(rec, info["text"][:20_000], auto_tags),
                                 source="bağlantı")
    item = library.get(item_id)
    notes = [n for n in [item.get("notes"), f"ISBN: {info['isbn']}" if info["isbn"] else ""] if n]
    attached = False
    if not (item["file_path"] and os.path.exists(item["file_path"])) and info["files"] and library_folder:
        for link in info["files"]:
            try:
                ext = ".epub" if link.lower().split("?")[0].endswith(".epub") else ".pdf"
                tmp = Path(library_folder) / f".cevrimici_{item_id}{ext}.part"
                with session.get(link, stream=True, timeout=(15, 180)) as r:
                    r.raise_for_status()
                    with open(tmp, "wb") as fh:
                        for block in r.iter_content(1 << 16):
                            fh.write(block)
                head = tmp.read_bytes()[:1024]
                if (ext == ".pdf" and b"%PDF-" in head) or (ext == ".epub" and head[:2] == b"PK"):
                    final = tmp.with_name(tmp.name[:-5])
                    os.replace(tmp, final)
                    attach_pdf(library, item_id, final, library_folder, move=True)
                    attached = True
                    break
                tmp.unlink(missing_ok=True)
            except (requests.RequestException, OSError):
                continue
    if not attached and not info["text"] and library_folder:
        try:                                                    # başka yerde yasal açık kopyası var mı?
            attached = try_open_copy(library, session, item_id, library.get(item_id), library_folder)
        except Exception as exc:
            diag(f"açık kopya ({url}): {describe_error(exc)}")
    if attached:
        pass
    elif info.get("preview"):
        notes.append(GOOGLE_PREVIEW_NOTE.format(preview=info["preview"]))
    elif info["access"] == "restricted":
        notes.append(ONLINE_RESTRICTED_NOTE.format(platform=info["platform"]))
    elif info["text"] and not attached:
        library.set_fulltext(item_id, info["text"])
        notes.append(ONLINE_OPEN_NOTE.format(platform=info["platform"]))
    if notes:
        joined = "\n".join(dict.fromkeys(n for n in notes if n))
        if joined != (item.get("notes") or ""):
            library.update(item_id, {"notes": joined})
    return item_id, created, ("dosya" if attached else "metin" if info["text"] else info["access"])


EBOOK_DRM_NOTE = ("Ödünç alınmış (DRM'li) e-kitap: Adobe Digital Editions ya da kütüphanenin okuma uygulamasıyla "
                  "açılır; ödünç süresi bitince dosya açılmaz. Alıntılarınızı alıntı kartlarına sayfa numarasıyla "
                  "kaydedin.")
ACSM_NOTE = ("Ödünç bileti (.acsm) eklendi, kitabın dosyası değil. Bileti Adobe Digital Editions ile açın; inen "
             "EPUB 'Belgeler\\My Digital Editions' klasöründe olur, onu 'PDF Bağla…' ile bu kayda bağlayabilirsiniz.")


def ebook_record(session, path, info) -> dict:
    """E-kitap dosyasının künyesi; ISBN varsa Crossref/Google Books ile tamamlanır."""
    people = []
    for c in info.get("creators") or []:
        people += text_to_people(c)
    base = {"type": "book", "title": info.get("title") or Path(path).stem, "authors": people,
            "year": info.get("year", ""), "publisher": info.get("publisher", ""), "language": info.get("language", "")}
    looked = book_record_by_isbn(session, info["isbn"]) if info.get("isbn") and session is not None else {}
    return merge_records(looked, base) if looked else base


def catalog_ebook(library, session, path: Path, sha: str, tags=(), log=None, library_folder=None, move=True,
                  source="", auto_tags=None):
    """EPUB ya da ACSM dosyasını kitap olarak kütüphaneye ekler. Dönüş: (kimlik, yeni_mi)"""
    path = Path(path)
    acsm = path.suffix.lower() == ".acsm"
    info = acsm_info(path) if acsm else epub_info(path)
    record = ebook_record(session, path, info)
    notes = []
    if info.get("isbn"):
        notes.append(f"ISBN: {info['isbn']}")
    if acsm:
        notes.append(ACSM_NOTE)
    elif info.get("drm"):
        notes.append(EBOOK_DRM_NOTE)
    text = "" if acsm else epub_text(path)
    tags = list(tags) + auto_group_tags(record, text[:20_000], auto_tags)
    existing = (None if acsm else library.find_by_sha(sha)) or library.find_by_doi(record.get("doi")) or \
        library.find_by_title(record.get("title"))
    if existing:
        old = library.get(existing)
        library.add_tags(existing, tags)
        if acsm or (old["file_path"] and Path(old["file_path"]).is_file()):
            if log:
                log("muted", f"   📚 Zaten kütüphanede: {old['title'][:80]}")
            return existing, False
        target = place_in_library(path, old, library_folder, move=move)
        library.update(existing, {"file_path": str(target), "sha256": sha,
                                  "notes": "\n".join(filter(None, [old.get("notes"), *notes]))})
        if text:
            library.set_fulltext(existing, text)
        return existing, False
    if not acsm:
        try:
            path = place_in_library(path, finalize_record(record), library_folder, move=move)
        except OSError as exc:
            if log:
                log("warn", f"   ⚠ Kütüphane klasörüne taşınamadı: {describe_error(exc)}")
    item_id, created = library.add(record, None if acsm else path, "" if acsm else sha, text, tags, source=source)
    if notes:
        old = library.get(item_id)
        library.update(item_id, {"notes": "\n".join(filter(None, [old.get("notes"), *notes]))})
    if log:
        kind = "ödünç bileti" if acsm else "DRM'li e-kitap" if info.get("drm") else "e-kitap"
        log("muted", f"   📚 Kütüphaneye eklendi ({kind}): {record.get('title', '')[:80]}")
    return item_id, created


def doc_head(path) -> str:
    """Eşleştirme için belgenin başı: PDF'in ilk sayfaları ya da EPUB'un künyesi ve başı."""
    head = pdf_text(path, max_pages=2, max_chars=20_000)
    if str(path).lower().endswith(".epub"):
        info = epub_info(path)
        head = " ".join([info.get("title", ""), " ".join(info.get("creators") or []), info.get("isbn", ""), head])
    return head


def downloaded_docs(folder):
    """Klasördeki PDF ve EPUB dosyaları."""
    return [p for pattern in ("*.pdf", "*.epub") for p in Path(folder).glob(pattern)]


def pdf_info(path) -> dict:
    try:
        from pypdf import PdfReader
        info = PdfReader(str(path)).metadata or {}
        return {"title": str(info.get("/Title") or ""), "author": str(info.get("/Author") or "")}
    except Exception:
        return {}


def same_title(a: str, b: str) -> bool:
    """İki başlık aynı yayını mı gösteriyor? (büyük/küçük harf, noktalama, alt başlık farkı tolere edilir)"""
    wa = [w for w in re.findall(r"\w+", fold(a or "")) if len(w) >= 3]
    wb = [w for w in re.findall(r"\w+", fold(b or "")) if len(w) >= 3]
    if len(wa) < 2 or len(wb) < 2:
        return False
    if " ".join(wa) == " ".join(wb):
        return True
    short, long_ = (wa, wb) if len(wa) <= len(wb) else (wb, wa)
    hit = sum(w in set(long_) for w in short) / len(short)
    return hit >= 0.9 and len(short) / len(long_) >= 0.6


def find_open_copies(session, item, email="", core_key="") -> dict:
    """Kaynağın yasal açık erişim kopyalarını OpenAlex ve Semantic Scholar'da arar (DOI varsa DOI ile,
    yoksa başlıkla; başlık eşleşmesi doğrulanır). Kurum arşivleri, arXiv, Zenodo, dergi sayfaları gibi
    konumlar gelir. Dönüş: {"pdfs": [...], "pages": [...], "by_doi": bool, "sources": [...]}"""
    title, year, doi = item.get("title") or "", str(item.get("year") or ""), normalize_doi(item.get("doi") or "")
    pdfs, pages, sources, trusted = [], [], [], []

    def add(url, bucket):
        if url and url.startswith("http") and not is_doi_host(url) and url not in pdfs and url not in pages:
            bucket.append(url)

    def year_ok(other):
        try:
            return not year or not other or abs(int(year[:4]) - int(str(other)[:4])) <= 1
        except ValueError:
            return True

    # OpenAlex
    try:
        params = openalex_params(email)
        if doi:
            r = session.get(f"{OPENALEX_API}/doi:{quote(doi, safe='/:;()._-')}", params=params, timeout=API_TIMEOUT)
            works = [r.json()] if r.ok else []
        elif len(title) >= 12:
            r = session.get(OPENALEX_API, params=dict(params, search=title, **{"per-page": 5}), timeout=API_TIMEOUT)
            works = r.json().get("results", []) if r.ok else []
        else:
            works = []
        for w in works:
            if not doi and not (same_title(title, w.get("title") or w.get("display_name") or "")
                                and year_ok(w.get("publication_year"))):
                continue
            locs = [w.get("best_oa_location")] + list(w.get("locations") or [])
            for loc in locs:
                if not loc or not loc.get("is_oa"):
                    continue
                add(loc.get("pdf_url"), pdfs)
                add(loc.get("landing_page_url"), pages)
            add((w.get("open_access") or {}).get("oa_url"), pages)
            if pdfs or pages:
                sources.append("OpenAlex")
            if doi:
                trusted.extend(pdfs)                        # DOI ile bulunan PDF bağlantıları güvenilir
            break
    except (requests.RequestException, ValueError, AttributeError) as exc:
        diag(f"OpenAlex: {describe_error(exc)}", throttle=True)

    # Semantic Scholar
    try:
        fields = {"fields": "title,year,openAccessPdf"}
        if doi:
            r = session.get(S2_API + "DOI:" + quote(doi, safe="/:;()._-"), params=fields, timeout=API_TIMEOUT)
            papers = [r.json()] if r.ok else []
        elif len(title) >= 12:
            r = session.get(S2_API + "search/match", params=dict(fields, query=title), timeout=API_TIMEOUT)
            papers = (r.json().get("data") or []) if r.ok else []
        else:
            papers = []
        for paper in papers[:1]:
            if not doi and not (same_title(title, paper.get("title") or "") and year_ok(paper.get("year"))):
                continue
            before = len(pdfs)
            add((paper.get("openAccessPdf") or {}).get("url"), pdfs)
            if len(pdfs) > before:
                sources.append("Semantic Scholar")
                if doi:
                    trusted.append(pdfs[-1])
    except (requests.RequestException, ValueError, AttributeError) as exc:
        diag(f"Semantic Scholar: {describe_error(exc)}", throttle=True)

    # CORE: dünyadaki kurum arşivlerinin tam metinleri (anahtarsız da çalışır; anahtar hızlandırır)
    if len(title) >= 12:
        try:
            q = f'doi:"{doi}"' if doi else f'title:"{title}"'
            headers = {"Accept": "application/json"}
            if core_key:
                headers["Authorization"] = f"Bearer {core_key}"
            r = session.get(CORE_API, params={"q": q, "limit": 3}, timeout=API_TIMEOUT, headers=headers)
            if r.status_code in (401, 403):
                diag("CORE: API anahtarı kabul edilmedi", throttle=True)
            for work in (r.json().get("results") or []) if r.ok else []:
                if not (same_title(title, work.get("title") or "") and year_ok(work.get("yearPublished"))):
                    continue
                before = len(pdfs)
                add(work.get("downloadUrl"), pdfs)
                for link in work.get("links") or []:
                    if link.get("type") == "download":
                        add(link.get("url"), pdfs)
                if len(pdfs) > before:
                    sources.append("CORE")
                    break
        except (requests.RequestException, ValueError, AttributeError) as exc:
            diag(f"CORE: {describe_error(exc)}", throttle=True)
    return {"pdfs": pdfs[:6], "pages": pages[:3], "by_doi": bool(doi), "sources": sources,
            "trusted": [u for u in trusted if u in pdfs[:6]]}


def title_matches_text(title: str, text: str) -> bool:
    """Crossref'ten gelen başlık PDF'in ilk sayfalarında geçiyor mu? (yanlış DOI'yi eler)"""
    words = [w for w in re.findall(r"\w+", fold(title)) if len(w) >= 4]
    if len(words) < 2:
        return True
    body = fold(text)
    return sum(w in body for w in words) / len(words) >= 0.6


# ── APA 7 ───────────────────────────────────────────────────────────────────

APA_WORDS = {
    "tr": {"nd": "t.y.", "in": "İçinde", "pp": "ss.", "ed": "Ed.", "eds": "Ed.",
           "phd": "Doktora tezi", "masters": "Yüksek lisans tezi"},
    "en": {"nd": "n.d.", "in": "In", "pp": "pp.", "ed": "Ed.", "eds": "Eds.",
           "phd": "Doctoral dissertation", "masters": "Master's thesis"},
}


def apa_segments(rec: dict, lang: str = "tr") -> list:
    """APA 7 kaynak satırı; italik kısımlar ayrı işaretli: [(metin, italik_mi), ...]"""
    w = APA_WORDS.get(lang, APA_WORDS["tr"])
    segs = []

    def add(text, italic=False):
        if text:
            segs.append((text, italic))

    kind = rec.get("type") or "other"
    title = (rec.get("title") or "").strip().rstrip(".")
    title_dot = title + ("" if title[-1:] in "?!" else ".") if title else ""
    italic_title = kind in ("book", "phd", "masters", "other")
    authors = apa_people(rec.get("authors"))
    if not authors and kind == "book" and rec.get("editors"):         # derleme / bildiri kitabı: Editör (Ed.).
        eds = rec["editors"]
        authors = apa_people(eds) + f" ({w['eds'] if len(eds) > 1 else w['ed']})."
    year = f"({rec.get('year') or w['nd']})."
    container = (rec.get("container") or "").strip().rstrip(".")
    pages = (rec.get("pages") or "").strip()
    publisher = (rec.get("publisher") or "").strip().rstrip(".")

    title_done = False
    if authors:
        add(authors + ("" if authors.endswith(".") else ".") + " " + year + " ")
    else:  # yazar yoksa başlık yazar yerine geçer
        add(title, italic_title)
        add(("" if title[-1:] in "?!" else ".") + " " + year + " ")
        title_done = True

    if kind == "article":
        if not title_done:
            add(title_dot + " ")
        if container:
            add(container, True)
            if rec.get("volume"):
                add(", ")
                add(rec["volume"], True)
            if rec.get("issue"):
                add(f"({rec['issue']})")
            if pages:
                add(f", {pages}")
            add(". ")
    elif kind in ("chapter", "conference"):
        if not title_done:
            add(title_dot + " ")
        if container:
            add(f"{w['in']} ")
            editors = rec.get("editors") or []
            if editors:
                add(f"{apa_editors(editors)} ({w['eds'] if len(editors) > 1 else w['ed']}), ")
            add(container, True)
            if pages:
                add(f" ({w['pp']} {pages})")
            add(". ")
        if publisher:
            add(publisher + ". ")
    elif kind in ("phd", "masters"):
        if not title_done:
            add(title, True)
        inst = rec.get("institution") or publisher
        m = re.search(r"YÖK Tez No:\s*(\d+)", rec.get("notes") or "")
        if m:                                    # APA 7: veri tabanından alınan tez
            add(f" ({'Tez No.' if lang == 'tr' else 'Thesis No.'} {m.group(1)})")
        add(f" [{w[kind]}{', ' + inst if inst else ''}]. ")
        if m and not rec.get("url"):
            add("Yükseköğretim Kurulu Ulusal Tez Merkezi. " if lang == "tr"
                else "Council of Higher Education National Thesis Center. ")
    else:  # kitap ve diğer
        if not title_done:
            add(title, True)
            add(". ")
        if kind == "other" and container:
            add(container + ". ")
        if publisher:
            add(publisher + ". ")

    if rec.get("doi"):
        add("https://doi.org/" + rec["doi"])
    elif rec.get("url"):
        add(rec["url"])

    # birleştirme sırasında oluşan '..' ve sondaki boşluk temizliği
    cleaned = []
    for text, italic in segs:
        if cleaned and not italic and text.startswith(".") and cleaned[-1][0].endswith("."):
            text = text[1:]
        cleaned.append((text, italic))
    if cleaned:
        cleaned[-1] = (cleaned[-1][0].rstrip(), cleaned[-1][1])
    return [(t, i) for t, i in cleaned if t]


def apa_text(rec: dict, lang: str = "tr") -> str:
    return "".join(t for t, _ in apa_segments(rec, lang))


def bibliography(records, lang="tr") -> list:
    """Alfabetik sıralı [(düz metin, segmentler)] listesi."""
    refs = [(apa_text(r, lang), apa_segments(r, lang)) for r in records]
    refs.sort(key=lambda ref: tr_sort_key(ref[0]))
    return refs


def write_bibliography_docx(path, refs, heading="Kaynakça"):
    """APA biçiminde (asılı girinti, çift satır aralığı, italikler) Word dosyası yazar."""
    def run(text, italic=False, bold=False):
        text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
        props = ('<w:rFonts w:ascii="Times New Roman" w:hAnsi="Times New Roman" w:cs="Times New Roman"/>'
                 + ("<w:b/>" if bold else "") + ("<w:i/>" if italic else "") + '<w:sz w:val="24"/>')
        return f'<w:r><w:rPr>{props}</w:rPr><w:t xml:space="preserve">{xml_escape(text)}</w:t></w:r>'

    spacing = '<w:spacing w:before="0" w:after="0" w:line="480" w:lineRule="auto"/>'
    body = [f'<w:p><w:pPr>{spacing}<w:jc w:val="center"/></w:pPr>{run(heading, bold=True)}</w:p>']
    for _, segs in refs:
        runs = "".join(run(t, i) for t, i in segs)
        body.append(f'<w:p><w:pPr>{spacing}<w:ind w:left="720" w:hanging="720"/></w:pPr>{runs}</w:p>')
    document = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"><w:body>'
        + "".join(body) +
        '<w:sectPr><w:pgSz w:w="11906" w:h="16838"/><w:pgMar w:top="1440" w:right="1440" '
        'w:bottom="1440" w:left="1440" w:header="708" w:footer="708" w:gutter="0"/></w:sectPr>'
        '</w:body></w:document>')
    content_types = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
        '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
        '<Default Extension="xml" ContentType="application/xml"/>'
        '<Override PartName="/word/document.xml" ContentType="application/'
        'vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/></Types>')
    rels = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/'
        'relationships/officeDocument" Target="word/document.xml"/></Relationships>')
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("[Content_Types].xml", content_types)
        zf.writestr("_rels/.rels", rels)
        zf.writestr("word/document.xml", document)


def intext_citation(rec: dict, page: str = "", lang: str = "tr") -> str:
    """APA 7 metin içi atıf: (Yılmaz, 2023, s. 45) · (Yılmaz & Kaya, 2023) · (Yılmaz vd., 2023)"""
    people = [p for p in rec.get("authors") or [] if p.get("family")]
    if not people:
        title = (rec.get("title") or "").split(":")[0]
        who = f"“{title[:60]}”"
    elif len(people) == 1:
        who = people[0]["family"]
    elif len(people) == 2:
        who = f"{people[0]['family']} & {people[1]['family']}"
    else:
        who = f"{people[0]['family']} {'vd.' if lang == 'tr' else 'et al.'}"
    year = rec.get("year") or APA_WORDS[lang]["nd"]
    page = (page or "").strip()
    if page:
        page = page.replace("-", "–")
        prefix = ("ss." if "–" in page else "s.") if lang == "tr" else ("pp." if "–" in page else "p.")
        return f"({who}, {year}, {prefix} {page})"
    return f"({who}, {year})"


def card_citation_text(card: dict, rec: dict, lang: str = "tr") -> str:
    quote = (card.get("quote") or "").strip()
    cite = intext_citation(rec, card.get("page", ""), lang)
    return f"“{quote}” {cite}" if quote else cite


# ── Dışa aktarma (Jenni, Zotero, Mendeley vb. için) ─────────────────────────

_BIB_TYPES = {"article": "article", "chapter": "incollection", "book": "book", "phd": "phdthesis",
              "masters": "mastersthesis", "conference": "inproceedings", "other": "misc"}
_RIS_TYPES = {"article": "JOUR", "chapter": "CHAP", "book": "BOOK", "phd": "THES",
              "masters": "THES", "conference": "CPAPER", "other": "GEN"}


def _bib_escape(text: str) -> str:
    return re.sub(r"([{}%&$#_])", r"\\\1", text or "")


def bibtex_key(rec: dict, used: set) -> str:
    family = (rec.get("authors") or [{}])[0].get("family", "") or "anon"
    base = re.sub(r"[^A-Za-z0-9]", "", unicodedata.normalize("NFKD", fold(family))) or "anon"
    word = next((w for w in re.findall(r"\w+", fold(rec.get("title", ""))) if len(w) > 3), "")
    key = f"{base}{rec.get('year', '')}{word}"
    candidate, n = key, 1
    while candidate in used:
        n += 1
        candidate = f"{key}{chr(96 + n)}"
    used.add(candidate)
    return candidate


def to_bibtex(records) -> str:
    out, used = [], set()
    for rec in records:
        kind = _BIB_TYPES.get(rec.get("type"), "misc")
        fields = [("title", rec.get("title")),
                  ("author", " and ".join(f"{p.get('family', '')}, {p.get('given', '')}".strip(", ")
                                          for p in rec.get("authors") or [])),
                  ("editor", " and ".join(f"{p.get('family', '')}, {p.get('given', '')}".strip(", ")
                                          for p in rec.get("editors") or [])),
                  ("year", rec.get("year"))]
        container = rec.get("container")
        if kind == "article":
            fields.append(("journal", container))
        elif kind in ("incollection", "inproceedings"):
            fields.append(("booktitle", container))
        fields += [("volume", rec.get("volume")), ("number", rec.get("issue")),
                   ("pages", (rec.get("pages") or "").replace("–", "--")),
                   ("publisher", rec.get("publisher")),
                   ("school", rec.get("institution") if kind.endswith("thesis") else ""),
                   ("doi", rec.get("doi")), ("url", rec.get("url")), ("language", rec.get("language")),
                   ("keywords", ", ".join(split_keywords(rec.get("keywords", "")) + list(rec.get("tags") or [])))]
        body = ",\n".join(f"  {k} = {{{_bib_escape(str(v))}}}" for k, v in fields if v)
        out.append(f"@{kind}{{{bibtex_key(rec, used)},\n{body}\n}}")
    return "\n\n".join(out) + "\n"


def to_ris(records) -> str:
    out = []
    for rec in records:
        lines = [f"TY  - {_RIS_TYPES.get(rec.get('type'), 'GEN')}", f"TI  - {rec.get('title', '')}"]
        lines += [f"AU  - {p.get('family', '')}, {p.get('given', '')}".rstrip(", ") for p in rec.get("authors") or []]
        lines += [f"ED  - {p.get('family', '')}, {p.get('given', '')}".rstrip(", ") for p in rec.get("editors") or []]
        pages = (rec.get("pages") or "").split("–")
        for tag, value in (("PY", rec.get("year")), ("T2", rec.get("container")), ("VL", rec.get("volume")),
                           ("IS", rec.get("issue")), ("SP", pages[0] if pages[0] else ""),
                           ("EP", pages[1] if len(pages) > 1 else ""), ("PB", rec.get("publisher")),
                           ("DO", rec.get("doi")), ("UR", rec.get("url")), ("LA", rec.get("language"))):
            if value:
                lines.append(f"{tag}  - {value}")
        lines += [f"KW  - {t}" for t in split_keywords(rec.get("keywords", "")) + list(rec.get("tags") or [])]
        lines.append("ER  - ")
        out.append("\n".join(lines))
    return "\n\n".join(out) + "\n"


# ── Tek kütüphane klasörü ───────────────────────────────────────────────────

def library_filename(rec: dict, ext: str = ".pdf") -> str:
    """Kütüphane klasöründeki standart ad: 'Soyad (Yıl) - Başlık.pdf'"""
    people = rec.get("authors") or (rec.get("editors") if rec.get("type") == "book" else None) or []
    who = people[0].get("family", "") if people else ""
    if len(people) > 2:
        who += " vd."
    elif len(people) == 2:
        who += f" ve {people[1].get('family', '')}"
    title = (rec.get("title") or "Başlıksız").strip()
    if len(title) > 110:
        title = title[:110].rsplit(" ", 1)[0] + "…"
    year = rec.get("year") or "t.y."
    name = f"{who} ({year}) - {title}" if who else f"{title} ({year})"
    return sanitize_filename(name + ext)


def place_in_library(path: Path, rec: dict, library_folder, move: bool = True) -> Path:
    """Dosyayı kütüphane klasörüne standart adıyla taşır (ya da kopyalar)."""
    if not library_folder:
        return path
    folder = Path(library_folder)
    folder.mkdir(parents=True, exist_ok=True)
    wanted = library_filename(rec, path.suffix.lower() or ".pdf")
    if path.parent.resolve() == folder.resolve() and path.name == wanted:
        return path
    target = unique_path(folder, wanted)
    if move:
        shutil.move(str(path), str(target))
    else:
        shutil.copy2(str(path), str(target))
    return target


# ── Kurum erişimi (VETİS vb.) ───────────────────────────────────────────────

DEFAULT_INSTITUTION_URL = "https://w3.sakarya.edu.tr/vetisbt/?dil=tr&p=0"
PUBLISHER_DATABASES = {
    "10.2307": "JSTOR", "10.1109": "IEEE Xplore", "10.1093": "Oxford University Press",
    "10.1145": "ACM Digital Library", "10.1007": "Springer", "10.1080": "Taylor & Francis",
    "10.4324": "Taylor & Francis (Routledge)", "10.1177": "SAGE", "10.1111": "Wiley",
    "10.1002": "Wiley", "10.1016": "ScienceDirect (Elsevier)", "10.1017": "Cambridge University Press",
    "10.1057": "Palgrave Macmillan", "10.1515": "De Gruyter", "10.1108": "Emerald",
    "10.1353": "Project MUSE", "10.5465": "Academy of Management", "10.1386": "Intellect",
}


def database_for_doi(doi: str) -> str:
    prefix = (normalize_doi(doi) or "").split("/")[0]
    return PUBLISHER_DATABASES.get(prefix, "")


# ── Katalog veritabanı (SQLite) ─────────────────────────────────────────────

_SCHEMA = """
CREATE TABLE IF NOT EXISTS items (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    title TEXT DEFAULT '', authors TEXT DEFAULT '[]', year TEXT DEFAULT '',
    type TEXT DEFAULT 'other', container TEXT DEFAULT '', volume TEXT DEFAULT '',
    issue TEXT DEFAULT '', pages TEXT DEFAULT '', publisher TEXT DEFAULT '',
    doi TEXT DEFAULT '', url TEXT DEFAULT '', editors TEXT DEFAULT '[]',
    institution TEXT DEFAULT '', language TEXT DEFAULT '',
    file_path TEXT DEFAULT '', sha256 TEXT DEFAULT '', notes TEXT DEFAULT '', added TEXT DEFAULT ''
);
CREATE INDEX IF NOT EXISTS idx_items_sha ON items(sha256);
CREATE INDEX IF NOT EXISTS idx_items_doi ON items(doi);
CREATE TABLE IF NOT EXISTS tags (item_id INTEGER, tag TEXT, PRIMARY KEY (item_id, tag));
CREATE TABLE IF NOT EXISTS fulltext (item_id INTEGER PRIMARY KEY, content TEXT);
CREATE TABLE IF NOT EXISTS cards (
    id INTEGER PRIMARY KEY AUTOINCREMENT, item_id INTEGER, page TEXT DEFAULT '',
    quote TEXT DEFAULT '', comment TEXT DEFAULT '', created TEXT DEFAULT ''
);
CREATE INDEX IF NOT EXISTS idx_cards_item ON cards(item_id);
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);
"""

# Her yazma işleminde meta.change_no bir artar (Claude bağlantısı gibi başka süreçlerin yazdıkları da sayılır).
# Ortak kütüphane 'burada değişti mi?' sorusunu dosyanın tamamını okumadan bununla yanıtlar.
# (Gövdede UPDATE: 'INSERT OR IGNORE' gibi dış komutların çakışma kuralı tetikleyicideki INSERT'i yutabiliyor.)
_CHANGE_TRIGGERS = "INSERT OR IGNORE INTO meta (key, value) VALUES ('change_no', '0');\n" + "".join(
    f"CREATE TRIGGER IF NOT EXISTS degisim_{table}_{op.lower()} AFTER {op} ON {table} BEGIN "
    "UPDATE meta SET value = CAST(value AS INTEGER) + 1 WHERE key='change_no'; END;\n"
    for table in ("items", "tags", "cards", "fulltext") for op in ("INSERT", "UPDATE", "DELETE"))

# Sonradan eklenen sütunlar (eski veritabanları da açılabilsin diye)
_EXTRA_COLUMNS = {
    "is_new": "INTEGER DEFAULT 0",      # haftalık taramadan gelip henüz incelenmedi
    "source": "TEXT DEFAULT ''",        # indirme / tarama / klasör / elle
    "matched": "TEXT DEFAULT ''",       # taramada eşleşen grup ve kelimeler
    "keywords": "TEXT DEFAULT ''",      # makalenin kendi anahtar kelimeleri ('; ' ile)
    "issn": "TEXT DEFAULT ''",          # derginin ISSN'leri ('1234-5678; 2345-6789'), Scopus eşleştirmesi için
    "pdf_tried": "TEXT DEFAULT ''",     # PDF'siz kaynak için en son ne zaman PDF arandı (YYYY-AA-GG)
    "no": "INTEGER DEFAULT 0",          # kayıt numarası: 1, 2, 3… (eklenme sırası, hiç değişmez)
    "ai_ozet": "TEXT DEFAULT ''",       # Claude'un kaynağı okuyup kaydettiği yapılandırılmış özet
}


_NO_RANGE_RE = re.compile(r"^\s*(?:#|no\b[:.]?)?\s*(\d{1,6})\s*(?:[-–—]|\.\.)\s*(\d{1,6})\s*$", re.I)
_NO_ONE_RE = re.compile(r"^\s*(?:#|no\b[:.]?)\s*(\d{1,6})\s*$", re.I)


def parse_no_range(text):
    """'120-220', '#120-220', 'No 120–220' ya da '#57' → (alt, üst); değilse None."""
    text = text or ""
    m = _NO_RANGE_RE.match(text)
    if m:
        lo, hi = int(m.group(1)), int(m.group(2))
        return (min(lo, hi), max(lo, hi))
    m = _NO_ONE_RE.match(text)
    if m:
        return (int(m.group(1)), int(m.group(1)))
    return None


def no_ranges_text(numbers, limit=None) -> str:
    """[3, 4, 5, 9, 12, 13] → '3–5, 9, 12–13' (çok uzunsa '…' ile kısaltır)."""
    nums = sorted({int(n) for n in numbers if n})
    parts, i = [], 0
    while i < len(nums):
        j = i
        while j + 1 < len(nums) and nums[j + 1] == nums[j] + 1:
            j += 1
        parts.append(str(nums[i]) if i == j else f"{nums[i]}–{nums[j]}")
        i = j + 1
    if limit and len(parts) > limit:
        return ", ".join(parts[:limit]) + " …"
    return ", ".join(parts)


def snapshot_db(src_path, dest_path) -> int:
    dest_path = Path(dest_path)
    dest_path.parent.mkdir(parents=True, exist_ok=True)
    if dest_path.exists():
        dest_path.unlink()
    src = sqlite3.connect(f"file:{Path(src_path).as_posix()}?mode=ro", uri=True, timeout=60)
    dest = sqlite3.connect(str(dest_path))
    try:
        src.backup(dest)
        row = dest.execute("SELECT value FROM meta WHERE key='change_no'").fetchone() if dest.execute(
            "SELECT 1 FROM sqlite_master WHERE name='meta'").fetchone() else None
    finally:
        dest.close()
        src.close()
    try:
        return int(row[0]) if row else 0
    except ValueError:
        return 0


def clean_tags(text_or_list) -> list:
    items = text_or_list if isinstance(text_or_list, (list, tuple)) else re.split(r"[,;\n]", text_or_list or "")
    seen, out = set(), []
    for tag in items:
        tag = re.sub(r"\s+", " ", str(tag)).strip()
        if tag and fold(tag) not in seen:
            seen.add(fold(tag))
            out.append(tag)
    return out


_EXISTS_CACHE = {}


def file_exists_cached(path, ttl_found=300, ttl_missing=20) -> bool:
    """Dosya var mı? Sonucu kısa süre saklar: bulut klasöründe yüzlerce dosyayı her seferinde yoklamak
    arayüzü kilitleyebiliyor."""
    if not path:
        return False
    path = str(path)
    now = time.monotonic()
    hit = _EXISTS_CACHE.get(path)
    if hit and now - hit[1] < (ttl_found if hit[0] else ttl_missing):
        return hit[0]
    try:
        ok = os.path.isfile(path)
    except OSError:
        ok = False
    _EXISTS_CACHE[path] = (ok, now)
    return ok


def forget_exists_cache():
    _EXISTS_CACHE.clear()


def file_exists_known(path, ttl_found=300, ttl_missing=20):
    """Önbellekteki sonuç (yoklamadan). Dönüş: (var_mı ya da None, eskimiş_mi)"""
    hit = _EXISTS_CACHE.get(str(path)) if path else None
    if not hit:
        return None, True
    return hit[0], time.monotonic() - hit[1] >= (ttl_found if hit[0] else ttl_missing)


class Library:
    """Kaynakların künyesi, etiketleri, notları ve PDF tam metni (dosyalar yerinde kalır)."""

    def __init__(self, path=None, root=None, relative=None):
        self.path = Path(path) if path else settings_path().parent / "kutuphane.db"
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.lock = threading.RLock()
        self.db = sqlite3.connect(str(self.path), check_same_thread=False, timeout=30)
        self.db.row_factory = sqlite3.Row
        self._ensure_schema()
        self.configure_paths(root, relative)

    def _ensure_schema(self):
        with self.lock, self.db:
            self.db.executescript(_SCHEMA)
            self.db.executescript(_CHANGE_TRIGGERS)
            have = {r[1] for r in self.db.execute("PRAGMA table_info(items)")}
            for column, decl in _EXTRA_COLUMNS.items():
                if column not in have:
                    self.db.execute(f"ALTER TABLE items ADD COLUMN {column} {decl}")
            self._number_items()

    def _number_items(self):
        """Numarasız (ya da başka kayıtla aynı numaralı) kaynaklara sıradaki numarayı verir.
        Eski kütüphanelerde numaralar eklenme sırasına göre 1'den başlar; verilen numara bir daha değişmez."""
        seen, fix = set(), []
        for item_id, no in self.db.execute("SELECT id, no FROM items ORDER BY added, id"):
            if no and no > 0 and no not in seen:
                seen.add(no)
            else:
                fix.append(item_id)
        nxt = max(max(seen, default=0), self._last_no())
        for item_id in fix:
            nxt += 1
            self.db.execute("UPDATE items SET no=? WHERE id=?", (nxt, item_id))
        if fix:
            self.db.execute("INSERT OR REPLACE INTO meta (key, value) VALUES ('last_no', ?)", (str(nxt),))

    def change_no(self) -> int:
        """Veritabanına şimdiye kadar yapılan yazma sayısı (eşitleme için)."""
        with self.lock:
            row = self.db.execute("SELECT value FROM meta WHERE key='change_no'").fetchone()
        try:
            return int(row[0]) if row else 0
        except ValueError:
            return 0

    def _last_no(self) -> int:
        """Şimdiye kadar verilmiş en büyük numara (silinen kaynakların numarası bir daha verilmez)."""
        row = self.db.execute("SELECT value FROM meta WHERE key='last_no'").fetchone()
        try:
            return int(row[0]) if row else 0
        except ValueError:
            return 0

    # --- PDF yolları: ortak kütüphanede kütüphane klasörüne göre (göreli) saklanır -----------
    def configure_paths(self, root=None, relative=None):
        settings = load_settings() if root is None or relative is None else {}
        root = root if root is not None else settings.get("library_folder")
        self.root = Path(root) if root else None
        self.relative = bool(settings.get("shared_library")) if relative is None else bool(relative)

    def _abs(self, stored):
        if not stored:
            return stored or ""
        if not os.path.isabs(stored):
            return str(self.root / stored) if self.root else stored
        if not self.root:
            return stored
        alt = self.root / Path(stored.replace("\\", "/")).name   # başka bilgisayardan kalma mutlak yol
        if threading.current_thread() is threading.main_thread():
            # arayüz bulutu beklemesin: yalnızca bilinen sonuçlar; bilinmeyenleri liste arka planda yoklar
            ok, _ = file_exists_known(stored)
            if ok is None or ok:
                return stored
            alt_ok, _ = file_exists_known(alt)
            return str(alt) if alt_ok is None or alt_ok else stored
        if not file_exists_cached(stored) and file_exists_cached(alt):
            return str(alt)
        return stored

    def _stored(self, path) -> str:
        if not path:
            return ""
        path = str(path)
        if self.relative and self.root and os.path.isabs(path):
            root = os.path.normcase(os.path.abspath(str(self.root))).rstrip("\\/")
            full = os.path.normcase(os.path.abspath(path))
            if full.startswith(root + os.sep):
                return Path(os.path.relpath(os.path.abspath(path), os.path.abspath(str(self.root)))).as_posix()
        return path

    def relativize_paths(self) -> int:
        """Kütüphane klasöründeki PDF'lerin yollarını göreli yapar (ortak kütüphaneye geçerken)."""
        changed = 0
        with self.lock, self.db:
            for item_id, fp in self.db.execute("SELECT id, file_path FROM items WHERE file_path!=''").fetchall():
                new = self._stored(self._abs(fp))
                if new != fp:
                    self.db.execute("UPDATE items SET file_path=? WHERE id=?", (new, item_id))
                    changed += 1
        return changed

    # --- ortak kütüphane: anlık kopya al/ver, birleştir --------------------------------
    def backup_to(self, path):
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        dest = sqlite3.connect(str(path))
        try:
            with self.lock:
                self.db.commit()
                self.db.backup(dest)
        finally:
            dest.close()

    def snapshot_to(self, path) -> int:
        """Veritabanının anlık kopyasını AYRI bir bağlantıyla alır (arayüzün kullandığı kilidi tutmaz).
        Dönüş: kopyadaki değişiklik sayacı."""
        return snapshot_db(self.path, path)

    def restore_from(self, path):
        src = sqlite3.connect(f"file:{Path(path).as_posix()}?mode=ro", uri=True)
        try:
            with self.lock:
                self.db.commit()
                src.backup(self.db)
        finally:
            src.close()
        self._ensure_schema()

    def merge_from(self, other) -> tuple:
        """Diğer kütüphanedeki kaynakları ekler; ortak olanlarda etiketleri, kartları ve boş alanları
        birleştirir. Dönüş: (eklenen, güncellenen)"""
        added = updated = 0
        for item in other.all_items():
            target = (self.find_by_sha(item["sha256"]) if item.get("sha256") else None) \
                or self.find_by_doi(item["doi"]) or self.find_by_title(item["title"])
            if target is None:
                rec = {k: item.get(k) for k in RECORD_FIELDS}
                with self.lock, self.db:
                    target, _ = self.add(rec, file_path=item["file_path"] or None, sha=item.get("sha256") or "",
                                         tags=item["tags"], source=item.get("source") or "",
                                         is_new=bool(item.get("is_new")), matched=item.get("matched") or "")
                    self.db.execute("UPDATE items SET added=?, notes=? WHERE id=?",
                                    (item.get("added") or "", item.get("notes") or "", target))
                added += 1
            else:
                mine = self.get(target)
                fill = {k: item[k] for k in RECORD_FIELDS if not mine.get(k) and item.get(k)}
                if not (mine["file_path"] and os.path.exists(mine["file_path"])) and item["file_path"] \
                        and os.path.exists(item["file_path"]):
                    fill.update(file_path=item["file_path"], sha256=item.get("sha256") or "")
                if fill:
                    self.update(target, fill)
                before = len(mine["tags"])
                self.add_tags(target, item["tags"])
                if len(self.get(target)["tags"]) != before or fill:
                    updated += 1
            have = {fold(c["quote"]) + "|" + c["page"] for c in self.cards(target)}
            for c in other.cards(item["id"]):
                if fold(c["quote"]) + "|" + c["page"] not in have:
                    self.add_card(target, c["page"], c["quote"], c["comment"])
            with self.lock:
                row = other.db.execute("SELECT content FROM fulltext WHERE item_id=?", (item["id"],)).fetchone()
                mine_ft = self.db.execute("SELECT 1 FROM fulltext WHERE item_id=?", (target,)).fetchone()
            if row and row[0] and not mine_ft:
                with self.lock, self.db:
                    self.db.execute("INSERT OR REPLACE INTO fulltext (item_id, content) VALUES (?, ?)",
                                    (target, row[0]))
        return added, updated

    # --- okuma ---------------------------------------------------------------
    def _to_item(self, row) -> dict:
        item = dict(row)
        for key in ("authors", "editors"):
            try:
                item[key] = json.loads(item[key] or "[]")
            except ValueError:
                item[key] = []
        if "file_path" in item:
            item["file_path"] = self._abs(item["file_path"])
        return item

    # Dosya yoklamaları (_to_item → _abs) kilidin DIŞINDA yapılır: bulut klasörü yavaşken arayüz beklemesin.
    def get(self, item_id: int):
        with self.lock:
            row = self.db.execute("SELECT * FROM items WHERE id=?", (item_id,)).fetchone()
            if not row:
                return None
            tags = [r[0] for r in self.db.execute("SELECT tag FROM tags WHERE item_id=?", (item_id,))]
        item = self._to_item(row)
        item["tags"] = sorted(tags, key=tr_sort_key)
        return item

    def all_items(self) -> list:
        with self.lock:
            rows = self.db.execute("SELECT * FROM items").fetchall()
            tag_rows = self.db.execute("SELECT item_id, tag FROM tags ORDER BY tag").fetchall()
        items = {row["id"]: self._to_item(row) for row in rows}
        for item in items.values():
            item["tags"] = []
        for item_id, tag in tag_rows:
            if item_id in items:
                items[item_id]["tags"].append(tag)
        return list(items.values())

    def all_tags(self) -> list:
        with self.lock:
            tags = [r[0] for r in self.db.execute("SELECT DISTINCT tag FROM tags")]
        return sorted(tags, key=tr_sort_key)

    def count(self) -> int:
        with self.lock:
            return self.db.execute("SELECT COUNT(*) FROM items").fetchone()[0]

    def find_by_sha(self, sha: str):
        with self.lock:
            row = self.db.execute("SELECT id FROM items WHERE sha256=? AND sha256!=''", (sha,)).fetchone()
        return row[0] if row else None

    def find_by_doi(self, doi: str):
        doi = normalize_doi(doi)
        if not doi:
            return None
        with self.lock:
            row = self.db.execute("SELECT id FROM items WHERE lower(doi)=?", (doi.lower(),)).fetchone()
        return row[0] if row else None

    def find_by_url(self, url: str):
        if not url:
            return None
        with self.lock:
            row = self.db.execute("SELECT id FROM items WHERE url=?", (url,)).fetchone()
        return row[0] if row else None

    def find_by_title(self, title: str):
        key = re.sub(r"\W+", " ", fold(title or "")).strip()
        if len(key) < 12:
            return None
        with self.lock:
            rows = self.db.execute("SELECT id, title FROM items").fetchall()
        for item_id, other in rows:
            if re.sub(r"\W+", " ", fold(other or "")).strip() == key:
                return item_id
        return None

    def find_by_tez_no(self, tez_no: str):
        with self.lock:
            row = self.db.execute("SELECT id FROM items WHERE notes LIKE ?", (f"%YÖK Tez No: {tez_no}%",)).fetchone()
        return row[0] if row else None

    def find_by_path(self, path):
        with self.lock:
            row = self.db.execute("SELECT id FROM items WHERE file_path IN (?, ?)",
                                  (str(path), self._stored(path))).fetchone()
        return row[0] if row else None

    def fulltext_ids(self, words) -> set:
        words = [fold(w) for w in words if w.strip()]
        if not words:
            return set()
        sql = "SELECT item_id FROM fulltext WHERE " + " AND ".join(["instr(content, ?) > 0"] * len(words))
        with self.lock:
            return {r[0] for r in self.db.execute(sql, words)}

    # --- yazma ---------------------------------------------------------------
    def add(self, record: dict, file_path=None, sha="", fulltext="", tags=(), source="",
            is_new=False, matched=""):
        """Kaynağı ekler. Aynı dosya (sha256) ya da aynı DOI zaten varsa onu günceller.
        Dönüş: (kimlik, yeni_mi)"""
        rec = finalize_record(record)
        with self.lock, self.db:
            existing = (self.find_by_sha(sha) if sha else None) or self.find_by_doi(rec["doi"])
            if existing:
                old = self.get(existing)
                updates = {}
                if file_path and (not old["file_path"] or not Path(old["file_path"]).is_file()):
                    updates.update(file_path=str(file_path), sha256=sha)
                for field in RECORD_FIELDS:          # boş alanları doldur, dolu olanlara dokunma
                    if not old.get(field) and rec.get(field):
                        updates[field] = rec[field]
                if updates:
                    self.update(existing, updates)
                if fulltext and updates.get("file_path"):
                    self.set_fulltext(existing, fulltext)
                self.add_tags(existing, tags)
                return existing, False
            cur = self.db.execute(
                "INSERT INTO items (title, authors, year, type, container, volume, issue, pages, "
                "publisher, doi, url, editors, institution, language, file_path, sha256, added, "
                "source, is_new, matched, keywords, issn, no) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (rec["title"], json.dumps(rec["authors"], ensure_ascii=False), rec["year"], rec["type"],
                 rec["container"], rec["volume"], rec["issue"], rec["pages"], rec["publisher"],
                 rec["doi"], rec["url"], json.dumps(rec["editors"], ensure_ascii=False),
                 rec["institution"], rec["language"], self._stored(file_path), sha,
                 datetime.now().strftime("%Y-%m-%d"), source, 1 if is_new else 0, matched,
                 rec["keywords"], rec["issn"],
                 max(self.db.execute("SELECT COALESCE(MAX(no), 0) FROM items").fetchone()[0], self._last_no()) + 1))
            item_id = cur.lastrowid
            self.db.execute("INSERT OR REPLACE INTO meta (key, value) VALUES ('last_no', "
                            "(SELECT MAX(no) FROM items WHERE id=?))", (item_id,))
            if fulltext:
                self.set_fulltext(item_id, fulltext)
            self.add_tags(item_id, tags)
            return item_id, True

    def get_fulltext(self, item_id) -> str:
        with self.lock:
            row = self.db.execute("SELECT content FROM fulltext WHERE item_id=?", (item_id,)).fetchone()
        return row[0] if row and row[0] else ""

    def fulltext_heads(self, ids, chars=5000) -> dict:
        """Kayıtların saklı (katlanmış) metninin başı: {kimlik: metin}. Mükerrer tespiti için."""
        wanted = set(ids)
        with self.lock:
            rows = self.db.execute("SELECT item_id, substr(content, 1, ?) FROM fulltext", (int(chars),)).fetchall()
        return {i: t for i, t in rows if i in wanted and t}

    def merge_items(self, keeper_id, other_ids, library_folder=None) -> int:
        """Mükerrer kayıtları birleştirir: etiketler, kartlar, boş alanlar, Claude özeti ve (gerekirse) PDF
        tutulan kayda geçer; öbürleri silinir. Fazla PDF kopyaları silinmez, 'Mükerrer PDF'ler' klasörüne taşınır."""
        keeper = self.get(keeper_id)
        moved = 0
        spare_dir = Path(library_folder) / "Mükerrer PDF'ler (silinebilir)" if library_folder else None
        for oid in other_ids:
            other = self.get(oid)
            if not other or oid == keeper_id:
                continue
            fill = {k: other[k] for k in RECORD_FIELDS if other.get(k) and not keeper.get(k)}
            keeper_has_file = keeper["file_path"] and os.path.isfile(keeper["file_path"])
            if not keeper_has_file and other["file_path"] and os.path.isfile(other["file_path"]):
                fill.update(file_path=other["file_path"], sha256=other.get("sha256") or "")
                with self.lock:
                    row = self.db.execute("SELECT content FROM fulltext WHERE item_id=?", (oid,)).fetchone()
                if row and row[0]:
                    self.set_fulltext(keeper_id, row[0])
            elif other["file_path"] and os.path.isfile(other["file_path"]) and spare_dir and \
                    os.path.normcase(other["file_path"]) != os.path.normcase(keeper["file_path"] or ""):
                try:
                    spare_dir.mkdir(parents=True, exist_ok=True)
                    shutil.move(other["file_path"], str(unique_path(spare_dir, Path(other["file_path"]).name)))
                    moved += 1
                except OSError:
                    pass
            if len(other.get("ai_ozet") or "") > len(keeper.get("ai_ozet") or ""):
                fill["ai_ozet"] = other["ai_ozet"]
            if other.get("notes") and other["notes"] not in (keeper.get("notes") or ""):
                fill["notes"] = "\n".join(filter(None, [keeper.get("notes"), other["notes"]]))
            if fill:
                self.update(keeper_id, fill)
                keeper = self.get(keeper_id)
            self.add_tags(keeper_id, other["tags"])
            with self.lock, self.db:
                self.db.execute("UPDATE cards SET item_id=? WHERE item_id=?", (keeper_id, oid))
            self.delete(oid)
        return moved

    def mark_reviewed(self, ids):
        """'Yeni' işaretini kaldırır (tek işlemde, binlerce kaynak için de hızlı)."""
        with self.lock, self.db:
            self.db.executemany("UPDATE items SET is_new=0 WHERE id=? AND is_new!=0", [(int(i),) for i in ids])

    def update(self, item_id: int, fields: dict):
        allowed = set(RECORD_FIELDS) | {"file_path", "sha256", "notes", "is_new", "source", "matched", "pdf_tried",
                                        "ai_ozet"}
        values = {}
        for key, value in fields.items():
            if key not in allowed:
                continue
            values[key] = json.dumps(value, ensure_ascii=False) if key in ("authors", "editors") else value
            if key == "file_path":
                values[key] = self._stored(value)
        if not values:
            return
        with self.lock, self.db:
            sets = ", ".join(f"{k}=?" for k in values)
            self.db.execute(f"UPDATE items SET {sets} WHERE id=?", (*values.values(), item_id))

    def set_tags(self, item_id: int, tags):
        with self.lock, self.db:
            self.db.execute("DELETE FROM tags WHERE item_id=?", (item_id,))
            self.add_tags(item_id, tags)

    def add_tags(self, item_id: int, tags):
        """Etiket ekler; 'miras' ile 'Miras' aynı sayılır, var olan yazım korunur."""
        with self.lock, self.db:
            spelling = {fold(t): t for (t,) in self.db.execute("SELECT DISTINCT tag FROM tags")}
            have = {fold(t) for (t,) in self.db.execute("SELECT tag FROM tags WHERE item_id=?", (item_id,))}
            rows = []
            for tag in clean_tags(tags):
                if fold(tag) not in have:
                    rows.append((item_id, spelling.get(fold(tag), tag)))
                    have.add(fold(tag))
            self.db.executemany("INSERT OR IGNORE INTO tags (item_id, tag) VALUES (?, ?)", rows)

    def set_fulltext(self, item_id: int, text: str):
        with self.lock, self.db:
            self.db.execute("INSERT OR REPLACE INTO fulltext (item_id, content) VALUES (?, ?)",
                            (item_id, fold(text)[:FULLTEXT_MAX_CHARS]))

    def delete(self, item_id: int):
        with self.lock, self.db:
            for table, col in (("items", "id"), ("tags", "item_id"), ("fulltext", "item_id"),
                               ("cards", "item_id")):
                self.db.execute(f"DELETE FROM {table} WHERE {col}=?", (item_id,))

    # --- alıntı kartları ---------------------------------------------------------
    def cards(self, item_id: int) -> list:
        with self.lock:
            return [dict(r) for r in self.db.execute(
                "SELECT * FROM cards WHERE item_id=? ORDER BY id", (item_id,))]

    def card_counts(self) -> dict:
        with self.lock:
            return dict(self.db.execute("SELECT item_id, COUNT(*) FROM cards GROUP BY item_id").fetchall())

    def add_card(self, item_id: int, page: str, quote: str, comment: str) -> int:
        with self.lock, self.db:
            cur = self.db.execute(
                "INSERT INTO cards (item_id, page, quote, comment, created) VALUES (?,?,?,?,?)",
                (item_id, page.strip(), quote.strip(), comment.strip(), datetime.now().strftime("%Y-%m-%d")))
            return cur.lastrowid

    def update_card(self, card_id: int, page: str, quote: str, comment: str):
        with self.lock, self.db:
            self.db.execute("UPDATE cards SET page=?, quote=?, comment=? WHERE id=?",
                            (page.strip(), quote.strip(), comment.strip(), card_id))

    def delete_card(self, card_id: int):
        with self.lock, self.db:
            self.db.execute("DELETE FROM cards WHERE id=?", (card_id,))

    def card_text_ids(self, words) -> set:
        """Kart metinlerinde (alıntı + yorum) geçen kelimelere göre kaynak kimlikleri."""
        words = [fold(w) for w in words if w.strip()]
        if not words:
            return set()
        hits = {}
        with self.lock:
            for item_id, text in self.db.execute("SELECT item_id, quote || ' ' || comment FROM cards"):
                hits.setdefault(item_id, []).append(fold(text))
        return {i for i, texts in hits.items() if all(any(w in t for t in texts) for w in words)}

    def items_added_since(self, date: str) -> list:
        with self.lock:
            ids = [r[0] for r in self.db.execute("SELECT id FROM items WHERE added >= ? ORDER BY id", (date,))]
        return [self.get(i) for i in ids]

    def items_without_file(self) -> list:
        return [i for i in self.all_items() if not i["file_path"] or not Path(i["file_path"]).is_file()]

    def close(self):
        with self.lock:
            self.db.close()


def catalog_pdf(library, session, path: Path, sha: str, meta=None, url="", doi=None,
                tags=(), log=None, library_folder=None, move=True, source="", is_new=False,
                matched="", auto_tags=None, known=None):
    """İndirilen ya da taranan bir PDF'i künyesiyle kütüphaneye ekler; dosyayı kütüphane
    klasörüne 'Soyad (Yıl) - Başlık.pdf' adıyla yerleştirir. Dönüş: (kimlik, yeni_mi)"""
    path = Path(path)
    head = pdf_text(path, max_pages=2, max_chars=20_000)
    page_rec = record_from_meta(meta, url) if meta else {}
    doi = doi or (page_rec.get("doi") if page_rec else None)
    from_pdf_doi = False
    if not doi:
        m = DOI_RE.search(head)
        if m:
            doi, from_pdf_doi = clean_url(m.group(1)), True
    cr = crossref_record(session, doi) if doi and session is not None else None
    if cr and from_pdf_doi and not title_matches_text(cr.get("title", ""), head):
        cr = None                                    # PDF'teki DOI başka bir yayına ait
        doi = None
    file_rec = record_from_filename(path.stem)
    book = book_like_record(session, path) if not (cr or page_rec.get("title") or (known or {}).get("title")) else {}
    if book.get("title"):
        file_rec = {}                                  # 'bildiri-kitabi_96567' gibi dosya adları başlık olmasın
    info = pdf_info(path) if not (cr or page_rec.get("title") or book.get("title")) else {}
    info_rec = {}
    if info.get("title") and len(info["title"]) > 10 and not re.search(r"\.docx?$|untitled|microsoft", info["title"], re.I):
        info_rec = {"title": info["title"], "authors": text_to_people(info.get("author", ""))}
    record = merge_records(cr or {}, merge_records(known or {}, merge_records(page_rec, merge_records(
        book, merge_records(file_rec if " - " in path.stem else {}, merge_records(info_rec, file_rec))))))
    if doi and not record.get("doi"):
        record["doi"] = doi
    if url and not record.get("url") and not is_doi_host(url):
        record["url"] = url
    if not record.get("keywords"):
        record["keywords"] = join_keywords(extract_keywords_from_text(head))
    tags = list(tags) + auto_group_tags(record, head, auto_tags)
    # Aynı dosya ya da DOI dosyasıyla birlikte zaten kütüphanedeyse taşımadan işaretle
    existing = library.find_by_sha(sha) or library.find_by_doi(record.get("doi"))
    if existing:
        old = library.get(existing)
        if old and old["file_path"] and Path(old["file_path"]).is_file():
            library.add_tags(existing, tags)
            if log:
                log("muted", f"   📚 Zaten kütüphanede: {Path(old['file_path']).name}")
            return existing, False
    try:
        path = place_in_library(path, finalize_record(record), library_folder, move=move)
    except OSError as exc:
        if log:
            log("warn", f"   ⚠ Kütüphane klasörüne taşınamadı: {describe_error(exc)}")
    fulltext = pdf_text(path)
    item_id, created = library.add(record, path, sha, fulltext, tags, source=source,
                                   is_new=is_new, matched=matched)
    if log:
        source = "Crossref" if cr else "makale sayfası" if page_rec.get("title") else "dosya adı/PDF"
        log("muted", f"   📚 Kütüphaneye {'eklendi' if created else 'işlendi'} (künye: {source})")
    return item_id, created


def report_links_in(folder: Path) -> dict:
    """Klasördeki indirme raporlarından {dosya adı: link} eşlemesi."""
    links = {}
    for report in sorted(folder.glob(REPORT_GLOB)):
        try:
            with open(report, encoding="utf-8-sig", newline="") as fh:
                for row in list(csv.reader(fh, delimiter=";"))[1:]:
                    if len(row) >= 4 and row[3] and row[1].startswith("http"):
                        links[row[3]] = row[1]
        except (OSError, csv.Error, UnicodeDecodeError):
            continue
    return links


class CompleteWorker(threading.Thread):
    """Eksik künye alanlarını tamamlar. Mesajlar: ("complete", sıra, toplam, başlık, no) ·
    ("complete_done", güncellenen_nolar, alan_sayıları, denenen, durduruldu_mu)"""

    def __init__(self, items, library, events):
        super().__init__(daemon=True)
        self.items = sorted(items, key=lambda i: i.get("no") or 0)
        self.library, self.events = library, events
        self.cancel = threading.Event()

    def run(self):
        updated, counts, tried = [], {}, 0
        session = make_session()
        try:
            for n, item in enumerate(self.items):
                if self.cancel.is_set():
                    break
                self.events.put(("complete", n, len(self.items), item["title"], item.get("no") or 0))
                current = self.library.get(item["id"])
                if not current:
                    continue
                tried += 1
                try:
                    changes = complete_record(session, current)
                except Exception as exc:
                    diag(f"künye tamamlama: {item['title'][:60]}: {describe_error(exc)}")
                    continue
                if changes.get("doi") and self.library.find_by_doi(changes["doi"]) not in (None, item["id"]):
                    changes.pop("doi")                       # aynı DOI başka kayıtta: ikilenmesin
                if changes:
                    self.library.update(item["id"], changes)
                    updated.append(item.get("no") or 0)
                    for key in changes:
                        counts[key] = counts.get(key, 0) + 1
        finally:
            session.close()
            self.events.put(("complete_done", updated, counts, tried, self.cancel.is_set()))


class ThesisCleanupWorker(threading.Thread):
    """Kütüphanedeki PDF'siz YÖK tezlerini Tez Merkezi'nde yeniden yoklar: PDF'i sonradan açılmışsa indirip
    bağlar, açılmamışsa çıkarılacaklar listesine koyar (silme kararı kullanıcıda).
    Mesajlar: ("thesis_check", sıra, toplam) · ("thesis_check_done", kapalılar, indirilen, hata_sayısı, durduruldu)"""

    def __init__(self, items, library, events, library_folder):
        super().__init__(daemon=True)
        self.items, self.library, self.events, self.library_folder = items, library, events, library_folder
        self.cancel = threading.Event()

    def run(self):
        closed, attached, errors = [], 0, 0
        session = make_session()
        try:
            yok_open_session(session)
            for n, item in enumerate(self.items):
                if self.cancel.is_set():
                    break
                self.events.put(("thesis_check", n, len(self.items)))
                tez = yok_tez_no(item)
                try:
                    hits = [r for r in search_yok(session, tez) if r.get("tez_no") == tez]
                    time.sleep(YOK_PAUSE)
                    if not hits:                       # Tez Merkezi'nde bulunamadı: dokunma
                        continue
                    url = yok_pdf_url(session, hits[0]["yok_keys"])
                    time.sleep(YOK_PAUSE)
                    if not url:
                        closed.append(item)
                        continue
                    if self.library_folder:
                        tmp = Path(self.library_folder) / f".yok_{tez}.part"
                        with session.get(url, stream=True, timeout=(15, 180)) as r:
                            r.raise_for_status()
                            with open(tmp, "wb") as fh:
                                for block in r.iter_content(1 << 16):
                                    fh.write(block)
                        if tmp.read_bytes()[:1024].find(b"%PDF-") >= 0:
                            attach_pdf(self.library, item["id"], tmp, self.library_folder, move=True)
                            attached += 1
                        else:
                            tmp.unlink(missing_ok=True)
                        time.sleep(YOK_PAUSE)
                except Exception as exc:
                    errors += 1
                    diag(f"tez denetimi {tez}: {describe_error(exc)}")
        except Exception:
            diag_exception("tez denetimi")
        finally:
            session.close()
            self.events.put(("thesis_check_done", closed, attached, errors, self.cancel.is_set()))


class AutoTagWorker(threading.Thread):
    """Kütüphanedeki kaynaklara anahtar kelime (PDF'ten) ve grup etiketi ekler; elle verilen
    etiketlere dokunmaz. Mesajlar: ("autotag", sıra, toplam) · ("autotag_done", taranan, etiketlenen, kelime_eklenen)"""

    def __init__(self, library, events, item_ids=None):
        super().__init__(daemon=True)
        self.library = library
        self.events = events
        self.item_ids = item_ids

    def run(self):
        items = self.library.all_items()
        if self.item_ids is not None:
            items = [i for i in items if i["id"] in set(self.item_ids)]
        tagged = kw_added = 0
        for n, item in enumerate(items, start=1):
            self.events.put(("autotag", n, len(items)))
            try:
                head = ""
                path = Path(item["file_path"]) if item["file_path"] else None
                if path and path.is_file():
                    head = pdf_text(path, max_pages=3, max_chars=30_000)
                if not item.get("keywords") and head:
                    kws = join_keywords(extract_keywords_from_text(head))
                    if kws:
                        self.library.update(item["id"], {"keywords": kws})
                        item["keywords"] = kws
                        kw_added += 1
                groups = auto_group_tags(item, head)
                before = {fold(t) for t in item["tags"]}
                if any(fold(g) not in before for g in groups):
                    self.library.add_tags(item["id"], groups)
                    tagged += 1
            except Exception:
                diag_exception("otomatik etiketleme")
        self.events.put(("autotag_done", len(items), tagged, kw_added))


class LibraryScanWorker(threading.Thread):
    """Seçilen PDF'leri (ya da bir klasördeki tüm PDF'leri) kütüphaneye alır.
    Mesajlar: ("scan", sıra, toplam, ad) · ("log", seviye, metin) · ("scan_done", eklenen, güncellenen, atlanan)"""

    def __init__(self, paths, library, events, cancel_event, tags=(), library_folder=None, move=False,
                 report_folders=(), auto_tags=None):
        self.auto_tags = auto_tags
        super().__init__(daemon=True)
        self.report_folders = [Path(f) for f in report_folders]
        self.library_folder = library_folder
        self.move = move
        self.paths = [Path(p) for p in paths]
        self.library = library
        self.events = events
        self.cancel = cancel_event
        self.tags = clean_tags(tags)

    def run(self):
        added = updated = skipped = 0
        session = make_session()
        links = {}
        for folder in {p.parent for p in self.paths}:
            links.update({str(folder / name): url for name, url in report_links_in(folder).items()})
        total = len(self.paths)
        try:
            for i, path in enumerate(self.paths, start=1):
                if self.cancel.is_set():
                    break
                self.events.put(("scan", i - 1, total, path.name))
                try:
                    sha = file_sha256(path)
                    existing = self.library.find_by_sha(sha)
                    if existing:
                        old = self.library.get(existing)
                        if old and old["file_path"] != str(path) and not Path(old["file_path"]).is_file():
                            self.library.update(existing, {"file_path": str(path)})
                        self.library.add_tags(existing, self.tags)
                        skipped += 1
                        continue
                    if path.suffix.lower() in EBOOK_EXTS:
                        _, created = catalog_ebook(self.library, session, path, sha, tags=self.tags,
                                                   library_folder=self.library_folder, move=self.move,
                                                   source="klasör", auto_tags=self.auto_tags)
                        added += 1 if created else 0
                        updated += 0 if created else 1
                        continue
                    url = links.get(str(path), "")
                    _, created = catalog_pdf(self.library, session, path, sha, url=url,
                                             doi=doi_from_url(url) if url else None, tags=self.tags,
                                             library_folder=self.library_folder, move=self.move,
                                             source="klasör", auto_tags=self.auto_tags)
                    if created:
                        added += 1
                    else:
                        updated += 1
                except Exception as exc:
                    self.events.put(("log", "error", f"{path.name} eklenemedi: {describe_error(exc)}"))
            pending = self._import_failed_from_reports(session)
        finally:
            session.close()
            self.events.put(("scan", total, total, ""))
            self.events.put(("scan_done", added, updated, skipped, locals().get("pending", 0)))

    def _import_failed_from_reports(self, session) -> int:
        """Eski indirme raporlarında inmemiş görünen kaynakları kütüphaneye PDF'siz kayıt olarak
        ekler; böylece 'PDF'i olmayanlar' listesinden kurum erişimiyle tamamlanabilirler."""
        failed, succeeded = {}, set()
        for folder in self.report_folders:
            for report in sorted(folder.glob(REPORT_GLOB)):
                try:
                    with open(report, encoding="utf-8-sig", newline="") as fh:
                        rows = list(csv.reader(fh, delimiter=";"))[1:]
                except (OSError, csv.Error, UnicodeDecodeError):
                    continue
                for row in rows:
                    if len(row) < 3 or not row[1].startswith("http"):
                        continue
                    key = history_key(row[1])
                    if row[2] in (STATUS_LABELS["ok"], STATUS_LABELS["dup"]):
                        succeeded.add(key)
                    elif row[2] in (STATUS_LABELS["error"], STATUS_LABELS["nopdf"], STATUS_LABELS["html"]):
                        failed[key] = (row[1], row[3] if len(row) > 3 else "")
        added = crossref_failures = 0
        for key, (url, filename) in failed.items():
            if key in succeeded or self.cancel.is_set():
                continue
            doi = doi_from_url(url)
            if self.library.find_by_doi(doi) or self.library.find_by_url(url):
                continue
            record = {}
            if doi and crossref_failures < 3:          # yalnızca bağlantı hataları sayılır
                try:
                    record = crossref_record(session, doi, raise_network_errors=True) or {}
                    crossref_failures = 0
                except requests.RequestException:
                    crossref_failures += 1
            if not record.get("title") and filename and " - " in filename:
                record = merge_records(record, record_from_filename(Path(filename).stem))
            if not record.get("title"):
                continue                     # künyesi bulunamayan linki boş kayıt olarak ekleme
            record["doi"] = record.get("doi") or doi or ""
            record["url"] = url if not doi else record.get("url", "")
            _, created = self.library.add(record, tags=self.tags, source="klasör")
            added += created
        return added


def attach_pdf(library, item_id: int, path, library_folder=None, move=True):
    """PDF'i olmayan bir kaynağa sonradan PDF bağlar (elle ya da İndirilenler izleyiciyle)."""
    item = library.get(item_id)
    path = Path(path)
    sha = file_sha256(path)
    target = place_in_library(path, item, library_folder, move=move)
    library.update(item_id, {"file_path": str(target), "sha256": sha})
    library.set_fulltext(item_id, pdf_text(target))
    return target


# ── Kaydedilmiş web sayfaları (.html): kaynağa çevir, PDF'ini yeniden ara ───────────────

HTML_ARCHIVE_DIR = "Web Sayfaları (eski)"
_NAME_RE = re.compile(r"^(?P<author>.+?) \((?P<year>\d{4}|t\.y\.)\) - (?P<title>.+)$")


def links_from_reports(folder: Path) -> dict:
    """Klasördeki indirme raporlarından dosya adı → link eşlemesi."""
    out = {}
    for report in sorted(Path(folder).glob(REPORT_GLOB)):
        try:
            with open(report, encoding="utf-8-sig", newline="") as fh:
                for row in list(csv.reader(fh, delimiter=";"))[1:]:
                    if len(row) >= 4 and row[1].startswith("http") and row[3]:
                        out[row[3]] = row[1]
        except (OSError, csv.Error, UnicodeDecodeError):
            continue
    return out


def record_from_html_file(path: Path, link: str = "") -> tuple:
    """Kaydedilmiş sayfadan künye. Dönüş: (kayıt, meta, sayfa_adresi)"""
    page = path.read_text(encoding="utf-8", errors="replace")
    meta = parse_citation_meta(page)
    m = re.search(r'<link[^>]+rel=["\']canonical["\'][^>]*href=["\']([^"\']+)', page, re.I) or \
        re.search(r'<meta[^>]+property=["\']og:url["\'][^>]*content=["\']([^"\']+)', page, re.I)
    url = link or (html.unescape(m.group(1)) if m else "")
    if not url:                                    # dergi/kitap sistemlerinde makalenin ya da kitabın sayfası
        m = re.search(r'href=["\'](https?://[^"\']+/(?:article/view|catalog/book|chapter)/[^"\'#?]+)', page, re.I)
        url = html.unescape(m.group(1)) if m else ""
    rec = record_from_meta(meta, url)
    ab = re.search(r'<meta[^>]+name=["\'](?:citation_abstract|dc\.description|description)["\'][^>]*content=["\']([^"\']{80,})',
                   page, re.I)
    rec["_abstract"] = _strip_tags(ab.group(1)) if ab else ""
    nm = _NAME_RE.match(path.stem)
    if nm:                                         # programın verdiği ad: 'Soyad (Yıl) - Başlık'
        if not rec.get("title"):
            rec["title"] = nm.group("title").replace("_", ":").rstrip("…")
        if not rec.get("authors") and nm.group("author") not in ("Yazarsız", "Anonim"):
            rec["authors"] = [{"family": nm.group("author").replace(" vd.", ""), "given": ""}]
        if not rec.get("year") and nm.group("year").isdigit():
            rec["year"] = nm.group("year")
    if not rec.get("title"):
        t = re.search(r"<title[^>]*>(.*?)</title>", page, re.I | re.S)
        rec["title"] = _strip_tags(t.group(1)) if t else path.stem
    return rec, meta, url


class PdfRetryWorker(threading.Thread):
    """PDF'siz kaynakların PDF'ini yeniden arar: açık erişim (Unpaywall), yayıncı sayfası, YÖK Tez.
    Kaynaklar kayıt numarası sırasıyla denenir.
    Mesajlar: ("retry", sıra, toplam, başlık, no) · ("retry_wait", saniye, ertelenen_sayısı) ·
              ("retry_done", bulunan, denenen, durduruldu_mu, bulunan_nolar, denenen_nolar, ertelenen_nolar,
               rapor_yolu)"""

    PAUSE = 2.0                         # yayıncı sunucularını yormamak için kaynaklar arası bekleme

    def __init__(self, items, library, events, library_folder, email="", label=""):
        super().__init__(daemon=True)
        self.items = sorted(items, key=lambda i: (not is_thesis(i), i.get("no") or 0))   # önce tezler (YÖK)
        self.library, self.events, self.library_folder, self.email = library, events, library_folder, email
        self.label = label
        self.cancel = threading.Event()
        self.rows = {}                  # kaynak kimliği → rapor satırı
        self._via = {}

    SECOND_PASS_WAIT = 300              # ertelenenler için en fazla bu kadar beklenir (sn)

    def _note(self, item, outcome):
        row = self.rows.setdefault(item["id"], {"item": item})
        row["outcome"] = outcome or "had"
        if outcome == "found":
            row.update(self._via.get(item["id"], {}))
        elif item["id"] in getattr(self, "_thesis_note", {}):
            row["thesis"] = self._thesis_note[item["id"]]

    def run(self):
        found_nos, tried_nos, deferred = [], [], []
        started = time.monotonic()
        report = None
        try:
            self.session = make_session()
            self.downloader = DownloadWorker([], self.library_folder, {
                "find_pdf": True, "save_html": False, "email": self.email, "library": None,
                "library_folder": self.library_folder}, queue.Queue(), self.cancel)
            self.yses = None
            today = datetime.now().strftime("%Y-%m-%d")
            total = len(self.items)
            for n, item in enumerate(self.items):
                if self.cancel.is_set():
                    break
                self.events.put(("retry", n, total, item["title"], item.get("no") or 0))
                outcome = self._attempt(item, n)
                self._note(item, outcome)
                if outcome is None:
                    continue
                tried_nos.append(item.get("no") or 0)
                if outcome == "found":
                    found_nos.append(item.get("no") or 0)
                if outcome == "limited":
                    deferred.append(item)                       # 'denendi' sayılmaz, sonra yeniden
                else:
                    self.library.update(item["id"], {"pdf_tried": today})
            # istek sınırına takılanlar: siteler dinlenince bir kez daha
            if deferred and not self.cancel.is_set():
                wait = min(max((THROTTLE.cooling(h) for h in list(THROTTLE.cool_until)), default=0),
                           self.SECOND_PASS_WAIT)
                if wait > 0:
                    self.events.put(("retry_wait", int(wait), len(deferred)))
                    self.cancel.wait(wait)
                retry_now, deferred = deferred, []
                for n, item in enumerate(retry_now):
                    if self.cancel.is_set():
                        deferred.extend(retry_now[n:])
                        break
                    self.events.put(("retry", n, len(retry_now), "(ertelenen) " + item["title"],
                                     item.get("no") or 0))
                    outcome = self._attempt(item, n)
                    self._note(item, outcome)
                    if outcome == "found":
                        found_nos.append(item.get("no") or 0)
                    if outcome == "limited":
                        deferred.append(item)
                    elif outcome is not None:
                        self.library.update(item["id"], {"pdf_tried": today})
            self.session.close()
        except Exception:
            diag_exception("PDF yeniden arama")
        try:
            report = write_retry_report(self.library_folder, self.label, [self.rows[k] for k in self.rows],
                                        [i for i in self.items if i["id"] not in self.rows],
                                        time.monotonic() - started, self.cancel.is_set(), bool(self.email),
                                        bool(load_settings().get("core_api_key")))
        except Exception:
            diag_exception("PDF arama raporu")
        self.events.put(("retry_done", len(found_nos), len(tried_nos), self.cancel.is_set(), found_nos,
                         tried_nos, [i.get("no") or 0 for i in deferred], str(report) if report else ""))

    def _attempt(self, item, n):
        """Tek kaynak için PDF arar. Dönüş: None (zaten PDF'i var) · 'found' · 'none' · 'limited'"""
        current = self.library.get(item["id"])
        if not current or (current["file_path"] and os.path.exists(current["file_path"])):
            return None
        THROTTLE.reset_flag()
        self.downloader._tried = set()
        try:
            if is_thesis(current):
                if self._try_yok(current, item):
                    return "found"
            links = (["https://doi.org/" + current["doi"]] if current["doi"] else []) + \
                    ([current["url"]] if current["url"] else [])
            self.downloader._tried = set()
            for link in links:
                self.downloader._last_saved = None
                result = self.downloader._download_one(self.session, link, n)
                if self._take_saved(item, result):
                    return "found"
            if links:
                time.sleep(self.PAUSE)
            if self.cancel.is_set():
                return "none"
            # başka yerlerde (kurum arşivleri, arXiv, Zenodo…) yasal açık kopya
            if self._try_open_copies(current, item, n):
                return "found"
        except Exception as exc:
            diag(f"PDF yeniden arama: {item['title'][:60]}: {describe_error(exc)}")
        return "limited" if THROTTLE.was_limited() else "none"

    def _try_yok(self, current, item) -> bool:
        """Tezi YÖK Tez Merkezi'nden dener: Tez No'yla, yoksa başlıkla bulup Tez No'yu kayda yazar."""
        if not hasattr(self, "_thesis_note"):
            self._thesis_note = {}
        try:
            if self.yses is None:
                self.yses = make_session()
                yok_open_session(self.yses)
            tez = yok_tez_no(current)
            rec = None
            if tez:
                rec = next((r for r in search_yok(self.yses, tez) if r.get("tez_no") == tez), None)
            else:
                rec = find_yok_thesis(self.yses, current)
                if rec and rec.get("tez_no"):
                    tez = rec["tez_no"]
                    self.library.update(item["id"], {"notes": "\n".join(filter(None, [
                        current.get("notes"), f"YÖK Tez No: {tez}"]))})
            time.sleep(YOK_PAUSE)
            if not rec:
                self._thesis_note[item["id"]] = "YÖK Tez Merkezi'nde bulunamadı"
                return False
            tmp, kind, reason = yok_download(self.yses, rec["yok_keys"], self.library_folder, tez or item["id"])
            if tmp:
                placed = attach_pdf(self.library, item["id"], tmp, self.library_folder, move=True)
                self._via[item["id"]] = {"via": "YÖK Tez Merkezi", "file": Path(placed).name}
                return True
            self._thesis_note[item["id"]] = reason
        except Exception as exc:
            self._thesis_note[item["id"]] = "YÖK'e ulaşılamadı: " + describe_error(exc)
            diag(f"YÖK tez arama: {describe_error(exc)}")
        return False

    def _take_saved(self, item, result) -> bool:
        saved = self.downloader._last_saved
        if result and result[0] == "ok" and saved and str(saved["path"]).lower().endswith(".pdf"):
            other = self.library.find_by_sha(saved["sha"])
            if other and other != item["id"]:
                Path(saved["path"]).unlink(missing_ok=True)
                return False
            placed = attach_pdf(self.library, item["id"], saved["path"], self.library_folder, move=True)
            self._via[item["id"]] = {"via": (result[2] if len(result) > 2 else "") or "yayıncı sayfası",
                                     "file": Path(placed).name}
            return True
        return False

    def _try_open_copies(self, current, item, n) -> bool:
        copies = find_open_copies(self.session, current, self.email, load_settings().get("core_api_key", ""))
        cands = copies["pdfs"] + copies["pages"]
        if not cands:
            return False
        first = (current.get("authors") or [{}])[0] or {}
        meta = {"citation_title": current["title"], "citation_author": first.get("family", ""),
                "citation_publication_date": str(current.get("year") or "")}
        self.downloader._last_saved = None
        # DOI ile bulunan PDF bağlantılarına güvenilir; başlıkla bulunanlarda inen PDF'in başlığı denetlenir
        result = self.downloader._try_candidates(
            self.session, cands, None, cands[0], n, meta,
            note="açık erişim kopyası (" + ", ".join(copies["sources"] or ["OpenAlex"]) + ")",
            trusted=copies["trusted"])
        return self._take_saved(item, result)


class HtmlImportWorker(threading.Thread):
    """Klasördeki .html sayfalarını kütüphane kaynağına çevirir, PDF'lerini yeniden arar;
    sayfaları kütüphane klasöründeki 'Web Sayfaları (eski)' klasörüne taşır.
    Mesajlar: ("scan", sıra, toplam, ad) · ("html_done", eklenen, pdf_bulunan, zaten_olan)"""

    def __init__(self, paths, library, events, library_folder, email="", tags=(), auto_tags=None):
        super().__init__(daemon=True)
        self.paths = [Path(p) for p in paths]
        self.library, self.events, self.library_folder = library, events, library_folder
        self.email, self.tags, self.auto_tags = email, list(tags), auto_tags
        self.cancel = threading.Event()

    def run(self):
        added = pdfs = existing = 0
        try:
            session = make_session()
            downloader = DownloadWorker([], self.library_folder, {
                "find_pdf": True, "save_html": False, "email": self.email, "library": None,
                "library_folder": self.library_folder}, queue.Queue(), self.cancel)
            reports = {}
            parsed = []
            for path in self.paths:
                folder = path.parent
                if folder not in reports:
                    reports[folder] = links_from_reports(folder)
                try:
                    parsed.append((path,) + record_from_html_file(path, reports[folder].get(path.name, "")))
                except OSError:
                    continue
            # aynı DOI birden çok sayfada geçiyorsa (dergi sayısının DOI'si gibi) güvenilmez: kullanma
            counts = {}
            for _, rec, _, _ in parsed:
                d = normalize_doi(rec.get("doi"))
                if d:
                    counts[d] = counts.get(d, 0) + 1
            archive = Path(self.library_folder) / HTML_ARCHIVE_DIR
            for n, (path, rec, meta, url) in enumerate(parsed):
                self.events.put(("scan", n, len(parsed), path.name))
                if normalize_doi(rec.get("doi")) and counts.get(normalize_doi(rec["doi"]), 0) > 1:
                    rec["doi"] = ""
                    meta.pop("citation_doi", None)
                    meta.pop("dc.identifier", None)
                known = self.library.find_by_doi(rec.get("doi")) or self.library.find_by_title(rec.get("title"))
                if known:
                    item_id = known
                    existing += 1
                    self.library.add_tags(item_id, self.tags)
                else:
                    abstract = rec.pop("_abstract", "")
                    group_tags = auto_group_tags(rec, abstract[:2500], self.auto_tags)
                    item_id, _ = self.library.add(rec, tags=self.tags + group_tags, source="web sayfası")
                    if abstract:
                        self.library.set_fulltext(item_id, abstract)
                    added += 1
                item = self.library.get(item_id)
                if not (item["file_path"] and os.path.exists(item["file_path"])):
                    links = [meta.get("citation_pdf_url")] + (["https://doi.org/" + rec["doi"]] if rec.get("doi") else []) + [url]
                    for link in [l for l in links if l and l.startswith("http")]:
                        try:
                            downloader._last_saved = None
                            downloader._tried = set()
                            result = downloader._download_one(session, link, n)
                            saved = downloader._last_saved
                            if result[0] == "ok" and saved and str(saved["path"]).lower().endswith(".pdf"):
                                other = self.library.find_by_sha(saved["sha"])
                                if other and other != item_id:
                                    break
                                attach_pdf(self.library, item_id, saved["path"], self.library_folder, move=True)
                                pdfs += 1
                                break
                        except Exception:
                            continue
                    self.library.update(item_id, {"pdf_tried": datetime.now().strftime("%Y-%m-%d")})
                try:
                    archive.mkdir(parents=True, exist_ok=True)
                    if path.parent.resolve() != archive.resolve():
                        shutil.move(str(path), str(unique_path(archive, path.name)))
                except OSError:
                    pass
            session.close()
        except Exception:
            diag_exception("html sayfaları")
        self.events.put(("html_done", added, pdfs, existing))


# ── Kaynakça içe aktarma: Piri, Google Scholar, Zotero, EndNote... (RIS / BibTeX) ──────

RIS_TYPES = {"JOUR": "article", "JFULL": "article", "MGZN": "article", "NEWS": "article", "EJOUR": "article",
             "CHAP": "chapter", "ECHAP": "chapter", "BOOK": "book", "EBOOK": "book", "EDBOOK": "book",
             "THES": "phd", "CONF": "conference", "CPAPER": "conference"}
BIB_TYPES = {"article": "article", "incollection": "chapter", "inbook": "chapter", "book": "book",
             "phdthesis": "phd", "mastersthesis": "masters", "inproceedings": "conference",
             "conference": "conference", "thesis": "phd"}


def parse_ris(text: str) -> list:
    out, cur = [], None
    for raw in text.splitlines():
        m = re.match(r"^([A-Z][A-Z0-9])  -\s?(.*)$", raw.rstrip())
        if not m:
            continue
        tag, value = m.group(1), m.group(2).strip()
        if tag == "TY":
            cur = {"type": RIS_TYPES.get(value.upper(), "other"), "authors": [], "editors": [], "_kw": [],
                   "_issn": []}
            continue
        if cur is None:
            continue
        if tag == "ER":
            out.append(cur)
            cur = None
        elif tag in ("AU", "A1"):
            p = parse_person(value)
            if p:
                cur["authors"].append(p)
        elif tag in ("A2", "ED", "A3"):
            p = parse_person(value)
            if p:
                cur["editors"].append(p)
        elif tag in ("TI", "T1") and not cur.get("title"):
            cur["title"] = value
        elif tag in ("T2", "JO", "JF", "JA", "BT", "T3") and not cur.get("container"):
            cur["container"] = value
        elif tag in ("PY", "Y1", "DA") and not cur.get("year"):
            cur["year"] = value
        elif tag == "VL":
            cur["volume"] = value
        elif tag == "IS":
            cur["issue"] = value
        elif tag == "SP":
            cur["pages"] = value
        elif tag == "EP" and cur.get("pages") and value:
            cur["pages"] = f"{cur['pages']}–{value}"
        elif tag == "DO":
            cur["doi"] = value
        elif tag in ("UR", "L2") and not cur.get("url"):
            cur["url"] = value
        elif tag == "PB":
            cur["publisher"] = value
        elif tag == "KW":
            cur["_kw"].extend(split_keywords(value))
        elif tag == "SN":
            cur["_issn"].append(value)
        elif tag in ("AB", "N2") and not cur.get("_abstract"):
            cur["_abstract"] = value
        elif tag == "LA":
            cur["language"] = value
        elif tag == "M3" and "master" in value.lower() and cur["type"] == "phd":
            cur["type"] = "masters"
    if cur:
        out.append(cur)
    return out


def _bib_value(text: str, i: int):
    """BibTeX alan değerini okur ({...}, "..." ya da sayı). Dönüş: (değer, yeni konum)"""
    while i < len(text) and text[i] in " \t\r\n":
        i += 1
    if i >= len(text):
        return "", i
    if text[i] == "{":
        depth, j = 0, i
        while j < len(text):
            if text[j] == "{":
                depth += 1
            elif text[j] == "}":
                depth -= 1
                if depth == 0:
                    return text[i + 1:j], j + 1
            j += 1
        return text[i + 1:], len(text)
    if text[i] == '"':
        j = i + 1
        while j < len(text) and not (text[j] == '"' and text[j - 1] != "\\"):
            j += 1
        return text[i + 1:j], j + 1
    m = re.match(r"[^,}\s]+", text[i:])
    return (m.group(0), i + m.end()) if m else ("", i)


_BIB_ACCENTS = {r"\c{c}": "ç", r"\c{C}": "Ç", r"\c{s}": "ş", r"\c{S}": "Ş", r"\u{g}": "ğ", r"\u{G}": "Ğ",
                r'\"{o}': "ö", r'\"{O}': "Ö", r'\"{u}': "ü", r'\"{U}': "Ü", r"\i": "ı", r"\.{I}": "İ",
                r'\"o': "ö", r'\"u': "ü", r"\&": "&"}


def _bib_clean(value: str) -> str:
    for k, v in _BIB_ACCENTS.items():
        value = value.replace(k, v).replace("{" + k + "}", v)
    return clean_text(re.sub(r"[{}]", "", value))


def parse_bibtex(text: str) -> list:
    out = []
    for m in re.finditer(r"@(\w+)\s*\{\s*[^,]*,", text):
        kind = m.group(1).lower()
        if kind in ("comment", "string", "preamble"):
            continue
        i, fields = m.end(), {}
        while i < len(text):
            fm = re.match(r"\s*([A-Za-z][\w-]*)\s*=", text[i:])
            if not fm:
                break
            value, i = _bib_value(text, i + fm.end())
            fields[fm.group(1).lower()] = _bib_clean(value)
            while i < len(text) and text[i] in " \t\r\n,":
                i += 1
            if i < len(text) and text[i] == "}":
                break
        rec = {"type": BIB_TYPES.get(kind, "other"),
               "authors": [p for p in (parse_person(a) for a in re.split(r"\s+and\s+", fields.get("author", ""))) if p],
               "editors": [p for p in (parse_person(a) for a in re.split(r"\s+and\s+", fields.get("editor", ""))) if p],
               "title": fields.get("title", ""),
               "container": fields.get("journal") or fields.get("booktitle") or fields.get("journaltitle", ""),
               "year": fields.get("year") or fields.get("date", ""), "volume": fields.get("volume", ""),
               "issue": fields.get("number") or fields.get("issue", ""), "pages": fields.get("pages", ""),
               "doi": fields.get("doi", ""), "url": fields.get("url", ""),
               "publisher": fields.get("publisher", ""), "institution": fields.get("school") or fields.get("institution", ""),
               "language": fields.get("language", ""), "_kw": split_keywords(fields.get("keywords", "")),
               "_issn": [fields.get("issn", "")], "_abstract": fields.get("abstract", "")}
        out.append(rec)
    return out


def read_references(path) -> list:
    raw = Path(path).read_bytes()
    text = raw.decode("utf-8-sig", errors="replace")
    if re.search(r"^TY  -", text, re.M):
        return parse_ris(text)
    if re.search(r"@\w+\s*\{", text):
        return parse_bibtex(text)
    raise ValueError("Dosya RIS ya da BibTeX biçiminde görünmüyor.")


def import_references(library, path, tags=(), auto_tags=None) -> tuple:
    """Kaynakça dosyasındaki kayıtları kütüphaneye ekler. Dönüş: (eklenen, zaten_olan, toplam)"""
    records = read_references(path)
    added = existing = 0
    for rec in records:
        if not (rec.get("title") or "").strip():
            continue
        abstract = rec.pop("_abstract", "")
        rec["keywords"] = join_keywords(rec.pop("_kw", []))
        rec["issn"] = join_issns(rec.pop("_issn", []))
        known = library.find_by_doi(rec.get("doi")) or library.find_by_title(rec.get("title"))
        if known:
            library.add_tags(known, tags)
            existing += 1
            continue
        group_tags = auto_group_tags(rec, abstract[:2500], auto_tags)
        item_id, created = library.add(rec, tags=list(tags) + group_tags, source="içe aktarma")
        if created:
            added += 1
            if abstract:
                library.set_fulltext(item_id, abstract)
        else:
            existing += 1
    return added, existing, len(records)


# ════════════════════════════════════════════════════════════════════════════
#  6) HAFTALIK TARAMA: anahtar kelimeler, DergiPark (OAI-PMH), Crossref, rapor
# ════════════════════════════════════════════════════════════════════════════

DERGIPARK_OAI = "https://dergipark.org.tr/api/public/oai/"
CROSSREF_SEARCH = "https://api.crossref.org/works"
CROSSREF_SELECT = ("DOI,title,subtitle,author,editor,container-title,issued,published-print,"
                   "published-online,type,abstract,subject,URL,ISSN")
SCAN_INTERVAL_DAYS = 7
SCAN_FIRST_WINDOW_DAYS = 7          # ilk taramada geriye dönük bakılacak gün
SCAN_MAX_OAI_PAGES = 600
SCAN_MAX_DOWNLOADS = 60             # bir taramada en fazla otomatik PDF denemesi
OAI_PAUSE = 1.0

DEFAULT_KEYWORDS = """\
# Her grup [Grup adı] satırıyla başlar; altındaki her satır bir arama terimidir.
# Terimler başlıkta, yazarın anahtar kelimelerinde ve özette aranır; büyük/küçük harf
# ve Türkçe karakter farkı gözetilmez, kelimenin sonuna gelen ekler de yakalanır
# ('halk oyun' → halk oyunları, halk oyunlarının...).
# 'bağlam:' satırı gruptaki her terim için; 'terim ; bağlam: a, b' yalnızca o terim için:
# terimle birlikte bu kelimelerden biri de geçmelidir (çok anlamlı terimler için).
# Terim yalnızca özette geçiyorsa bağlam kelimesi başlıkta ya da anahtar kelimelerde
# aranır; böylece özetinde bir kez 'collective memory' geçen mimarlık yazısı gelmez.
# 'kök → tam hâli': eşleştirmede kök, Crossref aramasında tam hâli kullanılır.
# '#' ile başlayan satırlar açıklamadır.

[Halk dansları ve sahneleme]
bağlam: dans, dance, halk oyun, folk, folklor, folklore, koreograf, choreograph, oyun havası, zeybek, halay, horon
halk oyun → halk oyunları
halk dans → halk dansları
folk dance
folklore on stage
spectacularization of folklore
staging folk
sahneleme
koreografi
choreograph → choreography
kültürel performans
cultural performance

[Etnokoreoloji ve notasyon]
etnokoreoloji
ethnochoreolog → ethnochoreology
koreoloji
choreolog → choreology
dans notasyon → dans notasyonu
dance notation
hareket notasyon → hareket notasyonu
movement notation
labanotation
laban notasyon → laban notasyonu
kinetografi
kinetography
benesh ; bağlam: dans, dance, notation, notasyon, movement, hareket
laban hareket analiz → laban hareket analizi
laban movement analysis

[Dijital dönüşüm, MR ve hareket yakalama]
bağlam: dans, dance, halk oyun, folk, folklor, folklore, koreograf, choreograph, somut olmayan, intangible, ritüel, ritual, zeybek, halay, horon
hareket yakala → hareket yakalama
motion captur → motion capture
karma gerçeklik
mixed reality
sanal gerçeklik
virtual reality
artırılmış gerçeklik
augmented reality
dijital arşiv
digital archive
digitization
dijitalleştirme
pose estimation
poz tahmin → poz tahmini
markerless

[Somut olmayan kültürel miras]
somut olmayan kültürel miras
intangible cultural heritage
yaşayan insan hazine → yaşayan insan hazineleri
living human treasure
miras statüsü ; bağlam: somut olmayan, intangible, unesco, gelenek, tradition, dans, dance, folklor, folklore
heritage status ; bağlam: somut olmayan, intangible, unesco, gelenek, tradition, dans, dance, folklor, folklore
dans belgeleme
dance documentation
safeguarding ; bağlam: somut olmayan, intangible, kültürel miras, cultural heritage, unesco, folklor, folklore, dans, dance

[Geleneksel sohbet toplantıları ve kültürel bellek]
geleneksel sohbet toplantı → geleneksel sohbet toplantıları
sohbet toplantı → sohbet toplantıları
traditional sohbet
sohbet meeting
kültürel bellek ; bağlam: sohbet, folklor, folklore, sözlü, oral, ritüel, ritual, dans, dance, halk kültür, folk, halk müzi, türkü, aşık, ozan, halkbilim
cultural memory ; bağlam: sohbet, folklor, folklore, sözlü, oral, ritüel, ritual, dans, dance, halk kültür, folk, halk müzi, türkü, aşık, ozan, halkbilim
toplumsal bellek ; bağlam: sohbet, folklor, folklore, sözlü, oral, ritüel, ritual, dans, dance, halk kültür, folk, halk müzi, türkü, aşık, ozan, halkbilim
collective memory ; bağlam: sohbet, folklor, folklore, sözlü, oral, ritüel, ritual, dans, dance, halk kültür, folk, halk müzi, türkü, aşık, ozan, halkbilim
birikme gece → birikme geceleri
ateş gezme → ateş gezmesi
sıra gecesi
ritual gathering
yaren ; bağlam: sohbet, toplantı, gelenek, folklor, halk, tradition
barana ; bağlam: sohbet, toplantı, gelenek, folklor, halk, tradition
gezek ; bağlam: sohbet, toplantı, gelenek, folklor, halk, tradition
oturak ; bağlam: sohbet, toplantı, gelenek, folklor, abdal, kırşehir, eğlence

[Dijital kültür]
dijital kültür
digital culture
e-kültürle → e-kültürleme
dijital kültürlenme
kültürel aktarım ; bağlam: dijital, digital, sosyal medya, social media, dans, dance, folklor, folklore, halk kültür, somut olmayan, intangible, gelenek
cultural transmission ; bağlam: dijital, digital, social media, dance, folklore, folk, intangible, tradition
algoritmik kültür
algorithmic culture
platform kültür → platform kültürü
platform culture

[Gelenek, icra ve yorum]
bağlam: dans, dance, halk oyun, folk, folklor, folklore, koreograf, choreograph, halk müzi, türk müzi, geleneksel müzik, traditional music, türkü, zeybek, halay
icracı
yorumcu
otantiklik
authenticity
geleneksellik
gelenek ve yorum
geleneğin icadı
invented tradition
invention of tradition
geleneksel icra

[Halk oyunları ve ritim eğitimi]
dans eğitim → dans eğitimi
dance education
dans pedagoji → dans pedagojisi
dance pedagogy
halk oyunları öğretim → halk oyunları öğretimi
halk oyunları eğitim → halk oyunları eğitimi
folk dance teaching
ritim eğitim → ritim eğitimi
rhythm education
ritim dikte
rhythmic dictation
aksak usul
aksak ritim
asma davul

[Dans, kimlik ve kültür politikası]
bağlam: dans, dance, halk oyun, folk dance, folklor, folklore, koreograf, choreograph, halk müzi, folk music, zeybek, halay, horon
kimlik
identity
ulus inşa → ulus inşası
nation-building
nation building
kültür politika → kültür politikası
cultural policy
kültürel diplomasi
cultural diplomacy
göç
migration
diaspora
milliyetçilik
nationalism

[Yöresel oyunlar]
bağlam: halk oyun, oyun, dans, dance, folk, folklor, yöre
zeybek
horon
halay
bar oyun → bar oyunları
erzurum bar → erzurum barları
teke yöre → teke yöresi
teke zeybe → teke zeybeği
kılıç kalkan
kaşık oyun → kaşık oyunları
karşılama ; bağlam: halk oyun, oyun havası, dans, dance, rumeli, trakya, roman

[Dans ve bedenlenmiş biliş]
bağlam: dans, dance, koreograf, choreograph, hareket, movement, müzik, music, ritim, rhythm
bedenlenmiş biliş
embodied cognition
embodiment ; bağlam: dance, dans
interpersonal coordination ; bağlam: dance, dans, movement
interactional synchrony
topluluk dans → topluluk dansı
community dance
community-based dance
dance improvisation
dans doğaçlama
distributed creativity
kinesthetic empathy
"""


def keywords_path() -> Path:
    return data_dir() / "anahtar_kelimeler.txt"


# Önceki sürümlerin varsayılan listeleri: kullanıcı bunları hiç değiştirmediyse yenisine geçilir
OLD_DEFAULT_KEYWORD_HASHES = {"cb93bc396b7182e6610e9ceec3fb010cf3ebd45421ba2d2925e219cfd047df38"}


def _text_hash(text: str) -> str:
    return hashlib.sha256((text or "").strip().encode("utf-8")).hexdigest()


def keywords_customized() -> bool:
    """Kullanıcı kendi listesini mi kullanıyor (varsayılandan farklı ve eski varsayılan değil)?"""
    try:
        text = keywords_path().read_text(encoding="utf-8")
    except OSError:
        return False
    return _text_hash(text) not in OLD_DEFAULT_KEYWORD_HASHES | {_text_hash(DEFAULT_KEYWORDS)}


def load_keywords_text() -> str:
    try:
        text = keywords_path().read_text(encoding="utf-8")
    except OSError:
        return DEFAULT_KEYWORDS
    if _text_hash(text) in OLD_DEFAULT_KEYWORD_HASHES:     # eski varsayılan → güncel varsayılan
        try:
            save_keywords_text(DEFAULT_KEYWORDS)
            diag("anahtar kelimeler yeni varsayılan listeye güncellendi")
        except OSError:
            pass
        return DEFAULT_KEYWORDS
    return text


def save_keywords_text(text: str):
    path = keywords_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _split_words(text: str) -> list:
    return [w.strip() for w in re.split(r"[,;]", text or "") if w.strip()]


def parse_keyword_groups(text: str) -> list:
    """[Grup] / bağlam: / terim ; bağlam: biçimindeki metni gruplara ayırır."""
    groups, current = [], None
    for raw in (text or "").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        m = re.match(r"^\[(.+)\]$", line)
        if m:
            current = {"name": m.group(1).strip(), "context": [], "terms": []}
            groups.append(current)
            continue
        if current is None:
            current = {"name": "Genel", "context": [], "terms": []}
            groups.append(current)
        m = re.match(r"^ba[gğ]lam\s*:\s*(.*)$", line, re.I)
        if m:
            current["context"] = _split_words(m.group(1))
            continue
        term, _, rest = line.partition(";")
        ctx = None
        m = re.match(r"^\s*ba[gğ]lam\s*:\s*(.*)$", rest, re.I)
        if m:
            ctx = _split_words(m.group(1))
        parts = re.split(r"→|->", term, maxsplit=1)
        term, query = (parts[0], parts[1]) if len(parts) == 2 else (term, "")
        if term.strip():
            current["terms"].append({"term": term.strip(), "context": ctx, "query": query.strip() or None})
    return [g for g in groups if g["terms"]]


_SOFTEN = {"k": "[kg]", "p": "[pb]", "t": "[td]"}


def _word_start(word: str):
    """Kelime başından eşleşir; Türkçe ünsüz yumuşamasını da tanır (bellek → belleği, kimlik → kimliği)."""
    w = fold(word).strip()
    if len(w) >= 4 and w[-1] in _SOFTEN:
        return re.compile(r"(?<!\w)" + re.escape(w[:-1]) + _SOFTEN[w[-1]])
    return re.compile(r"(?<!\w)" + re.escape(w))


class KeywordMatcher:
    """Metinde hangi grup/terimlerin geçtiğini bulur (Türkçe ekleri tolere eder)."""

    def __init__(self, groups):
        self.groups = []
        self.ctx_words = {}
        for g in groups:
            group_ctx = [_word_start(w) for w in g.get("context") or []]
            terms = []
            for t in g["terms"]:
                ctx = [_word_start(w) for w in t["context"]] if t.get("context") is not None else group_ctx
                self.ctx_words[(g["name"], t["term"])] = (t["context"] if t.get("context") is not None
                                                          else g.get("context") or [])
                terms.append((t["term"], _word_start(t["term"]), ctx, t.get("query") or t["term"]))
            self.groups.append((g["name"], terms))

    def match(self, text: str, strong: str = None) -> dict:
        """{grup adı: [eşleşen terimler]}
        strong: başlık + anahtar kelimeler. Verilirse, terim yalnızca özette (text) geçtiğinde
        bağlam kelimesi strong içinde aranır (özette bir kez geçen genel terimler gürültü yapmasın)."""
        body = fold(text if strong is None else strong + " " + text)
        head = body if strong is None else fold(strong)
        hits = {}
        for name, terms in self.groups:
            for term, rx, ctx, _ in terms:
                if not rx.search(body):
                    continue
                if ctx:
                    where = body if rx.search(head) else head
                    if not any(c.search(where) for c in ctx):
                        continue
                hits.setdefault(name, []).append(term)
        return hits

    def search_terms(self, with_context: bool = False) -> list:
        """Crossref'te aranacak sorgular. with_context: bağlamlı terime bağlamın ilk kelimesi eklenir
        ('authenticity' → 'authenticity dans'); geçmişe dönük taramada ilgililiği artırır."""
        out = []
        for name, terms in self.groups:
            for term, _, ctx, query in terms:
                if ctx and len(term) < 9 and not with_context:
                    continue          # 'bar', 'teke' gibi terimler Crossref'te anlamsız sonuç verir
                if with_context and ctx:
                    words = self.ctx_words.get((name, term)) or []
                    if not any(fold(w) in fold(query) for w in words):
                        query = " ".join([query] + words[:2])        # ör. "authenticity dans dance"
                out.append((name, query))
        return out


_MATCHER_CACHE = {"key": None, "matcher": None}


def get_matcher():
    """Anahtar kelime gruplarından eşleştirici (dosya değişince yeniden kurulur)."""
    try:
        key = keywords_path().stat().st_mtime
    except OSError:
        key = "varsayılan"
    if _MATCHER_CACHE["key"] != key:
        _MATCHER_CACHE.update(key=key, matcher=KeywordMatcher(parse_keyword_groups(load_keywords_text())))
    return _MATCHER_CACHE["matcher"]


def auto_group_tags(rec: dict, head: str = "", enabled=None) -> list:
    """Kaynağın başlığı ve anahtar kelimeleri (yoksa PDF'in ilk sayfası) hangi gruplara uyuyor?
    enabled: None ise ayardaki tercih, True/False ise bu ekleme için verilen seçim."""
    if not (load_settings().get("auto_tag", True) if enabled is None else enabled):
        return []
    matcher = get_matcher()
    hits = matcher.match(" ".join([rec.get("title") or "", rec.get("keywords") or ""]))
    if not hits and not rec.get("keywords") and head:
        hits = matcher.match(head[:2500])
    return list(hits)


def describe_hits(hits: dict) -> str:
    return " · ".join(f"{group}: {', '.join(dict.fromkeys(terms))}" for group, terms in hits.items())


# ── DergiPark OAI-PMH ───────────────────────────────────────────────────────

_NS = {"oai": "http://www.openarchives.org/OAI/2.0/",
       "dc": "http://purl.org/dc/elements/1.1/",
       "oai_dc": "http://www.openarchives.org/OAI/2.0/oai_dc/"}
_XML_LANG = "{http://www.w3.org/XML/1998/namespace}lang"


def parse_oai_page(xml_bytes: bytes):
    """Bir ListRecords sayfasını çözer. Dönüş: (kayıtlar, resumptionToken, toplam, hata)"""
    root = ET.fromstring(xml_bytes)
    error = root.find("oai:error", _NS)
    if error is not None:
        return [], None, 0, (error.get("code") or "error")
    records = []
    for rec in root.iter("{%s}record" % _NS["oai"]):
        header = rec.find("oai:header", _NS)
        if header is None or header.get("status") == "deleted":
            continue
        dc = rec.find("oai:metadata/oai_dc:dc", _NS)
        if dc is None:
            continue

        def values(tag):
            return [clean_text(e.text) for e in dc.findall(f"dc:{tag}", _NS) if e.text and e.text.strip()]

        titles = [(e.get(_XML_LANG) or "", clean_text(e.text)) for e in dc.findall("dc:title", _NS)
                  if e.text and e.text.strip()]
        identifiers = values("identifier")
        url = next((i for i in identifiers if i.startswith("http") and "doi.org" not in i), "")
        doi = next((normalize_doi(i) for i in identifiers if normalize_doi(i)), "")
        if not doi:
            doi = next((normalize_doi(r) for r in values("relation") if normalize_doi(r)), "")
        languages = values("language")
        title = titles[0][1] if titles else ""
        for lang, text in titles:                       # özgün dildeki başlığı tercih et
            if languages and lang and lang.lower()[:2] == languages[0].lower()[:2]:
                title = text
                break
        source = (values("source") or [""])[0]
        records.append({
            "id": (header.findtext("oai:identifier", "", _NS) or "").strip(),
            "title": title,
            "all_titles": [t for _, t in titles],
            "authors": [p for p in (parse_person(c) for c in values("creator")) if p],
            "subjects": values("subject"),
            "description": " ".join(values("description")),
            "year": " ".join(values("date")),
            "container": re.split(r"[;,(]", source)[0].strip() if source else "",
            "publisher": (values("publisher") or [""])[0],
            "language": languages[0] if languages else "",
            "url": url, "doi": doi or "", "type": "article", "source": "DergiPark",
            "keywords": join_keywords(k for subj in values("subject") for k in split_keywords(subj)),
            "issn": join_issns(find_issns(" ".join(values("source") + values("identifier")))),
        })
    token_el = root.find(".//oai:resumptionToken", _NS)
    token = token_el.text.strip() if token_el is not None and token_el.text and token_el.text.strip() else None
    total = 0
    if token_el is not None and (token_el.get("completeListSize") or "").isdigit():
        total = int(token_el.get("completeListSize"))
    return records, token, total, None


def harvest_dergipark(session, since, until=None, progress=None, cancel=None, set_spec=None,
                      until_date=None):
    """DergiPark'a 'since' tarihinden beri eklenen/güncellenen makaleleri sayfa sayfa getirir.

    DergiPark kayıt tarihlerini saatsiz (yalnızca gün) veriyor; saatli bir 'from' o günün
    kayıtlarını dışarıda bırakır. Bu yüzden gün bazında ve bir gün örtüşmeyle sorulur
    (örtüşen kayıtlar kütüphanede zaten olduğu için yeniden eklenmez)."""
    params = {"verb": "ListRecords", "metadataPrefix": "oai_dc"}
    if since is not None:
        params["from"] = (since - timedelta(days=1)).strftime("%Y-%m-%d")
    if until_date:
        params["until"] = until_date
    if set_spec:
        params["set"] = set_spec
    pages = fetched = 0
    while True:
        if cancel is not None and cancel.is_set():
            return
        r = session.get(DERGIPARK_OAI, params=params, timeout=(15, 120),
                        headers={"Accept": "application/xml"})
        r.raise_for_status()
        records, token, total, error = parse_oai_page(r.content)
        if error == "noRecordsMatch":
            return
        if error:
            raise DownloadError(f"DergiPark veri kapısı hata verdi: {error}")
        fetched += len(records)
        pages += 1
        if progress:
            progress(fetched, total)
        yield from records
        if not token or pages >= SCAN_MAX_OAI_PAGES:
            return
        params = {"verb": "ListRecords", "resumptionToken": token}
        time.sleep(OAI_PAUSE)


# Geçmişe dönük taramada adı alanla ilgili görünen DergiPark dergileri baştan sona taranır
RELEVANT_JOURNAL_WORDS = ["folklor", "folklore", "halkbilim", "halk bilim", "halk kultur", "muzik", "music",
                          "musik", "dans", "dance", "konserv", "conservator", "tiyatro", "theatre", "theater",
                          "sahne", "sanat", "art$", "arts$", "kultur", "culture", "cultural", "turk dunyasi",
                          "turkiyat", "turkoloji", "turkbilig", "etnograf", "etnoloji", "antropoloji",
                          "anthropolog", "miras", "heritage", "alevilik", "bektasi", "gelenek", "tradition"]
SOCIAL_JOURNAL_WORDS = ["sosyal bilim", "social science", "beseri", "insan bilim", "humanit", "edebiyat",
                        "iletisim", "egitim fakultesi", "spor bilim", "sport"]


def dergipark_sets(session) -> list:
    """DergiPark'taki bütün dergiler: [(kısa ad, dergi adı)]"""
    params = {"verb": "ListSets"}
    out = []
    for _ in range(200):
        r = session.get(DERGIPARK_OAI, params=params, timeout=(15, 120), headers={"Accept": "application/xml"})
        r.raise_for_status()
        root = ET.fromstring(r.content)
        for st in root.iter("{%s}set" % _NS["oai"]):
            spec = (st.findtext("oai:setSpec", "", _NS) or "").strip()
            name = (st.findtext("oai:setName", "", _NS) or "").strip()
            if spec:
                out.append((spec, name))
        token_el = root.find(".//oai:resumptionToken", _NS)
        token = token_el.text.strip() if token_el is not None and token_el.text and token_el.text.strip() else None
        if not token:
            break
        params = {"verb": "ListSets", "resumptionToken": token}
        time.sleep(OAI_PAUSE)
    return out


def relevant_journal_sets(sets, include_social=False) -> list:
    words = RELEVANT_JOURNAL_WORDS + (SOCIAL_JOURNAL_WORDS if include_social else [])
    parts = [re.escape(w[:-1]) + "(?![a-z])" if w.endswith("$") else re.escape(w) for w in words]
    rx = re.compile(r"(?<![a-z])(" + "|".join(parts) + ")")
    return [(spec, name) for spec, name in sets if rx.search(fold(name)) or rx.search(fold(spec))]


# ── YÖK Ulusal Tez Merkezi: sitenin kendi arama kutusunun kullandığı adresler ──────────
YOK_BASE = "https://tez.yok.gov.tr/UlusalTezMerkezi/"
YOK_PAUSE = 1.5                       # siteyi yormamak için istekler arası bekleme
YOK_TYPES = {"doktora": "phd", "sanatta yeterlik": "phd", "yuksek lisans": "masters"}
_YOK_CARD_RE = re.compile(r'data-index="(\d+)"\s+data-kayitno="([^"]+)"\s+data-tezno="([^"]+)"')


def _strip_tags(text) -> str:
    return clean_text(html.unescape(re.sub(r"<[^>]+>", " ", str(text or ""))))


def _yok_name(name: str) -> str:
    name = clean_text(name)
    return " ".join(title_case_word(w) for w in name.split(" ")) if name.isupper() else name


def yok_open_session(session):
    """Ana sayfayı açarak arama oturumu alır (site oturumsuz aramaya sonuç vermiyor)."""
    session.get(YOK_BASE, timeout=(15, 60))


def parse_yok_results(page: str) -> list:
    m = re.search(r"const referenceData = (\{.*?\n\s*\});", page, re.S)
    ref = {}
    if m:
        try:
            ref = json.loads(re.sub(r",(\s*\})", r"\1", m.group(1)))
        except ValueError:
            ref = {}
    out = []
    for chunk in page.split('class="result-card"')[1:]:
        cm = _YOK_CARD_RE.search(chunk[:400])
        if not cm:
            continue
        index, kayit, tez = cm.groups()
        meta = (ref.get(index) or {}).get("meta") or {}
        tr_title = _strip_tags(meta.get("title")) or _strip_tags(
            (re.search(r'class="card-title">(.*?)</div>', chunk, re.S) or [None, ""])[1])
        en = re.search(r'class="card-info" style="font-style: italic">(.*?)</div>', chunk, re.S)
        en_title = _strip_tags(en.group(1)) if en else ""
        no = re.search(r"Tez No:</strong>\s*(\d+)", chunk)
        kind = fold(meta.get("type", ""))
        out.append({
            "title": tr_title, "all_titles": [t for t in (tr_title, en_title) if t],
            "authors": [p for p in [parse_person(_yok_name(meta.get("author", "")))] if p],
            "year": str(meta.get("year") or ""), "type": next((v for k, v in YOK_TYPES.items() if k in kind), "other"),
            "institution": _yok_name(str(meta.get("yer") or "").split("/")[0].strip()),
            "language": "tr" if fold(meta.get("lang", "")).startswith("turk") else "",
            "subjects": [x.strip() for x in str(meta.get("subject") or "").split(";") if x.strip()],
            "description": "", "keywords": "", "source": "YÖK Tez", "url": "",
            "tez_no": no.group(1) if no else "", "yok_keys": (kayit, tez), "thesis_kind": meta.get("type", ""),
        })
    return out


def search_yok(session, query: str) -> list:
    """Tez Merkezi'nin hızlı aramasıyla (tüm alanlarda) arar; en fazla 2000 tez döner."""
    if len(query.strip()) < 3:
        return []
    r = session.post(YOK_BASE + "SearchTez", timeout=(15, 120),
                     data={"izin": "0", "tur": "0", "neden": query, "islem": "1", "nevi": "7"})
    r.raise_for_status()
    if "Hata" in r.url:
        raise DownloadError("YÖK Tez Merkezi aramayı kabul etmedi")
    return parse_yok_results(r.text)


def yok_detail(session, keys) -> dict:
    """Özet, anahtar kelimeler, danışman ve tam kurum bilgisi."""
    r = session.get(YOK_BASE + "tezBilgiDetay.jsp", params={"kayitNo": keys[0], "tezNo": keys[1]},
                    timeout=(15, 60))
    r.raise_for_status()
    try:
        return json.loads(r.text.strip())
    except ValueError:
        return {}


def yok_pdf_status(session, keys):
    """(PDF adresi | None, neden). Neden: yazar izin vermemiş / erişim belli bir tarihe kadar kapalı."""
    r = session.get(YOK_BASE + "getTezPdf.jsp", params={"kayitNo": keys[0], "tezNo": keys[1]},
                    timeout=(15, 60))
    r.raise_for_status()
    m = re.search(r"TezGoster\?key=([^'\"\s>]+)", r.text)
    if m:
        return YOK_BASE + "TezGoster?key=" + html.unescape(m.group(1)), ""
    text = _strip_tags(r.text)
    d = re.search(r"\b(\d{1,2}[./]\d{1,2}[./](?:19|20)\d{2})\b", text)
    if d:
        return None, f"erişim {d.group(1)} tarihine kadar kapalı"
    return None, "yazar PDF izni vermemiş"


def yok_pdf_url(session, keys):
    """Yazarı izin verdiyse PDF adresi, vermediyse None."""
    return yok_pdf_status(session, keys)[0]


def yok_download(session, keys, folder, name):
    """İzinli tezin PDF'ini indirir. Dönüş: (geçici dosya | None, 'pdf' | 'closed' | 'failed', neden).
    PDF yerine sayfa ya da hata gelirse oturum tazelenip bir kez daha denenir; neden tanılama kaydına yazılır."""
    url, reason = yok_pdf_status(session, keys)
    if not url:
        return None, "closed", reason
    tmp = Path(folder) / f".yok_{name}.part"
    last = ""
    for attempt in range(2):
        time.sleep(YOK_PAUSE)
        try:
            with session.get(url, stream=True, timeout=(15, 180), headers={"Referer": YOK_BASE}) as r:
                if r.status_code >= 400:
                    last = f"HTTP {r.status_code}"
                else:
                    with open(tmp, "wb") as fh:
                        for block in r.iter_content(1 << 16):
                            fh.write(block)
                    head = tmp.read_bytes()[:4096]
                    if head[:1024].find(b"%PDF-") >= 0:
                        return tmp, "pdf", ""
                    title = re.search(rb"<title[^>]*>(.*?)</title>", head, re.I | re.S)
                    last = "PDF yerine sayfa geldi" + (
                        f" (“{_strip_tags(title.group(1).decode('utf-8', 'replace')).strip()[:60]}”)" if title else "")
        except requests.RequestException as exc:
            last = describe_error(exc)
        tmp.unlink(missing_ok=True)
        if attempt == 0:
            try:                                      # oturumu ve indirme anahtarını tazele
                yok_open_session(session)
                url, reason = yok_pdf_status(session, keys)
            except Exception as exc:
                last = describe_error(exc)
                break
            if not url:
                return None, "closed", reason
    diag(f"YÖK tez PDF'i indirilemedi ({name}): {last}")
    return None, "failed", "indirme başarısız: " + (last or "bilinmeyen hata")


def find_yok_thesis(session, item):
    """Tez No'su olmayan tez kaydını Tez Merkezi'nde başlıkla bulur (Türkçe ya da İngilizce başlık + yıl + yazar)."""
    title = re.split(r"[:.?!]\s", item.get("title") or "")[0].strip()
    if len(title) < 12:
        return None
    year = str(item.get("year") or "")[:4]
    fam = fold(((item.get("authors") or [{}])[0] or {}).get("family", "")) if item.get("authors") else ""
    for rec in search_yok(session, title)[:200]:
        if not any(same_title(item.get("title") or "", t) or same_title(title, t) for t in rec.get("all_titles") or []):
            continue
        ry = str(rec.get("year") or "")[:4]
        if year.isdigit() and ry.isdigit() and abs(int(year) - int(ry)) > 1:
            continue
        rf = fold(((rec.get("authors") or [{}])[0] or {}).get("family", "")) if rec.get("authors") else ""
        if fam and rf and fam != rf:
            continue
        return rec
    return None


def yok_open_html(tez_no: str) -> Path:
    """Tezi Tez Merkezi'nde açan küçük sayfa (site tez numarasıyla doğrudan bağlantı vermiyor)."""
    safe = re.sub(r"\D", "", tez_no) or "x"
    path = settings_path().parent / "yok_tezleri" / f"tez_{safe}.html"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"""<!doctype html><meta charset="utf-8"><title>YÖK Tez {html.escape(tez_no)}</title>
<body onload="document.forms[0].submit()"><form method="post" action="{YOK_BASE}SearchTez">
<input type="hidden" name="izin" value="0"><input type="hidden" name="tur" value="0">
<input type="hidden" name="neden" value="{html.escape(tez_no)}"><input type="hidden" name="islem" value="1">
<input type="hidden" name="nevi" value="8"><noscript><button>Tez Merkezi'nde aç</button></noscript></form></body>""",
                    encoding="utf-8")
    return path


def yok_keywords(text) -> list:
    """'Anahtar Kelime: Bar halk oyunları = Bar folk games ; Etnokoreoloji = ...' → Türkçe hâlleri"""
    text = re.sub(r"^(Anahtar Kelime(ler)?|Keywords?)\s*:\s*", "", _strip_tags(text), flags=re.I)
    return [part.split("=")[0].strip() for part in text.split(";") if part.split("=")[0].strip()]


def yok_tez_no(item) -> str:
    m = re.search(r"YÖK Tez No:\s*(\d+)", item.get("notes") or "")
    return m.group(1) if m else ""


def is_thesis(item) -> bool:
    return item.get("type") in ("phd", "masters") or bool(yok_tez_no(item))


def yok_queries(matcher, include_context: bool = True) -> list:
    """Tez Merkezi'nde aranacak terimler: tam hâli; tek başına çok anlamlı kısa terimler hariç.
    include_context=False: bağlam isteyen genel terimler ('virtual reality' gibi binlerce tez
    döndürenler) atlanır; haftalık taramada siteyi gereksiz yormamak için."""
    out = []
    for _, terms in matcher.groups:
        for term, _, ctx, query in terms:
            if ctx and (len(term) < 9 or not include_context):
                continue
            if query not in out and len(query) >= 3:
                out.append(query)
    return out


def search_crossref_deep(session, query: str, since=None, limit: int = 1000):
    """Crossref'te tüm zamanlarda (ya da 'since' yayın tarihinden beri) ilgililik sırasıyla arar."""
    params = {"query.bibliographic": query, "rows": min(1000, limit), "cursor": "*", "select": CROSSREF_SELECT}
    if since is not None:
        params["filter"] = f"from-pub-date:{since.strftime('%Y-%m-%d')}"
    got = 0
    while got < limit:
        r = session.get(CROSSREF_SEARCH, params=params, timeout=(15, 90), headers={"Accept": "application/json"})
        if r.status_code == 400:
            raise DownloadError(f"Crossref sorguyu reddetti (HTTP 400): {r.text[:200]}")
        r.raise_for_status()
        message = r.json().get("message") or {}
        items = message.get("items") or []
        for msg in items:
            rec = record_from_crossref(msg)
            rec["description"] = clean_text(msg.get("abstract", ""))
            rec["subjects"] = msg.get("subject") or []
            rec["url"] = msg.get("URL", "")
            rec["source"] = "Crossref"
            yield rec
        got += len(items)
        cursor = message.get("next-cursor")
        if not items or not cursor or len(items) < params["rows"]:
            return
        params = dict(params, cursor=cursor)
        time.sleep(0.5)


def search_crossref(session, query: str, since: datetime, rows: int = 100):
    params = {"query.bibliographic": query, "rows": rows,
              "filter": f"from-created-date:{(since - timedelta(days=1)).strftime('%Y-%m-%d')}",
              # Yalnızca Crossref'in kabul ettiği (denenmiş) alanlar: geçersiz tek bir alan bütün
              # sorguyu reddettirir. Cilt/sayı/sayfa, eşleşen kayıtlar için ayrıca tam kayıttan alınır.
              "select": CROSSREF_SELECT}
    r = session.get(CROSSREF_SEARCH, params=params, timeout=(15, 60), headers={"Accept": "application/json"})
    if r.status_code == 400:
        raise DownloadError(f"Crossref sorguyu reddetti (HTTP 400): {r.text[:200]}")
    r.raise_for_status()
    out = []
    for msg in (r.json().get("message") or {}).get("items") or []:
        rec = record_from_crossref(msg)
        rec["description"] = clean_text(msg.get("abstract", ""))
        rec["subjects"] = msg.get("subject") or []
        rec["url"] = msg.get("URL", "")
        rec["source"] = "Crossref"
        out.append(rec)
    return out


# ── OpenAlex ve ERIC (resmî, açık arama arayüzleri) ──────────────────────────

def openalex_params(email="") -> dict:
    """OpenAlex isteklerine eklenecek kimlik: kullanıcının ücretsiz anahtarı (varsa) ve e-postası."""
    params = {}
    try:
        key = (load_settings().get("openalex_api_key") or "").strip()
    except Exception:
        key = ""
    if key:
        params["api_key"] = key
    if email:
        params["mailto"] = email
    return params


_OPENALEX_TYPES = {"article": "article", "review": "article", "letter": "article", "editorial": "article",
                   "book-chapter": "chapter", "book": "book", "dissertation": "phd",
                   "proceedings-article": "conference", "preprint": "article", "report": "other"}


def openalex_abstract(inverted) -> str:
    """OpenAlex özeti kelime → konum listesi olarak verir; düz metne çevirir."""
    if not isinstance(inverted, dict):
        return ""
    words = []
    for word, positions in inverted.items():
        for pos in positions or []:
            if isinstance(pos, int) and pos < 5000:
                words.append((pos, word))
    return " ".join(w for _, w in sorted(words))


def record_from_openalex(w: dict) -> dict:
    loc = w.get("primary_location") or {}
    src = loc.get("source") or {}
    bib = w.get("biblio") or {}
    first, last = bib.get("first_page") or "", bib.get("last_page") or ""
    authors = []
    for a in w.get("authorships") or []:
        person = parse_person(((a.get("author") or {}).get("display_name")) or a.get("raw_author_name") or "")
        if person:
            authors.append(person)
    best = w.get("best_oa_location") or {}
    oa = w.get("open_access") or {}
    rtype = _OPENALEX_TYPES.get(w.get("type") or "", "other")
    if rtype == "article" and not src.get("display_name"):
        rtype = "other"
    return {
        "title": clean_text(w.get("title") or w.get("display_name") or ""), "authors": authors,
        "year": str(w.get("publication_year") or ""), "type": rtype,
        "container": clean_text(src.get("display_name") or ""), "volume": str(bib.get("volume") or ""),
        "issue": str(bib.get("issue") or ""),
        "pages": f"{first}-{last}" if first and last and first != last else str(first or ""),
        "publisher": clean_text(src.get("host_organization_name") or ""),
        "doi": normalize_doi(w.get("doi") or "") or "", "language": w.get("language") or "",
        "issn": join_issns(src.get("issn") or []),
        "keywords": ", ".join(k.get("display_name", "") for k in (w.get("keywords") or [])[:8]
                              if isinstance(k, dict) and k.get("display_name")),
        "description": clean_text(openalex_abstract(w.get("abstract_inverted_index"))),
        "url": loc.get("landing_page_url") or oa.get("oa_url") or w.get("id") or "",
        "pdf_url": best.get("pdf_url") or "", "source": "OpenAlex",
    }


def _openalex_get(session, params):
    r = session.get(OPENALEX_API, params=params, timeout=(15, 60), headers={"Accept": "application/json"})
    if r.status_code == 429:
        raise RateLimited("OpenAlex günlük ücretsiz kullanım sınırı doldu"
                          + ("" if params.get("api_key") else " (anahtarsız sınır düşüktür; Tarama sekmesinden "
                                                              "ücretsiz anahtar eklenebilir)"))
    if r.status_code in (401, 403):
        raise DownloadError("OpenAlex anahtarı kabul edilmedi (Tarama sekmesindeki anahtarı kontrol edin)")
    if r.status_code == 400:
        raise DownloadError(f"OpenAlex sorguyu reddetti (HTTP 400): {r.text[:200]}")
    r.raise_for_status()
    return r.json()


def search_openalex(session, query: str, since=None, limit: int = 100, newest_first=False, email=""):
    """OpenAlex'te arar (başlık, özet ve tam metin). since: bu yayın tarihinden sonrakiler.
    newest_first: haftalık taramada en yeniler; geçmişe dönük taramada ilgililik sırası."""
    params = dict(openalex_params(email), search=query, **{"per-page": min(200, max(limit, 1))})
    if since is not None:
        params["filter"] = f"from_publication_date:{since.strftime('%Y-%m-%d')}"
    if newest_first:
        params["sort"] = "publication_date:desc"
    params["cursor"] = "*"
    got = 0
    while got < limit:
        data = _openalex_get(session, params)
        results = data.get("results") or []
        for w in results:
            if isinstance(w, dict) and (w.get("title") or w.get("display_name")):
                yield record_from_openalex(w)
        got += len(results)
        cursor = (data.get("meta") or {}).get("next_cursor")
        if not results or not cursor or len(results) < params["per-page"]:
            return
        params = dict(params, cursor=cursor)


_ERIC_TYPES = (("Doctoral Dissertations", "phd"), ("Masters Theses", "masters"), ("Journal Articles", "article"),
               ("Books", "book"), ("Proceedings", "conference"), ("Meeting Papers", "conference"))


def record_from_eric(doc: dict) -> dict:
    def as_list(v):
        return v if isinstance(v, list) else [v] if v else []
    eid = str(doc.get("id") or "")
    ptypes = " ".join(as_list(doc.get("publicationtype")))
    rtype = next((t for key, t in _ERIC_TYPES if key in ptypes), "other")
    langs = " ".join(as_list(doc.get("language")))
    full = str(doc.get("e_fulltextauth") or "").strip().lower() in ("1", "true", "t", "yes")
    return {
        "title": clean_text(doc.get("title") or ""), "authors": [p for p in map(parse_person, as_list(doc.get("author"))) if p],
        "year": str(doc.get("publicationdateyear") or ""), "type": rtype,
        "container": clean_text(doc.get("source") or "") if rtype == "article" else "",
        "publisher": clean_text(doc.get("source") or "") if rtype in ("book", "other") else "",
        "issn": join_issns(find_issns(" ".join(as_list(doc.get("issn"))))),
        "language": "en" if "English" in langs or not langs else "",
        "description": clean_text(doc.get("description") or ""),
        "subjects": [clean_text(x) for x in as_list(doc.get("subject"))],
        "url": f"https://eric.ed.gov/?id={eid}" if eid else (doc.get("url") or ""),
        "pdf_url": f"https://files.eric.ed.gov/fulltext/{eid}.pdf" if full and eid else "",
        "source": "ERIC", "doi": "",
    }


ERIC_FIELDS = ("id,title,author,source,publicationdateyear,description,subject,publicationtype,"
               "issn,language,e_fulltextauth,url")


def batch_terms(queries, size=8) -> list:
    """Haftalık taramada terimleri 'VEYA' ile birleştirir: OpenAlex'in günlük ücretsiz sınırı ve
    ERIC'e gereksiz yük için 100 terim yerine ~13 sorgu."""
    terms = list(dict.fromkeys(q for _, q in queries if q and '"' not in q))
    out = []
    for i in range(0, len(terms), size):
        part = terms[i:i + size]
        out.append(("", " OR ".join(f'"{t}"' if " " in t else t for t in part)))
    return out


def eric_query_ok(query: str) -> bool:
    """ERIC yalnızca İngilizce: Türkçe harfli terimlerle boşuna sorgu atılmaz."""
    return not re.search(r"[çğıöşüÇĞİÖŞÜ]", query or "")


def search_eric(session, query: str, since_year=None, limit: int = 200):
    """ERIC (ABD Eğitim Bakanlığı eğitim araştırmaları dizini) resmî arama arayüzü."""
    phrase = f'"{query}"' if " " in query.strip() and '"' not in query else query
    base = {"format": "json", "fields": ERIC_FIELDS, "rows": min(200, limit)}
    search = f"({phrase}) AND publicationdateyear:[{since_year} TO 2100]" if since_year else phrase
    start = 0
    while start < limit:
        r = session.get(ERIC_API, params=dict(base, search=search, start=start), timeout=(15, 60),
                        headers={"Accept": "application/json"})
        if r.status_code >= 400 and since_year and search != phrase:
            search = phrase                                   # tarih süzgeci kabul edilmezse sonuçlar burada süzülür
            continue
        if r.status_code == 429:
            raise RateLimited("ERIC 'çok fazla istek' dedi")
        r.raise_for_status()
        docs = ((r.json() or {}).get("response") or {}).get("docs") or []
        for doc in docs:
            rec = record_from_eric(doc)
            if not rec["title"]:
                continue
            if since_year and rec["year"].isdigit() and int(rec["year"]) < since_year:
                continue
            yield rec
        start += len(docs)
        if len(docs) < base["rows"]:
            return


# ── Tarama raporu (HTML) ────────────────────────────────────────────────────

def _h(text) -> str:
    return html.escape(str(text or ""))


def write_retry_report(library_folder, label, rows, untouched, seconds, stopped, has_email, has_core) -> Path:
    """'PDF'leri Yeniden Ara' sonunda HTML rapor: kaç kaynak arandı, kaçının PDF'i nereden bulundu,
    bulunamayanlar (makale sayfası ve Google Akademik bağlantılarıyla), ertelenenler."""
    folder = Path(library_folder or settings_path().parent) / "Tarama Raporları"
    now = datetime.now()
    path = unique_path(folder, f"PDF Arama Raporu {now:%Y-%m-%d %H%M}.html")
    found = [r for r in rows if r["outcome"] == "found"]
    none = [r for r in rows if r["outcome"] == "none"]
    limited = [r for r in rows if r["outcome"] == "limited"]
    had = [r for r in rows if r["outcome"] == "had"]

    def who(item):
        people = item.get("authors") or []
        name = people[0].get("family", "") if people else ""
        return name + (" vd." if len(people) > 2 else f" ve {people[1].get('family', '')}" if len(people) == 2 else "")

    def line(row, extra=""):
        item = row["item"]
        meta = " · ".join(x for x in (who(item), item.get("container"), str(item.get("year") or "")) if x)
        return (f'<li><div class="t"><span class="no">No {_h(item.get("no") or "?")}</span> {_h(item.get("title"))}</div>'
                f'<div class="m">{_h(meta)}</div>{extra}</li>')

    def found_line(row):
        via = re.sub(r"^[\d.,]+\s*[KMG]?B,?\s*", "", row.get("via", "")).strip()       # '515 KB, …' boyutu at
        via = {"makale sayfasındaki PDF bağlantısından": "yayıncının makale sayfası",
               "doğrudan PDF bağlantısı": "doğrudan PDF bağlantısı"}.get(via, via) or "yayıncı sayfası"
        return line(row, f'<div class="c"><span class="chip ok">PDF bağlandı</span><span class="chip">{_h(via)}</span>'
                         f'<span class="kw">{_h(row.get("file", ""))}</span></div>')

    def missing_line(row, cls="warn", label="Bulunamadı"):
        item = row["item"]
        links = [f'<a href="{_h(item_open_link(item))}">Makale sayfası</a>',
                 f'<a href="{_h(search_link(item, "Google Akademik"))}">Google Akademik</a>',
                 f'<a href="{_h(search_link(item, "BASE (kurum arşivleri)"))}">BASE</a>']
        db = database_for_doi(item.get("doi") or "")
        if row.get("thesis"):
            links[0] = f'<a href="{_h(item_open_link(item))}">Tez Merkezi</a>'
            label = f"Tez · {row['thesis']}"
        return line(row, f'<div class="c"><span class="chip {cls}">{_h(label)}</span>'
                         + (f'<span class="chip inst">kurum erişimi: {_h(db)}</span>' if db else "")
                         + f'<span class="links">{" · ".join(links)}</span></div>')

    searched = ["yayıncı sayfası (DOI / link)"] + (["Unpaywall"] if has_email else []) + \
        ["OpenAlex", "Semantic Scholar", "CORE" + (" (anahtarlı)" if has_core else ""), "YÖK Tez Merkezi (tezlerde)"]
    minutes = max(1, round(seconds / 60))
    sections = []
    if found:
        sections.append(f'<section><h2>PDF\'i bulunup bağlananlar <small>{len(found)}</small></h2>'
                        f'<ul>{"".join(found_line(r) for r in found)}</ul></section>')
    if none:
        sections.append(f'<section><h2>Bulunamayanlar <small>{len(none)}</small></h2>'
                        '<p class="note">Bunların herkese açık kopyası bulunamadı. Kurum erişiminizle makale sayfasından '
                        'ya da Google Akademik sonuçlarındaki [PDF] bağlantılarından indirebilirsiniz; '
                        '"PDF\'sizleri Sırayla Aç" bu adımı kolaylaştırır.</p>'
                        f'<ul>{"".join(missing_line(r) for r in none)}</ul></section>')
    if limited:
        sections.append(f'<section><h2>Ertelenenler <small>{len(limited)}</small></h2>'
                        '<p class="note">Site "çok fazla istek" dediği için aranamadı; "denenmedi" sayıldı. Bir süre sonra '
                        'aynı aralıkla yeniden başlatın.</p>'
                        f'<ul>{"".join(missing_line(r, "inst", "Ertelendi") for r in limited)}</ul></section>')
    if untouched and stopped:
        sections.append(f'<section><h2>Durdurulduğu için sıra gelmeyenler <small>{len(untouched)}</small></h2>'
                        f'<ul>{"".join(line({"item": i}) for i in untouched)}</ul></section>')
    if not sections:
        sections.append('<p class="empty">Aranacak PDF\'siz kaynak yoktu.</p>')
    tried = len(found) + len(none) + len(limited)
    rate = f"%{round(100 * len(found) / tried)}" if tried else "–"
    doc = f"""<!doctype html><html lang="tr"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>PDF Arama Raporu {now:%d.%m.%Y %H:%M}</title>
<style>
:root{{--bg:#f6f5f2;--card:#fff;--text:#1d1d1f;--muted:#6b6b70;--line:#e3e1dc;--accent:#1f6f4e;
--ok:#1f8f4e;--warn:#b7791f;--inst:#2b6cb0}}
@media (prefers-color-scheme:dark){{:root{{--bg:#16171a;--card:#1f2125;--text:#ececef;--muted:#9a9ca3;
--line:#2e3036;--accent:#5fc496;--ok:#5fc496;--warn:#e0b04c;--inst:#7fb3ee}}}}
*{{box-sizing:border-box}}body{{margin:0;background:var(--bg);color:var(--text);
font:15px/1.55 "Segoe UI",system-ui,sans-serif}}main{{max-width:880px;margin:0 auto;padding:32px 16px 64px}}
h1{{font-size:26px;margin:0 0 4px}}.sub{{color:var(--muted);margin:0 0 24px}}
.stats{{display:flex;flex-wrap:wrap;gap:12px;margin-bottom:28px}}
.stat{{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:12px 16px;min-width:130px}}
.stat b{{display:block;font-size:22px}}.stat span{{color:var(--muted);font-size:13px}}
.stat.ok b{{color:var(--ok)}}.stat.warn b{{color:var(--warn)}}
h2{{font-size:18px;margin:28px 0 10px;padding-bottom:6px;border-bottom:1px solid var(--line)}}
h2 small{{color:var(--muted);font-weight:normal}}ul{{list-style:none;padding:0;margin:0}}
li{{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:12px 14px;margin:8px 0}}
.t{{font-weight:600}}.no{{color:var(--muted);font-weight:400;margin-right:4px}}
.m{{color:var(--muted);font-size:13px;margin-top:2px}}.c{{margin-top:6px;display:flex;flex-wrap:wrap;gap:6px;align-items:center}}
.chip{{font-size:12px;border:1px solid var(--line);border-radius:999px;padding:1px 9px;color:var(--muted)}}
.chip.ok{{color:var(--ok);border-color:var(--ok)}}.chip.warn{{color:var(--warn);border-color:var(--warn)}}
.chip.inst{{color:var(--inst);border-color:var(--inst)}}.kw{{font-size:12px;color:var(--muted)}}
.links{{font-size:13px}}.links a{{color:var(--accent)}}.note,.empty{{color:var(--muted);font-size:14px}}
footer{{color:var(--muted);font-size:12px;margin-top:40px}}
</style></head><body><main>
<h1>PDF Arama Raporu</h1>
<p class="sub">{_h(label or "PDF'siz kaynaklar")} · {now:%d.%m.%Y %H:%M} · ~{minutes} dk{" · durduruldu" if stopped else ""}<br>
Aranan yerler: {_h(", ".join(searched))}</p>
<div class="stats">
<div class="stat"><b>{tried}</b><span>kaynak arandı</span></div>
<div class="stat ok"><b>{len(found)}</b><span>PDF bulunup bağlandı ({rate})</span></div>
<div class="stat warn"><b>{len(none)}</b><span>bulunamadı</span></div>
{f'<div class="stat"><b>{len(limited)}</b><span>ertelendi (site yoğun)</span></div>' if limited else ''}
{f'<div class="stat"><b>{len(had)}</b><span>bu arada PDF&#39;i gelmişti</span></div>' if had else ''}
</div>
{''.join(sections)}
<footer>{_h(APP_NAME)} v{_h(APP_VERSION)}</footer>
</main></body></html>"""
    folder.mkdir(parents=True, exist_ok=True)
    path.write_text(doc, encoding="utf-8")
    return path


def write_scan_report(path: Path, info: dict, found: list, added_items: list) -> Path:
    """found: [{"record", "hits", "status", "item_id"}] · added_items: o hafta eklenen kaynaklar"""
    groups = {}
    for entry in found:
        if entry["status"] in ("known", "thesis_skipped"):   # zaten raporlandı / PDF'siz tez eklenmedi
            continue
        for group in entry["hits"]:
            groups.setdefault(group, []).append(entry)
    scopus = load_scopus()
    status_label = {"pdf": ("PDF indirildi", "ok"), "nopdf": ("PDF yok", "warn"),
                    "institution": ("Kurum erişimi gerekebilir", "inst"), "known": ("Zaten kütüphanede", "muted"),
                    "thesis_closed": ("Tez · PDF'i yayımlanmamış", "warn"),
                    "thesis_failed": ("Tez · PDF indirilemedi", "warn"),
                    "thesis_untried": ("Tez · PDF denenmedi", "muted"),
                    "pdf_found": ("Kütüphanedeydi · PDF'i şimdi bulundu", "ok")}

    def card(entry, group):
        rec = dict(entry["record"])
        shown = finalize_record({k: rec.get(k) for k in RECORD_FIELDS if rec.get(k)})
        rec.update(title=shown["title"], year=shown["year"])
        authors = ", ".join(p.get("family", "") for p in (rec.get("authors") or [])[:4])
        if len(rec.get("authors") or []) > 4:
            authors += " vd."
        link = ("https://doi.org/" + rec["doi"]) if rec.get("doi") else rec.get("url", "")
        label, cls = status_label.get(entry["status"], ("", "muted"))
        db = database_for_doi(rec.get("doi", "")) if entry["status"] == "institution" else ""
        meta = " · ".join(x for x in (authors, rec.get("container"), rec.get("year")) if x)
        terms = ", ".join(dict.fromkeys(entry["hits"][group]))
        sc = scopus_label(dict(rec, issn=shown["issn"]), scopus)
        sc_chip = f'<span class="chip sc">{_h(sc)}</span>' if sc else ""
        title = _h(rec.get("title") or "(başlıksız)")
        title_html = f'<a href="{_h(link)}">{title}</a>' if link else title
        note = entry.get("note") or ""
        return (f'<li><div class="t">{title_html}</div><div class="m">{_h(meta)}</div>'
                f'<div class="c"><span class="chip {cls}">{_h(label)}{" · " + _h(db) if db else ""}'
                f'{" · " + _h(note) if note else ""}</span>'
                f'{sc_chip}<span class="chip">{_h(rec.get("source", ""))}</span>'
                f'<span class="kw">eşleşen: {_h(terms)}</span></div></li>')

    sections = []
    for group, entries in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        items = "".join(card(e, group) for e in entries)
        sections.append(f'<section><h2>{_h(group)} <small>{len(entries)}</small></h2><ul>{items}</ul></section>')
    if not sections:
        sections.append('<p class="empty">Bu dönemde anahtar kelimelerinizle eşleşen yeni yayın bulunmadı.</p>')

    def apa_html(item):
        return "".join(f"<i>{_h(t)}</i>" if italic else _h(t) for t, italic in apa_segments(item, "tr"))

    added_rows = "".join(
        f'<li><div class="t apa">{apa_html(i)}</div>'
        f'<div class="m">{_h({"tarama": "Taramadan", "geçmiş tarama": "Geçmiş taramadan", "indirme": "İndirmeden", "klasör": "Klasörden"}.get(i.get("source"), "Elle"))}'
        f'{" · PDF var" if i.get("file_path") else " · PDF yok"}</div></li>'
        for i in added_items)
    errors = "".join(f"<li>{_h(e)}</li>" for e in info.get("errors", []))
    pdf_count = sum(1 for e in found if e["status"] in ("pdf", "pdf_found"))
    new_count = sum(1 for e in found if e["status"] not in ("known", "pdf_found", "thesis_skipped"))
    doc = f"""<!doctype html><html lang="tr"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Tarama Raporu {_h(info['until'])}</title>
<style>
:root{{--bg:#f6f5f2;--card:#fff;--text:#1d1d1f;--muted:#6b6b70;--line:#e3e1dc;--accent:#1f6f4e;
--ok:#1f8f4e;--warn:#b7791f;--inst:#2b6cb0}}
@media (prefers-color-scheme:dark){{:root{{--bg:#16171a;--card:#1f2125;--text:#ececef;--muted:#9a9ca3;
--line:#2e3036;--accent:#5fc496;--ok:#5fc496;--warn:#e0b04c;--inst:#7fb3ee}}}}
*{{box-sizing:border-box}}body{{margin:0;background:var(--bg);color:var(--text);
font:15px/1.55 "Segoe UI",system-ui,sans-serif}}main{{max-width:880px;margin:0 auto;padding:32px 16px 64px}}
h1{{font-size:26px;margin:0 0 4px}}.sub{{color:var(--muted);margin:0 0 24px}}
.stats{{display:flex;flex-wrap:wrap;gap:12px;margin-bottom:28px}}
.stat{{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:12px 16px;min-width:130px}}
.stat b{{display:block;font-size:22px}}.stat span{{color:var(--muted);font-size:13px}}
h2{{font-size:18px;margin:28px 0 10px;padding-bottom:6px;border-bottom:1px solid var(--line)}}
h2 small{{color:var(--muted);font-weight:normal}}ul{{list-style:none;padding:0;margin:0}}
li{{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:12px 14px;margin:8px 0}}
.t{{font-weight:600}}.t.apa{{font-weight:400}}.t a{{color:var(--text);text-decoration:none}}.t a:hover{{color:var(--accent);text-decoration:underline}}
.m{{color:var(--muted);font-size:13px;margin-top:2px}}.c{{margin-top:6px;display:flex;flex-wrap:wrap;gap:6px;align-items:center}}
.chip{{font-size:12px;border:1px solid var(--line);border-radius:999px;padding:1px 9px;color:var(--muted)}}
.chip.ok{{color:var(--ok);border-color:var(--ok)}}.chip.warn{{color:var(--warn);border-color:var(--warn)}}
.chip.inst{{color:var(--inst);border-color:var(--inst)}}.chip.sc{{color:#e9711c;border-color:#e9711c}}.kw{{font-size:12px;color:var(--muted)}}
.empty{{color:var(--muted)}}footer{{color:var(--muted);font-size:12px;margin-top:40px}}
</style></head><body><main>
<h1>{_h(info.get('title') or 'Haftalık Tarama Raporu')}</h1>
<p class="sub">{_h(info['since'])} – {_h(info['until'])} arası · Kaynaklar: {_h(', '.join(info.get('sources', [])))}</p>
<div class="stats">
<div class="stat"><b>{new_count}</b><span>yeni yayın</span></div>
<div class="stat"><b>{pdf_count}</b><span>PDF indirildi</span></div>
<div class="stat"><b>{info.get('dergipark', 0)}</b><span>DergiPark kaydı tarandı</span></div>
<div class="stat"><b>{info.get('crossref', 0)}</b><span>Crossref kaydı tarandı</span></div>
{f'<div class="stat"><b>{info.get("openalex", 0)}</b><span>OpenAlex kaydı tarandı</span></div>' if "OpenAlex" in info.get("sources", []) else ''}
{f'<div class="stat"><b>{info.get("eric", 0)}</b><span>ERIC kaydı tarandı</span></div>' if "ERIC" in info.get("sources", []) else ''}
{f'<div class="stat"><b>{info.get("yok", 0)}</b><span>YÖK tezi tarandı</span></div>' if "YÖK Tez" in info.get("sources", []) else ''}
{f'<div class="stat"><b>{info.get("yok_skipped", 0)}</b><span>PDF&#39;i olmayan tez eklenmedi</span></div>' if info.get("yok_skipped") else ''}
{f'<div class="stat"><b>{len(added_items)}</b><span>kütüphaneye eklendi (tümü)</span></div>' if added_items else ''}
</div>
{''.join(sections)}
{f'<section><h2>Bu dönemde kütüphaneye eklenen tüm kaynaklar <small>{len(added_items)}</small></h2><ul>{added_rows}</ul></section>' if added_items else ''}
{f'<section><h2>Tarama sırasında oluşan sorunlar</h2><ul>{errors}</ul></section>' if errors else ''}
<footer>{_h(APP_NAME)} v{_h(APP_VERSION)} · {_h(info.get('created', ''))}</footer>
</main></body></html>"""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(doc, encoding="utf-8")
    return path


# ── Tarama işçisi ───────────────────────────────────────────────────────────

def utc_now() -> datetime:
    return datetime.now(timezone.utc).replace(tzinfo=None, microsecond=0)


def scan_lock_path() -> Path:
    return settings_path().parent / "tarama.lock"


def pid_alive(pid: int) -> bool:
    """Süreç hâlâ çalışıyor mu? (Windows'ta os.kill süreci öldürdüğü için kullanılmaz.)"""
    if pid <= 0:
        return False
    if sys.platform.startswith("win"):
        import ctypes
        kernel32 = ctypes.windll.kernel32
        handle = kernel32.OpenProcess(0x1000, False, pid)      # PROCESS_QUERY_LIMITED_INFORMATION
        if not handle:
            return False
        try:
            code = ctypes.c_ulong()
            kernel32.GetExitCodeProcess(handle, ctypes.byref(code))
            return code.value == 259                            # STILL_ACTIVE
        finally:
            kernel32.CloseHandle(handle)
    try:
        os.kill(pid, 0)
        return True
    except OSError:
        return False


def acquire_scan_lock() -> bool:
    """Aynı anda iki tarama (uygulama + zamanlanmış görev) çalışmasın. Yarıda kapanmış bir
    taramanın bıraktığı kilit (süreci artık yaşamıyorsa) yok sayılır."""
    path = scan_lock_path()
    try:
        if path.exists() and time.time() - path.stat().st_mtime < 3 * 3600:
            try:
                owner = int(path.read_text(encoding="utf-8").strip() or 0)
            except (OSError, ValueError):
                owner = 0
            if owner != os.getpid() and pid_alive(owner):
                return False
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(str(os.getpid()), encoding="utf-8")
        return True
    except OSError:
        return True


def release_scan_lock():
    try:
        scan_lock_path().unlink()
    except OSError:
        pass


# ── Geçmişe dönük tarama ayarları ve kaldığı yer ────────────────────────────
RETRO_PERIODS = {"Son 1 yıl": 1, "Son 3 yıl": 3, "Son 5 yıl": 5, "Son 10 yıl": 10, "Tüm zamanlar": 0}
RETRO_CROSSREF_LIMIT = {1: 300, 3: 600, 5: 1000, 10: 1500, 0: 2000}   # terim başına en ilgili kayıt
RETRO_OPENALEX_LIMIT = {1: 200, 3: 400, 5: 400, 10: 600, 0: 600}      # anahtarlı; anahtarsız 200
OPENALEX_WEEKLY_LOOKBACK = 120     # gün: dergiler sayıları geriye tarihli yayımlayabildiği için
RETRO_DOWNLOADS = {"Bulunanların hepsini dene": None, "En fazla 200 PDF": 200, "PDF indirme (yalnızca künye)": 0}
RETRO_SCOPES = {"Alan dergileri (önerilen)": "alan", "Alan + sosyal bilimler dergileri": "sosyal",
                "Bütün DergiPark (saatler sürer)": "tum"}


def retro_period_label(years: int) -> str:
    return next((k for k, v in RETRO_PERIODS.items() if v == years), f"Son {years} yıl")


def _retro_key(retro: dict) -> str:
    parts = [str(retro.get("years")), retro.get("scope", ""), str(retro.get("dergipark", True)),
             str(retro.get("crossref", True)), ",".join(sorted(retro.get("groups") or [])),
             str(retro.get("yok", True))]
    if retro.get("openalex") or retro.get("eric"):       # eski yarım taramaların anahtarı değişmesin
        parts += [str(bool(retro.get("openalex"))), str(bool(retro.get("eric")))]
    return hashlib.sha1("|".join(parts).encode("utf-8")).hexdigest()[:16]


def retro_state_for(retro: dict) -> dict:
    """Aynı seçeneklerle yarım kalmış tarama varsa onun durumu, yoksa yeni durum."""
    saved = _read_json(data_dir() / "gecmis_tarama.json")
    if saved.get("key") == _retro_key(retro):
        saved.setdefault("done", [])
        return saved
    return {"key": _retro_key(retro), "done": [], "retro": retro,
            "started": datetime.now().strftime("%d.%m.%Y %H:%M")}


def pending_retro():
    """Yarım kalmış geçmişe dönük tarama (ayarlarıyla) ya da None."""
    saved = _read_json(data_dir() / "gecmis_tarama.json")
    return saved if saved.get("key") and saved.get("retro") else None


def save_retro_state(state):
    path = data_dir() / "gecmis_tarama.json"
    try:
        if state is None:
            path.unlink(missing_ok=True)
        else:
            _write_json(path, state)
    except OSError:
        pass


class ScanWorker(threading.Thread):
    """Haftalık tarama. Mesajlar: ("scan_status", metin) · ("scan_progress", oran 0-1)
    · ("log", seviye, metin) · ("scan_finished", rapor_yolu | None, özet)"""

    def __init__(self, library, settings: dict, events, cancel_event):
        super().__init__(daemon=True)
        self.library = library
        self.settings = settings
        self.events = events
        self.cancel = cancel_event
        self.report_path = None
        self.summary = ""

    def status(self, text):
        self.events.put(("scan_status", text))
        diag(f"tarama: {text}", throttle=True)

    def log(self, level, text):
        self.events.put(("log", level, text))

    def run(self):
        diag("tarama başladı")
        if not acquire_scan_lock():
            diag("tarama: kilit dolu, başka tarama sürüyor")
            self.summary = "Başka bir tarama zaten çalışıyor."
            self.events.put(("scan_finished", None, self.summary))
            return
        try:
            self._run()
        except Exception as exc:
            diag_exception("tarama hatası")
            self.summary = f"Tarama yarıda kaldı: {describe_error(exc)}"
            self.log("error", self.summary)
            self.events.put(("scan_finished", None, self.summary))
        finally:
            diag(f"tarama bitti: {self.summary}")
            release_scan_lock()

    def _run(self):
        if self.settings.get("retro"):
            return self._run_retro()
        now = utc_now()
        last = self.settings.get("last_scan")
        try:
            since = datetime.fromisoformat(last) if last else now - timedelta(days=SCAN_FIRST_WINDOW_DAYS)
        except ValueError:
            since = now - timedelta(days=SCAN_FIRST_WINDOW_DAYS)
        if self.settings.get("force_days"):                # "Son 7 günü yeniden tara"
            since = now - timedelta(days=int(self.settings["force_days"]))
        since = max(since, now - timedelta(days=60))       # çok uzun aralar için sınır
        matcher = KeywordMatcher(parse_keyword_groups(load_keywords_text()))
        session = make_session()
        info = {"since": since.strftime("%d.%m.%Y"), "until": now.strftime("%d.%m.%Y"),
                "sources": [], "errors": [], "dergipark": 0, "crossref": 0, "openalex": 0, "eric": 0,
                "created": datetime.now().strftime("%d.%m.%Y %H:%M")}
        candidates = {}       # anahtar → {"record", "hits"}
        reached = []          # ulaşılabilen kaynaklar (hiçbiri yoksa tarama 'yapılmamış' sayılır)

        def key_of(rec):
            return (rec.get("doi") or "").lower() or rec.get("url") or fold(rec.get("title", ""))

        def consider(rec):
            # dergi adı bilerek dışarıda: 'Millî Folklor'da çıkan her makale 'folklor' bağlamı sayılmasın
            strong = " ".join([rec.get("title", ""), " ".join(rec.get("all_titles", [])),
                               " ".join(rec.get("subjects", [])), rec.get("keywords", "")])
            hits = matcher.match(rec.get("description", ""), strong=strong)
            if hits:
                k = key_of(rec)
                if k in candidates:
                    for g, terms in hits.items():
                        candidates[k]["hits"].setdefault(g, []).extend(terms)
                else:
                    candidates[k] = {"record": rec, "hits": hits}

        # 1) DergiPark
        if self.settings.get("scan_dergipark", True):
            self.status("DergiPark'taki yeni makaleler alınıyor…")
            info["sources"].append("DergiPark")
            try:
                def progress(done, total):
                    self.events.put(("scan_progress", min(done / total, 1.0) * 0.6 if total else 0.3))
                    self.status(f"DergiPark: {done}{' / ' + str(total) if total else ''} kayıt incelendi")
                for rec in harvest_dergipark(session, since, now, progress, self.cancel):
                    info["dergipark"] += 1
                    consider(rec)
                reached.append("DergiPark")
            except Exception as exc:
                info["errors"].append(f"DergiPark: {describe_error(exc)}")
                self.log("warn", f"DergiPark taranamadı: {describe_error(exc)}")

        # 2) Crossref
        if self.settings.get("scan_crossref", True) and not self.cancel.is_set():
            info["sources"].append("Crossref")
            queries = matcher.search_terms()
            failures_in_row = 0
            for n, (group, query) in enumerate(queries, start=1):
                if self.cancel.is_set():
                    break
                self.status(f"Crossref: “{query}” aranıyor ({n}/{len(queries)})")
                self.events.put(("scan_progress", 0.6 + 0.25 * n / max(len(queries), 1)))
                try:
                    for rec in search_crossref(session, query, since):
                        info["crossref"] += 1
                        consider(rec)
                    failures_in_row = 0
                    if "Crossref" not in reached:
                        reached.append("Crossref")
                except Exception as exc:
                    failures_in_row += 1
                    info["errors"].append(f"Crossref “{query}”: {describe_error(exc)}")
                    if failures_in_row >= 3:      # internet yok ya da Crossref kapalı: boşuna bekleme
                        info["errors"].append("Crossref'e üst üste ulaşılamadı; bu hafta Crossref taraması atlandı.")
                        self.log("warn", "Crossref'e ulaşılamadı; Crossref taraması atlandı.")
                        break
                time.sleep(0.3)

        # 2b) OpenAlex ve ERIC: her terim için en yeni yayınlar
        email = self.settings.get("email", "")
        extra = []
        if self.settings.get("scan_openalex", True):
            extra.append(("OpenAlex", "openalex", batch_terms(matcher.search_terms()),
                          lambda q: search_openalex(session, q, since - timedelta(days=OPENALEX_WEEKLY_LOOKBACK),
                                                    limit=200, newest_first=True, email=email)))
        if self.settings.get("scan_eric", True):
            extra.append(("ERIC", "eric", batch_terms([(g, q) for g, q in matcher.search_terms() if eric_query_ok(q)]),
                          lambda q: search_eric(session, q, since_year=since.year - 1, limit=200)))
        for name, counter, queries, run in extra:
            if self.cancel.is_set():
                break
            info["sources"].append(name)
            self._search_source(name, counter, queries, run, consider, info, reached)

        # 3) YÖK Ulusal Tez Merkezi: yeni tezler (bu yıl ve geçen yıl)
        if self.settings.get("scan_yok", True) and not self.cancel.is_set():
            info["sources"].append("YÖK Tez")
            this_year = now.year

            def recent(rec):
                y = re.search(r"\d{4}", rec.get("year") or "")
                return bool(y) and int(y.group(0)) >= this_year - 1
            queries = yok_queries(matcher, include_context=False)
            failures = 0
            for n, query in enumerate(queries, start=1):
                if self.cancel.is_set():
                    break
                self.status(f"YÖK Tez: “{query}” aranıyor ({n}/{len(queries)})")
                try:
                    self._collect_yok(query, candidates, matcher, info, recent)
                    failures = 0
                    if "YÖK Tez" not in reached:
                        reached.append("YÖK Tez")
                except Exception as exc:
                    failures += 1
                    info["errors"].append(f"YÖK Tez “{query}”: {describe_error(exc)}")
                    if failures >= 3:
                        self.log("warn", "YÖK Tez Merkezi'ne ulaşılamadı; tez taraması atlandı.")
                        break

        # 4) Kütüphaneye ekleme + açık erişim PDF
        found = []
        self._prepare_downloads(info)
        self._process(session, candidates, found, info, SCAN_MAX_DOWNLOADS, "tarama")
        session.close()

        if not reached:
            self.summary = ("Hiçbir kaynağa ulaşılamadı (internet bağlantısını kontrol edin); "
                            "tarama bir sonraki açılışta yeniden denenecek.")
            self.log("warn", self.summary)
            self.events.put(("scan_progress", 0.0))
            self.events.put(("scan_finished", None, self.summary))
            return
        added_items = self.library.items_added_since(since.strftime("%Y-%m-%d"))
        folder = Path(self.library_folder or settings_path().parent) / "Tarama Raporları"
        self.report_path = write_scan_report(folder / f"Tarama_{datetime.now():%Y-%m-%d_%H%M%S}.html",
                                             info, found, added_items)
        new = sum(1 for e in found if e["status"] not in ("known", "thesis_skipped"))
        pdfs = sum(1 for e in found if e["status"] == "pdf")
        self.summary = f"{new} yeni yayın bulundu, {pdfs} tanesinin PDF'i indi."
        failed = len(set(getattr(self, "failed_theses", [])))
        if failed:
            self.summary += f" {failed} izinli tezin PDF'i indirilemedi."
        if not self.cancel.is_set():
            self.settings["last_scan"] = now.isoformat()
            self.settings["last_report"] = str(self.report_path)
            current = load_settings()
            current.update(last_scan=self.settings["last_scan"], last_report=self.settings["last_report"])
            save_settings(current)
        self.events.put(("scan_progress", 1.0))
        self.events.put(("scan_finished", str(self.report_path), self.summary))


    def _search_source(self, name, counter, queries, run, consider, info, reached, state=None, after=None):
        """Bir arama kaynağında her terimi sorgular. Günlük sınır dolarsa (429) o kaynak bu tarama için
        bırakılır; geçmişe dönük taramada kalan terimler sonraki çalıştırmada kaldığı yerden devam eder.
        after(query): her terimden sonra (geçmişe dönük taramada bulunanları işlemek için)."""
        failures = 0
        for n, (group, query) in enumerate(queries, start=1):
            if self.cancel.is_set():
                return
            step = f"{counter}:{query}"
            if state is not None and step in state["done"]:
                continue
            self.status(f"{name}: “{query[:70]}{'…' if len(query) > 70 else ''}” aranıyor ({n}/{len(queries)})")
            try:
                for rec in run(query):
                    info[counter] = info.get(counter, 0) + 1
                    consider(rec)
                failures = 0
                if name not in reached:
                    reached.append(name)
            except RateLimited as exc:
                if state is not None:
                    self.limited_sources = getattr(self, "limited_sources", []) + [name]
                info["errors"].append(f"{name}: {describe_error(exc)}; kalan terimler bu taramada atlandı.")
                self.log("warn", f"{name}: {describe_error(exc)}")
                return
            except Exception as exc:
                failures += 1
                info["errors"].append(f"{name} “{query}”: {describe_error(exc)}")
                if failures >= 3:
                    info["errors"].append(f"{name}'e üst üste ulaşılamadı; {name} taraması atlandı.")
                    self.log("warn", f"{name}'e ulaşılamadı; {name} taraması atlandı.")
                    return
                continue
            if after is not None:
                after(query)
            if state is not None and not self.cancel.is_set():
                state["done"].append(step)
                save_retro_state(state)

    # ── bulunanları kütüphaneye işleme (haftalık ve geçmişe dönük ortak) ─────────────────
    def _prepare_downloads(self, info):
        self.library_folder = self.settings.get("library_folder") or None
        if self.library_folder:
            try:
                Path(self.library_folder).mkdir(parents=True, exist_ok=True)
            except OSError as exc:
                info["errors"].append(f"Kütüphane klasörü oluşturulamadı: {describe_error(exc)}")
                self.library_folder = None
        self.downloader = DownloadWorker([], self.library_folder or str(Path.home()), {
            "find_pdf": True, "save_html": False, "email": self.settings.get("email", ""),
            "library": self.library, "library_folder": self.library_folder}, queue.Queue(), self.cancel)
        self.attempts = 0

    def _process(self, session, candidates, found, info, max_downloads, source, label="Yeni yayınlar"):
        library_folder, downloader = self.library_folder, self.downloader
        total = len(candidates)
        for n, entry in enumerate(list(candidates.values()), start=1):
            if self.cancel.is_set():
                break
            rec, hits = entry["record"], entry["hits"]
            if source == "tarama":
                self.events.put(("scan_progress", 0.85 + 0.15 * n / max(total, 1)))
            self.status(f"{label} kütüphaneye ekleniyor ({n}/{total})")
            known = (self.library.find_by_doi(rec.get("doi")) or self.library.find_by_url(rec.get("url"))
                     or self.library.find_by_title(rec.get("title"))
                     or (rec.get("tez_no") and self.library.find_by_tez_no(rec["tez_no"])))
            if known:
                status = "known"
                if rec.get("source") == "YÖK Tez" and rec.get("yok_keys") and max_downloads != 0:
                    status = self._retry_known_thesis(rec, known, info) or "known"
                elif getattr(self, "retry_missing_pdf", False) and max_downloads != 0:
                    status = self._retry_pdf(session, rec, known, n, max_downloads, info) or "known"
                found.append({"record": rec, "hits": hits, "status": status, "item_id": known})
                continue
            if rec.get("source") == "YÖK Tez":
                status, item_id, *note = self._add_thesis(rec, hits, source, max_downloads, info)
                found.append({"record": rec, "hits": hits, "status": status, "item_id": item_id,
                              "note": note[0] if note else ""})
                continue
            if rec.get("source") in ("Crossref", "OpenAlex") and rec.get("doi"):
                full = crossref_record(session, rec["doi"])         # cilt, sayı, sayfa, yayınevi
                if full:
                    rec = dict(merge_records(full, rec), source=rec["source"], url=rec.get("url", ""),
                               pdf_url=rec.get("pdf_url", ""))
                    entry["record"] = rec
            tags = list(hits)
            matched = describe_hits(hits)
            status, item_id = "nopdf", None
            link = ("https://doi.org/" + rec["doi"]) if rec.get("doi") else (rec.get("pdf_url") or rec.get("url"))
            if link and (max_downloads is None or self.attempts < max_downloads) and library_folder:
                self.attempts += 1
                try:
                    downloader._last_saved = None
                    downloader._tried = set()
                    result = downloader._download_one(session, link, n)
                    saved = downloader._last_saved
                    if result[0] == "ok" and saved:
                        item_id, _ = catalog_pdf(self.library, session, saved["path"], saved["sha"],
                                                 meta=saved["meta"], url=rec.get("url") or link,
                                                 doi=rec.get("doi") or None, tags=tags,
                                                 library_folder=library_folder, source=source,
                                                 is_new=True, matched=matched,
                                                 known={k: rec.get(k) for k in RECORD_FIELDS if rec.get(k)})
                        status = "pdf"
                except Exception as exc:
                    info["errors"].append(f"{rec.get('title', '')[:60]}: {describe_error(exc)}")
            if item_id is None:
                record = {k: rec.get(k) for k in RECORD_FIELDS if rec.get(k)}
                item_id, _ = self.library.add(record, tags=tags, source=source, is_new=True,
                                              matched=matched)
                if rec.get("doi") and database_for_doi(rec["doi"]):
                    status = "institution"
            else:
                self.library.update(item_id, {"is_new": 1, "matched": matched})
            found.append({"record": rec, "hits": hits, "status": status, "item_id": item_id})

    def _retry_known_thesis(self, rec, item_id, info):
        """Kütüphanede PDF'siz duran YÖK tezini (izinliyse) indirir; kotadan sayılmaz, günde bir kez denenir."""
        item = self.library.get(item_id)
        if not item or (item["file_path"] and os.path.exists(item["file_path"])) or not self.library_folder:
            return None
        today = datetime.now().strftime("%Y-%m-%d")
        if item.get("pdf_tried") == today:
            return None
        self.library.update(item_id, {"pdf_tried": today})
        if not yok_tez_no(item) and rec.get("tez_no"):
            self.library.update(item_id, {"notes": "\n".join(filter(None, [item.get("notes"),
                                                                           f"YÖK Tez No: {rec['tez_no']}"]))})
        status, _ = self._fetch_thesis(rec, item_id, None, info)
        return "pdf_found" if status == "pdf" else None

    def _retry_pdf(self, session, rec, item_id, n, max_downloads, info):
        """Kütüphanede PDF'siz duran kaynağın PDF'ini yeniden dener (7 günde en fazla bir kez)."""
        item = self.library.get(item_id)
        if not item or (item["file_path"] and os.path.exists(item["file_path"])) or not self.library_folder:
            return None
        today = datetime.now().strftime("%Y-%m-%d")
        if item.get("pdf_tried") and item["pdf_tried"] > (datetime.now() - timedelta(days=7)).strftime("%Y-%m-%d"):
            return None
        if max_downloads is not None and self.attempts >= max_downloads:
            return None
        self.attempts += 1
        self.library.update(item_id, {"pdf_tried": today})
        try:
            if rec.get("source") == "YÖK Tez" and rec.get("yok_keys"):
                yses = self._yok()
                url = yok_pdf_url(yses, rec["yok_keys"])
                time.sleep(YOK_PAUSE)
                if not url:
                    return None
                tmp = Path(self.library_folder) / f".yok_{rec.get('tez_no') or item_id}.part"
                with yses.get(url, stream=True, timeout=(15, 180)) as r:
                    r.raise_for_status()
                    with open(tmp, "wb") as fh:
                        for block in r.iter_content(1 << 16):
                            fh.write(block)
                if tmp.read_bytes()[:1024].find(b"%PDF-") < 0:
                    tmp.unlink(missing_ok=True)
                    return None
                attach_pdf(self.library, item_id, tmp, self.library_folder, move=True)
                return "pdf_found"
            doi = rec.get("doi") or item.get("doi")
            link = ("https://doi.org/" + doi) if doi else (rec.get("url") or item.get("url"))
            if not link or session is None:
                return None
            self.downloader._last_saved = None
            self.downloader._tried = set()
            result = self.downloader._download_one(session, link, n)
            saved = self.downloader._last_saved
            if result[0] != "ok" or not saved:
                return None
            other = self.library.find_by_sha(saved["sha"])
            if other and other != item_id:                      # bu PDF başka bir kaynağa ait
                return None
            attach_pdf(self.library, item_id, saved["path"], self.library_folder, move=True)
            return "pdf_found"
        except Exception as exc:
            info["errors"].append(f"{(item.get('title') or '')[:60]}: {describe_error(exc)}")
            return None

    def _yok(self):
        if getattr(self, "yok_session", None) is None:
            self.yok_session = make_session()
            yok_open_session(self.yok_session)
        return self.yok_session

    def _add_thesis(self, rec, hits, source, max_downloads, info):
        """YÖK tezini kütüphaneye ekler; yazar izin verdiyse PDF'ini indirir. 'PDF'i yayımlanmamış tezleri
        ekleme' açıksa (varsayılan) PDF'i olmayan tez hiç eklenmez."""
        session = self._yok()
        if self.settings.get("yok_skip_closed", True):
            try:
                url = yok_pdf_url(session, rec["yok_keys"])
                time.sleep(YOK_PAUSE)
            except Exception as exc:
                info["errors"].append(f"YÖK Tez {rec.get('tez_no')}: {describe_error(exc)}")
                url = "?"                                   # bilinmiyor: eskisi gibi ekle
            if not url:
                info["yok_skipped"] = info.get("yok_skipped", 0) + 1
                return "thesis_skipped", None
        try:
            detail = yok_detail(session, rec["yok_keys"])
            time.sleep(YOK_PAUSE)
        except Exception:
            detail = {}
        if detail.get("yer"):
            rec["institution"] = _yok_name(str(detail["yer"]).split("/")[0].strip()) or rec["institution"]
        record = {k: rec.get(k) for k in RECORD_FIELDS if rec.get(k)}
        record["keywords"] = join_keywords(yok_keywords(detail.get("anahtarKelimeTr") or detail.get("anahtarKelimeEn")))
        tags = list(hits)
        matched = describe_hits(hits)
        item_id, _ = self.library.add(record, tags=tags, source=source, is_new=True, matched=matched)
        notes = f"YÖK Tez No: {rec.get('tez_no')}" + (f" · {rec.get('thesis_kind')}" if rec.get("thesis_kind") else "")
        danisman = _strip_tags(detail.get("danisman") or "")
        if danisman:
            notes += f" · {danisman}"
        self.library.update(item_id, {"notes": notes})
        abstract = _strip_tags(detail.get("trOzet") or detail.get("enOzet") or "")
        if abstract:
            self.library.set_fulltext(item_id, abstract)
        status, note = self._fetch_thesis(rec, item_id, max_downloads, info)
        return status, item_id, note

    def _fetch_thesis(self, rec, item_id, max_downloads, info):
        """İzinli tezin PDF'ini indirir. Tezler ortak indirme kotasından sayılmaz (az sayıda ve resmî kaynak);
        yalnızca 'PDF indirme (yalnızca künye)' seçiliyse denenmez. Dönüş: (durum, açıklama)"""
        if not self.library_folder or max_downloads == 0:
            return "thesis_untried", "PDF indirme bu taramada kapalıydı"
        try:
            tmp, kind, reason = yok_download(self._yok(), rec["yok_keys"], self.library_folder,
                                             rec.get("tez_no") or item_id)
        except Exception as exc:
            tmp, kind, reason = None, "failed", "indirme başarısız: " + describe_error(exc)
        if tmp:
            attach_pdf(self.library, item_id, tmp, self.library_folder, move=True)
            return "pdf", ""
        if kind == "closed":
            return "thesis_closed", reason
        info["errors"].append(f"YÖK Tez {rec.get('tez_no')}: {reason}")
        self.failed_theses = getattr(self, "failed_theses", []) + [item_id]
        return "thesis_failed", reason

    def _collect_yok(self, query, candidates, matcher, info, year_ok=None):
        for rec in search_yok(self._yok(), query):
            info["yok"] = info.get("yok", 0) + 1
            if year_ok and not year_ok(rec):
                continue
            strong = " ".join([rec["title"], " ".join(rec["all_titles"]), " ".join(rec["subjects"])])
            hits = matcher.match("", strong=strong)
            if hits:
                k = "yok:" + (rec.get("tez_no") or fold(rec["title"]))
                if k in candidates:
                    for g, terms in hits.items():
                        candidates[k]["hits"].setdefault(g, []).extend(terms)
                else:
                    candidates[k] = {"record": rec, "hits": hits}
        time.sleep(YOK_PAUSE)

    # ── geçmişe dönük tarama: 'tüm zamanlar' dahil, kaldığı yerden sürdürülebilir ─────────────
    def _run_retro(self):
        retro = self.settings["retro"]
        years = int(retro.get("years") or 0)
        now = utc_now()
        since = now - timedelta(days=365 * years) if years else None
        groups = parse_keyword_groups(load_keywords_text())
        if retro.get("groups"):
            groups = [g for g in groups if g["name"] in retro["groups"]] or groups
        matcher = KeywordMatcher(groups)
        max_downloads = retro.get("max_downloads")              # None: hepsi, 0: indirme yok
        state = retro_state_for(retro)
        session = make_session()
        period = retro_period_label(years)
        info = {"since": since.strftime("%d.%m.%Y") if since else "en eski kayıt",
                "until": now.strftime("%d.%m.%Y"), "sources": [], "errors": [], "dergipark": 0,
                "crossref": 0, "openalex": 0, "eric": 0, "created": datetime.now().strftime("%d.%m.%Y %H:%M"),
                "title": f"Geçmişe Dönük Tarama · {period}"}
        found, reached = [], []
        self._prepare_downloads(info)
        self.retry_missing_pdf = True

        def year_ok(rec):
            if not since:
                return True
            m = re.search(r"\b(1[5-9]\d\d|20\d\d)\b", str(rec.get("year") or ""))
            return not m or int(m.group(1)) >= since.year

        def collect(records, candidates, counter):
            for rec in records:
                if counter:
                    info[counter] = info.get(counter, 0) + 1
                if not year_ok(rec):
                    continue
                strong = " ".join([rec.get("title", ""), " ".join(rec.get("all_titles", [])),
                                   " ".join(rec.get("subjects", [])), rec.get("keywords", "")])
                hits = matcher.match(rec.get("description", ""), strong=strong)
                if hits:
                    k = (rec.get("doi") or "").lower() or rec.get("url") or fold(rec.get("title", ""))
                    if k in candidates:
                        for g, terms in hits.items():
                            candidates[k]["hits"].setdefault(g, []).extend(terms)
                    else:
                        candidates[k] = {"record": rec, "hits": hits}

        # 1) DergiPark: alan dergileri baştan sona ya da bütün DergiPark yıl yıl
        chunks = []
        if retro.get("dergipark", True):
            info["sources"].append("DergiPark")
            try:
                if retro.get("scope") == "tum":
                    first = since.year if since else 2005
                    chunks = [("yil", str(y), str(y)) for y in range(now.year, first - 1, -1)]
                else:
                    self.status("DergiPark dergi listesi alınıyor…")
                    sets = relevant_journal_sets(dergipark_sets(session), retro.get("scope") == "sosyal")
                    chunks = [("dergi", spec, name) for spec, name in sets]
                reached.append("DergiPark")
            except Exception as exc:
                info["errors"].append(f"DergiPark dergi listesi alınamadı: {describe_error(exc)}")
                self.log("warn", f"DergiPark'a ulaşılamadı: {describe_error(exc)}")
        queries = matcher.search_terms(with_context=True) if retro.get("crossref", True) else []
        steps = len(chunks) + len(queries)
        done_steps = 0
        for kind, key, name in chunks:
            if self.cancel.is_set():
                break
            done_steps += 1
            chunk_id = f"{kind}:{key}"
            if chunk_id in state["done"]:
                continue
            self.events.put(("scan_progress", done_steps / max(steps, 1)))
            label = f"DergiPark {key}" if kind == "yil" else name
            candidates = {}
            try:
                def progress(done, total, label=label):
                    self.status(f"{label}: {done}{' / ' + str(total) if total else ''} kayıt "
                                f"({done_steps}/{steps})")
                if kind == "yil":
                    records = harvest_dergipark(session, datetime(int(key), 1, 1, tzinfo=timezone.utc),
                                                progress=progress, cancel=self.cancel, until_date=f"{key}-12-31")
                else:
                    records = harvest_dergipark(session, None, progress=progress, cancel=self.cancel,
                                                set_spec=key)
                collect(records, candidates, "dergipark")
            except Exception as exc:
                info["errors"].append(f"{label}: {describe_error(exc)}")
                continue
            self._process(session, candidates, found, info, max_downloads, "geçmiş tarama", label)
            if not self.cancel.is_set():
                state["done"].append(chunk_id)
                save_retro_state(state)

        # 1b) YÖK Ulusal Tez Merkezi: her terimde bulunan bütün tezler (en eskisine kadar)
        if retro.get("yok", True) and not self.cancel.is_set():
            info["sources"].append("YÖK Tez")
            yq = yok_queries(matcher)
            failures = 0
            for n, query in enumerate(yq, start=1):
                if self.cancel.is_set():
                    break
                if "yok:" + query in state["done"]:
                    continue
                self.status(f"YÖK Tez: “{query}” ({n}/{len(yq)})")
                candidates = {}
                try:
                    self._collect_yok(query, candidates, matcher, info, year_ok)
                    failures = 0
                    if "YÖK Tez" not in reached:
                        reached.append("YÖK Tez")
                except Exception as exc:
                    failures += 1
                    info["errors"].append(f"YÖK Tez “{query}”: {describe_error(exc)}")
                    if failures >= 3:
                        self.log("warn", "YÖK Tez Merkezi'ne ulaşılamadı; tez taraması atlandı.")
                        break
                    continue
                self._process(None, candidates, found, info, max_downloads, "geçmiş tarama", "Tezler")
                if not self.cancel.is_set():
                    state["done"].append("yok:" + query)
                    save_retro_state(state)

        # 2) Crossref: her terim için tüm zamanlarda en ilgili yayınlar
        if queries and not self.cancel.is_set():
            info["sources"].append("Crossref")
            limit = RETRO_CROSSREF_LIMIT.get(years, RETRO_CROSSREF_LIMIT[0])
            failures_in_row = 0
            for group, query in queries:
                if self.cancel.is_set():
                    break
                done_steps += 1
                if "crossref:" + query in state["done"]:
                    continue
                self.events.put(("scan_progress", done_steps / max(steps, 1)))
                self.status(f"Crossref: “{query}” ({done_steps}/{steps})")
                candidates = {}
                try:
                    collect(search_crossref_deep(session, query, since, limit), candidates, "crossref")
                    failures_in_row = 0
                    if "Crossref" not in reached:
                        reached.append("Crossref")
                except Exception as exc:
                    failures_in_row += 1
                    info["errors"].append(f"Crossref “{query}”: {describe_error(exc)}")
                    if failures_in_row >= 3:
                        self.log("warn", "Crossref'e ulaşılamadı; Crossref taraması atlandı.")
                        break
                    continue
                self._process(session, candidates, found, info, max_downloads, "geçmiş tarama", "Crossref")
                if not self.cancel.is_set():
                    state["done"].append("crossref:" + query)
                    save_retro_state(state)

        # 3) OpenAlex (makale, kitap, bölüm, tez, kurum arşivleri) ve ERIC (eğitim araştırmaları)
        email = self.settings.get("email", "")
        all_terms = matcher.search_terms(with_context=True)
        extra = []
        if retro.get("openalex"):
            oa_limit = RETRO_OPENALEX_LIMIT.get(years, 600) if openalex_params().get("api_key") else 200
            extra.append(("OpenAlex", "openalex", all_terms,
                          lambda q: search_openalex(session, q, since, limit=oa_limit, email=email)))
        if retro.get("eric"):
            extra.append(("ERIC", "eric", [(g, q) for g, q in all_terms if eric_query_ok(q)],
                          lambda q: search_eric(session, q, since_year=since.year if since else None,
                                                limit=RETRO_CROSSREF_LIMIT.get(years, 600))))
        for name, counter, terms, run in extra:
            if self.cancel.is_set():
                break
            info["sources"].append(name)
            bucket = {}

            def consider(rec, bucket=bucket, counter=counter):
                collect([rec], bucket, None)

            def after(query, bucket=bucket, name=name):
                self._process(session, bucket, found, info, max_downloads, "geçmiş tarama", name)
                bucket.clear()
            self._search_source(name, counter, terms, run, consider, info, reached, state=state, after=after)
        session.close()

        new = sum(1 for e in found if e["status"] not in ("known", "pdf_found", "thesis_skipped"))
        pdfs = sum(1 for e in found if e["status"] == "pdf")
        later = sum(1 for e in found if e["status"] == "pdf_found")
        limited = getattr(self, "limited_sources", [])
        finished = not self.cancel.is_set() and bool(reached) and not limited
        if finished:
            save_retro_state(None)
        folder = Path(self.library_folder or settings_path().parent) / "Tarama Raporları"
        self.report_path = write_scan_report(folder / f"Gecmis_Tarama_{datetime.now():%Y-%m-%d_%H%M%S}.html",
                                             info, found, []) if found else None
        if not reached:
            self.summary = "Hiçbir kaynağa ulaşılamadı (internet bağlantısını kontrol edin)."
        elif finished:
            self.summary = (f"Geçmişe dönük tarama bitti ({period}): {new} yeni kaynak, {pdfs} PDF"
                            + (f"; PDF'siz duran {later} kaynağın PDF'i de bulundu." if later else "."))
            failed = len(set(getattr(self, "failed_theses", [])))
            if failed:
                self.summary += f" {failed} izinli tezin PDF'i indirilemedi."
        elif limited and not self.cancel.is_set():
            self.summary = (f"Geçmişe dönük tarama şimdilik bitti: {new} yeni kaynak, {pdfs} PDF. "
                            f"{', '.join(limited)} günlük kullanım sınırına ulaştı; yarın 'Geçmişe Dönük Tara' → "
                            "'Kaldığı Yerden Devam Et' ile kalan terimler taranır.")
        else:
            self.summary = (f"Geçmişe dönük tarama durduruldu: şimdiye dek {new} yeni kaynak, {pdfs} PDF. "
                            "Aynı seçeneklerle yeniden başlatınca kaldığı yerden sürer.")
        self.events.put(("scan_progress", 1.0 if finished else 0.0))
        self.events.put(("scan_finished", str(self.report_path) if self.report_path else None, self.summary))

def scan_due(settings: dict) -> bool:
    last = settings.get("last_scan")
    if not last:
        return True
    try:
        return utc_now() - datetime.fromisoformat(last) >= timedelta(days=SCAN_INTERVAL_DAYS)
    except ValueError:
        return True


# ── Windows görev zamanlayıcısı ─────────────────────────────────────────────

TASK_NAME = "AkademikIndirici\\Haftalik Tarama"
WEEKDAYS = {"Pazartesi": "MON", "Salı": "TUE", "Çarşamba": "WED", "Perşembe": "THU",
            "Cuma": "FRI", "Cumartesi": "SAT", "Pazar": "SUN"}


def task_commands(day: str, hour: str):
    """Haftalık görevi kurma/kaldırma komutları. Uygulama bunları KENDİSİ çalıştırmaz:
    imzasız bir programın gizlice görev zamanlayıcısına dokunması Windows Defender'ın
    davranış tespitini tetikliyor (Behavior:Win32/Execution). Komutu kullanıcı bir kez
    Komut İstemi'ne yapıştırır."""
    exe = sys.executable if getattr(sys, "frozen", False) else "AkademikIndirici.exe"
    create = (f'schtasks /Create /F /SC WEEKLY /D {WEEKDAYS.get(day, "MON")} /ST {hour} '
              f'/TN "{TASK_NAME}" /TR "\\"{exe}\\" --tara"')
    delete = f'schtasks /Delete /F /TN "{TASK_NAME}"'
    return create, delete


def run_headless_scan():
    """Zamanlanmış görev: arayüz açmadan tarar, raporu yazar ve tarayıcıda açar."""
    settings = load_settings()
    library = Library()
    sync = LibrarySync(library)
    try:
        if sync.status() == "al":
            sync.pull()
            settings = load_settings()
    except Exception:
        diag_exception("tarama öncesi eşitleme")
    events = queue.Queue()
    worker = ScanWorker(library, settings, events, threading.Event())
    worker.run()
    try:
        if sync.status() in ("gonder", "ilk"):
            sync.push()
            write_phone_export(library, settings.get("library_folder"))
    except Exception:
        diag_exception("tarama sonrası eşitleme")
    library.close()
    if worker.report_path and settings.get("open_report", True):
        webbrowser.open(Path(worker.report_path).as_uri())


# ════════════════════════════════════════════════════════════════════════════
#  5b) ORTAK KÜTÜPHANE (Google Drive / OneDrive): kütüphane klasörü bulutta durur; her
#      bilgisayar kendi kopyasıyla çalışır, kopyalar klasördeki "_Kütüphane Verisi"nde buluşur.
#      Veritabanı doğrudan bulutta açılmaz (eşitleme onu bozabilir); anlık kopyası alınıp verilir.
# ════════════════════════════════════════════════════════════════════════════

SHARED_DIR_NAME = "_Kütüphane Verisi"
SHARED_DB_NAME = "kutuphane.db"
SHARED_META_NAME = "kutuphane_bilgi.json"
SHARED_STATE_NAME = "tarama_durumu.json"
PHONE_EXPORT_NAME = "Kütüphane (telefon için).xlsx"
SESSION_FRESH_MINUTES = 12


def machine_name() -> str:
    import platform
    return os.environ.get("COMPUTERNAME") or platform.node() or "bilgisayar"


_DIR_CACHE = {}
_MADE_DIRS = set()


def _isdir_cached(folder) -> bool:
    """Bulut klasörü (Drive) yoklaması yavaş olabildiği için sonucu kısa süre saklar."""
    now = time.monotonic()
    hit = _DIR_CACHE.get(folder)
    if hit and now - hit[1] < (120 if hit[0] else 10):
        return hit[0]
    ok = os.path.isdir(folder)
    _DIR_CACHE[folder] = (ok, now)
    return ok


def shared_dir(settings=None):
    """Ortak kütüphane açıksa ve klasöre ulaşılabiliyorsa '_Kütüphane Verisi' klasörü, değilse None."""
    s = settings if settings is not None else _load_settings_raw()
    folder = s.get("library_folder")
    if not s.get("shared_library") or not folder or not _isdir_cached(folder):
        return None
    return Path(folder) / SHARED_DIR_NAME


def data_dir() -> Path:
    """Anahtar kelimeler, Scopus listesi ve indirme geçmişi: ortak kütüphanede bulutta, değilse bu bilgisayarda."""
    shared = shared_dir()
    if shared is not None:
        if str(shared) in _MADE_DIRS:
            return shared
        try:
            shared.mkdir(parents=True, exist_ok=True)
            _MADE_DIRS.add(str(shared))
            return shared
        except OSError:
            pass
    return settings_path().parent


_SHARED_STATE = {"path": "", "data": {}, "t": None}


def shared_state(shared, max_age=120.0) -> dict:
    """Buluttaki tarama durumu (son tarama tarihi). Arayüz iş parçacığı bulutu beklemesin diye bellekten
    okunur; arka plan eşitlemesi max_age=0 ile tazeler."""
    path = str(Path(shared) / SHARED_STATE_NAME)
    c = _SHARED_STATE
    if c["path"] == path and c["t"] is not None and max_age > 0:
        if time.monotonic() - c["t"] < max_age or threading.current_thread() is threading.main_thread():
            return dict(c["data"])
    data = _read_json(path)
    c.update(path=path, data=data, t=time.monotonic())
    return dict(data)


def _read_json(path):
    try:
        with open(path, encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def _write_json(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(data, fh, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def _file_stat(path):
    try:
        st = os.stat(path)
        return [st.st_mtime_ns, st.st_size]
    except OSError:
        return None


def _file_hash(path) -> str:
    h = hashlib.sha256()
    try:
        with open(path, "rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
    except OSError:
        return ""
    return h.hexdigest()


def _rotate_backups(folder: Path, prefix: str, keep: int = 5):
    files = sorted(folder.glob(prefix + "*.db"), key=lambda p: p.stat().st_mtime, reverse=True)
    for old in files[keep:]:
        try:
            old.unlink()
        except OSError:
            pass


class LibrarySync:
    """Bu bilgisayarın kütüphanesi ile buluttaki ortak kopya arasındaki eşitleme.
    Durumlar: kapali · ilk (bulutta kopya yok) · esit · gonder (burada değişti) ·
    al (öbür bilgisayarda değişti) · cakisma (ikisinde de değişti)"""

    def __init__(self, library):
        self.lib = library
        self.op_lock = threading.RLock()        # gönder/al/birleştir aynı anda iki kez çalışmasın

    # yardımcılar
    def folder(self):
        return shared_dir()

    def _state(self) -> dict:
        return _load_settings_raw().get("sync") or {}

    def _save_state(self, **kw):
        with _SETTINGS_LOCK:
            s = _load_settings_raw()
            state = s.get("sync") or {}
            state.update(kw)
            s["sync"] = state
            save_settings(s)

    def meta(self) -> dict:
        folder = self.folder()
        return _read_json(folder / SHARED_META_NAME) if folder else {}

    def local_changed(self) -> bool:
        state = self._state()
        if "synced_change" in state:
            return self.lib.change_no() != state["synced_change"]
        if not state.get("local_hash"):
            return self.lib.count() > 0
        if _file_stat(self.lib.path) == state.get("local_stat"):
            return False
        changed = _file_hash(self.lib.path) != state["local_hash"]
        if not changed:                                   # yalnızca tarih değişmiş
            self._save_state(local_stat=_file_stat(self.lib.path))
        return changed

    def shared_changed(self) -> bool:
        meta = self.meta()
        return bool(meta.get("rev")) and meta.get("rev") != self._state().get("shared_rev")

    def status(self) -> str:
        folder = self.folder()
        if folder is None:
            return "kapali"
        if not (folder / SHARED_DB_NAME).is_file():
            return "ilk"
        local, shared = self.local_changed(), self.shared_changed()
        if local and shared:
            return "cakisma"
        return "gonder" if local else "al" if shared else "esit"

    def _mark_synced(self, rev, change=None):
        self._save_state(synced_change=self.lib.change_no() if change is None else change,
                         shared_rev=rev, last_sync=datetime.now().strftime("%d.%m.%Y %H:%M"))

    def _backup_local(self):
        folder = settings_path().parent / "Yedekler"
        self.lib.snapshot_to(folder / f"kutuphane_{datetime.now():%Y%m%d_%H%M%S}.db")
        _rotate_backups(folder, "kutuphane_")

    # işlemler
    def push(self, force=False) -> str:
        with self.op_lock:
            return self._push(force)

    def pull(self) -> str:
        with self.op_lock:
            return self._pull()

    def merge(self) -> tuple:
        with self.op_lock:
            return self._merge()

    def _push(self, force=False) -> str:
        folder = self.folder()
        if folder is None:
            return "kapali"
        if not force and self.shared_changed():
            return "cakisma"
        folder.mkdir(parents=True, exist_ok=True)
        snapshot = settings_path().parent / f"gonderilecek_{os.getpid()}_{threading.get_ident()}.db"
        change = self.lib.snapshot_to(snapshot)               # arayüzün kilidini tutmaz
        target = folder / SHARED_DB_NAME
        backups = folder / "Yedekler"
        if target.is_file() and not any(backups.glob(f"ortak_{datetime.now():%Y%m%d}_*.db")):
            try:                                              # önceki ortak kopya: günde bir yedek yeter
                backups.mkdir(exist_ok=True)
                shutil.copy2(target, backups / f"ortak_{datetime.now():%Y%m%d_%H%M%S}.db")
                _rotate_backups(backups, "ortak_")
            except OSError:
                pass
        tmp = folder / (SHARED_DB_NAME + ".tmp")
        if tmp.exists():
            tmp.unlink()
        shutil.copyfile(snapshot, tmp)                        # bulut klasörüne yazmak yavaş olabilir: kilitsiz
        os.replace(tmp, target)
        snapshot.unlink(missing_ok=True)
        import uuid
        rev = uuid.uuid4().hex
        _write_json(folder / SHARED_META_NAME, {"rev": rev, "machine": machine_name(), "items": self.lib.count(),
                                                "saved_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
                                                "version": APP_VERSION})
        self._mark_synced(rev, change)
        diag(f"ortak kütüphaneye gönderildi ({self.lib.count()} kaynak)")
        return "gonderildi"

    def _local_copy_of_shared(self) -> Path:
        """Buluttaki kopyayı önce yerel geçici dosyaya alır (eşitleme sürerken okumamak için)."""
        tmp = settings_path().parent / "ortak_gecici.db"
        shutil.copy2(self.folder() / SHARED_DB_NAME, tmp)
        return tmp

    def _pull(self) -> str:
        meta = self.meta()
        tmp = self._local_copy_of_shared()
        self._backup_local()
        with self.lib.lock:
            self.lib.restore_from(tmp)
            change = self.lib.change_no()
        tmp.unlink(missing_ok=True)
        self._mark_synced(meta.get("rev"), change)
        diag(f"ortak kütüphane alındı ({meta.get('machine')}, {meta.get('saved_at')})")
        return "alindi"

    def _merge(self) -> tuple:
        """Ortak kopya esas alınır, bu bilgisayarda olup orada olmayanlar eklenir, sonra gönderilir."""
        meta = self.meta()
        mine_path = settings_path().parent / "yerel_gecici.db"
        self.lib.snapshot_to(mine_path)
        self._backup_local()
        tmp = self._local_copy_of_shared()
        self.lib.restore_from(tmp)
        tmp.unlink(missing_ok=True)
        mine = Library(mine_path, root=self.lib.root, relative=self.lib.relative)
        try:
            result = self.lib.merge_from(mine)
        finally:
            mine.close()
            mine_path.unlink(missing_ok=True)
        self._save_state(shared_rev=meta.get("rev"))
        self.push(force=True)
        return result

    def other_sessions(self) -> list:
        """Ortak kütüphaneyi şu an açık tutan başka bilgisayarlar."""
        folder = self.folder()
        if folder is None:
            return []
        out, now = [], time.time()
        for f in folder.glob("oturum_*.json"):
            info = _read_json(f)
            if info.get("machine") and info["machine"] != machine_name() \
                    and now - float(info.get("ts", 0)) < SESSION_FRESH_MINUTES * 60:
                out.append(info["machine"])
        return out

    def heartbeat(self, closing=False):
        folder = self.folder()
        if folder is None:
            return
        path = folder / f"oturum_{re.sub(r'[^A-Za-z0-9_-]', '_', machine_name())}.json"
        try:
            if closing:
                path.unlink(missing_ok=True)
            else:
                _write_json(path, {"machine": machine_name(), "ts": time.time()})
        except OSError:
            pass


# ── Telefon için Excel dökümü (Drive uygulaması/Google E-Tablolar ile açılır) ─────

def _xlsx_cell(ref, value):
    text = xml_escape(str(value or ""))
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    return f'<c r="{ref}" t="inlineStr" s="{1 if ref[1:] == "1" else 0}"><is><t xml:space="preserve">{text}</t></is></c>'


def _xlsx_sheet(rows, widths) -> str:
    def col(i):
        name = ""
        i += 1
        while i:
            i, rem = divmod(i - 1, 26)
            name = chr(65 + rem) + name
        return name
    body = "".join(f'<row r="{r}">' + "".join(_xlsx_cell(f"{col(c)}{r}", v) for c, v in enumerate(row)) + "</row>"
                   for r, row in enumerate(rows, 1))
    cols = "".join(f'<col min="{i + 1}" max="{i + 1}" width="{w}" customWidth="1"/>' for i, w in enumerate(widths))
    return ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
            '<sheetViews><sheetView workbookViewId="0"><pane ySplit="1" topLeftCell="A2" activePane="bottomLeft" '
            'state="frozen"/></sheetView></sheetViews>'
            f'<cols>{cols}</cols><sheetData>{body}</sheetData></worksheet>')


def write_xlsx(path, sheets):
    """sheets: [(ad, satırlar, sütun_genişlikleri)] — ek kütüphane gerektirmeyen yalın xlsx."""
    path = Path(path)
    names = "".join(f'<sheet name="{xml_escape(n[:31])}" sheetId="{i}" r:id="rId{i}"/>'
                    for i, (n, _, _) in enumerate(sheets, 1))
    rels = "".join(f'<Relationship Id="rId{i}" Type="http://schemas.openxmlformats.org/officeDocument/2006/'
                   f'relationships/worksheet" Target="worksheets/sheet{i}.xml"/>' for i in range(1, len(sheets) + 1))
    rels += (f'<Relationship Id="rId{len(sheets) + 1}" Type="http://schemas.openxmlformats.org/officeDocument/'
             f'2006/relationships/styles" Target="styles.xml"/>')
    overrides = "".join(f'<Override PartName="/xl/worksheets/sheet{i}.xml" ContentType="application/'
                        f'vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>'
                        for i in range(1, len(sheets) + 1))
    tmp = path.with_name(path.name + ".tmp")
    with zipfile.ZipFile(tmp, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("[Content_Types].xml",
                    '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.'
                    'openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="'
                    'application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" '
                    'ContentType="application/xml"/><Override PartName="/xl/workbook.xml" ContentType="'
                    'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
                    '<Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-'
                    f'officedocument.spreadsheetml.styles+xml"/>{overrides}</Types>')
        zf.writestr("_rels/.rels", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships '
                    'xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" '
                    'Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" '
                    'Target="xl/workbook.xml"/></Relationships>')
        zf.writestr("xl/workbook.xml", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook '
                    'xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.'
                    f'openxmlformats.org/officeDocument/2006/relationships"><sheets>{names}</sheets></workbook>')
        zf.writestr("xl/_rels/workbook.xml.rels", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                    '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                    f'{rels}</Relationships>')
        zf.writestr("xl/styles.xml", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><styleSheet '
                    'xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><fonts count="2"><font>'
                    '<sz val="11"/><name val="Calibri"/></font><font><b/><sz val="11"/><name val="Calibri"/></font>'
                    '</fonts><fills count="2"><fill><patternFill patternType="none"/></fill><fill><patternFill '
                    'patternType="gray125"/></fill></fills><borders count="1"><border><left/><right/><top/>'
                    '<bottom/><diagonal/></border></borders><cellStyleXfs count="1"><xf numFmtId="0" fontId="0" '
                    'fillId="0" borderId="0"/></cellStyleXfs><cellXfs count="2"><xf numFmtId="0" fontId="0" '
                    'fillId="0" borderId="0" xfId="0" applyAlignment="1"><alignment vertical="top" wrapText="1"/>'
                    '</xf><xf numFmtId="0" fontId="1" fillId="0" borderId="0" xfId="0" applyFont="1"/></cellXfs>'
                    '<cellStyles count="1"><cellStyle name="Normal" xfId="0" builtinId="0"/></cellStyles>'
                    '</styleSheet>')
        for i, (_, rows, widths) in enumerate(sheets, 1):
            zf.writestr(f"xl/worksheets/sheet{i}.xml", _xlsx_sheet(rows, widths))
    os.replace(tmp, path)
    return path


def write_phone_export(library, folder) -> Path:
    """Kütüphanenin telefondan okunacak dökümü: kaynaklar ve alıntı kartları iki sayfada."""
    scopus = load_scopus()
    items = sorted(library.all_items(), key=lambda i: (tr_sort_key(first_author_label(i)), i["year"]))
    rows = [["Yazar", "Yıl", "Başlık", "Dergi / Kitap", "Etiketler", "Scopus", "PDF dosyası", "APA 7",
             "Alıntı kartları", "DOI / Link", "Eklenme"]]
    cards_rows = [["Kaynak", "Sayfa", "Alıntı", "Yorum", "Atıf"]]
    all_cards = {}
    with library.lock:
        for row in library.db.execute("SELECT * FROM cards ORDER BY id"):
            all_cards.setdefault(row["item_id"], []).append(dict(row))
    for item in items:
        cards = all_cards.get(item["id"], [])
        has_pdf = file_exists_cached(item["file_path"])
        rows.append([first_author_label(item), item["year"], item["title"], item["container"],
                     ", ".join(item["tags"]), scopus_label(item, scopus) if scopus else "",
                     Path(item["file_path"]).name if has_pdf else "PDF yok", apa_text(item, "tr"),
                     "\n".join(f"s. {c['page']}: “{c['quote']}”" + (f" — {c['comment']}" if c["comment"] else "")
                               for c in cards),
                     ("https://doi.org/" + item["doi"]) if item["doi"] else item["url"], item["added"]])
        for c in cards:
            cards_rows.append([f"{first_author_label(item)} ({item['year'] or 't.y.'}) {shorten(item['title'], 60)}",
                               c["page"], c["quote"], c["comment"], card_citation_text(c, item)])
    return write_xlsx(Path(folder) / PHONE_EXPORT_NAME,
                      [("Kaynaklar", rows, [20, 6, 50, 28, 24, 10, 30, 60, 50, 30, 11]),
                       ("Alıntı Kartları", cards_rows, [36, 8, 60, 40, 30])])


# ════════════════════════════════════════════════════════════════════════════
#  6a) SCOPUS LİSTESİ: Elsevier'in yayımladığı kaynak listesi (xlsx) bir kez içe aktarılır;
#      kaynaklar dergi ISSN'ine ya da adına göre "Scopus'ta" diye işaretlenir.
# ════════════════════════════════════════════════════════════════════════════

SCOPUS_LIST_PAGE = "https://www.elsevier.com/resources/scopus-titlelists"
SCOPUS_LABELS = {"aktif": "Scopus", "pasif": "Scopus (pasif)", "cikarildi": "Scopus'tan çıkarıldı"}
_XLSX_NS = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
_REL_NS = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}"


def scopus_path() -> Path:
    return data_dir() / "scopus_listesi.json"


def journal_key(title: str) -> str:
    """Dergi adını karşılaştırma için sadeleştirir ('The Journal of X & Y' = 'journal of x and y')."""
    t = fold(title or "").replace("&", " and ")
    t = re.sub(r"\(.*?\)", " ", t)
    t = re.sub(r"^the\s+", "", t.strip())
    return re.sub(r"[^a-z0-9]+", "", t)


def _col_index(ref: str) -> int:
    n = 0
    for ch in re.match(r"[A-Z]+", ref).group(0):
        n = n * 26 + ord(ch) - 64
    return n - 1


def xlsx_sheets(path):
    """xlsx dosyasındaki sayfaları (ad, satır üreteci) olarak verir; ek kütüphane gerektirmez."""
    zf = zipfile.ZipFile(path)
    shared = []
    if "xl/sharedStrings.xml" in zf.namelist():
        with zf.open("xl/sharedStrings.xml") as fh:
            for _, el in ET.iterparse(fh):
                if el.tag == _XLSX_NS + "si":
                    shared.append("".join(t.text or "" for t in el.iter(_XLSX_NS + "t")))
                    el.clear()
    rels = {}
    if "xl/_rels/workbook.xml.rels" in zf.namelist():
        for rel in ET.fromstring(zf.read("xl/_rels/workbook.xml.rels")):
            rels[rel.get("Id")] = rel.get("Target", "")
    workbook = ET.fromstring(zf.read("xl/workbook.xml"))
    sheets = []
    for sh in workbook.iter(_XLSX_NS + "sheet"):
        target = rels.get(sh.get(_REL_NS + "id"), "")
        target = target.lstrip("/")
        target = target if target.startswith("xl/") else "xl/" + target
        sheets.append((sh.get("name") or "", target))

    def rows(target):
        with zf.open(target) as fh:
            for _, el in ET.iterparse(fh):
                if el.tag != _XLSX_NS + "row":
                    continue
                row = {}
                for c in el.iter(_XLSX_NS + "c"):
                    kind, ref = c.get("t"), c.get("r") or "A1"
                    if kind == "inlineStr":
                        value = "".join(t.text or "" for t in c.iter(_XLSX_NS + "t"))
                    else:
                        v = c.find(_XLSX_NS + "v")
                        value = v.text if v is not None and v.text is not None else ""
                        if kind == "s" and value.isdigit() and int(value) < len(shared):
                            value = shared[int(value)]
                    row[_col_index(ref)] = value.strip()
                el.clear()
                if row:
                    width = max(row) + 1
                    yield [row.get(i, "") for i in range(width)]

    return [(name, (lambda t=target: rows(t))) for name, target in sheets if target in zf.namelist()]


def _find_columns(header) -> dict:
    cols = {}
    for i, h in enumerate(fold(x) for x in header):
        if "issn" in h:
            electronic = "e-issn" in h or "eissn" in h or "electronic" in h or h.startswith("e ")
            cols.setdefault("eissn" if electronic else "issn", i)
        elif "title" in h and "title" not in cols and "history" not in h and "related" not in h:
            cols["title"] = i
        elif "active or inactive" in h or h in ("active", "status", "active/inactive"):
            cols["status"] = i
        elif "discontinued" in h and "quality" in h:
            cols.setdefault("discontinued", i)
        elif h.startswith("source type"):
            cols["type"] = i
    return cols


def parse_scopus_xlsx(path) -> dict:
    """Scopus kaynak listesini okur → {"issn": {kod: [başlık, durum]}, "titles": {anahtar: [...]}}"""
    issn, titles, discontinued, count = {}, {}, set(), 0
    main_found = False
    for name, rows in xlsx_sheets(path):
        it = rows()
        header, cols = None, {}
        for _ in range(8):                          # başlık satırı ilk birkaç satırdan biri
            try:
                header = next(it)
            except StopIteration:
                header = None
                break
            cols = _find_columns(header)
            if "title" in cols and ("issn" in cols or "eissn" in cols):
                break
        if not header or "title" not in cols or not ({"issn", "eissn"} & set(cols)):
            continue
        is_discontinued_sheet = "discontinu" in fold(name) or "removed" in fold(name)
        if not is_discontinued_sheet and main_found:
            continue
        for row in it:
            get = lambda k: row[cols[k]] if k in cols and cols[k] < len(row) else ""   # noqa: E731
            title = get("title")
            codes = [c for c in (norm_issn(get("issn")), norm_issn(get("eissn"))) if c]
            if not title and not codes:
                continue
            if is_discontinued_sheet:
                discontinued.update(codes)
                continue
            status = "pasif" if fold(get("status")).startswith("inactive") else "aktif"
            if get("discontinued") and fold(get("discontinued")) not in ("no", "0", "-"):
                status = "cikarildi"
            entry = [title, status]
            for c in codes:
                issn[c] = entry
            if title:
                titles.setdefault(journal_key(title), entry)
            count += 1
        if not is_discontinued_sheet:
            main_found = True
    if not count:
        raise ValueError("Dosyada Scopus kaynak listesi bulunamadı (ISSN ve başlık sütunları yok).")
    for c in discontinued:
        if c in issn:
            issn[c][1] = "cikarildi"
        else:
            issn[c] = ["", "cikarildi"]
    return {"issn": issn, "titles": titles, "count": count}


_SCOPUS_CACHE = {"key": None, "data": None}


def load_scopus():
    path = scopus_path()
    now = time.monotonic()
    if _SCOPUS_CACHE.get("path") == str(path) and now - _SCOPUS_CACHE.get("checked", -1e9) < 60:
        return _SCOPUS_CACHE["data"]                 # bulutta olabilir: dakikada bir yoklamak yeter
    _SCOPUS_CACHE.update(path=str(path), checked=now)
    try:
        key = path.stat().st_mtime
    except OSError:
        _SCOPUS_CACHE.update(key=None, data=None)
        return None
    if _SCOPUS_CACHE["key"] != key:
        try:
            with open(path, encoding="utf-8") as fh:
                _SCOPUS_CACHE.update(key=key, data=json.load(fh))
        except (OSError, ValueError):
            return None
    return _SCOPUS_CACHE["data"]


def import_scopus_list(xlsx_path) -> dict:
    data = parse_scopus_xlsx(xlsx_path)
    data.update(file=Path(xlsx_path).name, imported=datetime.now().strftime("%d.%m.%Y"))
    path = scopus_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(data, fh, ensure_ascii=False, separators=(",", ":"))
    os.replace(tmp, path)
    _SCOPUS_CACHE.update(key=None, checked=-1e9)
    return data


def scopus_info(item, data=None):
    """Kaynağın dergisi Scopus listesinde mi? → ("aktif"|"pasif"|"cikarildi", dergi adı) ya da None.
    Önce ISSN'e, yoksa dergi adına bakılır. Liste yüklenmemişse None."""
    data = data if data is not None else load_scopus()
    if not data:
        return None
    for code in find_issns(item.get("issn") or ""):
        hit = data["issn"].get(code)
        if hit:
            return hit[1], hit[0] or item.get("container", "")
    if item.get("type") in ("article", "conference", "other", "chapter") and item.get("container"):
        hit = data["titles"].get(journal_key(item["container"]))
        if hit:
            return hit[1], hit[0]
    return None


def scopus_label(item, data=None) -> str:
    info = scopus_info(item, data)
    return SCOPUS_LABELS[info[0]] if info else ""


class ScopusImportWorker(threading.Thread):
    """Listeyi içe aktarır, sonra DOI'si olup ISSN'i eksik kaynakların ISSN'ini Crossref'ten tamamlar."""

    MAX_LOOKUPS = 600

    def __init__(self, xlsx_path, library, events, cancel_event):
        super().__init__(daemon=True)
        self.xlsx_path, self.library, self.events, self.cancel = xlsx_path, library, events, cancel_event

    def run(self):
        try:
            self.events.put(("scopus", "status", "Liste okunuyor… (bir dakika sürebilir)"))
            data = import_scopus_list(self.xlsx_path)
            self.events.put(("scopus", "status", f"{data['count']:,} kaynak içe aktarıldı.".replace(",", ".")))
            todo = [i for i in self.library.all_items() if i["doi"] and not i.get("issn")][:self.MAX_LOOKUPS]
            session = make_session()
            for n, item in enumerate(todo, 1):
                if self.cancel.is_set():
                    break
                rec = crossref_record(session, item["doi"])
                if rec and rec.get("issn"):
                    self.library.update(item["id"], {"issn": rec["issn"]})
                if n % 10 == 0 or n == len(todo):
                    self.events.put(("scopus", "status", f"Dergi ISSN'leri tamamlanıyor: {n}/{len(todo)}"))
                time.sleep(0.15)
            items = self.library.all_items()
            found = sum(1 for i in items if (scopus_info(i, data) or ("",))[0] in ("aktif", "pasif"))
            self.events.put(("scopus", "done", f"Liste yüklendi · kütüphanenizde {found} kaynak Scopus'taki "
                                               f"dergilerde"))
            diag(f"Scopus listesi içe aktarıldı: {data['count']} kaynak, eşleşen {found}")
        except Exception as exc:
            diag_exception("Scopus listesi")
            self.events.put(("scopus", "error", f"Liste okunamadı: {exc}"))


# ════════════════════════════════════════════════════════════════════════════
#  6b) CLAUDE BAĞLANTISI (MCP sunucusu): Claude masaüstü uygulaması kütüphaneyi
#      bu araçlarla okur ve düzenler. Çalıştırma: AkademikKutuphaneMCP.exe --mcp
# ════════════════════════════════════════════════════════════════════════════

MCP_SERVER_NAME = "akademik-kutuphane"
# ── Claude için metin dizini: bütün PDF'lerin sayfa sayfa aranabilir hâli ────────────────────
# Kütüphane veritabanından ayrı, bu bilgisayarda durur (Drive'a gönderilmez; her bilgisayar kendi
# dizinini kurar). Program açıkken arka planda kurulur, yeni eklenenler kendiliğinden dizine girer.

INDEX_NAME = "metin_dizini.db"
INDEX_PAGE_LIMIT = 400
_PASSAGE_CHARS = 1400


def index_path() -> Path:
    return settings_path().parent / INDEX_NAME


def pdf_pages(path, max_pages=INDEX_PAGE_LIMIT, pause=0.0) -> list:
    """[(sayfa_no, sayfa_etiketi, metin)] — etiket, yayıncının basılı sayfa numarasıdır (varsa)."""
    from pypdf import PdfReader
    reader = PdfReader(str(path))
    try:
        labels = list(reader.page_labels)
    except Exception:
        labels = []
    out = []
    for i, page in enumerate(reader.pages[:max_pages]):
        try:
            text = page.extract_text() or ""
        except Exception:
            text = ""
        label = str(labels[i]) if i < len(labels) else ""
        out.append((i + 1, label if label and label != str(i + 1) else "", text))
        if pause:
            time.sleep(pause)                                   # arka planda: arayüze nefes aldır
    return out


def epub_sections(path) -> list:
    text = epub_text(path, max_chars=FULLTEXT_MAX_CHARS)
    size = 6000
    return [(n + 1, f"bölüm-parça {n + 1}", text[i:i + size]) for n, i in enumerate(range(0, len(text), size))]


# ── Taranmış PDF'ler: Windows'un kendi metin tanıması (Windows.Media.Ocr) ─────────────────────
# Ek program kurmaz; Windows 10/11'in OCR'ı ve PDF çizicisi (Windows.Data.Pdf) kullanılır.

OCR_PAGE_LIMIT = 400
_OCR_STATE = {"checked": False, "error": ""}


def ocr_unavailable_reason() -> str:
    """Boş: kullanılabilir. Değilse nedeni (Windows değil, program eski sürüm…)."""
    if _OCR_STATE["checked"]:
        return _OCR_STATE["error"]
    _OCR_STATE["checked"] = True
    if sys.platform != "win32":
        _OCR_STATE["error"] = "metin tanıma yalnızca Windows'ta çalışır"
        return _OCR_STATE["error"]
    try:
        import importlib
        for mod in ("winrt.windows.media.ocr", "winrt.windows.data.pdf", "winrt.windows.graphics.imaging",
                    "winrt.windows.storage", "winrt.windows.storage.streams", "winrt.windows.globalization"):
            importlib.import_module(mod)
    except ImportError:
        _OCR_STATE["error"] = ("bu program dosyasında metin tanıma bileşeni yok; programın yeni sürümünü "
                               "(v2.35 ve sonrası) bir kez indirip kurun")
    return _OCR_STATE["error"]


def ocr_pdf(path, pages=None, language="", cancel=None, pause=0.0) -> dict:
    """PDF sayfalarını resme çizip Windows OCR ile yazıya çevirir. pages: 1'den başlayan sayfa numaraları
    (None: hepsi, en fazla OCR_PAGE_LIMIT). Dönüş: {sayfa_no: metin}"""
    import asyncio
    import warnings
    from winrt.windows.data.pdf import PdfDocument, PdfPageRenderOptions
    from winrt.windows.globalization import Language
    from winrt.windows.graphics.imaging import BitmapDecoder, BitmapPixelFormat, SoftwareBitmap
    from winrt.windows.media.ocr import OcrEngine
    from winrt.windows.storage import StorageFile
    from winrt.windows.storage.streams import InMemoryRandomAccessStream
    try:
        from winrt.runtime import init_apartment, MTA
        init_apartment(MTA)
    except Exception:
        pass

    def engine_for(lang):
        for tag in ([lang] if lang else []) + ["tr", "en-US", "en"]:
            try:
                language_obj = Language(tag)
                if OcrEngine.is_language_supported(language_obj):
                    return OcrEngine.try_create_from_language(language_obj)
            except Exception:
                continue
        return OcrEngine.try_create_from_user_profile_languages()

    async def run():
        out = {}
        file = await StorageFile.get_file_from_path_async(str(Path(path).resolve()))
        doc = await PdfDocument.load_from_file_async(file)
        engine = engine_for(language)
        if engine is None:
            raise RuntimeError("Windows'ta metin tanıma dili yüklü değil (Ayarlar → Dil → Türkçe → Dil özellikleri)")
        limit = int(OcrEngine.max_image_dimension or 10000)
        wanted = pages or range(1, min(int(doc.page_count), OCR_PAGE_LIMIT) + 1)
        for number in wanted:
            if cancel is not None and cancel.is_set():
                break
            if not 1 <= number <= doc.page_count:
                continue
            page = doc.get_page(number - 1)
            size = page.size
            scale = min(2.5, limit / max(size.width, size.height, 1)) if size.width and size.height else 2.0
            options = PdfPageRenderOptions()
            options.destination_width = max(1, int(size.width * scale))
            options.destination_height = max(1, int(size.height * scale))
            stream = InMemoryRandomAccessStream()
            with warnings.catch_warnings():                 # pywinrt: eski ad uyarısı (işlev aynı)
                warnings.simplefilter("ignore", DeprecationWarning)
                await page.render_with_options_to_stream_async(stream, options)
            decoder = await BitmapDecoder.create_async(stream)
            bitmap = await decoder.get_software_bitmap_async()
            if bitmap.bitmap_pixel_format not in (BitmapPixelFormat.BGRA8, BitmapPixelFormat.GRAY8):
                bitmap = SoftwareBitmap.convert(bitmap, BitmapPixelFormat.BGRA8)
            result = await engine.recognize_async(bitmap)
            out[number] = "\n".join(line.text for line in result.lines)
            page.close()
            stream.close()
            if pause:
                await asyncio.sleep(pause)
        return out

    return asyncio.run(run())


def _minimal_text_pdf(path, text):
    """Ek kütüphane olmadan tek sayfalık metinli PDF (OCR öz denetimi için)."""
    content = f"BT /F1 28 Tf 60 700 Td ({text}) Tj ET".encode("latin-1")
    objs = [b"<< /Type /Catalog /Pages 2 0 R >>", b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
            b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R "
            b"/Resources << /Font << /F1 5 0 R >> >> >>",
            b"<< /Length %d >>\nstream\n" % len(content) + content + b"\nendstream",
            b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>"]
    data, offsets = b"%PDF-1.4\n", []
    for i, obj in enumerate(objs, 1):
        offsets.append(len(data))
        data += b"%d 0 obj\n" % i + obj + b"\nendobj\n"
    xref = len(data)
    data += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    data += b"".join(b"%010d 00000 n \n" % o for o in offsets)
    data += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, xref)
    Path(path).write_bytes(data)


def ocr_selftest() -> str:
    reason = ocr_unavailable_reason()
    if reason:
        return "OCR YOK: " + reason
    import tempfile
    path = Path(tempfile.mkdtemp()) / "ocr_deneme.pdf"
    _minimal_text_pdf(path, "Halk oyunlari sahneleme 2026")
    text = ocr_pdf(path).get(1, "")
    return "OCR TAMAM: " + text if "sahneleme" in text.lower() else "OCR SONUCU BEKLENMEDİK: " + repr(text)


def split_passages(text, limit=_PASSAGE_CHARS) -> list:
    """Sayfa metnini paragraf/cümle sınırlarından ~1400 karakterlik parçalara böler."""
    text = re.sub(r"[ \t]+", " ", text or "").strip()
    text = re.sub(r"-\n(?=[a-zçğıöşü])", "", text)                  # satır sonu tirelemesi
    if len(text) <= limit:
        return [text] if len(text) > 40 else []
    parts, current = [], ""
    for piece in re.split(r"(?<=[.!?…])\s+|\n{2,}", text):
        if len(current) + len(piece) + 1 > limit and current:
            parts.append(current.strip())
            current = ""
        current += " " + piece
        while len(current) > limit * 1.5:
            parts.append(current[:limit].strip())
            current = current[limit:]
    if current.strip():
        parts.append(current.strip())
    return [p for p in parts if len(p) > 40]


class PassageIndex:
    """Sayfa numaralı metin parçaları + tam metin arama (SQLite FTS5; yoksa basit yedek arama)."""

    def __init__(self, path=None, readonly=False):
        self.path = Path(path) if path else index_path()
        self.lock = threading.RLock()
        if readonly:
            if not self.path.is_file():
                raise FileNotFoundError(self.path)
            self.db = sqlite3.connect(f"file:{self.path.as_posix()}?mode=ro", uri=True, check_same_thread=False,
                                      timeout=30)
        else:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            self.db = sqlite3.connect(str(self.path), check_same_thread=False, timeout=30)
            with self.db:
                self.db.executescript("""
                CREATE TABLE IF NOT EXISTS docs (item_id INTEGER PRIMARY KEY, sig TEXT, pages INTEGER, chars INTEGER,
                                                 paged INTEGER, indexed TEXT);
                CREATE TABLE IF NOT EXISTS passages (id INTEGER PRIMARY KEY, item_id INTEGER, page INTEGER,
                                                     label TEXT, text TEXT, folded TEXT);
                CREATE INDEX IF NOT EXISTS idx_pass_item ON passages(item_id);
                """)
                for table, column, decl in (("passages", "kind", "TEXT DEFAULT ''"),
                                            ("docs", "page_offset", "INTEGER DEFAULT 0")):
                    have = {r[1] for r in self.db.execute(f"PRAGMA table_info({table})")}
                    if column not in have:
                        self.db.execute(f"ALTER TABLE {table} ADD COLUMN {column} {decl}")
                # yer kazanmak için içeriksiz dizin (SQLite 3.43+); eski SQLite'ta içerik passages'tan okunur
                for ddl in ("CREATE VIRTUAL TABLE IF NOT EXISTS pfts USING fts5(folded, content='', "
                            "contentless_delete=1, tokenize='unicode61 remove_diacritics 2')",
                            "CREATE VIRTUAL TABLE IF NOT EXISTS pfts USING fts5(folded, content='passages', "
                            "content_rowid='id', tokenize='unicode61 remove_diacritics 2')"):
                    try:
                        self.db.execute(ddl)
                        break
                    except sqlite3.OperationalError:
                        continue
        row = self.db.execute("SELECT sql FROM sqlite_master WHERE name='pfts'").fetchone()
        self.fts = bool(row)
        self.contentless = bool(row) and "contentless_delete" in (row[0] or "")
        self.has_kind = "kind" in {r[1] for r in self.db.execute("PRAGMA table_info(passages)")}
        self.has_offset = "page_offset" in {r[1] for r in self.db.execute("PRAGMA table_info(docs)")}

    def close(self):
        with self.lock:
            self.db.close()

    def signatures(self) -> dict:
        with self.lock:
            return dict(self.db.execute("SELECT item_id, sig FROM docs"))

    def put(self, item_id, sig, passages, paged, page_offset=0):
        """passages: [(sayfa, etiket, metin[, tür, bağlam])] — bağlam (başlık, bölüm adı) yalnızca aramaya
        katılır, gösterilmez (bağlamsal BM25)."""
        with self.lock, self.db:
            self._drop(item_id)
            for entry in passages:
                page, label, text = entry[:3]
                kind = entry[3] if len(entry) > 3 else ""
                context = entry[4] if len(entry) > 4 else ""
                searchable = fold((context + " | " if context else "") + text)
                if self.has_kind:
                    cur = self.db.execute("INSERT INTO passages (item_id, page, label, text, folded, kind) "
                                          "VALUES (?,?,?,?,?,?)", (item_id, page, label, text,
                                                                   "" if self.contentless else searchable, kind))
                else:
                    cur = self.db.execute("INSERT INTO passages (item_id, page, label, text, folded) VALUES (?,?,?,?,?)",
                                          (item_id, page, label, text, "" if self.contentless else searchable))
                if self.fts:
                    self.db.execute("INSERT INTO pfts (rowid, folded) VALUES (?, ?)", (cur.lastrowid, searchable))
            self.db.execute("INSERT OR REPLACE INTO docs (item_id, sig, pages, chars, paged, indexed) "
                            "VALUES (?,?,?,?,?,?)",
                            (item_id, sig, len({e[0] for e in passages}),
                             sum(len(e[2]) for e in passages if e[0] != 0), int(paged or 0),
                             datetime.now().strftime("%Y-%m-%d %H:%M")))
            if self.has_offset and page_offset:
                self.db.execute("UPDATE docs SET page_offset=? WHERE item_id=?", (int(page_offset), item_id))

    def passages_of_kind(self, kind) -> list:
        """[(kimlik, metin)] — belge sırasıyla."""
        if not self.has_kind:
            return []
        with self.lock:
            return self.db.execute("SELECT item_id, text FROM passages WHERE kind=? ORDER BY item_id, id",
                                   (kind,)).fetchall()

    def page_offset(self, item_id) -> int:
        if not self.has_offset:
            return 0
        with self.lock:
            row = self.db.execute("SELECT page_offset FROM docs WHERE item_id=?", (item_id,)).fetchone()
        return int(row[0] or 0) if row else 0

    def _drop(self, item_id):
        if self.fts:
            for rid, folded in self.db.execute("SELECT id, folded FROM passages WHERE item_id=?", (item_id,)).fetchall():
                if self.contentless:
                    self.db.execute("DELETE FROM pfts WHERE rowid=?", (rid,))
                else:
                    self.db.execute("INSERT INTO pfts (pfts, rowid, folded) VALUES ('delete', ?, ?)", (rid, folded))
        self.db.execute("DELETE FROM passages WHERE item_id=?", (item_id,))
        self.db.execute("DELETE FROM docs WHERE item_id=?", (item_id,))

    def remove_missing(self, valid_ids) -> int:
        valid = set(valid_ids)
        gone = [i for i in self.signatures() if i not in valid]
        with self.lock, self.db:
            for item_id in gone:
                self._drop(item_id)
        return len(gone)

    def stats(self) -> dict:
        with self.lock:
            docs, chars = self.db.execute("SELECT COUNT(*), COALESCE(SUM(chars), 0) FROM docs").fetchone()
            empty = self.db.execute("SELECT COUNT(*) FROM docs WHERE chars < 200 AND paged >= 1").fetchone()[0]
            ocr = self.db.execute("SELECT COUNT(*) FROM docs WHERE paged = 2 AND chars >= 200").fetchone()[0]
            passages = self.db.execute("SELECT COUNT(*) FROM passages").fetchone()[0]
        return {"kaynak": docs, "parca": passages, "karakter": chars, "metinsiz": empty, "ocr": ocr}

    def thin_docs(self) -> set:
        """Metni çıkmamış ve henüz metin tanıma denenmemiş PDF'ler."""
        with self.lock:
            return {r[0] for r in self.db.execute("SELECT item_id FROM docs WHERE chars < 200 AND paged = 1")}

    @staticmethod
    def _terms(query) -> list:
        words = re.findall(r"\w+", fold(query))
        stop = {"ve", "ile", "bir", "bu", "da", "de", "icin", "the", "and", "of", "in", "on", "for", "a", "an", "to",
                "ne", "nasil", "neden", "mi", "mu", "hangi", "olarak", "gibi", "daha", "cok", "en", "is", "are", "with"}
        return [w for w in words if w not in stop and len(w) >= 2]

    _SUFFIXES = sorted(["lerinin", "larinin", "lerinde", "larinda", "lerini", "larini", "lerine", "larina", "lerin",
                        "larin", "leri", "lari", "ler", "lar", "nin", "nun", "nda", "nde", "dan", "den", "tan", "ten",
                        "yla", "yle", "in", "un", "da", "de", "ta", "te", "la", "le", "si", "su", "yi", "yu", "i", "u",
                        "e", "a", "s"], key=len, reverse=True)

    @classmethod
    def stem(cls, word: str) -> str:
        """Türkçe/İngilizce ekleri kabaca atar ('oyunlarının'→'oyun', 'sahneleme'→'sahnele', 'dances'→'danc');
        aramada önek olarak kullanılır."""
        for _ in range(3):
            for suf in cls._SUFFIXES:
                if word.endswith(suf) and len(word) - len(suf) >= 4:
                    word = word[:-len(suf)]
                    break
            else:
                break
        return word

    def search(self, query, allowed=None, limit=15, per_item=2, kinds=None) -> list:
        """[(item_id, sayfa, etiket, metin, skor, tür)] — en ilgiliden başlayarak."""
        return rank_hits(self.raw(query, kinds), query, allowed, limit, per_item)

    def raw(self, query, kinds=None) -> list:
        """[(kimlik, sayfa, etiket, metin, skor, tür)] — kinds verilirse yalnızca o türdeki parçalar."""
        terms = self._terms(query)
        if not terms:
            return []
        kind_col = "p.kind" if self.has_kind else "''"
        phrases = [fold(p) for p in re.findall(r'"([^"]+)"', query)]
        with self.lock:
            if self.fts:
                stems = [self.stem(w) for w in terms]
                match = " OR ".join([f'"{t}"*' for t in dict.fromkeys(stems)])
                phrases_ok = [" ".join(re.findall(r"\w+", ph)) for ph in phrases if re.findall(r"\w+", ph)]
                if phrases_ok:
                    near = " AND ".join(f'"{ph}"' for ph in phrases_ok)
                    match = f"({near}) OR ({match})" if match else near
                where = ""
                params = [match]
                if kinds and self.has_kind:
                    where = " AND p.kind IN (" + ",".join("?" * len(kinds)) + ")"
                    params += list(kinds)
                try:
                    rows = self.db.execute(
                        f"SELECT p.item_id, p.page, p.label, p.text, bm25(pfts) AS score, {kind_col} FROM pfts "
                        f"JOIN passages p ON p.id = pfts.rowid WHERE pfts MATCH ?{where} ORDER BY score LIMIT 3000",
                        params).fetchall()
                except sqlite3.OperationalError:
                    rows = []
                rows = [(a, b, c, d, -e, k or "") for a, b, c, d, e, k in rows]
            else:
                like = [f"%{self.stem(w)}%" for w in terms]
                sql = f"SELECT item_id, page, label, text, folded, {kind_col.replace('p.', '')} FROM passages WHERE (" + \
                      " OR ".join(["folded LIKE ?"] * len(like)) + ")"
                rows = []
                for a, b, c, d, f, k in self.db.execute(sql, like).fetchall():
                    if kinds and (k or "") not in kinds:
                        continue
                    score = sum(self.stem(w) in f for w in terms) + \
                        sum(2 for ph in phrases if ph in f)
                    rows.append((a, b, c, d, float(score), k or ""))
                rows.sort(key=lambda r: -r[4])
        return rows


def rank_hits(rows, query, allowed=None, limit=15, per_item=2) -> list:
    """Birden çok terim geçen parçalar öne; kaynak başına en fazla per_item parça."""
    terms = [PassageIndex.stem(w) for w in PassageIndex._terms(query)]

    def coverage(text):
        f = fold(text)
        return sum(1 for w in terms if w in f)
    # kaynakça sayfalarındaki geçişler (yalnızca atıf) en sona
    rows = sorted(rows, key=lambda r: ((r[5] if len(r) > 5 else "") == "kaynakça", -coverage(r[3]), -r[4]))
    out, per = [], {}
    for row in rows:
        item_id, page, label, text, score = row[:5]
        if allowed is not None and item_id not in allowed:
            continue
        if per.get(item_id, 0) >= per_item:
            continue
        per[item_id] = per.get(item_id, 0) + 1
        out.append(tuple(row))
        if len(out) >= limit:
            break
    return out


def item_signature(item) -> str:
    base = item.get("sha256") or ("meta:" + hashlib.sha1(
        (str(item.get("file_path")) + str(item.get("title")) + str(item.get("notes"))).encode("utf-8")).hexdigest())
    extra = hashlib.sha1((str(item.get("ai_ozet") or "") + "|" + str(item.get("pages") or "")).encode("utf-8")).hexdigest()[:8]
    return f"{INDEX_VERSION}|{base}|{extra}"


INDEX_VERSION = "v3"                      # dizin biçimi değişince bütün kaynaklar yeniden işlenir

_REFS_RE = re.compile(r"^(?:\d+\.?\s*)?(kaynakca|kaynaklar|references?|bibliography|works cited|literatur(?:verzeichnis)?|"
                      r"referanslar|bibliyografya|bibliografia|bibliographie|referencias|kullanilan kaynaklar|"
                      r"yararlanilan kaynaklar|notes and references|sources)\s*:?$")
_HEAD_WORDS_RE = re.compile(r"^(?:\d+(?:\.\d+)*\.?\s+)?(giris|sonuc|sonuclar|tartisma|bulgular|yontem|yontem ve|"
                            r"amac|oz|ozet|abstract|introduction|conclusion|conclusions|discussion|method|methods|"
                            r"methodology|results|findings|literature review|alanyazin|kuramsal cerceve|"
                            r"theoretical framework|ekler|appendix|acknowledg\w*|tesekkur)\b")


def printed_page_offset(pages, item) -> int:
    """PDF sayfa sırası → basılı sayfa numarası farkı. Önce sayfaların üst/alt satırlarındaki numaralardan,
    olmazsa künyedeki sayfa aralığından (555–580) bulunur. 0: bulunamadı."""
    if any(label for _, label, _ in pages):
        return 0                                       # yayıncı sayfa etiketi koymuş; o kullanılır
    diffs = {}
    for n, _, text in pages:
        lines = [l.strip() for l in (text or "").splitlines() if l.strip()]
        seen = set()
        for line in lines[:3] + lines[-3:]:
            for num in re.findall(r"(?<![\d.,/-])(\d{1,4})(?![\d.,/-])", line):
                v = int(num)
                if 1900 <= v <= 2100 or v == 0 or v in seen:
                    continue
                seen.add(v)
                diffs[v - n] = diffs.get(v - n, 0) + 1
    if diffs:
        best, count = max(diffs.items(), key=lambda kv: kv[1])
        if best > 0 and count >= max(3, len(pages) * 0.3):
            return best
    m = re.match(r"\s*(\d+)\s*[-–—]\s*(\d+)", str(item.get("pages") or ""))
    if m:
        start, end = int(m.group(1)), int(m.group(2))
        span = end - start + 1
        if start > 1 and span == len(pages):
            return start - 1
        if start > 1 and span == len(pages) - 1:           # başta dergi kapak sayfası
            return start - 2
    return 0


def strip_running_lines(pages) -> list:
    """Her sayfada tekrarlanan üst/alt bilgileri (dergi adı, yazar, sayfa numarası) atar."""
    if len(pages) < 4:
        return pages

    def key(line):
        return re.sub(r"\d+", "#", fold(line)).strip()
    counts = {}
    for _, _, text in pages:
        lines = [l for l in (text or "").splitlines() if l.strip()]
        for k in {key(l) for l in lines[:3] + lines[-3:]}:
            counts[k] = counts.get(k, 0) + 1
    noisy = {k for k, c in counts.items() if c >= max(3, len(pages) * 0.4) and len(k) <= 160}
    out = []
    for n, label, text in pages:
        lines = (text or "").splitlines()
        idx = [i for i, l in enumerate(lines) if l.strip()]
        edge = set(idx[:3] + idx[-3:])
        kept = [l for i, l in enumerate(lines)
                if not (i in edge and (key(l) in noisy or re.fullmatch(r"[#\s\-–|.]*(sayfa|page|s\.)?[#\s\-–|.]*",
                                                                       key(l))))]
        out.append((n, label, "\n".join(kept)))
    return out


def _heading(line: str):
    """Satır bir bölüm başlığıysa (başlık, kaynakça_mı), değilse None."""
    raw = line.strip()
    if not raw or len(raw) > 90 or raw.endswith((".", ",", ";")) and not re.match(r"^\d+\.\s", raw):
        return None
    if re.search(r"(\.\s?){4,}|…{2,}|\s\d+\s*$", raw) and re.search(r"\d\s*$", raw):
        return None                                      # içindekiler satırı ('1.2 Başlık ........ 44')
    f = re.sub(r"\s+", " ", fold(raw)).strip(" :")
    if _REFS_RE.match(f):
        return raw, True
    letters = [c for c in raw if c.isalpha()]
    upper = len(letters) >= 4 and sum(c.isupper() for c in letters) / len(letters) > 0.8 and len(raw.split()) <= 10
    numbered = re.match(r"^\d+(\.\d+){0,3}\.?\s+[A-ZÇĞİÖŞÜ]", raw) and len(raw.split()) <= 12
    if _HEAD_WORDS_RE.match(f) and len(raw.split()) <= 8 or upper or numbered:
        return raw, False
    return None


def structured_passages(pages, title="", offset=0) -> list:
    """[(sayfa, basılı_etiket, metin, tür, bağlam)] — bölüm başlıklarını izler, kaynakçayı işaretler."""
    out, heading, in_refs = [], "", False
    half = len(pages) / 2
    for n, label, text in pages:
        label = label or (str(n + offset) if offset and n + offset > 0 else "")
        block = []

        def flush():
            body = "\n".join(block).strip()
            for part in split_passages(body):
                out.append((n, label, part, "kaynakça" if in_refs else "", f"{title} · {heading}" if heading else title))
            block.clear()
        for line in (text or "").splitlines():
            h = _heading(line)
            if h:
                flush()
                heading = h[0]
                if h[1] and n >= half:
                    in_refs = True
                elif not h[1] and in_refs and re.match(r"(?i)^(ek|ekler|appendix|annex)", fold(h[0])):
                    in_refs = False
                continue
            block.append(line)
        flush()
    return out


def summary_passage(library, item) -> tuple:
    """Belge düzeyi katman: künye + anahtar kelimeler + özet (Öz/Abstract) + Claude özeti tek parça."""
    people = "; ".join(f"{p.get('family', '')} {p.get('given', '')}".strip() for p in item.get("authors") or [])
    abstract = abstract_of(library.get_fulltext(item["id"]), 1500)
    text = " · ".join(x for x in (item.get("title"), people, str(item.get("year") or ""), item.get("container"),
                                  item.get("keywords"), ", ".join(item.get("tags") or []), abstract,
                                  item.get("ai_ozet")) if x)
    return (0, "künye", text, "künye", "")


def build_passages(library, item, cancel=None) -> tuple:
    """Kaynağın dizine girecek parçaları. Dönüş: (parçalar, sayfalı_mı)"""
    path = item.get("file_path") or ""
    pages = []
    paged = False
    if path and os.path.isfile(path):
        try:
            if path.lower().endswith(".pdf"):
                pages, paged = pdf_pages(path, pause=0.002), 1
            elif path.lower().endswith(".epub"):
                pages, paged = epub_sections(path), 1
        except Exception as exc:
            diag(f"dizin: {Path(path).name}: {describe_error(exc)}", throttle=True)
            pages = []
        # taranmış (metni olmayan) sayfalar: daha önce okunduysa kayıtlı metinden, yoksa Windows metin tanıması
        blank = [n for n, _, t in pages if len(t.strip()) < 30]
        stored_pages = library.get_fulltext(item["id"]).split("\f") if blank else []
        if blank and len(stored_pages) == len(pages) and sum(len(x) for x in stored_pages) > 200:
            pages = [(n, label, stored_pages[n - 1] if len(text.strip()) < 30 else text) for n, label, text in pages]
            blank, paged = [], 2
        if path.lower().endswith(".pdf") and blank and len(blank) >= max(1, len(pages) // 5) \
                and not ocr_unavailable_reason():
            try:
                found = ocr_pdf(path, pages=blank, language=guess_language(item), cancel=cancel, pause=0.01)
                if found:
                    pages = [(n, label, found.get(n) or text) for n, label, text in pages]
                    paged = 2
                    text_all = "\f".join(t for _, _, t in pages)           # sayfa sınırları korunur
                    if len(text_all.strip()) > 200:
                        library.set_fulltext(item["id"], text_all[:FULLTEXT_MAX_CHARS])
            except Exception as exc:
                diag(f"metin tanıma: {Path(path).name}: {describe_error(exc)}", throttle=True)
                paged = 2
    if not any(t.strip() for _, _, t in pages):
        stored = library.get_fulltext(item["id"])           # PDF okunamadıysa ya da yoksa: özet/kayıtlı metin
        pages = [(0, "", stored)] if stored else []
        paged = paged if pages else (2 if paged == 2 else 0)
    offset = 0
    if paged and pages and pages[0][0] != 0:
        offset = printed_page_offset(pages, item)
        pages = strip_running_lines(pages)
        out = [summary_passage(library, item)] + structured_passages(pages, item.get("title") or "", offset)
    else:
        out = [summary_passage(library, item)]
        for page, label, text in pages:
            out += [(page, label, part, "", item.get("title") or "") for part in split_passages(text)]
    build_passages.last_offset = offset
    return out, paged


INDEX_DIR_NAME = "Metin Dizini"
SHARD_SIZE = 250                         # parça dosyası başına kaynak (kayıt numarasına göre)
_SHARD_RE = re.compile(r"^dizin_(\d{3,})\.db$")


def shard_name(no) -> str:
    return f"dizin_{(max(int(no or 1), 1) - 1) // SHARD_SIZE + 1:03d}.db"


def local_index_dir() -> Path:
    return settings_path().parent / "metin_dizini"


def shared_index_dir():
    shared = shared_dir()
    return shared / INDEX_DIR_NAME if shared is not None else None


# ── Atıf ağı: kaynakça sayfalarından kim kime atıf yapmış, kütüphanede olmayan sık atıflı eserler ─────

CITATIONS_NAME = "atif_agi.json"
_REF_START_RE = re.compile(
    r"^\s*(?:\[\d{1,3}\]|\d{1,3}[.)])\s+\S|"                                  # [12] / 12. numaralı
    r"^\s*[A-ZÇĞİÖŞÜÁÉÍÓÚÑÄË][\w'’\-çğıöşüáéíóúñäëß]+(?:\s(?:van|von|de|da|del|der)?\s?[A-ZÇĞİÖŞÜ][\w'’\-]+)?,"
    r"\s*(?:[A-ZÇĞİÖŞÜÁÉÍÓÚÑ]\.|[A-ZÇĞİÖŞÜÁÉÍÓÚÑ][a-zçğıöşüáéíóúñäë]+)")
_YEAR_RE = re.compile(r"(?<!\d)(1[89]\d{2}|20[0-4]\d)[a-z]?(?!\d)")


def citations_path() -> Path:
    return settings_path().parent / CITATIONS_NAME


def split_references(text: str) -> list:
    """Kaynakça metnini tek tek kaynak satırlarına böler."""
    entries, current = [], ""
    # parçalara bölünürken satır sonları kaybolmuş olabilir: 'Soyad, A. (2019)' gibi başlangıçlardan yeniden böl
    text = re.sub(r"(?<=[.)\]])\s+(?=(?:\[\d{1,3}\]\s*)?[A-ZÇĞİÖŞÜÁÉÍÓÚÑ][\w'’\-çğıöşüáéíóúñäë]+,\s*"
                  r"(?:[A-ZÇĞİÖŞÜÁÉÍÓÚÑ]\.|[A-ZÇĞİÖŞÜÁÉÍÓÚÑ][a-zçğıöşüáéíóúñäë]+)[^\n]{0,120}?(?:1[89]|20)\d{2})",
                  "\n", text or "")
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if _REF_START_RE.match(line) and len(current) > 25:
            entries.append(current)
            current = line
        else:
            current = (current + " " + line).strip() if current else line
    if current:
        entries.append(current)
    return [re.sub(r"\s+", " ", e) for e in entries if _YEAR_RE.search(e) and 30 <= len(e) <= 1200]


def parse_reference(ref: str) -> dict:
    """Kaynak satırından ilk yazar, yıl, başlık ve DOI (kaba ama hızlı)."""
    text = re.sub(r"^\s*(?:\[\d+\]|\d{1,3}[.)])\s*", "", ref)
    doi_m = DOI_RE.search(text)
    year_m = _YEAR_RE.search(text)
    author = re.split(r"[,(]", text, 1)[0].strip(" .")
    title = ""
    if year_m:
        after = text[year_m.end():]
        after = re.sub(r"^[a-z]?\)?[.,:;]?\s*", "", after)
        parts = [p.strip(" \"“”'‘’") for p in re.split(r"(?<=[.?!])\s+(?=[A-ZÇĞİÖŞÜ“\"])", after) if p.strip()]
        title = next((p for p in parts if len(p) >= 12), parts[0] if parts else "")
    return {"author": author[:60], "year": year_m.group(1) if year_m else "", "title": title[:220].rstrip("."),
            "doi": normalize_doi(clean_url(doi_m.group(1))) if doi_m else "", "raw": ref[:400]}


def _sig_words(text) -> list:
    return [w for w in re.findall(r"\w+", fold(text or "")) if len(w) >= 4]


def build_citation_graph(library, index) -> dict:
    """Bütün kaynakça parçalarını okuyup atıf ağını çıkarır (PDF açmaz; metin dizinini kullanır)."""
    items = library.all_items()
    by_doi = {normalize_doi(i["doi"]).lower(): i["id"] for i in items if i.get("doi")}
    by_author = {}
    for i in items:
        fam = fold((i.get("authors") or [{}])[0].get("family", "")) if i.get("authors") else ""
        if fam:
            by_author.setdefault(fam, []).append(i)
    texts = {}
    for name in index.names():
        for item_id, text in index.shard(name).passages_of_kind("kaynakça"):
            texts.setdefault(item_id, []).append(text)
    edges, missing = set(), {}
    for citing, chunks in texts.items():
        for ref in split_references("\n".join(chunks)):
            info = parse_reference(ref)
            target = by_doi.get(info["doi"].lower()) if info["doi"] else None
            if not target and info["author"] and info["year"]:
                fam = fold(info["author"].split()[0] if " " in info["author"] and info["author"].isupper()
                           else info["author"]).split(" ")[0]
                words = set(_sig_words(info["title"]))
                for cand in by_author.get(fam, []):
                    if str(cand.get("year") or "")[:4] and abs(int(str(cand["year"])[:4]) - int(info["year"])) > 1:
                        continue
                    cw = set(_sig_words(cand["title"]))
                    if words and cw and len(words & cw) / max(1, min(len(words), len(cw))) >= 0.6:
                        target = cand["id"]
                        break
            if target:
                if target != citing:
                    edges.add((citing, target))
                continue
            if not info["year"] or not info["author"] or len(_sig_words(info["title"])) < 2:
                continue
            key = info["doi"].lower() or (fold(info["author"]).split(" ")[0] + "|" + info["year"] + "|" +
                                          " ".join(_sig_words(info["title"])[:5]))
            entry = missing.setdefault(key, {**info, "citing": []})
            if citing not in entry["citing"]:
                entry["citing"].append(citing)
    top = sorted((m for m in missing.values() if len(m["citing"]) >= 2), key=lambda m: -len(m["citing"]))[:600]
    data = {"built": datetime.now().strftime("%Y-%m-%d %H:%M"), "edges": sorted(edges), "missing": top,
            "parsed_items": len(texts)}
    _write_json(citations_path(), data)
    return data


def load_citations() -> dict:
    return _read_json(citations_path())


def citation_counts(data) -> dict:
    counts = {}
    for _, cited in data.get("edges") or []:
        counts[cited] = counts.get(cited, 0) + 1
    return counts


# ── PDF'lerdeki vurgular, altı çizililer ve notlar → alıntı kartları ─────────────────────────────

HIGHLIGHT_STATE = "vurgu_tarama.json"
_HIGHLIGHT_TYPES = {"/Highlight", "/Underline", "/Squiggly"}
_NOTE_TYPES = {"/Text", "/FreeText"}


def pdf_highlights(path) -> list:
    """[(pdf_sayfa, vurgulanan_metin, not)] — vurgu/altı çizili/not ekleri."""
    from pypdf import PdfReader
    reader = PdfReader(str(path))
    out = []
    for n, page in enumerate(reader.pages, start=1):
        try:
            annots = page.get("/Annots")
            annots = annots.get_object() if annots is not None else []
        except Exception:
            continue
        marks = []
        for ref in annots or []:
            try:
                a = ref.get_object()
                sub = a.get("/Subtype")
                note = str(a.get("/Contents") or "").strip()
                if sub in _HIGHLIGHT_TYPES:
                    q = [float(v) for v in (a.get("/QuadPoints") or [])]
                    rects = []
                    for i in range(0, len(q) - 7, 8):
                        xs, ys = q[i:i + 8:2], q[i + 1:i + 8:2]
                        rects.append((min(xs), min(ys), max(xs), max(ys)))
                    if not rects and a.get("/Rect"):
                        r = [float(v) for v in a["/Rect"]]
                        rects = [(min(r[0], r[2]), min(r[1], r[3]), max(r[0], r[2]), max(r[1], r[3]))]
                    marks.append((rects, note))
                elif sub in _NOTE_TYPES and note:
                    out.append((n, "", note))
            except Exception:
                continue
        if not marks:
            continue
        pieces = []

        def visit(text, cm, tm, font, size):
            if not text or not text.strip():
                return
            x = tm[4] * cm[0] + tm[5] * cm[2] + cm[4]
            y = tm[4] * cm[1] + tm[5] * cm[3] + cm[5]
            pieces.append((x, y, text))
        try:
            page.extract_text(visitor_text=visit)
        except Exception:
            continue
        for rects, note in marks:
            got = []
            for x, y, text in pieces:
                for x0, y0, x1, y1 in rects:
                    if y0 - 3 <= y <= y1 + 1 and x0 - 4 <= x <= x1:
                        got.append(text)
                        break
            quote = re.sub(r"\s+", " ", " ".join(got)).strip()
            if quote or note:
                out.append((n, quote, note))
    return out


def title_looks_bad(item) -> bool:
    """Başlık dosya adından ya da PDF'in iç bilgisinden kalmış gibi mi? ('bildiri-kitabi_96567', 'Microsoft Word - x')"""
    t = (item.get("title") or "").strip()
    if not t:
        return True
    f = fold(t)
    if re.search(r"\.(pdf|docx?|epub)$", f) or f.startswith(("microsoft word", "untitled", "adsiz", "kapak")):
        return True
    if " " not in t and re.search(r"[-_]", t):
        return True
    if re.search(r"_\d{3,}$", t) or re.fullmatch(r"(indir|download|document|retrieve|fulltext|tam ?metin)\W*\d*", f):
        return True
    if t.count("-") + t.count("_") >= 3 and t.count(" ") <= 1:
        return True
    return bool(re.fullmatch(r"[\d\W_]+", t))


def reextract_record(session, item) -> dict:
    """Kayıtlı PDF'ten künyeyi baştan çıkarır (DOI → Crossref; bildiri kitabı / ISBN; PDF iç bilgisi).
    Daha iyi bir künye bulunamazsa {}."""
    path = item.get("file_path") or ""
    if not path.lower().endswith(".pdf") or not os.path.isfile(path):
        return {}
    head = pdf_text(path, max_pages=2, max_chars=20_000)
    rec = {}
    m = DOI_RE.search(head)
    if m and session is not None:
        doi = clean_url(m.group(1))
        cr = crossref_record(session, doi)
        if cr and title_matches_text(cr.get("title", ""), head):
            rec = dict(cr, doi=doi)
    if not rec.get("title"):
        book = book_like_record(session, path)
        if book.get("title"):
            rec = book
    if not rec.get("title"):
        info = pdf_info(path)
        title = info.get("title") or ""
        if len(title) > 10 and not title_looks_bad({"title": title}):
            rec = {"title": title, "authors": text_to_people(info.get("author", ""))}
    if not rec.get("title"):
        return {}
    new = finalize_record(rec)
    if fold(new["title"]) == fold(item.get("title") or "") and new.get("type") == item.get("type"):
        return {}
    return new


class ReextractWorker(threading.Thread):
    """Seçilen kayıtların künyesini PDF'ten yeniden çıkarır (önizleme için; kütüphaneye yazmaz).
    Mesajlar: ("rx", sıra, toplam) · ("rx_done", [(kayıt, yeni_künye)], durduruldu)"""

    def __init__(self, items, events):
        super().__init__(name="künye-yeniden", daemon=True)
        self.items, self.events = items, events
        self.cancel = threading.Event()

    def run(self):
        found = []
        session = make_session()
        try:
            for n, item in enumerate(self.items, start=1):
                if self.cancel.is_set():
                    break
                self.events.put(("rx", n, len(self.items)))
                try:
                    new = reextract_record(session, item)
                except Exception as exc:
                    diag(f"künye yeniden çıkarma: {describe_error(exc)}")
                    new = {}
                if new:
                    found.append((item, new))
        finally:
            session.close()
            self.events.put(("rx_done", found, self.cancel.is_set()))


class HighlightWorker(threading.Thread):
    """PDF'lerdeki vurguları alıntı kartlarına aktarır; değişmeyen dosyalar bir dahaki sefere atlanır.
    Mesajlar: ("hl", sıra, toplam) · ("hl_done", eklenen_kart, kaynak_sayısı, durduruldu)"""

    def __init__(self, library, events):
        super().__init__(name="vurgular", daemon=True)
        self.library, self.events = library, events
        self.cancel = threading.Event()

    def run(self):
        added, sources = 0, set()
        state_path = settings_path().parent / HIGHLIGHT_STATE
        state = _read_json(state_path)
        try:
            items = [i for i in self.library.all_items()
                     if (i.get("file_path") or "").lower().endswith(".pdf") and os.path.isfile(i["file_path"])]
            offsets = {}
            try:
                idx = ShardedIndex(readonly=True)
                offsets = {i["id"]: idx.page_offset(i["id"], i.get("no")) for i in items}
                idx.close()
            except Exception:
                pass
            for n, item in enumerate(items):
                if self.cancel.is_set():
                    break
                if n % 10 == 0:
                    self.events.put(("hl", n, len(items)))
                stamp = str(_stat(item["file_path"]))
                if state.get(str(item["id"])) == stamp:
                    continue
                try:
                    marks = pdf_highlights(item["file_path"])
                except Exception as exc:
                    diag(f"vurgular: {Path(item['file_path']).name}: {describe_error(exc)}", throttle=True)
                    marks = []
                have = {(c["page"], fold(c["quote"])[:120], fold(c["comment"])[:120])
                        for c in self.library.cards(item["id"])}
                for page, marked, note in marks:
                    off = offsets.get(item["id"]) or 0
                    shown = str(page + off) if off else str(page)
                    comment = (note + " " if note else "") + "[PDF işaretlemesi]"
                    key = (shown, fold(marked)[:120], fold(comment)[:120])
                    if key in have:
                        continue
                    self.library.add_card(item["id"], shown, marked, comment)
                    have.add(key)
                    added += 1
                    sources.add(item["id"])
                state[str(item["id"])] = stamp
                time.sleep(0.01)
            _write_json(state_path, state)
        except Exception:
            diag_exception("vurgu aktarımı")
        self.events.put(("hl_done", added, len(sources), self.cancel.is_set()))


TWIN_HEAD_CHARS = 5000


def _title_words(title) -> list:
    main = re.split(r"[:.?!]\s", title or "")[0]
    return re.findall(r"\w+", fold(main))


def _title_pattern(title):
    words = _title_words(title)
    if len(words) < 3 or sum(len(w) >= 4 for w in words) < 2:
        return None
    return re.compile(r"\b" + r"\W+".join(re.escape(w) for w in words[:8]) + r"\b")


def title_position(title, folded_head, pattern=None) -> int:
    """Başlık (ilk 8 kelimesi, sırasıyla) belgenin başında nerede geçiyor? Yoksa -1.
    'Türkiye'de' / 'TÜRKİYE’DE' gibi yazım farkları katlanarak yok sayılır."""
    pattern = pattern or _title_pattern(title)
    m = pattern.search(folded_head or "") if pattern else None
    return m.start() if m else -1


def _twin_compatible(a, b, folded_head) -> bool:
    """Başlığı b'nin PDF'inde geçen a, gerçekten aynı yayın mı? (kitap ↔ bölüm, farklı DOI, uzak yıl elenir)"""
    da, db = (normalize_doi(a.get("doi") or "") or "").lower(), (normalize_doi(b.get("doi") or "") or "").lower()
    if da and db and da != db:
        return False
    ta, tb = a.get("type") or "other", b.get("type") or "other"
    if ta != tb and "other" not in (ta, tb) and {ta, tb} != {"phd", "masters"}:
        return False
    ya, yb = str(a.get("year") or "")[:4], str(b.get("year") or "")[:4]
    if ya.isdigit() and yb.isdigit() and abs(int(ya) - int(yb)) > 2:
        return False
    fam = fold(((a.get("authors") or [{}])[0] or {}).get("family", "")) if a.get("authors") else ""
    if fam and len(fam) >= 3:
        other = fold(((b.get("authors") or [{}])[0] or {}).get("family", "")) if b.get("authors") else ""
        if fam != other and not re.search(r"\b" + re.escape(fam) + r"\b", folded_head or ""):
            return False
    return True


def preferred_keeper(a, b, folded_head):
    """İkizden hangisi tutulsun? PDF'te başlığı önce geçen (yayının asıl dilindeki) kayıt."""
    pa, pb = title_position(a["title"], folded_head), title_position(b["title"], folded_head)
    if pa >= 0 and (pb < 0 or pa < pb):
        return a
    return b


def find_pdf_twins(library, items=None) -> dict:
    """PDF'i olmayan ama aynı yayını başka bir kaydın PDF'i taşıyan kayıtlar (ör. Türkçe başlıklı kayıt PDF'siz,
    İngilizce başlıklı ikizi PDF'li): {pdfsiz_kimlik: {"holder": kimlik, "keeper": kimlik}}.
    Ölçüt: aynı DOI, ya da PDF'siz kaydın başlığı öbürünün PDF'inin ilk sayfalarında + yıl/yazar/tür uyumu."""
    items = items if items is not None else library.all_items()
    holders = {i["id"]: i for i in items if i.get("file_path")}
    nopdf = [i for i in items if not i.get("file_path")]
    if not holders or not nopdf:
        return {}
    out = {}
    by_doi = {}
    for h in holders.values():
        if h.get("doi"):
            by_doi.setdefault((normalize_doi(h["doi"]) or "").lower(), h)
    heads = library.fulltext_heads(holders.keys(), TWIN_HEAD_CHARS)
    for it in nopdf:
        h = by_doi.get((normalize_doi(it["doi"]) or "").lower() or "-") if it.get("doi") else None
        if h is not None:
            keeper = preferred_keeper(it, h, heads.get(h["id"], ""))
            out[it["id"]] = {"holder": h["id"], "keeper": keeper["id"]}
    wanted = {}
    for it in nopdf:
        if it["id"] not in out:
            words = [w for w in _title_words(it.get("title")) if len(w) >= 5]
            if len(words) >= 2:
                wanted[it["id"]] = words
    needed = {w for words in wanted.values() for w in words}
    inverted = {}
    for hid, head in heads.items():
        for w in needed.intersection(re.findall(r"\w{5,}", head)):
            inverted.setdefault(w, set()).add(hid)
    for it in nopdf:
        words = wanted.get(it["id"])
        if not words:
            continue
        pattern = _title_pattern(it.get("title"))
        if pattern is None:
            continue
        cands = None
        for w in sorted(set(words), key=lambda w: len(inverted.get(w, ())))[:3]:
            hits = inverted.get(w, set())
            cands = hits if cands is None else cands & hits
            if not cands:
                break
        for hid in sorted(cands or ()):
            head = heads[hid]
            if title_position(it["title"], head, pattern) < 0 or not _twin_compatible(it, holders[hid], head):
                continue
            keeper = preferred_keeper(it, holders[hid], head)
            out[it["id"]] = {"holder": hid, "keeper": keeper["id"]}
            break
    return out


def find_duplicates(items, twins=None) -> list:
    """Aynı yayının birden çok kaydı: aynı DOI, ya da aynı başlık (ön baskı/yayımlanmış hâli dahil) + aynı ilk
    yazar ya da yakın yıl. Dönüş: [[kayıt, …], …] — her grubun ilki tutulması önerilen kayıt."""
    parent = {i["id"]: i["id"] for i in items}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra
    buckets = {}
    for i in items:
        if i.get("doi"):
            buckets.setdefault("doi:" + normalize_doi(i["doi"]).lower(), []).append(i)
        words = _sig_words(re.split(r"[:.?]\s", i.get("title") or "")[0])
        if len(words) >= 3:
            buckets.setdefault("t:" + " ".join(words[:5]), []).append(i)
    for key, group in buckets.items():
        if len(group) < 2:
            continue
        for a in group[1:]:
            b = group[0]
            if key.startswith("doi:"):
                union(b["id"], a["id"])
                continue
            fa = fold((a.get("authors") or [{}])[0].get("family", "")) if a.get("authors") else ""
            fb = fold((b.get("authors") or [{}])[0].get("family", "")) if b.get("authors") else ""
            ya, yb = str(a.get("year") or "")[:4], str(b.get("year") or "")[:4]
            close_year = not ya or not yb or (ya.isdigit() and yb.isdigit() and abs(int(ya) - int(yb)) <= 2)
            same_author = bool(fa and fb and fa == fb)
            unknown_author = not fa or not fb
            if close_year and (same_author or (unknown_author and same_title(a["title"], b["title"]))):
                union(b["id"], a["id"])
    preferred = set()
    for nid, t in (twins or {}).items():
        if nid in parent and t["holder"] in parent:
            union(t["holder"], nid)
            preferred.add(t["keeper"])
    groups = {}
    for i in items:
        groups.setdefault(find(i["id"]), []).append(i)

    def score(i):
        has_file = bool(i.get("file_path")) and os.path.isfile(i["file_path"])
        return (i["id"] in preferred, has_file, bool(i.get("doi")), sum(1 for k in RECORD_FIELDS if i.get(k)),
                -(i.get("no") or 0))
    return [sorted(g, key=score, reverse=True) for g in groups.values() if len(g) > 1]


class ShardedIndex:
    """Kayıt numarasına göre 250'şer kaynaklık parça dosyalarından oluşan metin dizini. Ortak kütüphanede
    parçalar Drive'da durur; her bilgisayar değişen parçaları yerel önbelleğine alır, aramayı oradan yapar.
    Yeni kaynak eklenince yalnızca son parça (birkaç on MB) yeniden yüklenir."""

    def __init__(self, folder=None, readonly=False):
        self.folder = Path(folder) if folder else local_index_dir()
        self.readonly = readonly
        if not readonly:
            self.folder.mkdir(parents=True, exist_ok=True)
        self.shards = {}

    def names(self) -> list:
        try:
            return sorted(p.name for p in self.folder.iterdir() if _SHARD_RE.match(p.name))
        except OSError:
            return []

    def shard(self, name) -> PassageIndex:
        if name not in self.shards:
            self.shards[name] = PassageIndex(self.folder / name, readonly=self.readonly)
        return self.shards[name]

    def close(self):
        for idx in self.shards.values():
            idx.close()
        self.shards = {}

    def search(self, query, allowed=None, limit=15, per_item=2, kinds=None) -> list:
        rows = []
        for name in self.names():
            try:
                rows += self.shard(name).raw(query, kinds)
            except sqlite3.Error:
                continue
        return rank_hits(rows, query, allowed, limit, per_item)

    def page_offset(self, item_id, no=None) -> int:
        names = [shard_name(no)] if no else self.names()
        for name in names:
            if name in self.names():
                try:
                    off = self.shard(name).page_offset(item_id)
                except sqlite3.Error:
                    off = 0
                if off:
                    return off
        return 0

    def stats(self) -> dict:
        total = {"kaynak": 0, "parca": 0, "karakter": 0, "metinsiz": 0, "ocr": 0}
        for name in self.names():
            try:
                for k, v in self.shard(name).stats().items():
                    total[k] += v
            except sqlite3.Error:
                continue
        return total

    def thin_docs(self) -> set:
        out = set()
        for name in self.names():
            out |= self.shard(name).thin_docs()
        return out

    def signatures(self) -> dict:
        """{kimlik: (imza, parça adı)}"""
        out = {}
        for name in self.names():
            for item_id, sig in self.shard(name).signatures().items():
                out[item_id] = (sig, name)
        return out


def _stat(path):
    try:
        st = os.stat(path)
        return [st.st_size, st.st_mtime_ns]
    except OSError:
        return None


class IndexWorker(threading.Thread):
    """Metin dizinini arka planda günceller. Ortak kütüphanede: önce Drive'daki değişen parçaları alır; sonra
    (dizini o an başka bilgisayar güncellemiyorsa) eksik/değişen kaynakları okur ve yalnızca değişen
    parçaları Drive'a geri yükler. Mesajlar: ("index", yapılan, toplam) · ("index_done", istatistik, durduruldu)"""

    LOCK_NAME = "dizin_kilidi.json"
    LOCK_FRESH = 20 * 60

    def __init__(self, library, events):
        super().__init__(name="metin-dizini", daemon=True)
        self.library, self.events = library, events
        self.cancel = threading.Event()

    # --- Drive ile eşitleme ---------------------------------------------------
    def _cache_state(self, local):
        return _read_json(local / "onbellek.json")

    def _pull(self, remote, local) -> int:
        """Drive'da değişmiş parçaları yerel önbelleğe alır."""
        state = self._cache_state(local)
        got = 0
        for f in sorted(remote.glob("dizin_*.db")):
            if not _SHARD_RE.match(f.name):                  # 'dizin_003 (1).db' gibi çakışma kopyalarını atla
                continue
            st = _stat(f)
            if st and st != state.get(f.name) or not (local / f.name).is_file():
                tmp = local / (f.name + ".iniyor")
                try:
                    shutil.copyfile(f, tmp)
                    os.replace(tmp, local / f.name)
                    state[f.name] = st
                    got += 1
                except OSError:
                    tmp.unlink(missing_ok=True)                 # Claude o an okuyor olabilir: sonra yeniden
        _write_json(local / "onbellek.json", state)
        return got

    def _push(self, remote, local, names):
        state = self._cache_state(local)
        for name in names:
            tmp = remote / (name + ".yukleniyor")
            try:
                shutil.copyfile(local / name, tmp)
                os.replace(tmp, remote / name)
                state[name] = _stat(remote / name)
            except OSError as exc:
                diag(f"dizin yüklenemedi {name}: {describe_error(exc)}")
        _write_json(local / "onbellek.json", state)

    def _take_lock(self, remote) -> bool:
        info = _read_json(remote / self.LOCK_NAME)
        if info.get("machine") not in (None, machine_name()) and time.time() - float(info.get("ts", 0)) < self.LOCK_FRESH:
            self.holder = info.get("machine")
            return False
        _write_json(remote / self.LOCK_NAME, {"machine": machine_name(), "ts": time.time()})
        return True

    def _release_lock(self, remote):
        try:
            if _read_json(remote / self.LOCK_NAME).get("machine") == machine_name():
                (remote / self.LOCK_NAME).unlink(missing_ok=True)
        except OSError:
            pass

    def _migrate_single_file(self, index, items):
        """v2.30'un tek dosyalık dizinini parçalara böler (yeniden okumaya gerek kalmasın)."""
        old = index_path()
        if not old.is_file():
            return
        try:
            src = PassageIndex(old, readonly=True)
            nos = {i["id"]: i.get("no") or 0 for i in items}
            for item_id, sig in src.signatures().items():
                if item_id not in nos:
                    continue
                with src.lock:
                    rows = src.db.execute("SELECT page, label, text FROM passages WHERE item_id=? ORDER BY id",
                                          (item_id,)).fetchall()
                    paged = (src.db.execute("SELECT paged FROM docs WHERE item_id=?", (item_id,)).fetchone()
                             or [0])[0]
                index.shard(shard_name(nos[item_id])).put(item_id, sig, rows, bool(paged))
            src.close()
            old.replace(old.with_suffix(".db.eski"))
        except Exception:
            diag_exception("dizin taşıma")

    def run(self):
        index = None
        old_switch = sys.getswitchinterval()
        sys.setswitchinterval(0.0005)        # PDF okuma CPU'yu yorarken arayüz iş parçacığı sırasını çabuk alsın
        remote, locked, self.holder = shared_index_dir(), False, None
        local = local_index_dir()
        try:
            local.mkdir(parents=True, exist_ok=True)
            if remote is not None:
                remote.mkdir(parents=True, exist_ok=True)
                self._pull(remote, local)
                locked = self._take_lock(remote)
            index = ShardedIndex(local)
            items = sorted(self.library.all_items(), key=lambda i: i.get("no") or 0)
            if not index.names():
                self._migrate_single_file(index, items)
            stats_only = remote is not None and not locked
            dirty = set()
            if not stats_only:
                have = index.signatures()
                valid = {i["id"]: shard_name(i.get("no")) for i in items}
                for item_id, (sig, name) in have.items():   # silinen ya da numarası değişen kaynaklar
                    if valid.get(item_id) != name:
                        with index.shard(name).lock, index.shard(name).db:
                            index.shard(name)._drop(item_id)
                        dirty.add(name)
                thin = index.thin_docs() if not ocr_unavailable_reason() else set()
                todo = [i for i in items if have.get(i["id"], ("", ""))[0] != item_signature(i)
                        or have.get(i["id"], ("", ""))[1] != shard_name(i.get("no"))]
                todo += [i for i in items if i["id"] in thin and i not in todo]    # taranmışlar: metin tanıma
                last_push = time.time()
                for n, item in enumerate(todo):
                    if self.cancel.is_set():
                        break
                    if n % 5 == 0:
                        self.events.put(("index", n, len(todo)))
                    name = shard_name(item.get("no"))
                    build_passages.last_offset = 0
                    passages, paged = build_passages(self.library, item, self.cancel)
                    if self.cancel.is_set():
                        break
                    index.shard(name).put(item["id"], item_signature(item), passages, paged,
                                          getattr(build_passages, "last_offset", 0))
                    dirty.add(name)
                    time.sleep(0.05)                            # arayüze nefes aldır
                    if remote is not None and time.time() - last_push > 10 * 60 and dirty:
                        index.close()                           # uzun ilk kurulumda ara ara Drive'a yükle
                        self._push(remote, local, sorted(dirty))
                        dirty.clear()
                        _write_json(remote / self.LOCK_NAME, {"machine": machine_name(), "ts": time.time()})
                        last_push = time.time()
                index.close()
                if remote is not None and dirty:
                    self._push(remote, local, sorted(dirty))
            stats = ShardedIndex(local, readonly=True)
            result = stats.stats()
            stats.close()
            result.update(toplam=len(items), ortak=remote is not None, baska_bilgisayar=self.holder,
                          ocr_yok=ocr_unavailable_reason())
            self.events.put(("index_done", result, self.cancel.is_set()))
        except Exception:
            diag_exception("metin dizini")
            self.events.put(("index_done", {}, True))
        finally:
            sys.setswitchinterval(old_switch)
            if index is not None:
                index.close()
            if remote is not None and locked:
                self._release_lock(remote)


def abstract_of(text: str, limit=900) -> str:
    """Kayıtlı tam metinden özet bölümü (Öz/Özet/Abstract başlığından sonrası), yoksa baştan bir parça."""
    if not text:
        return ""
    m = re.search(r"(?i)\b(ÖZ|ÖZET|Öz|Özet|ABSTRACT|Abstract)\b\s*[:.\n]", text[:20000])
    body = text[m.end():] if m else text
    body = re.sub(r"\s+", " ", body).strip()
    return body[:limit] + ("…" if len(body) > limit else "")


MCP_INSTRUCTIONS = (
    "Bu araçlar kullanıcının kişisel akademik kütüphanesine (Akademik Kaynak İndirici; binlerce kaynak, PDF tam "
    "metinleriyle) erişir. Kullanıcı alanıyla ilgili bir soru sorduğunda, değerlendirme, derleme ya da fikir "
    "istediğinde ÖNCE kütüphanede ara: geniş sorularda kaynak_bul ile ilgili kaynakları seç, metinde_ara ile bütün "
    "PDF'lerin içinde kavramın geçtiği sayfaları bul. "
    "Kullanıcı Türkçe yazar ama kütüphanede İngilizce ve başka dillerde (İspanyolca, Bulgarca, Almanca…; dağılım "
    "kutuphane_ozeti'nde) çok kaynak var: her aramada sorguyu bu dillere çevirip 'ceviriler' ile birlikte gönder, "
    "eş anlamlılarla birkaç arama yap. Genel bakış için kaynak_ozetleri; derin okuma için pdf_metni_oku. Yabancı "
    "kaynaklardan aktarılanları Türkçeye çevirerek yaz, doğrudan alıntıda özgün dili koru ya da çevirdiğini belirt. "
    "Yanıtını kütüphanedeki kaynaklara dayandır, her bilgi için APA metin içi atıf "
    "ve basılı sayfa ver ((Yazar, yıl, s. X)); kaynakça sayfalarındaki geçişleri bilgi kaynağı sayma. Bir kaynağı "
    "derinlemesine okuduğunda ozet_kaydet ile yapılandırılmış özetini kaydet (sonraki sorular hızlanır). "
    "Kütüphanede olmayan genel bilgiyi ayrıca belirt. Önemli alıntıları "
    "kullanıcı isterse alinti_karti_ekle ile kaydet. Kaynak silmeden önce açık onay al. Kaynakça APA 7'dir."
)

STATUS_FILTER_VALUES = ["hepsi", "pdf_var", "pdf_yok", "yeni", "karti_olan", "scopus", "scopus_disi"]


def search_items(library, query="", tag="", status="hepsi", fulltext=False, year_min=None,
                 year_max=None, no_min=None, no_max=None) -> list:
    """Arayüzdeki arama/filtre mantığının aynısı (Claude araçları için)."""
    items = library.all_items()
    rng = parse_no_range(query)
    if rng:
        query, no_min, no_max = "", rng[0], rng[1]
    cards = library.card_counts()
    scopus = load_scopus()
    words = [w for w in fold(query or "").split() if w]
    extra = set()
    if words:
        extra |= library.card_text_ids(words)
        if fulltext:
            extra |= library.fulltext_ids(words)
    out = []
    for item in items:
        item["has_pdf"] = bool(item["file_path"]) and Path(item["file_path"]).is_file()
        item["cards"] = cards.get(item["id"], 0)
        sc = scopus_info(item, scopus) if scopus else None
        item["_scopus"] = SCOPUS_LABELS[sc[0]] if sc else ""
        blob = fold(" ".join([item["title"], people_to_text(item["authors"]), item["container"], item["year"],
                              item["notes"] or "", " ".join(item["tags"]), item["doi"], item.get("keywords", ""),
                              item.get("matched", "")]))
        if words and not (all(w in blob for w in words) or item["id"] in extra):
            continue
        if tag and fold(tag) not in {fold(t) for t in item["tags"]}:
            continue
        ok = {"hepsi": True, "pdf_var": item["has_pdf"], "pdf_yok": not item["has_pdf"],
              "yeni": bool(item["is_new"]), "karti_olan": item["cards"] > 0,
              "scopus": item["_scopus"] in ("Scopus", "Scopus (pasif)"),
              "scopus_disi": item["_scopus"] not in ("Scopus", "Scopus (pasif)")}.get(status or "hepsi", True)
        if not ok:
            continue
        try:
            year = int(item["year"]) if item["year"] else None
        except ValueError:
            year = None
        if year_min and (year is None or year < int(year_min)):
            continue
        if year_max and (year is None or year > int(year_max)):
            continue
        if no_min and (item.get("no") or 0) < int(no_min):
            continue
        if no_max and (item.get("no") or 0) > int(no_max):
            continue
        out.append(item)
    if no_min or no_max:
        out.sort(key=lambda i: i.get("no") or 0)
    else:
        out.sort(key=lambda i: (tr_sort_key(first_author_label(i)), i["year"]))
    return out


def _brief(item) -> dict:
    return {"id": item["id"], "kayit_no": item.get("no") or 0, "yazar": first_author_label(item), "yil": item["year"], "baslik": item["title"],
            "dergi_kitap": item["container"], "tur": ITEM_TYPES.get(item["type"], "Diğer"),
            "etiketler": item["tags"], "anahtar_kelimeler": split_keywords(item.get("keywords", "")),
            "pdf_var": bool(item["file_path"]) and Path(item["file_path"]).is_file(),
            "yeni": bool(item["is_new"]), "doi": item["doi"],
            "scopus": item["_scopus"] if "_scopus" in item else scopus_label(item)}


def _ids(value) -> list:
    if isinstance(value, (int, str)):
        value = [value]
    return [int(v) for v in value or []]


class McpTools:
    """Claude'a açılan araçlar. Her araç: (açıklama, giriş şeması, işlev)."""

    def __init__(self, library: Library):
        self.lib = library

    def definitions(self) -> list:
        s = lambda d: {"type": "string", "description": d}          # noqa: E731
        ids = {"type": "array", "items": {"type": "integer"}, "description": "Kaynak kimlikleri (kutuphane_ara'dan)"}
        return [
            ("kutuphane_ara", "Kütüphanede kaynak arar. Başlık, yazar, dergi, etiket, anahtar kelime ve alıntı "
                              "kartlarında arar; istenirse PDF tam metninde de. Sonuçta id'ler döner. Kullanıcı "
                              "'No 120' ya da '120-220 arası' derse kayıt numarasını (kayit_no) kastediyordur: "
                              "no_min/no_max kullanın; diğer araçlara kayit_no değil id verilir.",
             {"type": "object", "properties": {
                 "sorgu": s("Aranacak kelimeler (boş: hepsi)"),
                 "etiket": s("Yalnızca bu etiketi taşıyanlar"),
                 "durum": {"type": "string", "enum": STATUS_FILTER_VALUES,
                           "description": "Durum filtresi (scopus: dergisi Scopus listesinde olanlar; liste "
                                          "uygulamada yüklendiyse çalışır)"},
                 "pdf_icinde_ara": {"type": "boolean", "description": "PDF tam metninde de ara"},
                 "yil_min": {"type": "integer"}, "yil_max": {"type": "integer"},
                 "no_min": {"type": "integer", "description": "Kayıt numarası en az"},
                 "no_max": {"type": "integer", "description": "Kayıt numarası en çok"},
                 "limit": {"type": "integer", "description": "En fazla sonuç (varsayılan 50)"}}}),
            ("metinde_ara", "Kütüphanedeki BÜTÜN PDF'lerin metninde arar ve kavramın geçtiği sayfaları (parçaları) "
                            "en ilgiliden başlayarak döndürür: kaynak, dili, APA atıfı, sayfa ve metin. Bir konuda "
                            "bilgi, değerlendirme ya da derleme istendiğinde ilk adım budur. Kütüphane çok dillidir: "
                            "Türkçe sorgunun İngilizce (ve gerekirse başka dillerdeki) karşılıklarını 'ceviriler'e "
                            "yazın; tam ifade için tırnak kullanın (\"halk oyunları\").",
             {"type": "object", "properties": {
                 "sorgu": s("Aranacak kavram/kelimeler"),
                 "ceviriler": {"type": "array", "items": {"type": "string"},
                               "description": "Aynı sorgunun başka dillerdeki karşılıkları (ör. İngilizce, "
                                              "kütüphanede bulunan diğer diller); hepsi birlikte aranır ve "
                                              "sonuçlar dillere dengeli dağıtılır. Kullanıcı Türkçe yazsa da "
                                              "yabancı kaynakları bulmak için mutlaka kullanın."},
                 "etiket": s("Yalnızca bu etiketteki kaynaklarda"),
                 "yil_min": {"type": "integer"}, "yil_max": {"type": "integer"},
                 "no_min": {"type": "integer"}, "no_max": {"type": "integer"},
                 "kaynak_basina": {"type": "integer", "description": "Kaynak başına en fazla parça (varsayılan 2)"},
                 "limit": {"type": "integer", "description": "En fazla parça (varsayılan 15, en çok 40)"}},
              "required": ["sorgu"]}),
            ("kaynak_bul", "Soruyla en ilgili KAYNAKLARI bulur (belge düzeyi: başlık, yazar, anahtar kelimeler, "
                           "özet ve kayıtlı Claude özetleri üzerinde). Geniş bir soruda önce bununla okunacak "
                           "kaynakları seçin, sonra metinde_ara / pdf_metni_oku ile içine inin.",
             {"type": "object", "properties": {
                 "sorgu": s("Konu/kavramlar"),
                 "ceviriler": {"type": "array", "items": {"type": "string"},
                               "description": "Sorgunun başka dillerdeki karşılıkları"},
                 "limit": {"type": "integer", "description": "En fazla kaynak (varsayılan 15, en çok 40)"}},
              "required": ["sorgu"]}),
            ("atif_agi", "Kütüphanenin atıf ağı (kaynakça sayfalarından çıkarılır). id verilirse: o kaynağa "
                         "kütüphanede kimlerin atıf yaptığı ve onun atıf yaptığı kütüphane kaynakları. id yoksa: "
                         "kütüphanede en çok atıf alan temel kaynaklar ve kütüphanede OLMAYAN ama kaynaklarınızın "
                         "sık atıf yaptığı eserler (eksik temel literatür).",
             {"type": "object", "properties": {"id": {"type": "integer"},
                                               "limit": {"type": "integer", "description": "Liste uzunluğu (20)"}}}),
            ("ozet_kaydet", "Bir kaynağı okuduktan sonra onun yapılandırılmış özetini kütüphaneye kaydeder; sonraki "
                            "sorularda bu özet arama ve yanıt için kullanılır (kütüphane böylece giderek 'öğrenir'). "
                            "Biçim: Ana argüman · Yöntem/veri · Temel bulgular · Kavramlar · Sınırlılıklar · "
                            "Kullanıcının alanına katkısı. Türkçe yazın; varsa önceki özetin üzerine yazar.",
             {"type": "object", "properties": {"id": {"type": "integer"}, "ozet": s("Yapılandırılmış özet")},
              "required": ["id", "ozet"]}),
            ("kaynak_ozetleri", "Birçok kaynağın kısa künyesini, özetini (Öz/Abstract), anahtar kelimelerini ve "
                                "etiketlerini tek seferde verir; bir konunun ya da etiketin genel haritasını çıkarmak, "
                                "okunacakları seçmek için.",
             {"type": "object", "properties": {
                 "idler": ids, "etiket": s("Bu etiketteki kaynaklar"), "sorgu": s("Başlık/anahtar kelime araması"),
                 "no_min": {"type": "integer"}, "no_max": {"type": "integer"},
                 "limit": {"type": "integer", "description": "En fazla kaynak (varsayılan 40, en çok 100)"}}}),
            ("baglantidan_oku", "Kaynağın kayıttaki bağlantısından (çevrimiçi kitap/sayfa) metni okur; yalnızca "
                                "herkese açık içerik okunur, kurum girişi ya da ödünç gerektiren sayfalar okunamaz "
                                "(o zaman kullanıcının alıntı kartlarına bakın). Uzun metinlerde 'baslangic' ile "
                                "devam edin.",
             {"type": "object", "properties": {"id": {"type": "integer"},
                                               "baslangic": {"type": "integer", "description": "Karakter konumu (0)"}},
              "required": ["id"]}),
            ("kaynak_detay", "Bir kaynağın tüm künyesini, etiketlerini, anahtar kelimelerini, alıntı kartlarını, "
                             "PDF yolunu ve APA kaynakça satırını verir.",
             {"type": "object", "properties": {"id": {"type": "integer"}}, "required": ["id"]}),
            ("pdf_metni_oku", "Kaynağın PDF'inden metin okur (sayfa sayfa). Özet çıkarmak ya da alıntı bulmak için.",
             {"type": "object", "properties": {
                 "id": {"type": "integer"},
                 "baslangic_sayfa": {"type": "integer", "description": "1'den başlar (varsayılan 1)"},
                 "sayfa_sayisi": {"type": "integer", "description": "En fazla 15 (varsayılan 5)"}},
              "required": ["id"]}),
            ("etiket_ekle", "Kaynaklara etiket ekler.",
             {"type": "object", "properties": {"idler": ids, "etiketler": {"type": "array", "items": {"type": "string"}}},
              "required": ["idler", "etiketler"]}),
            ("etiket_kaldir", "Kaynaklardan etiket kaldırır.",
             {"type": "object", "properties": {"idler": ids, "etiketler": {"type": "array", "items": {"type": "string"}}},
              "required": ["idler", "etiketler"]}),
            ("kunye_guncelle", "Kaynağın künye alanlarını günceller. Yazarlar 'Soyad, Ad; Soyad, Ad' biçiminde.",
             {"type": "object", "properties": {
                 "id": {"type": "integer"},
                 "alanlar": {"type": "object", "description": "title, authors, year, type (article/chapter/book/phd/"
                                                              "masters/conference/other), container, volume, issue, "
                                                              "pages, publisher, doi, url, editors, institution, "
                                                              "keywords ('a; b')"}},
              "required": ["id", "alanlar"]}),
            ("alinti_karti_ekle", "Kaynağa alıntı kartı ekler (sayfa, alıntı, kullanıcının yorumu).",
             {"type": "object", "properties": {"id": {"type": "integer"}, "sayfa": s("Sayfa ya da aralık"),
                                               "alinti": s("Alıntı metni"), "yorum": s("Yorum/not")},
              "required": ["id"]}),
            ("kaynakca_olustur", "Seçilen kaynakların (id'ler ya da etiket) APA 7 kaynakçasını üretir; istenirse "
                                 "Word dosyası olarak kütüphane klasörüne kaydeder.",
             {"type": "object", "properties": {"idler": ids, "etiket": s("Bu etiketteki tüm kaynaklar"),
                                               "dil": {"type": "string", "enum": ["tr", "en"]},
                                               "word_dosyasi": {"type": "boolean"}}}),
            ("incelendi_isaretle", "Taramadan gelen 'yeni' işaretini kaldırır.",
             {"type": "object", "properties": {"idler": ids}, "required": ["idler"]}),
            ("kutuphaneden_cikar", "Kaynakları kütüphaneden çıkarır. ÖNCE kullanıcıdan açık onay al. "
                                   "pdf_sil=true ise PDF dosyaları da silinir.",
             {"type": "object", "properties": {"idler": ids, "pdf_sil": {"type": "boolean"}}, "required": ["idler"]}),
            ("linkleri_indir", "Metindeki linkleri/DOI'leri (en fazla 15) indirir ve kütüphaneye ekler.",
             {"type": "object", "properties": {"metin": s("Link, DOI ya da kaynakça içeren metin"),
                                               "etiketler": {"type": "array", "items": {"type": "string"}}},
              "required": ["metin"]}),
            ("kutuphane_ozeti", "Kütüphane istatistikleri: toplam, PDF'siz, yeni, etiket dağılımı, son tarama.",
             {"type": "object", "properties": {}}),
        ]

    # ── araç işlevleri ──────────────────────────────────────────────────────
    def call(self, name: str, args: dict):
        fn = getattr(self, "t_" + name, None)
        if fn is None:
            raise ValueError(f"Bilinmeyen araç: {name}")
        return fn(**(args or {}))

    def t_kutuphane_ara(self, sorgu="", etiket="", durum="hepsi", pdf_icinde_ara=False, yil_min=None,
                        yil_max=None, limit=50, no_min=None, no_max=None):
        items = search_items(self.lib, sorgu, etiket, durum, pdf_icinde_ara, yil_min, yil_max, no_min, no_max)
        limit = max(1, min(int(limit or 50), 300))
        return {"toplam": len(items), "gosterilen": min(len(items), limit),
                "kaynaklar": [_brief(i) for i in items[:limit]]}

    def _index(self):
        index = ShardedIndex(readonly=True)
        if not index.names():
            try:                                               # v2.30 tek dosyalık dizin (henüz bölünmediyse)
                return PassageIndex(readonly=True)
            except (FileNotFoundError, sqlite3.Error):
                return None
        return index

    def t_metinde_ara(self, sorgu, etiket="", yil_min=None, yil_max=None, no_min=None, no_max=None,
                      kaynak_basina=2, limit=20, ceviriler=None):
        index = self._index()
        if index is None:
            raise ValueError("Metin dizini henüz hazır değil. Akademik Kaynak İndirici programını açık bırakın; "
                             "dizin arka planda kurulur (Tarama sekmesinde ilerlemesi görünür). O zamana kadar "
                             "kutuphane_ara ve pdf_metni_oku kullanılabilir.")
        try:
            allowed = None
            if etiket or yil_min or yil_max or no_min or no_max:
                allowed = {i["id"] for i in search_items(self.lib, "", etiket, "hepsi", False, yil_min, yil_max,
                                                         no_min, no_max)}
            limit = max(1, min(int(limit or 20), 40))
            per_item = max(1, min(int(kaynak_basina or 2), 5))
            queries = [sorgu] + [q for q in (ceviriler or []) if isinstance(q, str) and q.strip()][:6]
            lists = [index.search(q, allowed, limit=limit, per_item=per_item) for q in queries]
            hits, seen, per = [], set(), {}
            for rank in range(limit):                         # dillere dengeli: sırayla her sorgudan bir parça
                for lst in lists:
                    if rank < len(lst):
                        h = lst[rank]
                        key = (h[0], h[1], h[3][:80])
                        if key in seen or per.get(h[0], 0) >= per_item:
                            continue
                        seen.add(key)
                        per[h[0]] = per.get(h[0], 0) + 1
                        hits.append(h)
                if len(hits) >= limit:
                    break
            hits = hits[:limit]
            stats = index.stats()
        finally:
            index.close()
        items = {}
        out = []
        for item_id, page, label, text, score, *rest in hits:
            kind = rest[0] if rest else ""
            item = items.get(item_id) or self.lib.get(item_id)
            if not item:
                continue
            items[item_id] = item
            shown = label or (str(page) if page else "")
            out.append({"id": item_id, "kayit_no": item.get("no") or 0, "baslik": item["title"],
                        "dil": _LANG_NAMES.get(guess_language(item), guess_language(item)),
                        "atif": intext_citation(item, shown if page else ""),
                        "sayfa": shown or ("künye/özet" if page == 0 else ""), "pdf_sayfasi": page or None,
                        "bolum": "kaynakça (yalnızca atıf)" if kind == "kaynakça" else "",
                        "metin": text[:1500]})
        return {"sorgu": sorgu, "aranan": [sorgu] + list(ceviriler or []), "bulunan_parca": len(out),
                "kaynak_sayisi": len(items),
                "dizin": {"dizindeki_kaynak": stats["kaynak"], "kutuphanedeki_kaynak": self.lib.count(),
                          "metinsiz_pdf": stats["metinsiz"]},
                "parcalar": out,
                "not": "Atıfta 'sayfa' (basılı sayfa numarası) kullanılır; pdf_sayfasi, pdf_metni_oku'daki "
                       "baslangic_sayfa değeridir."}

    def t_baglantidan_oku(self, id, baslangic=0):
        item = self.lib.get(int(id))
        if not item:
            raise ValueError(f"{id} numaralı kaynak yok")
        text, source = "", ""
        if item.get("url"):
            session = make_session()
            try:
                info = online_book_info(session, item["url"])
            finally:
                session.close()
            if info["access"] == "restricted":
                cards = self.lib.cards(item["id"])
                raise ValueError(f"Bu bağlantı ({info['platform']}) kurum girişi ya da ödünç alma istiyor; içerik "
                                 f"okunamıyor. Kullanıcının bu kaynakta {len(cards)} alıntı kartı var "
                                 "(kaynak_detay ile bakın).")
            text, source = info["text"], info["platform"]
        if not text:
            text, source = self.lib.get_fulltext(item["id"]), "kayıtlı metin"
        if not text:
            raise ValueError("Bu kaynağın okunabilir çevrimiçi metni yok (PDF'i varsa pdf_metni_oku kullanın).")
        start = max(0, int(baslangic or 0))
        chunk = text[start:start + 40_000]
        return {"baslik": item["title"], "kaynak": source, "toplam_karakter": len(text), "baslangic": start,
                "sonraki": start + len(chunk) if start + len(chunk) < len(text) else None, "metin": chunk}

    def t_kaynak_bul(self, sorgu, ceviriler=None, limit=15):
        index = self._index()
        if index is None or not hasattr(index, "names"):
            raise ValueError("Metin dizini henüz hazır değil; kutuphane_ara kullanılabilir.")
        try:
            limit = max(1, min(int(limit or 15), 40))
            seen, hits = set(), []
            for q in [sorgu] + [c for c in (ceviriler or []) if isinstance(c, str) and c.strip()][:6]:
                for h in index.search(q, limit=limit, per_item=1, kinds=["künye"]):
                    if h[0] not in seen:
                        seen.add(h[0])
                        hits.append(h)
        finally:
            index.close()
        hits.sort(key=lambda h: -h[4])
        out = []
        for h in hits[:limit]:
            item = self.lib.get(h[0])
            if not item:
                continue
            out.append({"id": item["id"], "kayit_no": item.get("no") or 0, "atif": intext_citation(item),
                        "baslik": item["title"], "dil": _LANG_NAMES.get(guess_language(item), guess_language(item)),
                        "ozet": abstract_of(self.lib.get_fulltext(item["id"]), 700),
                        "claude_ozeti": item.get("ai_ozet") or "",
                        "pdf_var": bool(item["file_path"]) and Path(item["file_path"]).is_file()})
        return {"sorgu": sorgu, "kaynaklar": out}

    def t_atif_agi(self, id=None, limit=20):
        data = load_citations()
        if not data:
            raise ValueError("Atıf ağı henüz hesaplanmadı; metin dizini kurulunca kendiliğinden hesaplanır.")
        limit = max(1, min(int(limit or 20), 100))
        brief = lambda i: {"id": i["id"], "kayit_no": i.get("no") or 0, "atif": intext_citation(i),   # noqa: E731
                           "baslik": i["title"]}
        edges = data.get("edges") or []
        if id:
            item = self.lib.get(int(id))
            if not item:
                raise ValueError(f"{id} numaralı kaynak yok")
            citing = [self.lib.get(a) for a, b in edges if b == item["id"]]
            cited = [self.lib.get(b) for a, b in edges if a == item["id"]]
            return {"kaynak": brief(item), "kutuphanede_atif_yapanlar": [brief(i) for i in citing if i][:limit],
                    "kutuphanede_atif_yaptiklari": [brief(i) for i in cited if i][:limit]}
        counts = citation_counts(data)
        top = [dict(brief(self.lib.get(k)), atif_sayisi=v) for k, v in sorted(counts.items(), key=lambda kv: -kv[1])
               if self.lib.get(k)][:limit]
        missing = [{"atif_sayisi": len(m["citing"]), "yazar": m["author"], "yil": m["year"], "baslik": m["title"],
                    "doi": m.get("doi") or "", "kaynak_satiri": m["raw"][:250]} for m in (data.get("missing") or [])[:limit]]
        return {"hesaplandi": data.get("built"), "kaynakcasi_okunan": data.get("parsed_items"),
                "en_cok_atif_alanlar": top, "kutuphanede_olmayan_sik_atiflilar": missing}

    def t_ozet_kaydet(self, id, ozet):
        item = self.lib.get(int(id))
        if not item:
            raise ValueError(f"{id} numaralı kaynak yok")
        text = (ozet or "").strip()
        if len(text) < 40:
            raise ValueError("Özet çok kısa")
        stamped = f"{text}\n\n[Claude özeti · {datetime.now():%d.%m.%Y}]"
        self.lib.update(item["id"], {"ai_ozet": stamped})
        return {"tamam": True, "kayit_no": item.get("no") or 0, "baslik": item["title"]}

    def t_kaynak_ozetleri(self, idler=None, etiket="", sorgu="", no_min=None, no_max=None, limit=40):
        if idler:
            items = [i for i in (self.lib.get(x) for x in _ids(idler)) if i]
        else:
            items = search_items(self.lib, sorgu, etiket, "hepsi", False, None, None, no_min, no_max)
        limit = max(1, min(int(limit or 40), 100))
        out = []
        for item in items[:limit]:
            text = self.lib.get_fulltext(item["id"])
            out.append({"id": item["id"], "kayit_no": item.get("no") or 0,
                        "kunye": apa_text(item, "tr"), "anahtar_kelimeler": split_keywords(item.get("keywords", "")),
                        "etiketler": item.get("tags") or [], "ozet": abstract_of(text),
                        "claude_ozeti": item.get("ai_ozet") or "",
                        "pdf_var": bool(item["file_path"]) and Path(item["file_path"]).is_file()})
        return {"toplam": len(items), "gosterilen": len(out), "kaynaklar": out}

    def t_kaynak_detay(self, id):
        item = self.lib.get(int(id))
        if not item:
            raise ValueError(f"{id} numaralı kaynak yok")
        detail = _brief(item)
        detail.update({
            "yazarlar": people_to_text(item["authors"]), "editorler": people_to_text(item["editors"]),
            "cilt": item["volume"], "sayi": item["issue"], "sayfalar": item["pages"], "yayinevi": item["publisher"],
            "kurum": item["institution"], "url": item["url"], "pdf_yolu": item["file_path"], "issn": item["issn"],
            "eklenme": item["added"], "kaynagi": item.get("source", ""), "tarama_eslesmesi": item.get("matched", ""),
            "kurum_erisimi_veritabani": database_for_doi(item["doi"]),
            "apa": apa_text(item, "tr"), "metin_ici_atif": intext_citation(item),
            "claude_ozeti": item.get("ai_ozet") or "",
            "alinti_kartlari": [{"id": c["id"], "sayfa": c["page"], "alinti": c["quote"], "yorum": c["comment"],
                                 "atifla": card_citation_text(c, item)} for c in self.lib.cards(item["id"])],
        })
        return detail

    def t_pdf_metni_oku(self, id, baslangic_sayfa=1, sayfa_sayisi=5):
        item = self.lib.get(int(id))
        if not item or not item["file_path"] or not Path(item["file_path"]).is_file():
            raise ValueError("Bu kaynağın PDF'i yok")
        if item["file_path"].lower().endswith(".epub"):
            parts = epub_sections(item["file_path"])
            if not parts:
                raise ValueError("Bu e-kitap okunamıyor (kopya korumalı olabilir)")
            start = max(1, int(baslangic_sayfa or 1))
            count = max(1, min(int(sayfa_sayisi or 5), 10))
            chosen = parts[start - 1:start - 1 + count]
            return {"baslik": item["title"], "toplam_sayfa": len(parts),
                    "metin": "\n".join(f"--- {label} ---\n{text}" for _, label, text in chosen)[:60_000],
                    "not": "EPUB'da basılı sayfa yok; parçalar ~6000 karakterdir."}
        from pypdf import PdfReader
        reader = PdfReader(item["file_path"])
        start = max(1, int(baslangic_sayfa or 1))
        count = max(1, min(int(sayfa_sayisi or 5), 15))
        pages, texts = [], {}
        for n in range(start, min(start + count, len(reader.pages) + 1)):
            try:
                texts[n] = reader.pages[n - 1].extract_text() or ""
            except Exception:
                texts[n] = ""
        blank = [n for n, t in texts.items() if len(t.strip()) < 30]
        if blank and not ocr_unavailable_reason():                # taranmış sayfa: Windows metin tanıması
            try:
                texts.update({n: t for n, t in ocr_pdf(item["file_path"], pages=blank[:8],
                                                       language=guess_language(item)).items() if t})
            except Exception as exc:
                diag(f"Claude OCR: {describe_error(exc)}", throttle=True)
        offset = 0
        try:
            idx = ShardedIndex(readonly=True)
            offset = idx.page_offset(item["id"], item.get("no"))
            idx.close()
        except Exception:
            offset = 0
        labels = {}
        try:
            labels = {i + 1: str(v) for i, v in enumerate(reader.page_labels)}
        except Exception:
            labels = {}
        for n, text in texts.items():
            printed = labels.get(n) if labels.get(n) and labels.get(n) != str(n) else (str(n + offset) if offset else "")
            pages.append(f"--- PDF sayfası {n}" + (f" (basılı s. {printed})" if printed else "") + f" ---\n{text}")
        body = "\n".join(pages)[:60_000]
        return {"baslik": item["title"], "toplam_sayfa": len(reader.pages), "metin": body,
                "not": "Atıfta 'basılı s.' numarasını kullanın (yoksa PDF sayfası)."}

    def t_etiket_ekle(self, idler, etiketler):
        for i in _ids(idler):
            self.lib.add_tags(i, etiketler)
        return {"tamam": True, "etiketlenen": len(_ids(idler))}

    def t_etiket_kaldir(self, idler, etiketler):
        drop = {fold(t) for t in clean_tags(etiketler)}
        for i in _ids(idler):
            item = self.lib.get(i)
            if item:
                self.lib.set_tags(i, [t for t in item["tags"] if fold(t) not in drop])
        return {"tamam": True}

    def t_kunye_guncelle(self, id, alanlar):
        item = self.lib.get(int(id))
        if not item:
            raise ValueError(f"{id} numaralı kaynak yok")
        fields = dict(alanlar or {})
        for key in ("authors", "editors"):
            if isinstance(fields.get(key), str):
                fields[key] = text_to_people(fields[key])
        if isinstance(fields.get("keywords"), list):
            fields["keywords"] = join_keywords(fields["keywords"])
        merged = finalize_record(merge_records(fields, item))
        if "title" in fields:
            merged["title"] = str(fields["title"]).strip().rstrip(".")
        self.lib.update(int(id), {k: merged[k] for k in RECORD_FIELDS})
        return {"tamam": True, "apa": apa_text(self.lib.get(int(id)))}

    def t_alinti_karti_ekle(self, id, sayfa="", alinti="", yorum=""):
        item = self.lib.get(int(id))
        if not item:
            raise ValueError(f"{id} numaralı kaynak yok")
        card_id = self.lib.add_card(int(id), str(sayfa or ""), alinti or "", yorum or "")
        card = next(c for c in self.lib.cards(int(id)) if c["id"] == card_id)
        return {"kart_id": card_id, "atifla": card_citation_text(card, item)}

    def t_kaynakca_olustur(self, idler=None, etiket="", dil="tr", word_dosyasi=False):
        if idler:
            records = [self.lib.get(i) for i in _ids(idler)]
        elif etiket:
            records = search_items(self.lib, tag=etiket)
        else:
            raise ValueError("idler ya da etiket verin")
        records = [r for r in records if r]
        refs = bibliography(records, dil if dil in ("tr", "en") else "tr")
        out = {"kaynak_sayisi": len(refs), "kaynakca": "\n".join(t for t, _ in refs)}
        if word_dosyasi:
            folder = Path(load_settings().get("library_folder") or Path.home()) / "Kaynakçalar"
            folder.mkdir(parents=True, exist_ok=True)
            path = unique_path(folder, f"Kaynakça {datetime.now():%Y-%m-%d %H%M}.docx")
            write_bibliography_docx(path, refs, "Kaynakça" if dil != "en" else "References")
            out["word_dosyasi"] = str(path)
        return out

    def t_incelendi_isaretle(self, idler):
        for i in _ids(idler):
            self.lib.update(i, {"is_new": 0})
        return {"tamam": True}

    def t_kutuphaneden_cikar(self, idler, pdf_sil=False):
        removed = []
        for i in _ids(idler):
            item = self.lib.get(i)
            if not item:
                continue
            if pdf_sil and item["file_path"] and Path(item["file_path"]).is_file():
                try:
                    Path(item["file_path"]).unlink()
                except OSError:
                    pass
            self.lib.delete(i)
            removed.append(item["title"])
        return {"cikarilan": removed}

    def t_linkleri_indir(self, metin, etiketler=None):
        links = extract_links(metin)[:15]
        if not links:
            return {"mesaj": "Metinde link ya da DOI bulunamadı."}
        settings = load_settings()
        folder = settings.get("library_folder") or str(default_library_dir())
        Path(folder).mkdir(parents=True, exist_ok=True)
        events = queue.Queue()
        DownloadWorker(links, folder, {
            "find_pdf": True, "save_html": False, "skip_existing": True, "email": settings.get("email", ""),
            "library": self.lib, "library_folder": folder, "tags": etiketler or []}, events, threading.Event()).run()
        lines, summary = [], None
        while not events.empty():
            m = events.get()
            if m[0] == "log" and m[1] in ("success", "error", "warn") or (m[0] == "log" and "Tekrar indirilmedi" in m[2]):
                lines.append(m[2].strip())
            if m[0] == "done":
                summary = m[1]
        return {"sonuc": summary, "ayrinti": lines[-40:]}

    def t_kutuphane_ozeti(self):
        items = search_items(self.lib)
        tags = {}
        for i in items:
            for t in i["tags"]:
                tags[t] = tags.get(t, 0) + 1
        settings = load_settings()
        langs = {}
        for i in items:
            name = _LANG_NAMES.get(guess_language(i), guess_language(i))
            langs[name] = langs.get(name, 0) + 1
        return {"toplam": len(items), "diller_tahmini": dict(sorted(langs.items(), key=lambda kv: -kv[1])),
                "pdf_yok": sum(1 for i in items if not i["has_pdf"]),
                "scopus_dergilerinde": (sum(1 for i in items if i["_scopus"] in ("Scopus", "Scopus (pasif)"))
                                        if load_scopus() else "Scopus listesi yüklenmedi"),
                "yeni": sum(1 for i in items if i["is_new"]), "alinti_karti_olan": sum(1 for i in items if i["cards"]),
                "etiketler": dict(sorted(tags.items(), key=lambda kv: -kv[1])),
                "son_tarama": settings.get("last_scan"), "son_rapor": settings.get("last_report"),
                "kutuphane_klasoru": settings.get("library_folder")}


def run_mcp_server():
    """Claude masaüstü uygulaması için stdio MCP sunucusu (satır satır JSON-RPC 2.0)."""
    stdin = sys.stdin.buffer
    stdout = sys.stdout.buffer
    sys.stdout = sys.stderr                       # başka hiçbir çıktı protokolü bozmasın
    library = Library()
    tools = McpTools(library)
    definitions = tools.definitions()
    diag("Claude bağlantısı (MCP) başladı")
    sync = LibrarySync(library)
    writes = {"etiket_ekle", "etiket_kaldir", "kunye_guncelle", "alinti_karti_ekle", "incelendi_isaretle",
              "kutuphaneden_cikar", "linkleri_indir"}
    last_push = [0.0]

    def sync_safely(action):
        try:
            state = sync.status()
            if action == "start" and state == "al":
                sync.pull()
            elif action in ("write", "exit") and state in ("gonder", "ilk"):
                if action == "exit" or time.time() - last_push[0] > 120:
                    sync.push()
                    last_push[0] = time.time()
            elif state == "cakisma":
                diag("MCP: ortak kütüphanede çakışma var; uygulama açılınca çözülecek")
        except Exception:
            diag_exception("MCP eşitleme")

    sync_safely("start")

    def send(message):
        stdout.write((json.dumps(message, ensure_ascii=False) + "\n").encode("utf-8"))
        stdout.flush()

    for raw in stdin:
        line = raw.decode("utf-8", errors="replace").strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except ValueError:
            send({"jsonrpc": "2.0", "id": None, "error": {"code": -32700, "message": "Parse error"}})
            continue
        method, mid = msg.get("method"), msg.get("id")
        if mid is None:                           # bildirim (ör. notifications/initialized)
            continue
        try:
            if method == "initialize":
                version = (msg.get("params") or {}).get("protocolVersion") or "2025-06-18"
                result = {"protocolVersion": version, "capabilities": {"tools": {"listChanged": False}},
                          "serverInfo": {"name": MCP_SERVER_NAME, "version": APP_VERSION},
                          "instructions": MCP_INSTRUCTIONS}
            elif method == "ping":
                result = {}
            elif method == "tools/list":
                result = {"tools": [{"name": n, "description": d, "inputSchema": schema}
                                    for n, d, schema in definitions]}
            elif method == "tools/call":
                params = msg.get("params") or {}
                try:
                    data = tools.call(params.get("name", ""), params.get("arguments") or {})
                    if params.get("name") in writes:
                        sync_safely("write")
                    result = {"content": [{"type": "text", "text": json.dumps(data, ensure_ascii=False, indent=1)}],
                              "isError": False}
                except Exception as exc:
                    diag_exception(f"MCP aracı {params.get('name')}")
                    result = {"content": [{"type": "text", "text": f"Hata: {exc}"}], "isError": True}
            elif method in ("resources/list", "prompts/list"):
                result = {method.split("/")[0]: []}
            else:
                send({"jsonrpc": "2.0", "id": mid, "error": {"code": -32601, "message": f"Yöntem yok: {method}"}})
                continue
            send({"jsonrpc": "2.0", "id": mid, "result": result})
        except Exception as exc:
            diag_exception("MCP")
            send({"jsonrpc": "2.0", "id": mid, "error": {"code": -32603, "message": str(exc)}})
    sync_safely("exit")
    library.close()


MCP_EXE_NAME = "AkademikKutuphaneMCP"


def mcpb_manifest() -> dict:
    tools = McpTools.__new__(McpTools).definitions()
    exe = f"{MCP_EXE_NAME}.exe"
    return {
        "manifest_version": "0.3",
        "name": MCP_SERVER_NAME,
        "display_name": "Akademik Kütüphanem",
        "version": re.sub(r"^(\d+)\.(\d+)$", r"\1.\2.0", APP_VERSION),
        "description": "Akademik Kaynak İndirici kütüphanesini Claude'a açar: arama, etiket, alıntı kartı, "
                       "APA kaynakça, PDF okuma, link indirme.",
        "author": {"name": "Akademik Kaynak İndirici"},
        "server": {"type": "binary", "entry_point": f"server/{exe}",
                   "mcp_config": {"command": "${__dirname}/server/" + exe, "args": ["--mcp"], "env": {}}},
        "icon": "icon.png",
        "tools": [{"name": n, "description": d} for n, d, _ in tools],
        "compatibility": {"platforms": ["win32"]},
    }


def pack_mcpb(server_dir, out_path):
    """PyInstaller klasörünü (server/) ve manifest'i tek .mcpb (zip) dosyasında toplar."""
    server_dir, out_path = Path(server_dir), Path(out_path)
    with zipfile.ZipFile(out_path, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("manifest.json", json.dumps(mcpb_manifest(), ensure_ascii=False, indent=2))
        zf.writestr("icon.png", icon_png(256))
        for f in sorted(server_dir.rglob("*")):
            if f.parent == server_dir and f.stem == "AkademikIndirici":
                continue                          # arayüz programı uzantıda gerekmez
            if f.is_file():
                zf.write(f, "server/" + f.relative_to(server_dir).as_posix())
    return out_path


def mcp_exe_path() -> Path:
    """Programla aynı klasördeki Claude bağlantı programı (yalnızca .exe sürümünde vardır)."""
    if getattr(sys, "frozen", False):
        return Path(sys.executable).with_name(f"{MCP_EXE_NAME}.exe")
    return Path(__file__).resolve().with_name(f"{MCP_EXE_NAME}.exe")


def mcp_server_entry() -> dict:
    return {"command": str(mcp_exe_path()), "args": ["--mcp"]}


def claude_config_snippet() -> str:
    """Uzantı kurulamazsa elle eklenecek claude_desktop_config.json girdisi."""
    return json.dumps({"mcpServers": {MCP_SERVER_NAME: mcp_server_entry()}}, ensure_ascii=False, indent=2)


def claude_config_paths() -> list:
    """Claude masaüstü uygulamasının ayar dosyası (normal kurulum ve Microsoft Store kurulumu)."""
    paths = []
    if os.environ.get("APPDATA"):
        paths.append(Path(os.environ["APPDATA"]) / "Claude" / "claude_desktop_config.json")
    if os.environ.get("LOCALAPPDATA"):
        for pkg in sorted(Path(os.environ["LOCALAPPDATA"], "Packages").glob("Claude_*")):
            paths.append(pkg / "LocalCache" / "Roaming" / "Claude" / "claude_desktop_config.json")
    return paths


def connect_claude_desktop() -> list:
    """Bağlantıyı Claude'un ayar dosyasına ekler; diğer ayarlara dokunmaz, önce yedek alır.
    Yazılan dosyaların listesini döndürür. Claude kurulu değilse boş liste."""
    written = []
    for path in claude_config_paths():
        if not path.parent.is_dir():
            continue
        data = {}
        if path.is_file():
            raw = path.read_text(encoding="utf-8-sig").strip()
            if raw:
                try:
                    data = json.loads(raw)
                except ValueError:
                    raise ValueError(f"Claude'un ayar dosyası okunamadı (bozuk JSON):\n{path}")
                if not isinstance(data, dict):
                    raise ValueError(f"Claude'un ayar dosyası beklenmedik biçimde:\n{path}")
                backup = path.with_name(path.name + ".yedek")
                if not backup.exists():
                    shutil.copy2(path, backup)
        servers = data.get("mcpServers")
        if not isinstance(servers, dict):
            servers = {}
        servers[MCP_SERVER_NAME] = mcp_server_entry()
        data["mcpServers"] = servers
        tmp = path.with_name(path.name + ".tmp")
        tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        os.replace(tmp, path)
        written.append(path)
    return written


# ════════════════════════════════════════════════════════════════════════════
#  7) AYARLAR (klasör, e-posta ve seçenekler bir sonraki açılışta hatırlanır)
# ════════════════════════════════════════════════════════════════════════════

def settings_path() -> Path:
    base = os.environ.get("APPDATA") or str(Path.home() / "AppData" / "Roaming" if sys.platform == "win32"
                                             else Path.home())
    return Path(base) / "AkademikIndirici" / "ayarlar.json"


def _load_settings_raw() -> dict:
    try:
        with open(settings_path(), encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def load_settings() -> dict:
    """Bu bilgisayarın ayarları; ortak kütüphanede son tarama bilgisi buluttaki ortak dosyadan gelir."""
    data = _load_settings_raw()
    shared = shared_dir(data)
    if shared is not None:
        state = shared_state(shared)
        if state.get("last_scan"):
            data["last_scan"] = state["last_scan"]
            name = state.get("last_report_name")
            if name:
                data["last_report"] = str(Path(data["library_folder"]) / "Tarama Raporları" / name)
    return data


_SETTINGS_LOCK = threading.RLock()


def update_settings(**changes):
    """Ayar dosyasında yalnızca verilen anahtarları değiştirir (iş parçacıkları arasında güvenli)."""
    with _SETTINGS_LOCK:
        current = _load_settings_raw()
        current.update(changes)
        save_settings(current)


def save_settings(data: dict):
    with _SETTINGS_LOCK:
        _save_settings(data)


def _save_settings(data: dict):
    try:
        path = settings_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_name(path.name + ".tmp")
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
    except OSError:
        pass
    shared = shared_dir(data)
    if shared is not None and data.get("last_scan"):
        try:
            state = shared_state(shared)
            if not state.get("last_scan") or data["last_scan"] > state["last_scan"]:
                new = {"last_scan": data["last_scan"], "machine": machine_name(),
                       "last_report_name": Path(data["last_report"]).name if data.get("last_report") else ""}
                _write_json(shared / SHARED_STATE_NAME, new)
                _SHARED_STATE.update(path=str(shared / SHARED_STATE_NAME), data=new, t=time.monotonic())
        except OSError:
            pass


# ── Uygulama simgesi: açık kitaba inen ok (16–256 piksel, tek .ico içinde) ─────────────
# Derleme tarifi (AkademikIndirici.spec) exe simgesini de buradan üretir.
APP_ICON_ICO_B64 = (
    "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"
)


def app_icon_bytes() -> bytes:
    import base64
    return base64.b64decode(APP_ICON_ICO_B64)


def icon_png(size: int = 256) -> bytes:
    """.ico içindeki en yakın boyutlu PNG."""
    import struct
    data = app_icon_bytes()
    count = struct.unpack_from("<H", data, 4)[0]
    best = None
    for i in range(count):
        w, _, _, _, _, _, length, offset = struct.unpack_from("<BBBBHHII", data, 6 + 16 * i)
        w = w or 256
        if best is None or abs(w - size) < abs(best[0] - size):
            best = (w, data[offset:offset + length])
    return best[1]


def icon_file() -> str:
    """Pencere simgesi için .ico dosyası (bu bilgisayarda bir kez yazılır)."""
    path = settings_path().parent / "uygulama.ico"
    data = app_icon_bytes()
    try:
        if not path.is_file() or path.read_bytes() != data:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    except OSError:
        return ""
    return str(path)


def set_window_icon(win, delay: int = 0):
    """Pencereye uygulama simgesini koyar (CustomTkinter'in kendi simgesinin yerine)."""
    def apply():
        try:
            if sys.platform == "win32":
                path = icon_file()
                if path:
                    win.iconbitmap(path)
            else:
                import tkinter
                import base64
                photo = tkinter.PhotoImage(master=win, data=base64.b64encode(icon_png(64)).decode())
                win._app_icon = photo
                win.iconphoto(False, photo)
        except Exception:
            pass
    if delay:
        win.after(delay, apply)
    else:
        apply()


# ── Kendiliğinden güncelleme: program her açılışta GitHub'daki güncel kodu alır ─────────
# exe yalnızca Python'u ve kütüphaneleri taşır; uygulamanın kodu daha yeniyse önbellekten yüklenir.
# Yeni dosya indirilip çalıştırılmaz, yeni süreç başlatılmaz: kod aynı program içinde içe aktarılır.

UPDATE_URL = "https://raw.githubusercontent.com/erdoganumut-cyber/akademik-indirici/main/akademik_indirici.py"
UPDATE_ENV = "AKADEMIK_GUNCEL_KOD"
LAUNCHER_ENV = "AKADEMIK_EXE_SURUMU"


def version_tuple(v) -> tuple:
    return tuple(int(x) for x in re.findall(r"\d+", str(v or "0"))) or (0,)


def code_constant(text: str, name: str) -> str:
    m = re.search(rf'^{name}\s*=\s*"([^"]+)"', text or "", re.M)
    return m.group(1) if m else ""


def update_dir() -> Path:
    return settings_path().parent / "guncelleme"


def cached_update():
    """(yol, sürüm, gereken_exe_sürümü) ya da (None, '', '')"""
    path = update_dir() / "akademik_indirici.py"
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return None, "", ""
    return path, code_constant(text, "APP_VERSION"), code_constant(text, "MIN_LAUNCHER") or "0"


def launcher_version() -> str:
    return os.environ.get(LAUNCHER_ENV) or APP_VERSION


def updates_enabled() -> bool:
    return (getattr(sys, "frozen", False) or bool(os.environ.get("AKADEMIK_GUNCELLEME_TESTI"))) \
        and load_settings().get("auto_update", True)


def fetch_update(timeout=(3, 20)):
    """GitHub'daki kod bu programdan ve önbellektekinden yeniyse indirir. Dönüş: yeni sürüm ya da None."""
    r = requests.get(UPDATE_URL, timeout=timeout, headers={"Cache-Control": "no-cache",
                                                            "User-Agent": f"AkademikIndirici/{APP_VERSION}"})
    if r.status_code != 200:
        return None
    text = r.content.decode("utf-8")
    version = code_constant(text, "APP_VERSION")
    _, cached, _ = cached_update()
    newest = max(version_tuple(launcher_version()), version_tuple(cached))
    if not version or version_tuple(version) <= newest or "def main(" not in text:
        return None
    compile(text, "akademik_indirici.py", "exec")            # yarım/bozuk indirme çalıştırılmasın
    folder = update_dir()
    folder.mkdir(parents=True, exist_ok=True)
    tmp = folder / "akademik_indirici.py.tmp"
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, folder / "akademik_indirici.py")
    diag(f"güncelleme indirildi: v{version}")
    return version


def run_updated_code() -> bool:
    """Önbellekteki kod bu programdan yeniyse onu çalıştırır. Çalıştırdıysa True."""
    if os.environ.get(UPDATE_ENV):
        return False
    path, version, needs = cached_update()
    if not path or version_tuple(version) <= version_tuple(APP_VERSION):
        return False
    bad = update_dir() / "hatali_surum.txt"
    if bad.is_file() and bad.read_text(encoding="utf-8").strip() == version:
        return False
    if version_tuple(needs) > version_tuple(APP_VERSION):
        os.environ["AKADEMIK_EXE_ESKI"] = version             # arayüz kullanıcıya söyler
        return False
    import importlib.util
    os.environ[UPDATE_ENV] = version
    os.environ[LAUNCHER_ENV] = APP_VERSION
    try:
        spec = importlib.util.spec_from_file_location("akademik_guncel", path)
        module = importlib.util.module_from_spec(spec)
        sys.modules["akademik_guncel"] = module
        spec.loader.exec_module(module)
    except Exception:
        diag_exception(f"güncel kod v{version} yüklenemedi; programın kendi sürümü açılıyor")
        bad.write_text(version, encoding="utf-8")
        os.environ.pop(UPDATE_ENV, None)
        return False
    module.main()
    return True


# ── Tanılama kaydı: uygulama beklenmedik biçimde kapanırsa nedenini görmek için ─────

_DIAG_LOCK = threading.Lock()
_DIAG_LAST = [0.0]
_FAULT_FILE = None


def diag_path() -> Path:
    return settings_path().parent / "tanilama_kaydi.txt"


def diag(text: str, throttle: bool = False):
    """Kısa olay kaydı. throttle=True olanlar en fazla 2 saniyede bir yazılır."""
    now = time.time()
    if throttle and now - _DIAG_LAST[0] < 2:
        return
    _DIAG_LAST[0] = now
    try:
        with _DIAG_LOCK:
            path = diag_path()
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.exists() and path.stat().st_size > 2_000_000:      # 2 MB'ı geçmesin
                path.replace(path.with_suffix(".eski.txt"))
            with open(path, "a", encoding="utf-8") as fh:
                fh.write(f"{datetime.now():%Y-%m-%d %H:%M:%S} [{os.getpid()}] {text}\n")
    except OSError:
        pass


def diag_exception(context: str):
    import traceback
    diag(f"HATA ({context}):\n" + traceback.format_exc())


def install_crash_logging():
    """Yakalanmayan hataları ve Python'un kendisinin çökmesini kayda geçirir."""
    global _FAULT_FILE
    import faulthandler
    import traceback

    def excepthook(exc_type, exc, tb):
        diag("YAKALANMAYAN HATA:\n" + "".join(traceback.format_exception(exc_type, exc, tb)))

    def thread_hook(args):
        diag(f"İŞ PARÇACIĞI HATASI ({getattr(args.thread, 'name', '?')}):\n"
             + "".join(traceback.format_exception(args.exc_type, args.exc_value, args.exc_traceback)))

    sys.excepthook = excepthook
    threading.excepthook = thread_hook
    try:
        path = settings_path().parent / "cokme_kaydi.txt"
        path.parent.mkdir(parents=True, exist_ok=True)
        _FAULT_FILE = open(path, "a", encoding="utf-8")
        faulthandler.enable(file=_FAULT_FILE, all_threads=True)
    except OSError:
        pass
    diag(f"uygulama açıldı: v{APP_VERSION} · {' '.join(sys.argv[1:]) or 'arayüz'} · "
         f"{'exe' if getattr(sys, 'frozen', False) else 'python'} · {sys.platform}")


# ════════════════════════════════════════════════════════════════════════════
#  8) ARAYÜZ (CustomTkinter)
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


def _windows_downloads():
    """Windows'un gerçek İndirilenler klasörü (OneDrive'a ya da başka sürücüye taşınmış olabilir)."""
    if sys.platform != "win32":
        return None
    try:
        import ctypes
        from ctypes import wintypes
        import uuid as _uuid

        class GUID(ctypes.Structure):
            _fields_ = [("Data1", wintypes.DWORD), ("Data2", wintypes.WORD), ("Data3", wintypes.WORD),
                        ("Data4", ctypes.c_ubyte * 8)]
        u = _uuid.UUID("{374DE290-123F-4565-9164-39C4925E467B}")       # FOLDERID_Downloads
        guid = GUID(u.fields[0], u.fields[1], u.fields[2],
                    (ctypes.c_ubyte * 8).from_buffer_copy(u.bytes[8:]))
        out = ctypes.c_wchar_p()
        if ctypes.windll.shell32.SHGetKnownFolderPath(ctypes.byref(guid), 0, None, ctypes.byref(out)) != 0:
            return None
        path = out.value
        ctypes.windll.ole32.CoTaskMemFree(out)
        return Path(path) if path else None
    except Exception:
        return None


def downloads_folders() -> list:
    """İzlenecek indirme klasörleri: ayarda seçilen ya da Windows'un İndirilenler klasörü
    (OneDrive'a taşınmışsa o) ve ev klasöründeki Downloads."""
    custom = _load_settings_raw().get("downloads_folder")
    if custom and os.path.isdir(custom):
        return [Path(custom)]
    out = []
    for p in (_windows_downloads(), Path.home() / "Downloads", Path.home() / "OneDrive" / "Downloads",
              Path.home() / "OneDrive" / "İndirilenler"):
        if p and p.is_dir() and all(os.path.normcase(str(p)) != os.path.normcase(str(q)) for q in out):
            out.append(p)
    return out or [Path.home() / "Downloads"]


def downloads_folder() -> Path:
    return downloads_folders()[0]


SEARCH_SITES = ["Google Akademik", "Google (PDF dosyası)", "BASE (kurum arşivleri)", "CORE (açık erişim)",
                "Semantic Scholar", "DergiPark"]


def search_link(item, site) -> str:
    """Başlıkla elle arama için tarayıcı adresi (aramayı ve indirmeyi kullanıcı yapar)."""
    title = re.sub(r"\s+", " ", item.get("title") or "").strip()
    exact = quote(f'"{title}"')
    return {
        "Google Akademik": "https://scholar.google.com/scholar?q=" + exact,
        "Google (PDF dosyası)": "https://www.google.com/search?q=" + exact + quote(" filetype:pdf"),
        "BASE (kurum arşivleri)": "https://www.base-search.net/Search/Results?lookfor=" + exact,
        "CORE (açık erişim)": "https://core.ac.uk/search?q=" + exact,
        "Semantic Scholar": "https://www.semanticscholar.org/search?q=" + quote(title),
        "DergiPark": "https://dergipark.org.tr/tr/search?q=" + quote(title) + "&section=articles",
    }[site]


def item_open_link(item) -> str:
    """Kaynağın PDF'ine ulaşılacak sayfa: DOI, link, YÖK tezi ya da başlıkla Google Akademik araması."""
    tez = yok_tez_no(item)
    if tez:                                           # tezlerde önce Tez Merkezi'ndeki kaydı
        return yok_open_html(tez).as_uri()
    if item.get("doi"):
        return "https://doi.org/" + item["doi"]
    if item.get("url"):
        return item["url"]
    return "https://scholar.google.com/scholar?q=" + quote(f'"{item.get("title", "")}"')


def default_library_dir() -> Path:
    docs = Path.home() / "Documents"
    return (docs if docs.is_dir() else Path.home()) / "Akademik Kütüphanem"


def show_in_file_manager(path: Path):
    path = Path(path)
    open_in_file_manager(path.parent)


def open_file(path: Path):
    if sys.platform.startswith("win"):
        os.startfile(str(path))  # type: ignore[attr-defined]
    elif sys.platform == "darwin":
        subprocess.Popen(["open", str(path)])
    else:
        subprocess.Popen(["xdg-open", str(path)])


def import_dialog(parent, count, known_tags=(), title=None, show_move=True, unit="PDF"):
    """Kütüphaneye alma seçenekleri. Dönüş: (taşı_mı, etiketler, otomatik_etiket) ya da None."""
    win = ctk.CTkToplevel(parent)
    win.title("Kütüphaneye ekle")
    set_window_icon(win, delay=260)
    win.resizable(False, False)
    win.transient(parent)
    result = [None]
    pad = {"padx": 20, "sticky": "ew"}
    win.grid_columnconfigure(0, weight=1)
    ctk.CTkLabel(win, text=title or f"{count} {unit} kütüphaneye eklenecek",
                 font=ctk.CTkFont(size=15, weight="bold"), anchor="w").grid(row=0, column=0, pady=(18, 8), **pad)
    move_var = ctk.StringVar(value="tasi")
    if show_move:
        ctk.CTkRadioButton(win, text="Kütüphane klasörüne taşı (tek klasör, önerilen)", variable=move_var,
                           value="tasi").grid(row=1, column=0, pady=2, **pad)
        ctk.CTkRadioButton(win, text="Kopyala, asılları yerinde kalsın", variable=move_var,
                           value="kopyala").grid(row=2, column=0, pady=2, **pad)
    ctk.CTkLabel(win, text="Etiketler", font=ctk.CTkFont(size=13, weight="bold"), anchor="w").grid(
        row=3, column=0, pady=(14, 2), **pad)
    entry = ctk.CTkEntry(win, height=30, width=460, placeholder_text="Elle etiket (isteğe bağlı, virgülle): "
                                                                    "ör. tez bölüm 2")
    entry.grid(row=4, column=0, pady=2, **pad)
    if known_tags:
        ctk.CTkLabel(win, text="Var olanlar: " + shorten(", ".join(known_tags), 150), text_color=MUTED,
                     font=ctk.CTkFont(size=11), wraplength=460, justify="left", anchor="w").grid(
            row=5, column=0, **pad)
    auto_var = ctk.BooleanVar(value=load_settings().get("auto_tag", True))
    ctk.CTkCheckBox(win, text="Otomatik etiketle: konu grubu etiketlerini (anahtar kelime gruplarınıza göre) "
                              "kendisi eklesin", variable=auto_var).grid(row=6, column=0, pady=(10, 2), **pad)
    ctk.CTkLabel(win, text="İkisi birlikte de kullanılabilir: elle yazdığınız etiketler her kaynağa, otomatik "
                           "etiketler yalnızca konusu uyan kaynaklara eklenir.", text_color=MUTED,
                 font=ctk.CTkFont(size=11), wraplength=460, justify="left", anchor="w").grid(row=7, column=0, **pad)
    row = ctk.CTkFrame(win, fg_color="transparent")
    row.grid(row=8, column=0, pady=18, **pad)

    def ok(_=None):
        result[0] = (move_var.get() == "tasi", clean_tags(entry.get()), bool(auto_var.get()))
        win.destroy()
    ctk.CTkButton(row, text="Ekle", command=ok).pack(side="left")
    ctk.CTkButton(row, text="Vazgeç", fg_color="transparent", border_width=1, text_color=TEXT,
                  command=win.destroy).pack(side="left", padx=8)
    entry.bind("<Return>", ok)

    def place():
        win.update_idletasks()
        x = parent.winfo_rootx() + max(0, (parent.winfo_width() - win.winfo_width()) // 2)
        y = parent.winfo_rooty() + max(0, (parent.winfo_height() - win.winfo_height()) // 3)
        win.geometry(f"+{x}+{y}")
        win.lift()
        entry.focus_force()
        win.grab_set()
    win.after(50, place)
    parent.wait_window(win)
    return result[0]


def choice_dialog(parent, title, text, options):
    """Birden çok düğmeli soru penceresi. Dönüş: seçilen düğmenin sırası ya da None (kapatıldı)."""
    win = ctk.CTkToplevel(parent)
    win.title(title)
    set_window_icon(win, delay=260)
    win.resizable(False, False)
    win.transient(parent)
    result = [None]
    ctk.CTkLabel(win, text=title, font=ctk.CTkFont(size=15, weight="bold"), anchor="w").pack(
        fill="x", padx=20, pady=(18, 6))
    ctk.CTkLabel(win, text=text, justify="left", anchor="w", wraplength=520).pack(fill="x", padx=20)
    row = ctk.CTkFrame(win, fg_color="transparent")
    row.pack(fill="x", padx=20, pady=18)

    def pick(i):
        result[0] = i
        win.destroy()
    for i, label in enumerate(options):
        style = {} if i == 0 else {"fg_color": "transparent", "border_width": 1, "text_color": TEXT}
        ctk.CTkButton(row, text=label, command=lambda i=i: pick(i), **style).pack(side="left", padx=(0, 8))
    win.protocol("WM_DELETE_WINDOW", win.destroy)

    def place():
        win.update_idletasks()
        x = parent.winfo_rootx() + max(0, (parent.winfo_width() - win.winfo_width()) // 2)
        y = parent.winfo_rooty() + max(0, (parent.winfo_height() - win.winfo_height()) // 3)
        win.geometry(f"+{x}+{y}")
        win.lift()
        win.focus_force()
        win.grab_set()
    win.after(50, place)
    parent.wait_window(win)
    return result[0]


def add_italic_tag(textbox):
    """CTkTextbox'a, kutunun kendi yazısıyla aynı boyutta 'i' (italik) etiketi ekler."""
    from tkinter import font as tkfont
    inner = textbox._textbox
    try:
        actual = tkfont.Font(root=inner, font=inner.cget("font")).actual()
        inner.tag_configure("i", font=(actual["family"], actual["size"], "italic"))
    except Exception:
        inner.tag_configure("i", font=("TkDefaultFont", 10, "italic"))


def remember_setting(key, value):
    update_settings(**{key: value})


class FreezeWatchdog(threading.Thread):
    """Arayüz ('Yanıt vermiyor') donarsa ana iş parçacığının o an ne yaptığını tanılama kaydına yazar."""

    LIMIT = 5.0

    def __init__(self):
        super().__init__(name="donma-bekçisi", daemon=True)
        self.beat = time.monotonic()
        self.main_id = threading.main_thread().ident

    def run(self):
        import traceback
        reported, worst = False, 0.0
        while True:
            time.sleep(1.0)
            lag = time.monotonic() - self.beat
            if lag > self.LIMIT and not reported:
                frame = sys._current_frames().get(self.main_id)
                stack = "".join(traceback.format_stack(frame)[-14:]) if frame else "(yok)"
                others = ", ".join(t.name for t in threading.enumerate() if t.is_alive() and t is not self
                                   and t.ident != self.main_id)
                diag(f"ARAYÜZ DONDU ({lag:.0f} sn). Çalışan iş parçacıkları: {others or '-'}\n"
                     f"Ana iş parçacığı şurada:\n{stack}")
                reported, worst = True, lag
            elif reported:
                worst = max(worst, lag)
                if lag < 2:
                    diag(f"arayüz yeniden yanıt veriyor (donma ~{worst:.0f} sn sürdü)")
                    reported = False


class CitationWindow(ctk.CTkToplevel):
    """Atıf ağı: kütüphanede en çok atıf alan kaynaklar ve kütüphanede olmayan sık atıflı eserler."""

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("Atıf ağı ve eksik temel kaynaklar")
        set_window_icon(self, delay=260)
        self.geometry("980x620")
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)
        top = ctk.CTkFrame(self, fg_color="transparent")
        top.grid(row=0, column=0, sticky="ew", padx=14, pady=(12, 6))
        self.info = ctk.CTkLabel(top, text="", anchor="w", justify="left", wraplength=700)
        self.info.pack(side="left")
        self.rebuild_btn = ctk.CTkButton(top, text="Yeniden Hesapla", width=130, command=self.rebuild)
        self.rebuild_btn.pack(side="right")
        tabs = ctk.CTkTabview(self)
        tabs.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.t_in = self._tree(tabs.add("Kütüphanede en çok atıf alanlar"),
                               (("n", "Atıf", 60), ("no", "No", 60), ("who", "Yazar", 160), ("year", "Yıl", 60),
                                ("title", "Başlık", 560)))
        miss = tabs.add("Kütüphanede olmayan sık atıflı eserler")
        self.t_out = self._tree(miss, (("n", "Atıf", 60), ("who", "Yazar", 160), ("year", "Yıl", 60),
                                       ("title", "Başlık / kaynak", 520), ("doi", "DOI", 140)))
        bar = ctk.CTkFrame(miss, fg_color="transparent")
        bar.grid(row=1, column=0, sticky="ew", pady=(6, 0))
        self.add_btn = ctk.CTkButton(bar, text="Seçilenleri İndir Sekmesine Ekle", width=230, command=self.add_selected)
        self.add_btn.pack(side="left")
        self.all_btn = ctk.CTkButton(bar, text="Tümünü İndir", width=130, fg_color="#1F8F4E", hover_color="#18723E",
                                     command=self.download_all)
        self.all_btn.pack(side="left", padx=(8, 0))
        ctk.CTkLabel(bar, text="DOI'si olmayanlar için Crossref'te aranır; bulunanlar İndir sekmesine yazılır.",
                     text_color=MUTED, font=ctk.CTkFont(size=12)).pack(side="left", padx=10)
        self.t_in.bind("<Double-1>", lambda _: self.show_in_library())
        self.data = load_citations()
        self.fill()
        if not self.data:
            self.rebuild()

    def _tree(self, parent, cols):
        from tkinter import ttk
        parent.grid_columnconfigure(0, weight=1)
        parent.grid_rowconfigure(0, weight=1)
        tree = ttk.Treeview(parent, columns=[c[0] for c in cols], show="headings", selectmode="extended",
                            style="Lib.Treeview")
        for key, text, width in cols:
            tree.heading(key, text=text)
            tree.column(key, width=width, stretch=key == "title", anchor="center" if key in ("n", "no", "year") else "w")
        tree.grid(row=0, column=0, sticky="nsew")
        return tree

    def fill(self):
        lib = self.app.library
        for tree in (self.t_in, self.t_out):
            tree.delete(*tree.get_children())
        if not self.data:
            self.info.configure(text="Atıf ağı hesaplanıyor…")
            return
        counts = citation_counts(self.data)
        for item_id, n in sorted(counts.items(), key=lambda kv: -kv[1])[:500]:
            item = lib.get(item_id)
            if item:
                self.t_in.insert("", "end", iid=str(item_id), values=(n, item.get("no") or "", first_author_label(item),
                                                                      item.get("year"), item["title"]))
        for k, m in enumerate(self.data.get("missing") or []):
            self.t_out.insert("", "end", iid=f"m{k}", values=(len(m["citing"]), m["author"], m["year"],
                                                              m["title"] or m["raw"][:160], m.get("doi") or ""))
        self.info.configure(text=f"{self.data.get('parsed_items', 0)} kaynağın kaynakçası okundu · kütüphane içi "
                                 f"{len(self.data.get('edges') or [])} atıf · kütüphanede olmayan ve en az 2 "
                                 f"kaynağınızın atıf yaptığı {len(self.data.get('missing') or [])} eser · "
                                 f"{self.data.get('built', '')}")

    def rebuild(self):
        self.rebuild_btn.configure(state="disabled", text="Hesaplanıyor…")
        lib, events = self.app.library, self.app.events

        def work():
            try:
                idx = ShardedIndex(readonly=True)
                data = build_citation_graph(lib, idx)
                idx.close()
            except Exception:
                diag_exception("atıf ağı")
                data = {}
            events.put(("cite_done", data))
        threading.Thread(target=work, daemon=True).start()

    def on_built(self, data):
        if not self.winfo_exists():
            return
        self.rebuild_btn.configure(state="normal", text="Yeniden Hesapla")
        self.data = data or {}
        self.fill()
        if not data:
            self.info.configure(text="Metin dizini henüz hazır değil; dizin kurulunca yeniden deneyin.")

    def show_in_library(self):
        sel = self.t_in.selection()
        if sel:
            tab = self.app.library_tab
            self.app.tabs.set("Kütüphanem")
            tab.search.delete(0, "end")
            tab.refresh()
            tab.select(int(sel[0]))

    def download_all(self):
        chosen = list((self.data or {}).get("missing") or [])
        if not chosen:
            messagebox.showinfo(APP_NAME, "Listede kütüphanede olmayan eser yok.", parent=self)
            return
        need = sum(1 for m in chosen if not m.get("doi"))
        if not messagebox.askyesno(APP_NAME, f"Listedeki {len(chosen)} eserin hepsi indirilsin mi?\n\n"
                                   + (f"DOI'si olmayan {need} eser için önce Crossref'te arama yapılır "
                                      f"(birkaç dakika sürebilir). " if need else "")
                                   + "Bulunanlar İndir sekmesine yazılıp indirme kendiliğinden başlar; "
                                     "açık erişimli olanların PDF'i iner, kütüphanede olanlar atlanır.",
                                   parent=self):
            return
        self._resolve(chosen, start=True)

    def add_selected(self):
        chosen = [self.data["missing"][int(i[1:])] for i in self.t_out.selection()]
        if not chosen:
            messagebox.showinfo(APP_NAME, "Önce listeden eser seçin (Ctrl ya da Shift ile birden çok).", parent=self)
            return
        self._resolve(chosen, start=False)

    def _resolve(self, chosen, start):
        self.add_btn.configure(state="disabled", text="DOI'ler aranıyor…")
        self.all_btn.configure(state="disabled")
        events = self.app.events

        def work():
            links, unresolved = [], []
            session = make_session()
            try:
                for n, m in enumerate(chosen, start=1):
                    if n % 5 == 0 or n == len(chosen):
                        events.put(("cite_prog", n, len(chosen)))
                    doi = m.get("doi")
                    if not doi:
                        msg = crossref_search(session, {"title": m["title"], "year": m["year"],
                                                        "authors": [{"family": m["author"].split(",")[0]}]})
                        doi = record_from_crossref(msg)["doi"] if msg else ""
                    (links.append("https://doi.org/" + doi) if doi else unresolved.append(m["raw"]))
            finally:
                session.close()
            events.put(("cite_links", list(dict.fromkeys(links)), unresolved, start))
        threading.Thread(target=work, daemon=True).start()

    def on_progress(self, n, total):
        if self.winfo_exists():
            self.add_btn.configure(text=f"DOI'ler aranıyor… {n}/{total}")

    def on_links(self, links, unresolved, start=False):
        if not self.winfo_exists():
            return
        self.add_btn.configure(state="normal", text="Seçilenleri İndir Sekmesine Ekle")
        self.all_btn.configure(state="normal")
        if links:
            box = self.app.input_box
            box.insert("end", ("\n" if box.get("1.0", "end-1c").strip() else "") +
                       "──── Eksik temel kaynaklar ────\n" + "\n".join(links) + "\n")
        busy = bool(self.app.worker and self.app.worker.is_alive())
        if start and links and not busy:
            self.app.tabs.set("İndir")
            self.app._start()
            msg = f"{len(links)} eserin indirmesi başladı; ilerlemeyi İndir sekmesinden izleyebilirsiniz."
        elif start and links:
            msg = (f"{len(links)} eser İndir sekmesine eklendi. Şu an başka bir indirme sürdüğü için o bitince "
                   "'İndirmeyi Başlat'a basın.")
        else:
            msg = f"{len(links)} eser İndir sekmesine eklendi; oradan 'İndirmeyi Başlat' ile indirebilirsiniz."
        if unresolved:
            self.clipboard_clear()
            self.clipboard_append("\n".join(unresolved))
            msg += (f"\n\n{len(unresolved)} eserin DOI'si bulunamadı (çoğu kitap ya da eski yayın); kaynak "
                    "satırları panoya kopyalandı — Piri'de ya da Google Akademik'te aratabilirsiniz.")
        messagebox.showinfo(APP_NAME, msg, parent=self)


class DuplicatesWindow(ctk.CTkToplevel):
    """Mükerrer kayıtlar: gruplar listelenir, seçilen gruplar tek kayıtta birleştirilir."""

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("Mükerrer kayıtlar")
        set_window_icon(self, delay=260)
        self.geometry("900x600")
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)
        items = app.library.all_items()
        self.groups = find_duplicates(items, find_pdf_twins(app.library, items))
        head = ("Mükerrer kayıt bulunamadı." if not self.groups else
                f"{len(self.groups)} grup bulundu (başka dilde başlıklı ikizler PDF'in ilk sayfasından tanınır). Her "
                "grupta ★ işaretli kayıt tutulur; öbürlerinin PDF'i (kendisinde yoksa), etiketleri, alıntı "
                "kartları, boş künye alanları ve Claude özeti ona aktarılıp silinir. Fazla PDF kopyaları silinmez, "
                "kütüphane klasöründeki 'Mükerrer PDF'ler (silinebilir)' klasörüne taşınır.")
        ctk.CTkLabel(self, text=head, anchor="w", justify="left", wraplength=860).grid(
            row=0, column=0, sticky="ew", padx=14, pady=(12, 6))
        body = ctk.CTkScrollableFrame(self)
        body.grid(row=1, column=0, sticky="nsew", padx=10)
        body.grid_columnconfigure(0, weight=1)
        self.vars = []
        for g, group in enumerate(self.groups):
            var = ctk.BooleanVar(value=True)
            self.vars.append(var)
            box = ctk.CTkFrame(body)
            box.grid(row=g, column=0, sticky="ew", pady=4)
            ctk.CTkCheckBox(box, text=f"Grup {g + 1}: birleştir", variable=var).pack(anchor="w", padx=8, pady=(6, 2))
            for k, item in enumerate(group):
                has_file = bool(item.get("file_path")) and os.path.isfile(item["file_path"])
                line = (f"{'★' if k == 0 else '  '} No {item.get('no')} · {first_author_label(item)} "
                        f"({item.get('year') or 't.y.'}) {shorten(item['title'], 90)}"
                        f"{' · PDF' if has_file else ''}{' · DOI' if item.get('doi') else ''}")
                ctk.CTkLabel(box, text=line, anchor="w", font=ctk.CTkFont(size=12)).pack(anchor="w", padx=24)
        btns = ctk.CTkFrame(self, fg_color="transparent")
        btns.grid(row=2, column=0, sticky="e", padx=14, pady=10)
        ctk.CTkButton(btns, text="Kapat", width=90, fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.destroy).pack(side="left", padx=8)
        if self.groups:
            ctk.CTkButton(btns, text="Seçili Grupları Birleştir", width=190, command=self.merge).pack(side="left")

    def merge(self):
        chosen = [g for g, v in zip(self.groups, self.vars) if v.get()]
        if not chosen or not messagebox.askyesno(
                APP_NAME, f"{len(chosen)} grup birleştirilecek ({sum(len(g) - 1 for g in chosen)} kayıt silinecek). "
                          "Devam edilsin mi?", parent=self):
            return
        lib, moved = self.app.library, 0
        for group in chosen:
            moved += lib.merge_items(group[0]["id"], [i["id"] for i in group[1:]], self.app.library_folder())
        self.app.library_tab.refresh(keep_selection=False)
        self.app.toast(f"{len(chosen)} grup birleştirildi" + (f"; {moved} fazla PDF ayrı klasöre taşındı." if moved else "."))
        self.destroy()


class ReextractWindow(ctk.CTkToplevel):
    """PDF'ten yeniden çıkarılan künyelerin önizlemesi: eski → yeni; seçilenler uygulanır, dosya yeniden adlanır."""

    FIELDS = ("title", "authors", "editors", "year", "type", "container", "volume", "issue", "pages", "publisher",
              "doi", "issn")

    def __init__(self, app, results):
        super().__init__(app)
        self.app, self.results = app, results
        self.title("Künyeleri PDF'ten yeniden çıkar")
        set_window_icon(self, delay=260)
        self.geometry("980x620")
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)
        ctk.CTkLabel(self, text=f"{len(results)} kaydın PDF'inden farklı bir künye çıktı. Uygulanacakları işaretleyin; "
                                "PDF dosyası da yeni künyeye göre yeniden adlandırılır. Etiketler, kartlar ve notlar "
                                "değişmez.", anchor="w", justify="left", wraplength=940).grid(
            row=0, column=0, sticky="ew", padx=14, pady=(12, 6))
        body = ctk.CTkScrollableFrame(self)
        body.grid(row=1, column=0, sticky="nsew", padx=10)
        body.grid_columnconfigure(0, weight=1)
        self.vars = []
        for k, (item, new) in enumerate(results):
            var = ctk.BooleanVar(value=True)
            self.vars.append(var)
            box = ctk.CTkFrame(body)
            box.grid(row=k, column=0, sticky="ew", pady=4)
            ctk.CTkCheckBox(box, text=f"No {item.get('no')}", variable=var).pack(anchor="w", padx=8, pady=(6, 2))
            ctk.CTkLabel(box, text="Eski:  " + apa_text(item), anchor="w", justify="left", wraplength=880,
                         text_color=MUTED, font=ctk.CTkFont(size=12)).pack(anchor="w", padx=24)
            ctk.CTkLabel(box, text="Yeni:  " + apa_text(new) + f"   [{ITEM_TYPES.get(new.get('type'), '')}]",
                         anchor="w", justify="left", wraplength=880, font=ctk.CTkFont(size=12)).pack(
                anchor="w", padx=24, pady=(0, 6))
        btns = ctk.CTkFrame(self, fg_color="transparent")
        btns.grid(row=2, column=0, sticky="e", padx=14, pady=10)
        ctk.CTkButton(btns, text="Kapat", width=90, fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.destroy).pack(side="left", padx=8)
        if results:
            ctk.CTkButton(btns, text="Seçilenleri Uygula", width=170, command=self.apply).pack(side="left")
        self.after(80, self.lift)

    def apply(self):
        lib, folder = self.app.library, self.app.library_folder()
        done, renamed = 0, 0
        for (item, new), var in zip(self.results, self.vars):
            if not var.get() or not lib.get(item["id"]):
                continue
            fields = {k: new.get(k) for k in self.FIELDS if new.get(k)}
            if new.get("type") == "book" and new.get("editors") and not new.get("authors"):
                fields["authors"] = []                    # bildiri kitabı: ilk bildirinin yazarı kitabın yazarı değil
            if new.get("type") != "conference" and item.get("type") == "conference" and not new.get("container"):
                fields["container"] = ""
            for k in ("keywords", "language"):
                if new.get(k) and not item.get(k):
                    fields[k] = new[k]
            if fields.get("doi") and lib.find_by_doi(fields["doi"]) not in (None, item["id"]):
                fields.pop("doi")
            lib.update(item["id"], fields)
            done += 1
            current = lib.get(item["id"])
            if current and current["file_path"] and Path(current["file_path"]).is_file():
                try:
                    new_path = place_in_library(Path(current["file_path"]), current,
                                                folder or Path(current["file_path"]).parent)
                    if str(new_path) != current["file_path"]:
                        lib.update(item["id"], {"file_path": str(new_path)})
                        renamed += 1
                except OSError as exc:
                    diag(f"yeniden adlandırma: {describe_error(exc)}")
        self.app.library_tab.refresh()
        self.app.toast(f"{done} kaydın künyesi güncellendi" + (f", {renamed} dosya yeniden adlandırıldı." if renamed else "."))
        self.destroy()


class ReadingNotes(ctk.CTkToplevel):
    """Kitabı (tarayıcıda, okuma uygulamasında ya da PDF'te) okurken her zaman üstte duran küçük not penceresi:
    sayfa + alıntı + yorum → kaynağın alıntı kartı. Okumayı ve kopyalamayı kullanıcı yapar."""

    def __init__(self, app, item):
        super().__init__(app)
        self.app, self.item_id = app, item["id"]
        self.title(f"Okurken not · {shorten(item['title'], 50)}")
        set_window_icon(self, delay=260)
        self.attributes("-topmost", True)
        self.geometry(f"420x430+{max(0, self.winfo_screenwidth() - 450)}+80")      # sağ kenarda, okumayı kapatmasın
        self.grid_columnconfigure(0, weight=1)
        pad = {"padx": 14, "sticky": "ew"}
        head = ctk.CTkFrame(self, fg_color="transparent")
        head.grid(row=0, column=0, pady=(12, 4), **pad)
        ctk.CTkLabel(head, text="Sayfa:").pack(side="left")
        self.page = ctk.CTkEntry(head, width=70)
        self.page.pack(side="left", padx=6)
        ctk.CTkButton(head, text="Panodan Yapıştır", width=130, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=self.paste).pack(side="right")
        ctk.CTkLabel(self, text="Alıntı (okuyucudan kopyaladığınız metin):", anchor="w").grid(row=1, column=0, **pad)
        self.quote = ctk.CTkTextbox(self, height=150, wrap="word")
        self.quote.grid(row=2, column=0, pady=(2, 6), **pad)
        ctk.CTkLabel(self, text="Yorumunuz / not:", anchor="w").grid(row=3, column=0, **pad)
        self.comment = ctk.CTkTextbox(self, height=80, wrap="word")
        self.comment.grid(row=4, column=0, pady=(2, 6), **pad)
        btns = ctk.CTkFrame(self, fg_color="transparent")
        btns.grid(row=5, column=0, pady=(4, 4), **pad)
        ctk.CTkButton(btns, text="Kartı Kaydet  (Ctrl+Enter)", command=self.save).pack(side="left")
        ctk.CTkButton(btns, text="Kitabı Aç", width=90, fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.open_book).pack(side="left", padx=8)
        self.status = ctk.CTkLabel(self, text="", text_color=MUTED, anchor="w", font=ctk.CTkFont(size=12))
        self.status.grid(row=6, column=0, pady=(0, 10), **pad)
        self.bind("<Control-Return>", lambda _: self.save())
        self._count()

    def _count(self):
        n = len(self.app.library.cards(self.item_id))
        self.status.configure(text=f"Bu kaynakta {n} alıntı kartı var.")

    def paste(self):
        try:
            text = self.clipboard_get()
        except Exception:
            text = ""
        if text:
            self.quote.delete("1.0", "end")
            self.quote.insert("1.0", re.sub(r"[ \t]*\n[ \t]*", " ", text).strip())

    def open_book(self):
        item = self.app.library.get(self.item_id)
        if item and item["file_path"] and os.path.exists(item["file_path"]):
            open_file(Path(item["file_path"]))
        elif item:
            webbrowser.open_new_tab(item_open_link(item))

    def save(self):
        quote_text = self.quote.get("1.0", "end").strip()
        comment = self.comment.get("1.0", "end").strip()
        if not quote_text and not comment:
            self.status.configure(text="Önce alıntı ya da not yazın.", text_color=LOG_COLORS["warn"])
            return
        self.app.library.add_card(self.item_id, self.page.get().strip(), quote_text, comment)
        self.quote.delete("1.0", "end")
        self.comment.delete("1.0", "end")
        self.status.configure(text_color=MUTED)
        self._count()
        self.status.configure(text=self.status.cget("text") + "  ✓ kaydedildi")
        tab = self.app.library_tab
        if tab.current and tab.current["id"] == self.item_id:
            tab._render_cards()


class RangeDialog(ctk.CTkToplevel):
    """PDF'siz kaynaklardan hangi kayıt numaralarının işleneceğini seçtirir.
    on_start(kaynaklar, etiket, (alt, üst) ya da None) ile döner."""

    CHUNK = {"retry": 100, "queue": 25}
    SECONDS = {"retry": 8, "queue": 45}           # kaynak başına kabaca süre (tahmin için)

    def __init__(self, app, purpose, nopdf, visible_ids, chosen, on_start):
        super().__init__(app)
        self.app, self.purpose, self.nopdf, self.visible_ids = app, purpose, nopdf, visible_ids
        self.chosen, self.on_start = chosen, on_start
        self.twins = set(app.pdf_twins()) & {i["id"] for i in nopdf}
        retry = purpose == "retry"
        self.title("PDF'leri yeniden ara" if retry else "PDF'sizleri sırayla aç")
        set_window_icon(self, delay=260)
        self.transient(app)
        self.resizable(False, False)
        self.grid_columnconfigure(0, weight=1)
        pad = {"padx": 18, "sticky": "ew"}
        nos = [i.get("no") or 0 for i in nopdf]
        intro = (f"Kütüphanede PDF'i olmayan {len(nopdf)} kaynak var (No {no_ranges_text(nos, 6)}). "
                 "Hangi kayıt numaraları arasında çalışılsın?")
        if retry:
            intro += ("\n\nYayıncı sayfası, açık erişim kopyaları, YÖK Tez Merkezi ve başka yerler (OpenAlex, "
                      "Semantic Scholar, CORE kurum arşivleri) aranır; bulunan PDF kendiliğinden "
                      "kaynağına bağlanır. Bulunamayanları sonda Google Akademik'te sırayla açmayı önerir. "
                      "İstediğiniz an durdurabilirsiniz.")
            if not app.email_entry.get().strip():
                intro += ("\n\nİpucu: İndir sekmesine e-posta yazarsanız açık erişim kopyaları da (Unpaywall) "
                          "aranır; bulunan PDF sayısı belirgin artar.")
        else:
            intro += ("\n\nKaynaklar numara sırasıyla tarayıcıda açılır; her sayfada PDF'i siz indirirsiniz, program "
                      "İndirilenler'den alıp kaynağa bağlar.")
        ctk.CTkLabel(self, text=intro, justify="left", anchor="w", wraplength=440).grid(row=0, column=0, pady=(16, 10), **pad)

        self.mode = ctk.StringVar(value="selected" if chosen else "range")
        box = ctk.CTkFrame(self, fg_color="transparent")
        box.grid(row=1, column=0, **pad)
        ctk.CTkRadioButton(box, text="Kayıt no:", variable=self.mode, value="range",
                           command=self._update).grid(row=0, column=0, sticky="w")
        self.start_entry = ctk.CTkEntry(box, width=70, justify="center")
        self.start_entry.grid(row=0, column=1, padx=(6, 4))
        ctk.CTkLabel(box, text="–").grid(row=0, column=2)
        self.end_entry = ctk.CTkEntry(box, width=70, justify="center")
        self.end_entry.grid(row=0, column=3, padx=(4, 8))
        ctk.CTkButton(box, text="Tümü", width=54, height=26, fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self._all).grid(row=0, column=4)
        for entry in (self.start_entry, self.end_entry):
            entry.bind("<KeyRelease>", lambda _: self._range_typed())
        if chosen:
            ctk.CTkRadioButton(box, text=f"Tabloda seçtiğim {len(chosen)} PDF'siz kaynak "
                                         f"(No {no_ranges_text([i.get('no') for i in chosen], 5)})",
                               variable=self.mode, value="selected", command=self._update).grid(
                row=1, column=0, columnspan=5, sticky="w", pady=(8, 0))
        self.visible_var = ctk.BooleanVar(value=True)
        self.filtered = filtered = len([i for i in nopdf if i["id"] in visible_ids]) < len(nopdf)
        self.visible_check = ctk.CTkCheckBox(self, text="Yalnızca tabloda görünenler (arama / etiket filtresine uyanlar)",
                                             variable=self.visible_var, command=self._update)
        if filtered:
            self.visible_check.grid(row=2, column=0, pady=(10, 0), **pad)
        self.skip_var = ctk.BooleanVar(value=True)
        ctk.CTkCheckBox(self, text="Bugün zaten denenmiş olanları atla", variable=self.skip_var,
                        command=self._update).grid(row=3, column=0, pady=(8, 0), **pad)
        self.summary = ctk.CTkLabel(self, text="", justify="left", anchor="w", wraplength=440, text_color=MUTED,
                                    font=ctk.CTkFont(size=12))
        self.summary.grid(row=4, column=0, pady=(12, 0), **pad)
        extra = ctk.CTkFrame(self, fg_color="transparent")
        extra.grid(row=5, column=0, pady=(12, 0), **pad)
        self.core_entry = None
        self.open_mode = ctk.StringVar(value="page")
        if retry:
            ctk.CTkLabel(extra, text="CORE anahtarı (gerekmez, aramayı hızlandırır):",
                         font=ctk.CTkFont(size=12), text_color=MUTED).pack(side="left")
            self.core_entry = ctk.CTkEntry(extra, width=120, height=26, show="•", placeholder_text="boş bırakılabilir")
            self.core_entry.pack(side="left", padx=6)
            if load_settings().get("core_api_key"):
                self.core_entry.insert(0, load_settings()["core_api_key"])
            ctk.CTkButton(extra, text="Ücretsiz al…", width=90, height=26, fg_color="transparent", border_width=1,
                          text_color=TEXT, command=lambda: webbrowser.open_new_tab(CORE_KEY_PAGE)).pack(side="left")
        else:
            ctk.CTkLabel(extra, text="Açılacak sayfa:", font=ctk.CTkFont(size=12)).pack(anchor="w")
            ctk.CTkRadioButton(extra, text="Makale sayfası (yayıncı / kurum erişimi)", variable=self.open_mode,
                               value="page").pack(anchor="w", padx=(8, 0), pady=(4, 0))
            ctk.CTkRadioButton(extra, text="Google Akademik'te başlıkla arama (başka yerlerdeki kopyalar)",
                               variable=self.open_mode, value="scholar").pack(anchor="w", padx=(8, 0), pady=(4, 0))
        if self.twins:
            tw = ctk.CTkFrame(self, fg_color="transparent")
            tw.grid(row=6, column=0, pady=(12, 0), **pad)
            ctk.CTkLabel(tw, text=f"{len(self.twins)} kaydın PDF'i başka dilde başlıklı ikizinde duruyor; bunlar "
                                  "aranmaz. Birleştirince listeden çıkarlar.", text_color=LOG_COLORS["warn"],
                         font=ctk.CTkFont(size=12), wraplength=300, justify="left", anchor="w").pack(side="left")
            ctk.CTkButton(tw, text="Mükerrerleri Birleştir…", width=150, height=26, fg_color="transparent",
                          border_width=1, text_color=TEXT, command=self._open_duplicates).pack(side="right")
        btns = ctk.CTkFrame(self, fg_color="transparent")
        btns.grid(row=7, column=0, pady=16, padx=18, sticky="e")
        ctk.CTkButton(btns, text="Vazgeç", width=90, fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.destroy).pack(side="left", padx=(0, 8))
        self.ok_btn = ctk.CTkButton(btns, text="Başlat", width=110, command=self._ok)
        self.ok_btn.pack(side="left")
        self._prefill()
        self._update()
        self.after(60, self._center)

    def _center(self):
        try:
            self.update_idletasks()
            x = self.app.winfo_rootx() + (self.app.winfo_width() - self.winfo_width()) // 2
            y = self.app.winfo_rooty() + (self.app.winfo_height() - self.winfo_height()) // 3
            self.geometry(f"+{max(0, x)}+{max(0, y)}")
            self.lift()
            self.focus_force()
        except Exception:
            pass

    def _open_duplicates(self):
        self.destroy()
        DuplicatesWindow(self.app)

    def _base(self):
        """Filtrelerden geçen PDF'siz kaynaklar (numara aralığı hariç; PDF'i ikizinde olanlar hariç)."""
        today = datetime.now().strftime("%Y-%m-%d")
        out = [i for i in self.nopdf if i["id"] not in self.twins]
        if self.filtered and self.visible_var.get():
            out = [i for i in out if i["id"] in self.visible_ids]
        if self.skip_var.get():
            out = [i for i in out if (i.get("pdf_tried") or "") != today]
        return out

    def _prefill(self):
        # filtreler her şeyi eliyorsa (ör. hepsi bugün denendi) kutuları baştan kaldır, boş pencere açılmasın
        if not self._base() and self.skip_var.get():
            self.skip_var.set(False)
        if not self._base() and self.filtered and self.visible_var.get():
            self.visible_var.set(False)
        base = self._base() or self.nopdf
        key = "retry_next_no" if self.purpose == "retry" else "queue_next_no"
        start_no = int(_load_settings_raw().get(key) or 0)
        rest = [i for i in base if (i.get("no") or 0) >= start_no] or base
        chunk = rest[:self.CHUNK[self.purpose]]
        self._set_range(chunk[0].get("no") or 0, chunk[-1].get("no") or 0)

    def _set_range(self, lo, hi):
        for entry, value in ((self.start_entry, lo), (self.end_entry, hi)):
            entry.delete(0, "end")
            entry.insert(0, str(value))

    def _all(self):
        base = self._base() or self.nopdf
        self._set_range(base[0].get("no") or 0, base[-1].get("no") or 0)
        self.mode.set("range")
        self._update()

    def _range_typed(self):
        self.mode.set("range")
        self._update()

    def range(self):
        try:
            lo = int(self.start_entry.get().strip())
            hi = int(self.end_entry.get().strip())
        except ValueError:
            return None
        return (min(lo, hi), max(lo, hi))

    def selection(self):
        """(kaynaklar, etiket, aralık)"""
        if self.mode.get() == "selected" and self.chosen:
            today = datetime.now().strftime("%Y-%m-%d")
            items = [i for i in self.chosen if i["id"] not in self.twins
                     and not (self.skip_var.get() and (i.get("pdf_tried") or "") == today)]
            return items, f"seçilen {len(items)} kaynak (No {no_ranges_text([i.get('no') for i in items], 4)})", None
        rng = self.range()
        if not rng:
            return [], "", None
        items = [i for i in self._base() if rng[0] <= (i.get("no") or 0) <= rng[1]]
        return items, (f"No {rng[0]}" if rng[0] == rng[1] else f"No {rng[0]}–{rng[1]}"), rng

    def _update(self):
        items, label, rng = self.selection()
        if self.mode.get() == "range" and not rng:
            self.summary.configure(text="Başlangıç ve bitiş numarasını yazın (ör. 120 – 220).")
            self.ok_btn.configure(state="disabled")
            return
        if not items:
            self.summary.configure(text=self._why_empty(rng), text_color=LOG_COLORS["warn"])
            self.ok_btn.configure(state="disabled")
            return
        self.summary.configure(text_color=MUTED)
        minutes = max(1, round(len(items) * self.SECONDS[self.purpose] / 60))
        verb = "aranacak" if self.purpose == "retry" else "açılacak"
        listed = no_ranges_text([i.get("no") for i in items], 10)
        detail = f" — No {listed}" if rng and listed not in (f"{rng[0]}–{rng[1]}", str(rng[0])) else ""
        self.summary.configure(text=f"{label}: {len(items)} PDF'siz kaynak {verb}{detail}\n"
                                    f"Tahmini süre: ~{minutes} dk")
        self.ok_btn.configure(state="normal")

    def _why_empty(self, rng) -> str:
        """Seçim neden boş? Kullanıcıya hangi kutuyu kaldırması gerektiğini söyler."""
        today = datetime.now().strftime("%Y-%m-%d")
        pool = self.chosen if self.mode.get() == "selected" else \
            [i for i in self.nopdf if rng and rng[0] <= (i.get("no") or 0) <= rng[1]]
        if not pool:
            if rng and self.nopdf:
                lo, hi = self.nopdf[0].get("no") or 0, self.nopdf[-1].get("no") or 0
                return (f"No {rng[0]}–{rng[1]} arasında PDF'i olmayan kaynak yok. PDF'siz kaynaklar No {lo} ile "
                        f"{hi} arasında; 'Tümü'ne basabilirsiniz.")
            return "Bu seçimde PDF'i olmayan kaynak yok."
        reasons = []
        twin_n = sum(1 for i in pool if i["id"] in self.twins)
        if twin_n:
            reasons.append(f"{twin_n} tanesinin PDF'i ikiz kayıtta duruyor — 'Mükerrerleri Birleştir…' ile birleştirin")
        today_n = sum(1 for i in pool if (i.get("pdf_tried") or "") == today and i["id"] not in self.twins)
        hidden_n = sum(1 for i in pool if i["id"] not in self.visible_ids) \
            if self.filtered and self.visible_var.get() and self.mode.get() != "selected" else 0
        if self.skip_var.get() and today_n:
            reasons.append(f"{today_n} tanesi bugün zaten denendi — yeniden denemek için "
                           "'Bugün zaten denenmiş olanları atla' işaretini kaldırın")
        if hidden_n:
            reasons.append(f"{hidden_n} tanesi tablodaki arama/etiket filtresine uymuyor — "
                           "'Yalnızca tabloda görünenler' işaretini kaldırın")
        return f"Bu seçimde {len(pool)} PDF'siz kaynak var ama " + "; ".join(reasons or ["hepsi elendi"]) + "."

    def _ok(self):
        items, label, rng = self.selection()
        if not items:
            return
        self.open_mode_value = self.open_mode.get()
        if self.core_entry is not None:
            remember_setting("core_api_key", self.core_entry.get().strip())
        self.destroy()
        self.on_start(items, label, rng)


class PdfQueuePanel(ctk.CTkToplevel):
    """PDF'siz kaynakları sırayla tarayıcıda açar; İndirilenler'e düşen PDF'i o kaynağa bağlayıp
    bir sonrakine geçer. Her indirmeyi kullanıcı kendisi tıklar."""

    POLL_MS = 1500

    def __init__(self, app, items, label="", open_mode="page"):
        super().__init__(app)
        self.app, self.items, self.label = app, sorted(items, key=lambda i: i.get("no") or 0), label
        self.open_mode = open_mode
        self.index, self.attached, self.skipped, self.merged = -1, 0, 0, 0
        self.pending = None                        # eşleşmeyen PDF: kullanıcıya soruluyor
        self.folders = downloads_folders()
        self.seen = self._snapshot()
        self.sizes = {}
        self.title("PDF'sizleri sırayla aç")
        set_window_icon(self, delay=260)
        self.attributes("-topmost", True)
        self.resizable(False, False)
        self.grid_columnconfigure(0, weight=1)
        pad = {"padx": 16, "sticky": "ew"}
        self.counter = ctk.CTkLabel(self, text="", font=ctk.CTkFont(size=13, weight="bold"), anchor="w")
        self.counter.grid(row=0, column=0, pady=(14, 2), **pad)
        self.item_label = ctk.CTkLabel(self, text="", anchor="w", justify="left", wraplength=420)
        self.item_label.grid(row=1, column=0, **pad)
        self.status = ctk.CTkLabel(self, text="", text_color=MUTED, anchor="w", justify="left", wraplength=420,
                                   font=ctk.CTkFont(size=12))
        self.status.grid(row=2, column=0, pady=(6, 0), **pad)
        self.ask = ctk.CTkFrame(self, fg_color="transparent")
        self.ask.grid(row=3, column=0, **pad)
        btns = ctk.CTkFrame(self, fg_color="transparent")
        btns.grid(row=4, column=0, pady=12, **pad)
        ctk.CTkButton(btns, text="Sayfayı Yeniden Aç", width=140, command=self.open_current).pack(side="left")
        ctk.CTkButton(btns, text="Atla", width=70, fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.skip).pack(side="left", padx=6)
        ctk.CTkButton(btns, text="Bitir", width=70, fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.finish).pack(side="left")
        self.search_menu = ctk.CTkOptionMenu(btns, values=SEARCH_SITES, width=150, command=self._search_elsewhere,
                                             dynamic_resizing=False, fg_color="#5B5F66", button_color="#4A4E54",
                                             button_hover_color="#3D4046")
        self.search_menu.set("Başka yerde ara ▾")
        self.search_menu.pack(side="left", padx=(6, 0))
        self.folder_label = ctk.CTkLabel(self, text="", text_color=MUTED, anchor="w", font=ctk.CTkFont(size=11),
                                         wraplength=420, justify="left")
        self.folder_label.grid(row=5, column=0, **pad)
        ctk.CTkButton(self, text="İzlenen klasörü değiştir…", height=24, width=170, fg_color="transparent",
                      text_color=MUTED, font=ctk.CTkFont(size=11), command=self.change_folder).grid(
            row=6, column=0, padx=16, pady=(0, 12), sticky="w")
        self._show_folder()
        self.protocol("WM_DELETE_WINDOW", self.finish)
        self.after(80, self._place)
        self.next_item()
        self.after(self.POLL_MS, self.poll)

    def _place(self):
        self.update_idletasks()
        x = self.winfo_screenwidth() - self.winfo_width() - 30
        y = self.winfo_screenheight() - self.winfo_height() - 80
        self.geometry(f"+{max(0, x)}+{max(0, y)}")

    def _show_folder(self):
        self.folder_label.configure(text="İzlenen klasör: " + " · ".join(str(f) for f in self.folders))

    def change_folder(self):
        path = filedialog.askdirectory(parent=self, title="Tarayıcının PDF kaydettiği klasör")
        if path:
            current = _load_settings_raw()
            current["downloads_folder"] = os.path.normpath(path)
            save_settings(current)
            self.folders = [Path(path)]
            self.seen = self._snapshot()
            self._show_folder()

    def _snapshot(self) -> set:
        out = set()
        for folder in self.folders:
            try:
                out |= {str(p) for p in downloaded_docs(folder)}
            except OSError:
                pass
        return out

    @property
    def current(self):
        return self.items[self.index] if 0 <= self.index < len(self.items) else None

    def next_item(self):
        self._clear_ask()
        self.index += 1
        if self.index >= len(self.items):
            if self.items:
                remember_setting("queue_next_no", (self.items[-1].get("no") or 0) + 1)
            self.counter.configure(text="Bitti" + (f" · {self.label}" if self.label else ""))
            self.item_label.configure(text=f"{self.attached} kaynağın PDF'i bağlandı, {self.skipped} kaynak atlandı."
                                           + (f" {self.merged} mükerrer kayıt birleştirildi." if self.merged else ""))
            self.status.configure(text="Pencereyi kapatabilirsiniz.")
            return
        cur = self.current
        if cur and self.app.library.get(cur["id"]) is None:         # bu arada birleştirilip silinmiş
            return self.next_item()
        self.open_current()

    def open_current(self):
        item = self.current
        if not item:
            return
        self.counter.configure(text=f"No {item.get('no') or '?'} · {self.index + 1} / {len(self.items)} · "
                                    f"{self.attached} PDF bağlandı")
        who = first_author_label(item)
        self.item_label.configure(text=f"{who + ' ' if who else ''}({item['year'] or 't.y.'}). {shorten(item['title'], 140)}")
        db = database_for_doi(item.get("doi") or "")
        if self.open_mode == "scholar":
            self.status.configure(text="Google Akademik'te başlıkla arama açıldı. Sonuçlarda [PDF] bağlantısı varsa "
                                       "(kurum arşivi, ResearchGate, Academia…) indirin; dosya bu kaynağa bağlanıp "
                                       "bir sonraki açılacak. Yoksa 'Atla'.", text_color=MUTED)
            webbrowser.open_new_tab(search_link(item, "Google Akademik"))
            return
        self.status.configure(text="Sayfa tarayıcıda açıldı. PDF'i indirin; dosya İndirilenler'e düşünce bu kaynağa "
                                   "bağlanıp bir sonraki açılacak." + (f"\nKampüs dışındaysanız: VETİS → {db}." if db else ""),
                              text_color=MUTED)
        webbrowser.open_new_tab(item_open_link(item))

    def _search_elsewhere(self, site):
        self.search_menu.set("Başka yerde ara ▾")
        if self.current:
            webbrowser.open_new_tab(search_link(self.current, site))
            self.status.configure(text=f"{site} açıldı. Bulduğunuz PDF'i indirin; başlığı uyuyorsa bu kaynağa "
                                       "bağlanır.", text_color=MUTED)

    def skip(self):
        item = self.current
        if item:
            self.app.library.update(item["id"], {"pdf_tried": datetime.now().strftime("%Y-%m-%d")})
            self.skipped += 1
        self.next_item()

    def finish(self):
        if self.current:                             # yarıda bırakıldı: bir dahakine buradan başla
            remember_setting("queue_next_no", self.current.get("no") or 0)
        self.app.pdf_queue = None
        self.app.library_tab.refresh()
        self.destroy()

    def _clear_ask(self):
        self.pending = None
        for w in self.ask.winfo_children():
            w.destroy()
        self.ask.configure(height=1)                     # boş kalan çerçeve pencereyi uzatmasın

    def poll(self):
        if not self.winfo_exists():
            return
        try:
            if self.current and self.pending is None:
                found = [p for folder in self.folders if folder.is_dir() for p in downloaded_docs(folder)]
                for path in sorted(found, key=lambda p: p.stat().st_mtime):
                    if str(path) in self.seen:
                        continue
                    size = path.stat().st_size
                    if self.sizes.get(str(path)) != size or size == 0:      # indirme sürüyor olabilir
                        self.sizes[str(path)] = size
                        continue
                    self.seen.add(str(path))
                    self._handle(path)
                    break
        except Exception:
            diag_exception("sırayla açma")
        self.after(self.POLL_MS, self.poll)

    def _matches(self, item, path) -> bool:
        if path.stem.isdigit() and yok_tez_no(item) == path.stem:
            return True
        head = doc_head(path)
        m = DOI_RE.search(head)
        if m and item.get("doi") and normalize_doi(clean_url(m.group(1))) == normalize_doi(item["doi"]):
            return True
        return title_matches_text(item["title"], head)

    def _handle(self, path):
        item = self.current
        owner = self.app.library.find_by_sha(file_sha256(path))
        if owner:
            holder = self.app.library.get(owner) if owner != item["id"] else None
            if holder is None:
                self.status.configure(text=f"{path.name} zaten kütüphanede; yok sayıldı.", text_color=LOG_COLORS["warn"])
                return
            head = fold(doc_head(path))
            same_doi = item.get("doi") and holder.get("doi") and \
                (normalize_doi(item["doi"]) or "x").lower() == (normalize_doi(holder["doi"]) or "y").lower()
            if same_doi or (title_position(item["title"], head) >= 0 and _twin_compatible(item, holder, head)):
                return self._offer_merge(path, item, holder, head)
            self.status.configure(text=f"{path.name} zaten No {holder.get('no')} kaydına bağlı "
                                       f"(“{shorten(holder['title'], 60)}”) ve bu kaynağın başlığını içermiyor; "
                                       "yok sayıldı.", text_color=LOG_COLORS["warn"])
            return
        if self._matches(item, path):
            self._attach(path)
            return
        self.pending = path
        self.status.configure(text=f"İnen dosyanın ({path.name}) başlığı bu kaynakla eşleşmedi.",
                              text_color=LOG_COLORS["warn"])
        ctk.CTkButton(self.ask, text="Yine de bu kaynağa bağla", width=180,
                      command=lambda: self._attach(path)).pack(side="left")
        ctk.CTkButton(self.ask, text="Bu dosyayı yok say", width=140, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=self._ignore).pack(side="left", padx=6)

    def _offer_merge(self, path, item, holder, head):
        """İnen PDF başka bir kayıtta zaten var ve o kayıt bu kaynağın ikizi (başka dilde başlıklı aynı yayın)."""
        self.pending = path
        keeper = preferred_keeper(item, holder, head)
        self.status.configure(
            text=f"Bu PDF zaten No {holder.get('no')} kaydında (“{shorten(holder['title'], 70)}”) ve bu kaynağın "
                 f"başlığını da içeriyor: iki kayıt aynı yayın. Birleştirilsin mi? (No {keeper.get('no')} tutulur, "
                 "etiketler, kartlar ve notlar ona geçer)", text_color=LOG_COLORS["warn"])
        ctk.CTkButton(self.ask, text="Birleştir", width=110,
                      command=lambda: self._merge(item, holder, keeper)).pack(side="left")
        ctk.CTkButton(self.ask, text="Yok say", width=100, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=self._ignore).pack(side="left", padx=6)

    def _merge(self, item, holder, keeper):
        other = holder if keeper["id"] == item["id"] else item
        try:
            self.app.library.merge_items(keeper["id"], [other["id"]], self.app.library_folder())
        except Exception as exc:
            diag_exception("sırayla açma: birleştirme")
            self.status.configure(text=f"Birleştirilemedi: {describe_error(exc)}", text_color=LOG_COLORS["error"])
            return
        self.merged += 1
        self.app.library_tab.refresh()
        self.status.configure(text=f"✓ No {item.get('no')} ve No {holder.get('no')} birleştirildi; PDF No "
                                   f"{keeper.get('no')} kaydında.", text_color=LOG_COLORS["success"])
        self._clear_ask()
        self.after(1200, self.next_item)

    def _ignore(self):
        self._clear_ask()
        self.status.configure(text="Dosya yok sayıldı. Doğru PDF'i indirin ya da 'Atla'ya basın.", text_color=MUTED)

    def _attach(self, path):
        item = self.current
        try:
            placed = attach_pdf(self.app.library, item["id"], path, self.app.library_folder(), move=True)
        except OSError as exc:
            self.status.configure(text=f"Dosya taşınamadı: {exc}", text_color=LOG_COLORS["error"])
            return
        self.attached += 1
        self.app.library_tab.refresh()
        self.status.configure(text=f"✓ Bağlandı: {placed.name}", text_color=LOG_COLORS["success"])
        self._clear_ask()
        self.after(1200, self.next_item)


class RetroScanDialog(ctk.CTkToplevel):
    """Geçmişe dönük tarama seçenekleri: dönem, gruplar, kaynaklar, PDF indirme."""

    def __init__(self, app, scan_tab):
        super().__init__(app)
        self.app, self.scan_tab = app, scan_tab
        self.title("Geçmişe Dönük Tarama")
        set_window_icon(self, delay=260)
        self.resizable(False, True)
        self.transient(app)
        pad = {"padx": 20, "sticky": "ew"}
        self.grid_columnconfigure(0, weight=1)
        r = 0
        ctk.CTkLabel(self, text="Geçmişe dönük tarama", font=ctk.CTkFont(size=16, weight="bold"),
                     anchor="w").grid(row=r, column=0, pady=(18, 2), **pad); r += 1
        ctk.CTkLabel(self, text="Anahtar kelimelerinizle eşleşen eski yayınları da bulur, kütüphaneye ekler ve "
                                "açık erişimli olanların PDF'ini indirir. Uzun sürebilir; durdurursanız aynı "
                                "seçeneklerle yeniden başlatınca kaldığı yerden devam eder.",
                     text_color=MUTED, wraplength=520, justify="left", anchor="w").grid(row=r, column=0, **pad); r += 1
        pending = pending_retro()
        if pending:
            pr = pending["retro"]
            ctk.CTkLabel(self, text=f"Yarım kalan tarama: {retro_period_label(pr.get('years', 0))} · "
                                    f"{len(pending.get('done', []))} adım tamamlandı · başlangıç {pending.get('started', '')}",
                         text_color=LOG_COLORS["warn"], anchor="w").grid(row=r, column=0, pady=(10, 0), **pad); r += 1
            ctk.CTkButton(self, text="Kaldığı Yerden Devam Et", command=lambda: self._start(pr)).grid(
                row=r, column=0, pady=(4, 0), padx=20, sticky="w"); r += 1

        def label(text):
            nonlocal r
            ctk.CTkLabel(self, text=text, font=ctk.CTkFont(size=13, weight="bold"), anchor="w").grid(
                row=r, column=0, pady=(14, 4), **pad)
            r += 1
        label("Dönem")
        self.period = ctk.CTkSegmentedButton(self, values=list(RETRO_PERIODS))
        self.period.set("Tüm zamanlar")
        self.period.grid(row=r, column=0, **pad); r += 1
        label("Kaynaklar")
        self.use_dp = ctk.BooleanVar(value=True)
        self.use_cr = ctk.BooleanVar(value=True)
        self.use_yok = ctk.BooleanVar(value=True)
        self.use_oa = ctk.BooleanVar(value=load_settings().get("scan_openalex", True))
        self.use_eric = ctk.BooleanVar(value=load_settings().get("scan_eric", True))
        ctk.CTkCheckBox(self, text="YÖK Ulusal Tez Merkezi (bütün yüksek lisans ve doktora tezleri; izinlilerin PDF'i)",
                        variable=self.use_yok).grid(row=r, column=0, pady=2, **pad); r += 1
        ctk.CTkCheckBox(self, text="Crossref (uluslararası ve DOI'li Türkçe yayınlar, en eskisine kadar)",
                        variable=self.use_cr).grid(row=r, column=0, pady=2, **pad); r += 1
        ctk.CTkCheckBox(self, text="OpenAlex (makale, kitap, bölüm, dünya tezleri ve kurum arşivleri; özetleriyle)",
                        variable=self.use_oa, command=self._update_estimate).grid(row=r, column=0, pady=2, **pad); r += 1
        ctk.CTkCheckBox(self, text="ERIC (eğitim araştırmaları: dans, müzik ve beden eğitimi; çoğunun PDF'i açık)",
                        variable=self.use_eric, command=self._update_estimate).grid(row=r, column=0, pady=2, **pad); r += 1
        dp = ctk.CTkFrame(self, fg_color="transparent")
        dp.grid(row=r, column=0, pady=2, **pad); r += 1
        ctk.CTkCheckBox(dp, text="DergiPark:", variable=self.use_dp).pack(side="left")
        self.scope = ctk.CTkOptionMenu(dp, values=list(RETRO_SCOPES), width=280)
        self.scope.set(next(iter(RETRO_SCOPES)))
        self.scope.pack(side="left", padx=8)
        label("PDF")
        self.downloads = ctk.CTkOptionMenu(self, values=list(RETRO_DOWNLOADS), width=280)
        self.downloads.set(next(iter(RETRO_DOWNLOADS)))
        self.downloads.grid(row=r, column=0, padx=20, sticky="w"); r += 1
        label("Konu grupları")
        box = ctk.CTkScrollableFrame(self, height=120)
        box.grid(row=r, column=0, **pad); r += 1
        self.group_vars = {}
        for g in parse_keyword_groups(load_keywords_text()):
            var = ctk.BooleanVar(value=True)
            ctk.CTkCheckBox(box, text=f"{g['name']}  ({len(g['terms'])} terim)", variable=var).pack(anchor="w", pady=2)
            self.group_vars[g["name"]] = var
        self.estimate = ctk.CTkLabel(self, text="", text_color=MUTED, wraplength=520, justify="left", anchor="w")
        self.estimate.grid(row=r, column=0, pady=(10, 0), **pad); r += 1
        btns = ctk.CTkFrame(self, fg_color="transparent")
        btns.grid(row=r, column=0, pady=18, **pad); r += 1
        ctk.CTkButton(btns, text="Taramayı Başlat", fg_color="#1F8F4E", hover_color="#18723E",
                      command=self._start_new).pack(side="left")
        ctk.CTkButton(btns, text="Vazgeç", fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.destroy).pack(side="left", padx=8)
        for w in (self.period, self.scope, self.downloads):
            w.configure(command=lambda _=None: self._update_estimate())
        self._update_estimate()

        def place():
            self.update_idletasks()
            x = app.winfo_rootx() + max(0, (app.winfo_width() - self.winfo_width()) // 2)
            y = app.winfo_rooty() + max(0, (app.winfo_height() - self.winfo_height()) // 4)
            self.geometry(f"+{x}+{y}")
            self.lift()
            self.focus_force()
        self.after(60, place)

    def _collect_options(self) -> dict:
        groups = [n for n, v in self.group_vars.items() if v.get()]
        return {"years": RETRO_PERIODS[self.period.get()], "scope": RETRO_SCOPES[self.scope.get()],
                "dergipark": self.use_dp.get(), "crossref": self.use_cr.get(), "yok": self.use_yok.get(),
                "openalex": self.use_oa.get(), "eric": self.use_eric.get(),
                "groups": groups if len(groups) < len(self.group_vars) else [],
                "max_downloads": RETRO_DOWNLOADS[self.downloads.get()]}

    def _update_estimate(self):
        o = self._collect_options()
        text = {"alan": "DergiPark'ta adı folklor, halkbilim, müzik, dans, sanat, kültür, tiyatro, Türk "
                        "dünyası vb. olan dergiler baştan sona taranır (yaklaşık 1 saat).",
                "sosyal": "Alan dergilerine ek olarak sosyal bilimler, edebiyat, eğitim ve spor dergileri de "
                          "taranır (birkaç saat).",
                "tum": "Bütün DergiPark yıl yıl taranır; tüm zamanlar için bir gece sürebilir."}[o["scope"]]
        cr = (f" Crossref'te her terim için en ilgili {RETRO_CROSSREF_LIMIT.get(o['years'], 2000)} kayıt incelenir."
              if o["crossref"] else "")
        if o["yok"]:
            cr += " YÖK'te her terim için bulunan bütün tezler incelenir; eşleşen tezlerin PDF'i iner."
        if o["openalex"]:
            cr += (" OpenAlex'te her terim için en ilgili kayıtlar incelenir"
                   + ("." if openalex_params().get("api_key") else
                      " (anahtarsız günlük sınır düşüktür; dolarsa kalan terimler sonraki çalıştırmada sürer)."))
        self.estimate.configure(text=(text if o["dergipark"] else "") + cr +
                                " Program açık kaldığı sürece arka planda çalışır.")

    def _start_new(self):
        o = self._collect_options()
        if not any(o[k] for k in ("dergipark", "crossref", "yok", "openalex", "eric")):
            messagebox.showwarning(APP_NAME, "En az bir kaynak seçin.", parent=self)
            return
        self._start(o)

    def _start(self, options):
        self.destroy()
        self.app.tabs.set("Tarama")
        self.scan_tab.start_scan(retro=options)


class BibliographyDialog(ctk.CTkToplevel):
    """Seçilen kaynakların APA kaynakçası: panoya kopyala ya da Word olarak kaydet."""

    def __init__(self, master, records, lang="tr"):
        super().__init__(master)
        self.title(f"Kaynakça · {len(records)} kaynak")
        set_window_icon(self, delay=260)
        self.geometry("820x600")
        self.records = records
        self.lang = lang
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)

        bar = ctk.CTkFrame(self, fg_color="transparent")
        bar.grid(row=0, column=0, sticky="ew", padx=16, pady=(14, 6))
        bar.grid_columnconfigure(1, weight=1)
        self.lang_btn = ctk.CTkSegmentedButton(bar, values=["Türkçe", "English"], command=self._switch)
        self.lang_btn.set("Türkçe" if lang == "tr" else "English")
        self.lang_btn.grid(row=0, column=0)
        ctk.CTkLabel(bar, text="APA 7 · alfabetik · italikler Word dosyasında korunur",
                     text_color=MUTED, font=ctk.CTkFont(size=12)).grid(row=0, column=1, sticky="w", padx=12)

        self.box = ctk.CTkTextbox(self, wrap="word", font=ctk.CTkFont(size=13), border_width=1)
        self.box.grid(row=1, column=0, sticky="nsew", padx=16)
        add_italic_tag(self.box)
        self.box._textbox.tag_configure("p", lmargin1=0, lmargin2=36, spacing3=10)

        btns = ctk.CTkFrame(self, fg_color="transparent")
        btns.grid(row=2, column=0, sticky="ew", padx=16, pady=14)
        ctk.CTkButton(btns, text="Panoya Kopyala", command=self._copy).pack(side="left")
        ctk.CTkButton(btns, text="Word Olarak Kaydet…", command=self._save).pack(side="left", padx=8)
        ctk.CTkButton(btns, text="Kapat", fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.destroy).pack(side="right")
        self._render()
        self.after(100, self.lift)

    def _switch(self, value):
        self.lang = "tr" if value == "Türkçe" else "en"
        self._render()

    def _render(self):
        self.refs = bibliography(self.records, self.lang)
        self.box.configure(state="normal")
        self.box.delete("1.0", "end")
        for _, segs in self.refs:
            start = self.box._textbox.index("end-1c")
            for text, italic in segs:
                self.box._textbox.insert("end", text, ("i",) if italic else ())
            self.box._textbox.insert("end", "\n")
            self.box._textbox.tag_add("p", start, "end-1c")
        self.box.configure(state="disabled")

    def _copy(self):
        self.clipboard_clear()
        self.clipboard_append("\n".join(text for text, _ in self.refs))

    def _save(self):
        path = filedialog.asksaveasfilename(parent=self, defaultextension=".docx",
                                            filetypes=[("Word belgesi", "*.docx")],
                                            initialfile="Kaynakça.docx")
        if path:
            write_bibliography_docx(path, self.refs, "Kaynakça" if self.lang == "tr" else "References")
            try:
                open_file(Path(path))
            except Exception:
                pass


class LibraryTab:
    """'Kütüphanem' sekmesi: tablo, arama/filtre, künye düzenleme, alıntı kartları, kaynakça."""

    STATUS_FILTERS = ["Tümü", "Yeni (taramadan)", "PDF'i olanlar", "PDF'i olmayanlar", "Kartı olanlar",
                      "Scopus'taki dergiler"]
    TYPE_FILTERS = {"Tüm türler": None, "Makale": ("article",), "Kitap": ("book",), "Kitap bölümü": ("chapter",),
                    "Bildiri": ("conference",), "Tez (hepsi)": "thesis", "Doktora tezi": ("phd",),
                    "Yüksek lisans tezi": ("masters",), "Diğer": ("other",)}

    def __init__(self, parent, app):
        self.app = app
        self.lib = app.library
        self.parent = parent
        self.items = []
        self.by_id = {}
        self.current = None
        self.editing_card = None
        self._search_job = None
        self.sort_col, self.sort_rev = "added", True

        parent.grid_columnconfigure(0, weight=3)
        parent.grid_columnconfigure(1, weight=2)
        parent.grid_rowconfigure(1, weight=1)
        self._build_toolbar()
        self._build_table()
        self._build_detail()
        self._build_bottom()
        self.apply_style()
        self.refresh()

    # ── yerleşim ────────────────────────────────────────────────────────────
    def _build_toolbar(self):
        bar = ctk.CTkFrame(self.parent, fg_color="transparent")
        bar.grid(row=0, column=0, columnspan=2, sticky="ew", padx=8, pady=(4, 8))
        bar.grid_columnconfigure(0, weight=1)
        self.search = ctk.CTkEntry(bar, height=34,
                                   placeholder_text="Ara: başlık, yazar, dergi, etiket, alıntı kartı…  "
                                                    "· #120-220 = kayıt numarası aralığı")
        self.search.grid(row=0, column=0, sticky="ew")
        self.search.bind("<KeyRelease>", lambda _: self._schedule_refresh())
        self.fulltext_var = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(bar, text="PDF içinde de ara", variable=self.fulltext_var, width=20,
                        command=self.refresh, font=ctk.CTkFont(size=12)).grid(row=0, column=1, padx=10)
        self.tag_menu = ctk.CTkOptionMenu(bar, values=["Tüm etiketler"], width=170,
                                          command=lambda _: self.refresh(), dynamic_resizing=False)
        self.tag_menu.grid(row=0, column=2, padx=(0, 8))
        self.type_menu = ctk.CTkOptionMenu(bar, values=list(self.TYPE_FILTERS), width=140,
                                           command=lambda _: self.refresh(), dynamic_resizing=False)
        self.type_menu.grid(row=0, column=3, padx=(0, 8))
        self.status_menu = ctk.CTkOptionMenu(bar, values=self.STATUS_FILTERS, width=160,
                                             command=lambda _: self.refresh(), dynamic_resizing=False)
        self.status_menu.grid(row=0, column=4, padx=(0, 8))
        acts = ctk.CTkFrame(bar, fg_color="transparent")          # ikinci satır: işlemler
        acts.grid(row=1, column=0, columnspan=5, sticky="w", pady=(8, 0))
        outline = {"fg_color": "transparent", "border_width": 1, "text_color": TEXT}
        ctk.CTkButton(acts, text="Dosya Ekle…", width=100, command=self._add_pdfs).pack(side="left")
        ctk.CTkButton(acts, text="Klasör Tara…", width=110, command=self._scan_folder, **outline).pack(
            side="left", padx=(8, 0))
        self.autotag_btn = ctk.CTkButton(acts, text="Otomatik Etiketle", width=130, command=self._autotag, **outline)
        self.autotag_btn.pack(side="left", padx=(8, 0))
        self.complete_btn = ctk.CTkButton(acts, text="Eksik Künyeleri Tamamla", width=170, command=self._complete,
                                          **outline)
        self.complete_btn.pack(side="left", padx=(8, 0))
        self.retry_btn = ctk.CTkButton(acts, text="PDF'leri Yeniden Ara", width=150, fg_color="#1F8F4E",
                                       hover_color="#18723E", command=self._retry_pdfs)
        self.retry_btn.pack(side="left", padx=(16, 0))
        ctk.CTkButton(acts, text="PDF'sizleri Sırayla Aç", width=160, fg_color="#1F6F8B", hover_color="#185A71",
                      command=self._open_queue).pack(side="left", padx=(8, 0))
        self.allseen_btn = ctk.CTkButton(acts, text="Yenileri İncelendi Say", width=170, command=self._mark_all_reviewed,
                                         **outline)
        self.allseen_btn.pack(side="left", padx=(16, 0))
        self.tools_menu = ctk.CTkOptionMenu(acts, width=120, dynamic_resizing=False, command=self._tool_chosen,
                                            values=["Atıf ağı ve eksik kaynaklar…", "Mükerrer kayıtları bul…",
                                                    "PDF işaretlemelerini kartlara aktar…",
                                                    "Künyeyi PDF'ten yeniden çıkar…"])
        self.tools_menu.set("Araçlar ▾")
        self.tools_menu.pack(side="left", padx=(8, 0))

    def _build_table(self):
        from tkinter import ttk
        frame = ctk.CTkFrame(self.parent, corner_radius=12)
        frame.grid(row=1, column=0, sticky="nsew", padx=(8, 6))
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(0, weight=1)
        cols = ("no", "pdf", "author", "year", "title", "scopus", "tags")
        self.tree = ttk.Treeview(frame, columns=cols, show="headings", selectmode="extended",
                                 style="Lib.Treeview")
        for col, text, width, stretch in (("no", "No", 50, False), ("pdf", "", 34, False),
                                          ("author", "Yazar", 150, False),
                                          ("year", "Yıl", 52, False), ("title", "Başlık", 360, True),
                                          ("scopus", "Scopus", 74, False), ("tags", "Etiketler", 150, False)):
            self.tree.heading(col, text=text, command=lambda c=col: self._sort(c))
            self.tree.column(col, width=width, minwidth=30, stretch=stretch,
                             anchor="center" if col in ("pdf", "year", "scopus") else ("e" if col == "no" else "w"))
        self.tree.grid(row=0, column=0, sticky="nsew", padx=(6, 0), pady=6)
        sb = ctk.CTkScrollbar(frame, command=self.tree.yview)
        sb.grid(row=0, column=1, sticky="ns", pady=6)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.bind("<<TreeviewSelect>>", lambda _: self._on_select())
        self.tree.bind("<Double-1>", lambda _: self._open_pdf())
        self.tree.bind("<Delete>", lambda _: self._remove())

    def _build_detail(self):
        tabs = ctk.CTkTabview(self.parent, corner_radius=12)
        tabs.grid(row=1, column=1, sticky="nsew", padx=(6, 8))
        self.detail_tabs = tabs
        self._build_record_tab(tabs.add("Künye"))
        self._build_cards_tab(tabs.add("Alıntı Kartları"))
        self._build_apa_tab(tabs.add("APA"))
        st = tabs.add("Claude Özeti")
        st.grid_columnconfigure(0, weight=1)
        st.grid_rowconfigure(0, weight=1)
        self.summary_box = ctk.CTkTextbox(st, wrap="word", border_width=1, font=ctk.CTkFont(size=13))
        self.summary_box.grid(row=0, column=0, sticky="nsew")

    def _field(self, parent, row, label, widget):
        ctk.CTkLabel(parent, text=label, font=ctk.CTkFont(size=12), text_color=MUTED,
                     anchor="w").grid(row=row, column=0, sticky="nw", padx=(4, 8), pady=3)
        widget.grid(row=row, column=1, sticky="ew", pady=3, padx=(0, 4))

    def _build_record_tab(self, tab):
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_rowconfigure(1, weight=1)
        self.pdf_label = ctk.CTkLabel(tab, text="Bir kaynak seçin", anchor="w", justify="left",
                                      font=ctk.CTkFont(size=12, weight="bold"), wraplength=330)
        self.pdf_label.grid(row=0, column=0, sticky="ew", padx=6, pady=(0, 4))
        form = ctk.CTkScrollableFrame(tab, fg_color="transparent")
        form.grid(row=1, column=0, sticky="nsew")
        form.grid_columnconfigure(1, weight=1)
        self.f_title = ctk.CTkTextbox(form, height=64, wrap="word", border_width=1)
        self._field(form, 0, "Başlık", self.f_title)
        self.f = {}
        for row, (key, label, hint) in enumerate([
                ("authors", "Yazarlar", "Soyad, Ad; Soyad, Ad"),
                ("year", "Yıl", ""), ("container", "Dergi / Kitap", ""),
                ("volume", "Cilt", ""), ("issue", "Sayı", ""), ("pages", "Sayfa", "45–67"),
                ("publisher", "Yayınevi", ""), ("editors", "Editörler", "Soyad, Ad; Soyad, Ad"),
                ("institution", "Kurum (tez)", ""), ("doi", "DOI", "10.xxxx/…"),
                ("issn", "ISSN", "1234-5678"), ("url", "Link", ""),
                ("keywords", "Anahtar kelimeler", "makalenin kendi anahtar kelimeleri"),
                ("tags", "Etiketler", "virgülle ayırın")], start=1):
            entry = ctk.CTkEntry(form, placeholder_text=hint, height=30)
            self._field(form, row, label, entry)
            self.f[key] = entry
        self.f_type = ctk.CTkOptionMenu(form, values=list(ITEM_TYPES.values()), height=30)
        self._field(form, row + 1, "Tür", self.f_type)
        self.matched_label = ctk.CTkLabel(form, text="", text_color=MUTED, font=ctk.CTkFont(size=11),
                                          anchor="w", justify="left", wraplength=360)
        self.matched_label.grid(row=row + 2, column=0, columnspan=2, sticky="ew", padx=4, pady=(6, 0))

        btns = ctk.CTkFrame(tab, fg_color="transparent")
        btns.grid(row=2, column=0, sticky="ew", pady=(6, 0))
        for i in range(3):
            btns.grid_columnconfigure(i, weight=1)
        small = {"height": 30, "font": ctk.CTkFont(size=12)}
        outline = {"fg_color": "transparent", "border_width": 1, "text_color": TEXT}
        self.save_btn = ctk.CTkButton(btns, text="Kaydet", command=self._save_record, **small)
        self.save_btn.grid(row=0, column=0, sticky="ew", padx=2, pady=2)
        self.open_btn = ctk.CTkButton(btns, text="PDF'i Aç", command=self._open_pdf, **small, **outline)
        self.open_btn.grid(row=0, column=1, sticky="ew", padx=2, pady=2)
        self.show_btn = ctk.CTkButton(btns, text="Klasörde Göster", command=self._show_pdf, **small, **outline)
        self.show_btn.grid(row=0, column=2, sticky="ew", padx=2, pady=2)
        self.inst_btn = ctk.CTkButton(btns, text="Makaleyi Aç", command=self._open_institution,
                                      **small, **outline)
        self.inst_btn.grid(row=1, column=0, sticky="ew", padx=2, pady=2)
        self.attach_btn = ctk.CTkButton(btns, text="PDF Bağla…", command=self._attach_pdf, **small, **outline)
        self.attach_btn.grid(row=1, column=1, sticky="ew", padx=2, pady=2)
        self.crossref_btn = ctk.CTkButton(btns, text="Künyeyi DOI'den Al", command=self._refresh_from_doi,
                                          **small, **outline)
        self.crossref_btn.grid(row=1, column=2, sticky="ew", padx=2, pady=2)
        self.reviewed_btn = ctk.CTkButton(btns, text="İncelendi ✓", command=self._mark_reviewed,
                                          **small, **outline)
        self.reviewed_btn.grid(row=2, column=0, sticky="ew", padx=2, pady=2)
        self.remove_btn = ctk.CTkButton(btns, text="Kütüphaneden Çıkar", command=self._remove,
                                        fg_color="transparent", border_width=1, text_color="#C9353A",
                                        border_color="#C9353A", **small)
        self.remove_btn.grid(row=2, column=2, sticky="ew", padx=2, pady=2)
        self.vetis_btn = ctk.CTkButton(btns, text="VETİS (kampüs dışı)", command=self._open_vetis,
                                       **small, **outline)
        self.vetis_btn.grid(row=2, column=1, sticky="ew", padx=2, pady=2)
        self.search_menu = ctk.CTkOptionMenu(btns, values=SEARCH_SITES, command=self._search_elsewhere,
                                             height=30, font=ctk.CTkFont(size=12), dynamic_resizing=False,
                                             fg_color="#5B5F66", button_color="#4A4E54", button_hover_color="#3D4046")
        self.search_menu.set("Başlıkla başka yerde ara ▾")
        self.search_menu.grid(row=3, column=0, columnspan=2, sticky="ew", padx=2, pady=2)
        self.notes_btn = ctk.CTkButton(btns, text="Okurken Not Al", command=self._reading_notes, **small, **outline)
        self.notes_btn.grid(row=3, column=2, sticky="ew", padx=2, pady=2)

    def _reading_notes(self):
        if not self.current:
            return
        win = getattr(self, "notes_win", None)
        if win is not None and win.winfo_exists():
            win.destroy()
        self.notes_win = ReadingNotes(self.app, self.current)
        self.notes_win.open_book()

    def _search_elsewhere(self, site):
        self.search_menu.set("Başlıkla başka yerde ara ▾")
        if self.current:
            webbrowser.open_new_tab(search_link(self.current, site))
            self.app.toast(f"{site} tarayıcıda açıldı. PDF'i indirirseniz 'PDF Bağla…' ile bu kaynağa bağlayın.")

    def _build_cards_tab(self, tab):
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_rowconfigure(0, weight=1)
        self.cards_frame = ctk.CTkScrollableFrame(tab, fg_color="transparent")
        self.cards_frame.grid(row=0, column=0, sticky="nsew")
        self.cards_frame.grid_columnconfigure(0, weight=1)
        form = ctk.CTkFrame(tab, corner_radius=10)
        form.grid(row=1, column=0, sticky="ew", pady=(6, 0))
        form.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(form, text="Sayfa", font=ctk.CTkFont(size=12)).grid(row=0, column=0, padx=8, pady=(8, 2), sticky="w")
        self.card_page = ctk.CTkEntry(form, width=90, height=28, placeholder_text="45 ya da 45-47")
        self.card_page.grid(row=0, column=1, sticky="w", pady=(8, 2))
        ctk.CTkLabel(form, text="Alıntı", font=ctk.CTkFont(size=12)).grid(row=1, column=0, padx=8, sticky="nw")
        self.card_quote = ctk.CTkTextbox(form, height=70, wrap="word", border_width=1)
        self.card_quote.grid(row=1, column=1, sticky="ew", padx=(0, 8), pady=2)
        ctk.CTkLabel(form, text="Yorumum", font=ctk.CTkFont(size=12)).grid(row=2, column=0, padx=8, sticky="nw")
        self.card_comment = ctk.CTkTextbox(form, height=50, wrap="word", border_width=1)
        self.card_comment.grid(row=2, column=1, sticky="ew", padx=(0, 8), pady=2)
        row = ctk.CTkFrame(form, fg_color="transparent")
        row.grid(row=3, column=0, columnspan=2, sticky="ew", padx=8, pady=8)
        self.card_save = ctk.CTkButton(row, text="Kartı Ekle", width=110, command=self._save_card)
        self.card_save.pack(side="left")
        self.card_cancel = ctk.CTkButton(row, text="Vazgeç", width=80, fg_color="transparent",
                                         border_width=1, text_color=TEXT, command=self._reset_card_form)
        self.card_cancel.pack(side="left", padx=6)

    def _build_apa_tab(self, tab):
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_rowconfigure(1, weight=1)
        self.apa_lang = ctk.CTkSegmentedButton(tab, values=["Türkçe", "English"],
                                               command=lambda _: self._render_apa())
        self.apa_lang.set("Türkçe")
        self.apa_lang.grid(row=0, column=0, sticky="w", pady=(0, 6))
        self.apa_box = ctk.CTkTextbox(tab, wrap="word", border_width=1, font=ctk.CTkFont(size=13))
        self.apa_box.grid(row=1, column=0, sticky="nsew")
        add_italic_tag(self.apa_box)
        btns = ctk.CTkFrame(tab, fg_color="transparent")
        btns.grid(row=2, column=0, sticky="ew", pady=(6, 0))
        ctk.CTkButton(btns, text="Kaynakçayı Kopyala", width=150, command=self._copy_apa).pack(side="left")
        ctk.CTkButton(btns, text="Metin İçi Atfı Kopyala", width=160, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=self._copy_intext).pack(side="left", padx=6)

    def _build_bottom(self):
        bar = ctk.CTkFrame(self.parent, fg_color="transparent")
        bar.grid(row=2, column=0, columnspan=2, sticky="ew", padx=8, pady=(8, 2))
        bar.grid_columnconfigure(0, weight=1)
        self.count_label = ctk.CTkLabel(bar, text="", text_color=MUTED, font=ctk.CTkFont(size=12))
        self.count_label.grid(row=0, column=0, sticky="w")
        ctk.CTkButton(bar, text="Seçilenlerin Kaynakçası", width=170,
                      command=lambda: self._bibliography(selected=True)).grid(row=0, column=1, padx=4)
        ctk.CTkButton(bar, text="Listedekilerin Kaynakçası", width=170, fg_color="transparent",
                      border_width=1, text_color=TEXT,
                      command=lambda: self._bibliography(selected=False)).grid(row=0, column=2, padx=4)
        ctk.CTkButton(bar, text="Dışa Aktar (Jenni / Zotero)…", width=190, fg_color="transparent",
                      border_width=1, text_color=TEXT, command=self._export).grid(row=0, column=3, padx=4)
        ctk.CTkButton(bar, text="İçe Aktar (Piri / RIS / BibTeX)…", width=210, fg_color="transparent",
                      border_width=1, text_color=TEXT, command=self._import_refs).grid(row=0, column=4, padx=4)
        self.isbn_btn = ctk.CTkButton(bar, text="Kitap Ekle (ISBN / Bağlantı)…", width=200, fg_color="transparent",
                                      border_width=1, text_color=TEXT, command=self._add_isbn)
        self.isbn_btn.grid(row=0, column=5, padx=4)

    # ── görünüm ─────────────────────────────────────────────────────────────
    def apply_style(self):
        from tkinter import ttk
        dark = ctk.get_appearance_mode().lower() == "dark"
        bg, fg = ("#2b2b2b", "#e6e6e6") if dark else ("#fbfbfb", "#1d1d1f")
        head_bg = "#333333" if dark else "#ececec"
        sel = "#1f538d" if dark else "#cfe2f7"
        sel_fg = "#ffffff" if dark else "#0b2545"
        family = "Segoe UI" if sys.platform.startswith("win") else "DejaVu Sans"
        style = ttk.Style(self.parent)
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("Lib.Treeview", background=bg, fieldbackground=bg, foreground=fg,
                        rowheight=28, borderwidth=0, font=(family, 10))
        style.configure("Lib.Treeview.Heading", background=head_bg, foreground=fg, relief="flat",
                        font=(family, 10, "bold"), padding=(6, 4))
        style.map("Lib.Treeview", background=[("selected", sel)], foreground=[("selected", sel_fg)])
        style.map("Lib.Treeview.Heading", background=[("active", head_bg)])
        self.tree.tag_configure("new", font=(family, 10, "bold"))
        self.tree.tag_configure("nopdf", foreground="#8b919a")

    # ── veriler ─────────────────────────────────────────────────────────────
    def _schedule_refresh(self):
        if self._search_job:
            self.parent.after_cancel(self._search_job)
        self._search_job = self.parent.after(250, self.refresh)

    def refresh(self, keep_selection=True):
        selected = set(self.tree.selection()) if keep_selection else set()
        self.items = self.lib.all_items()
        self.by_id = {i["id"]: i for i in self.items}
        card_counts = self.lib.card_counts()
        scopus = load_scopus()
        to_check = []
        for item in self.items:
            known, stale = file_exists_known(item["file_path"])
            item["has_pdf"] = bool(item["file_path"]) if known is None else known    # bilinmiyorsa: var say
            if item["file_path"] and stale:
                to_check.append((item["file_path"], item["has_pdf"]))
            item["cards"] = card_counts.get(item["id"], 0)
            info = scopus_info(item, scopus) if scopus else None
            item["_scopus"] = info[0] if info else ""
            item["_blob"] = fold(" ".join([item["title"], people_to_text(item["authors"]), item["container"],
                                           item["year"], item["notes"], " ".join(item["tags"]), item["doi"],
                                           item.get("matched", ""), item.get("keywords", "")]))
        tags = self.lib.all_tags()
        current_tag = self.tag_menu.get()
        self.tag_menu.configure(values=["Tüm etiketler"] + tags)
        if current_tag not in tags:
            self.tag_menu.set("Tüm etiketler")

        no_range = parse_no_range(self.search.get())        # '#120-220': kayıt numarası aralığı
        words = [] if no_range else [w for w in fold(self.search.get()).split() if w]
        extra = set()
        if words:
            extra |= self.lib.card_text_ids(words)
            if self.fulltext_var.get():
                extra |= self.lib.fulltext_ids(words)
        tag = self.tag_menu.get()
        status = self.status_menu.get()
        kinds = self.TYPE_FILTERS.get(self.type_menu.get())

        def type_ok(item):
            if kinds is None:
                return True
            if kinds == "thesis":
                return is_thesis(item)
            return item.get("type") in kinds and not (kinds == ("other",) and is_thesis(item))

        def visible(item):
            if no_range and not (no_range[0] <= (item.get("no") or 0) <= no_range[1]):
                return False
            if not type_ok(item):
                return False
            if words and not (all(w in item["_blob"] for w in words) or item["id"] in extra):
                return False
            if tag != "Tüm etiketler" and tag not in item["tags"]:
                return False
            return {"Tümü": True, "Yeni (taramadan)": item["is_new"], "PDF'i olanlar": item["has_pdf"],
                    "PDF'i olmayanlar": not item["has_pdf"], "Kartı olanlar": item["cards"] > 0,
                    "Scopus'taki dergiler": item["_scopus"] in ("aktif", "pasif")}[status]

        shown = [i for i in self.items if visible(i)]
        keys = {"author": lambda i: tr_sort_key(first_author_label(i)), "year": lambda i: i["year"] or "0",
                "title": lambda i: tr_sort_key(i["title"]), "tags": lambda i: tr_sort_key(", ".join(i["tags"])),
                "pdf": lambda i: i["has_pdf"], "added": lambda i: (i["added"], i.get("no") or 0, i["id"]),
                "no": lambda i: i.get("no") or 0,
                "scopus": lambda i: {"aktif": 2, "pasif": 1}.get(i["_scopus"], 0)}
        if no_range and self.sort_col == "added":
            shown.sort(key=keys["no"])
        else:
            shown.sort(key=keys[self.sort_col], reverse=self.sort_rev)
        self.tree.delete(*self.tree.get_children())
        for item in shown:
            tags_ = []
            if item["is_new"]:
                tags_.append("new")
            if not item["has_pdf"]:
                tags_.append("nopdf")
            mark = "📄" if item["has_pdf"] else "—"
            title = ("● " if item["is_new"] else "") + item["title"]
            self.tree.insert("", "end", iid=str(item["id"]), tags=tags_,
                             values=(item.get("no") or "", mark, first_author_label(item), item["year"], title,
                                     {"aktif": "✓", "pasif": "pasif", "cikarildi": "✗"}.get(item["_scopus"], ""),
                                     ", ".join(item["tags"])))
        keep = [s for s in selected if self.tree.exists(s)]
        if keep:
            self.tree.selection_set(keep)
            self.tree.see(keep[0])
        new = sum(1 for i in self.items if i["is_new"])
        nopdf = sum(1 for i in self.items if not i["has_pdf"])
        if kinds is not None:
            typed = [i for i in self.items if type_ok(i)]
            label = self.type_menu.get().replace(" (hepsi)", "").lower()
            self.count_label.configure(text=f"{len(shown)} / {len(self.items)} kaynak · {len(typed)} {label} "
                                            f"(PDF'siz: {sum(1 for i in typed if not i['has_pdf'])})")
        else:
            self.count_label.configure(text=f"{len(shown)} / {len(self.items)} kaynak · {new} yeni · {nopdf} PDF'siz")
        shown_new = sum(1 for i in shown if i["is_new"])
        self.allseen_btn.configure(text=f"Yenileri İncelendi Say ({shown_new})" if shown_new else "Yenileri İncelendi Say",
                                   state="normal" if shown_new else "disabled")
        if not keep:
            self._show(None)
        if to_check:
            self._check_files(to_check)

    def _check_files(self, pairs):
        """PDF'lerin gerçekten yerinde olup olmadığını arka planda yoklar (Drive yavaşken arayüz donmasın);
        gösterilenden farklı çıkan olursa listeyi tazeler."""
        running = getattr(self, "_file_checker", None)
        if running is not None and running.is_alive():
            return
        events = self.app.events

        def work():
            differs = False
            for path, shown in pairs:
                try:
                    ok = os.path.isfile(path)
                except OSError:
                    ok = False
                _EXISTS_CACHE[str(path)] = (ok, time.monotonic())
                differs = differs or ok != shown
            if differs:
                events.put(("files_checked",))

        self._file_checker = threading.Thread(target=work, name="pdf-yoklama", daemon=True)
        self._file_checker.start()

    def _sort(self, col):
        if self.sort_col == col:
            self.sort_rev = not self.sort_rev
        else:
            self.sort_col, self.sort_rev = col, col in ("year", "pdf", "scopus")
            if col == "no":
                self.sort_col, self.sort_rev = "no", False
        self.refresh()

    def select(self, item_id):
        key = str(item_id)
        if self.tree.exists(key):
            self.tree.selection_set(key)
            self.tree.see(key)

    def selected_items(self):
        return [self.by_id[int(i)] for i in self.tree.selection() if int(i) in self.by_id]

    def _on_select(self):
        items = self.selected_items()
        self._show(items[0] if len(items) == 1 else None, multiple=len(items) > 1)

    # ── detay paneli ────────────────────────────────────────────────────────
    def _show(self, item, multiple=False):
        self.current = item
        self._reset_card_form()
        state = "normal" if item else "disabled"
        for btn in (self.save_btn, self.crossref_btn, self.attach_btn, self.inst_btn, self.reviewed_btn,
                    self.remove_btn, self.card_save, self.search_menu, self.notes_btn):
            btn.configure(state=state)
        db = database_for_doi(item["doi"]) if item else ""
        self.vetis_btn.configure(text=f"VETİS → {db}" if db else "VETİS (kampüs dışı)")
        if multiple:
            self.remove_btn.configure(state="normal")
            self.reviewed_btn.configure(state="normal")
        self.f_title.delete("1.0", "end")
        for entry in self.f.values():
            entry.delete(0, "end")
        for w in self.cards_frame.winfo_children():
            w.destroy()
        self.apa_box.configure(state="normal")
        self.apa_box.delete("1.0", "end")
        self.apa_box.configure(state="disabled")
        if not item:
            self.pdf_label.configure(text=f"{len(self.tree.selection())} kaynak seçili" if multiple
                                     else "Bir kaynak seçin", text_color=TEXT)
            self.matched_label.configure(text="")
            self.open_btn.configure(state="disabled")
            self.show_btn.configure(state="disabled")
            return
        has_pdf = item["has_pdf"] if "has_pdf" in item else file_exists_cached(item["file_path"])
        self.open_btn.configure(state="normal" if has_pdf else "disabled")
        self.show_btn.configure(state="normal" if has_pdf else "disabled")
        self.attach_btn.configure(text="PDF'i Değiştir…" if has_pdf else "PDF Bağla…")
        no = f"No {item.get('no')} · " if item.get("no") else ""
        if has_pdf:
            self.pdf_label.configure(text=f"{no}📄 {Path(item['file_path']).name}", text_color=TEXT)
        else:
            db = database_for_doi(item["doi"])
            hint = f" · kurum erişimi: {db}" if db else ""
            tried = f" · son arama: {item['pdf_tried']}" if item.get("pdf_tried") else ""
            self.pdf_label.configure(text=f"{no}PDF yok{hint}{tried}", text_color=LOG_COLORS["warn"])
        self.f_title.insert("1.0", item["title"])
        values = dict(item, authors=people_to_text(item["authors"]), editors=people_to_text(item["editors"]),
                      tags=", ".join(item["tags"]))
        for key, entry in self.f.items():
            if values.get(key):
                entry.insert(0, values[key])
        self.f_type.set(ITEM_TYPES.get(item["type"], "Diğer"))
        info = []
        if item.get("source"):
            info.append({"tarama": "Haftalık taramadan", "geçmiş tarama": "Geçmişe dönük taramadan", "içe aktarma": "Kaynakça dosyasından", "web sayfası": "Kaydedilmiş web sayfasından", "indirme": "İndiriciden", "klasör": "Klasör taramasından",
                         "elle": "Elle eklendi"}.get(item["source"], item["source"]))
        if item.get("added"):
            info.append(f"eklendi: {item['added']}")
        if item.get("matched"):
            info.append(f"eşleşen: {item['matched']}")
        sc = scopus_info(item)
        if sc:
            info.append(f"{SCOPUS_LABELS[sc[0]]}: {sc[1]}")
        elif load_scopus():
            info.append("Scopus listesinde bulunamadı")
        self.matched_label.configure(text=" · ".join(info))
        self.reviewed_btn.configure(state="normal" if item["is_new"] else "disabled")
        self._render_cards()
        self._render_apa()

    def _form_record(self):
        rec = {key: entry.get().strip() for key, entry in self.f.items()}
        rec["title"] = self.f_title.get("1.0", "end").strip()
        rec["authors"] = text_to_people(rec["authors"])
        rec["editors"] = text_to_people(rec["editors"])
        rec["type"] = TYPE_BY_LABEL.get(self.f_type.get(), "other")
        return rec

    def _save_record(self):
        if not self.current:
            return
        rec = self._form_record()
        tags = clean_tags(rec.pop("tags"))
        fixed = finalize_record(rec)
        fixed["title"] = rec["title"].strip().rstrip(".")       # kullanıcının yazımına dokunma
        self.lib.update(self.current["id"], {k: fixed[k] for k in RECORD_FIELDS})
        self.lib.set_tags(self.current["id"], tags)
        item_id = self.current["id"]
        # PDF'in adı yeni künyeye uysun
        item = self.lib.get(item_id)
        if item["file_path"] and Path(item["file_path"]).is_file():
            try:
                folder = self.app.library_folder()
                new_path = place_in_library(Path(item["file_path"]), item, folder or Path(item["file_path"]).parent)
                self.lib.update(item_id, {"file_path": str(new_path)})
            except OSError as exc:
                messagebox.showwarning(APP_NAME, f"Dosya yeniden adlandırılamadı:\n{exc}", parent=self.parent)
        self.refresh()
        self.select(item_id)
        self.app.toast("Künye kaydedildi.")

    def _render_summary(self, rec):
        self.summary_box.configure(state="normal")
        self.summary_box.delete("1.0", "end")
        self.summary_box.insert("1.0", (rec or {}).get("ai_ozet") or
                                "Bu kaynağın henüz Claude özeti yok.\n\nClaude Desktop'ta örneğin "
                                f"\"No {(rec or {}).get('no', '?')} numaralı kaynağı oku ve özetini kaydet\" "
                                "diyebilirsiniz; özet buraya ve arama dizinine girer.")
        self.summary_box.configure(state="disabled")

    def _render_apa(self):
        if not self.current:
            return
        rec = self.lib.get(self.current["id"])
        self._render_summary(rec)
        lang = "tr" if self.apa_lang.get() == "Türkçe" else "en"
        box = self.apa_box
        box.configure(state="normal")
        box.delete("1.0", "end")
        for text, italic in apa_segments(rec, lang):
            box._textbox.insert("end", text, ("i",) if italic else ())
        box._textbox.insert("end", "\n\nMetin içi atıf:  " + intext_citation(rec, "", lang))
        if is_shouting(rec["title"]) or any(w.isupper() and len(w) > 4 for w in rec["title"].split()):
            box._textbox.insert("end", "\n\n⚠ Başlıkta büyük harfle yazılmış kelimeler var; Künye sekmesinden düzeltebilirsiniz.")
        box.configure(state="disabled")

    def _copy_apa(self):
        if self.current:
            lang = "tr" if self.apa_lang.get() == "Türkçe" else "en"
            self._clip(apa_text(self.lib.get(self.current["id"]), lang))

    def _copy_intext(self):
        if self.current:
            lang = "tr" if self.apa_lang.get() == "Türkçe" else "en"
            self._clip(intext_citation(self.lib.get(self.current["id"]), "", lang))

    def _clip(self, text):
        self.parent.clipboard_clear()
        self.parent.clipboard_append(text)
        self.app.toast("Panoya kopyalandı.")

    # ── alıntı kartları ─────────────────────────────────────────────────────
    def _render_cards(self):
        for w in self.cards_frame.winfo_children():
            w.destroy()
        if not self.current:
            return
        rec = self.lib.get(self.current["id"])
        cards = self.lib.cards(rec["id"])
        if not cards:
            ctk.CTkLabel(self.cards_frame, text="Henüz kart yok. Aşağıdan sayfa, alıntı ve yorumunuzu yazıp ekleyin.",
                         text_color=MUTED, wraplength=360, justify="left").grid(row=0, column=0, sticky="w", pady=8)
        for row, card in enumerate(cards):
            box = ctk.CTkFrame(self.cards_frame, corner_radius=10, border_width=1)
            box.grid(row=row, column=0, sticky="ew", pady=4, padx=2)
            box.grid_columnconfigure(0, weight=1)
            head = f"s. {card['page']}" if card["page"] else "sayfa yok"
            ctk.CTkLabel(box, text=head, font=ctk.CTkFont(size=11, weight="bold"),
                         text_color=MUTED).grid(row=0, column=0, sticky="w", padx=10, pady=(6, 0))
            if card["quote"]:
                ctk.CTkLabel(box, text=f"“{card['quote']}”", wraplength=280, justify="left",
                             anchor="w").grid(row=1, column=0, sticky="ew", padx=10)
            if card["comment"]:
                ctk.CTkLabel(box, text=f"→ {card['comment']}", wraplength=280, justify="left", anchor="w",
                             text_color=MUTED, font=ctk.CTkFont(size=12)).grid(row=2, column=0, sticky="ew", padx=10)
            btns = ctk.CTkFrame(box, fg_color="transparent")
            btns.grid(row=3, column=0, sticky="w", padx=6, pady=(2, 6))
            ctk.CTkButton(btns, text="Atıfla Kopyala", width=110, height=24, font=ctk.CTkFont(size=11),
                          command=lambda c=card: self._clip(card_citation_text(c, rec))).pack(side="left", padx=2)
            ctk.CTkButton(btns, text="Düzenle", width=70, height=24, font=ctk.CTkFont(size=11),
                          fg_color="transparent", border_width=1, text_color=TEXT,
                          command=lambda c=card: self._edit_card(c)).pack(side="left", padx=2)
            ctk.CTkButton(btns, text="Sil", width=46, height=24, font=ctk.CTkFont(size=11),
                          fg_color="transparent", border_width=1, text_color="#C9353A", border_color="#C9353A",
                          command=lambda c=card: self._delete_card(c)).pack(side="left", padx=2)
        n = len(cards)
        self.detail_tabs._segmented_button._buttons_dict["Alıntı Kartları"].configure(
            text=f"Alıntı Kartları ({n})" if n else "Alıntı Kartları")

    def _reset_card_form(self):
        self.editing_card = None
        self.card_page.delete(0, "end")
        self.card_quote.delete("1.0", "end")
        self.card_comment.delete("1.0", "end")
        self.card_save.configure(text="Kartı Ekle")

    def _edit_card(self, card):
        self._reset_card_form()
        self.editing_card = card["id"]
        self.card_page.insert(0, card["page"])
        self.card_quote.insert("1.0", card["quote"])
        self.card_comment.insert("1.0", card["comment"])
        self.card_save.configure(text="Kartı Güncelle")

    def _save_card(self):
        if not self.current:
            return
        page = self.card_page.get()
        quote = self.card_quote.get("1.0", "end").strip()
        comment = self.card_comment.get("1.0", "end").strip()
        if not quote and not comment:
            return
        if self.editing_card:
            self.lib.update_card(self.editing_card, page, quote, comment)
        else:
            self.lib.add_card(self.current["id"], page, quote, comment)
        self._reset_card_form()
        self._render_cards()

    def _delete_card(self, card):
        if messagebox.askyesno(APP_NAME, "Bu alıntı kartı silinsin mi?", parent=self.parent):
            self.lib.delete_card(card["id"])
            self._render_cards()

    # ── eylemler ────────────────────────────────────────────────────────────
    def _open_pdf(self):
        item = self.current
        if item and item["file_path"] and Path(item["file_path"]).is_file():
            try:
                open_file(Path(item["file_path"]))
            except Exception as exc:
                messagebox.showerror(APP_NAME, f"PDF açılamadı:\n{exc}", parent=self.parent)

    def _show_pdf(self):
        item = self.current
        if item and item["file_path"] and Path(item["file_path"]).is_file():
            show_in_file_manager(Path(item["file_path"]))

    def _open_institution(self):
        """Makalenin (ya da tezin) sayfasını açar; soru sormaz."""
        item = self.current
        if not item:
            return
        webbrowser.open_new_tab(item_open_link(item))
        if yok_tez_no(item):
            note = "Tez, YÖK Tez Merkezi'nde açıldı. PDF simgesine tıklayın"
        else:
            db = database_for_doi(item["doi"])
            note = "Makale açıldı. PDF'i indirin" + (f" (kampüs dışındaysanız 'VETİS → {db}')" if db else "")
        self.app.toast(note + "; dosya bu kaynağa kendiliğinden bağlanır.")

    def _open_vetis(self):
        """Kampüs dışından erişim için kurum erişim sayfasını açar."""
        portal = self.app.settings.get("institution_url") or DEFAULT_INSTITUTION_URL
        webbrowser.open_new_tab(portal)
        item = self.current
        db = database_for_doi(item["doi"]) if item else ""
        self.app.toast("VETİS açıldı. Giriş yapıp " + (f"“{db}” veritabanında" if db else "ilgili veritabanında")
                       + " makaleyi arayın; indirdiğiniz PDF bu kaynağa kendiliğinden bağlanır.")

    def _attach_pdf(self):
        item = self.current
        if not item:
            return
        path = filedialog.askopenfilename(parent=self.parent, title="Bu kaynağın PDF'ini ya da e-kitabını seçin",
                                          filetypes=[("PDF ve EPUB", "*.pdf *.epub"), ("Tüm dosyalar", "*.*")])
        if not path:
            return
        move = messagebox.askyesno(APP_NAME, "Dosya kütüphane klasörüne TAŞINSIN mı?\n"
                                             "(Hayır derseniz kopyalanır, aslı yerinde kalır.)", parent=self.parent)
        try:
            attach_pdf(self.lib, item["id"], path, self.app.library_folder(), move=move)
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"PDF bağlanamadı:\n{exc}", parent=self.parent)
            return
        self.refresh()
        self.select(item["id"])

    def _refresh_from_doi(self):
        item = self.current
        doi = normalize_doi(self.f["doi"].get()) if item else None
        if not doi:
            messagebox.showinfo(APP_NAME, "Önce DOI alanını doldurun.", parent=self.parent)
            return
        self.crossref_btn.configure(state="disabled", text="Alınıyor…")

        def work():
            session = make_session()
            rec = crossref_record(session, doi)
            session.close()
            self.app.events.put(("crossref_done", item["id"], rec))
        threading.Thread(target=work, daemon=True).start()

    def crossref_done(self, item_id, rec):
        self.crossref_btn.configure(state="normal", text="Künyeyi DOI'den Al")
        if not rec:
            messagebox.showwarning(APP_NAME, "Crossref bu DOI için künye döndürmedi.", parent=self.parent)
            return
        rec = finalize_record(rec)
        self.lib.update(item_id, {k: rec[k] for k in RECORD_FIELDS if rec.get(k)})
        self.refresh()
        self.select(item_id)
        self.app.toast("Künye Crossref'ten güncellendi.")

    def _mark_reviewed(self):
        self.lib.mark_reviewed([item["id"] for item in self.selected_items()])
        self.refresh()

    def _tool_chosen(self, choice):
        self.tools_menu.set("Araçlar ▾")
        if choice.startswith("Atıf"):
            win = getattr(self, "cite_win", None)
            if win is not None and win.winfo_exists():
                win.lift()
            else:
                self.cite_win = CitationWindow(self.app)
        elif choice.startswith("Mükerrer"):
            DuplicatesWindow(self.app)
        elif choice.startswith("PDF"):
            self._import_highlights()
        elif choice.startswith("Künyeyi"):
            self._reextract()

    def _reextract(self):
        worker = getattr(self.app, "rx_worker", None)
        if worker and worker.is_alive():
            self.app.toast("Künyeler zaten çıkarılıyor.")
            return
        with_pdf = [i for i in self.selected_items() if (i.get("file_path") or "").lower().endswith(".pdf")]
        if not with_pdf:
            bad = [i for i in self.items if (i.get("file_path") or "").lower().endswith(".pdf") and title_looks_bad(i)]
            if not bad:
                messagebox.showinfo(APP_NAME, "Tabloda PDF'li kayıt seçin; seçtiklerinizin künyesi PDF'ten yeniden "
                                              "çıkarılıp önizlemede gösterilir.\n\n(Başlığı dosya adı gibi görünen "
                                              "kayıt bulunamadı.)", parent=self.parent)
                return
            if not messagebox.askokcancel(
                    APP_NAME, f"Seçili kayıt yok. Başlığı dosya adından kalmış gibi görünen {len(bad)} PDF'li kayıt "
                              f"(No {no_ranges_text([i.get('no') for i in bad], 6)}) yeniden çıkarılsın mı?\n\n"
                              "Önce önizleme gösterilir; siz onaylamadan hiçbir şey değişmez.", parent=self.parent):
                return
            with_pdf = bad
        self.app.rx_worker = ReextractWorker(with_pdf, self.app.events)
        self.app.rx_worker.start()

    def on_reextract_done(self, found, stopped):
        self.refresh()
        if not found:
            self.app.toast(("Durduruldu. " if stopped else "") + "PDF'lerden daha iyi bir künye çıkmadı.")
            return
        ReextractWindow(self.app, found)

    def _import_highlights(self):
        worker = getattr(self.app, "hl_worker", None)
        if worker and worker.is_alive():
            self.app.toast("İşaretlemeler zaten aktarılıyor.")
            return
        if not messagebox.askokcancel(
                APP_NAME, "Kütüphanedeki PDF'lerde Acrobat, Edge ya da başka bir okuyucuyla yaptığınız vurgular, "
                          "altı çizili yerler ve notlar sayfa numarasıyla alıntı kartlarına aktarılacak.\n\n"
                          "Her PDF bir kez okunur (ilk seferde biraz sürebilir, arka planda çalışır); sonra yalnızca "
                          "değişen dosyalara bakılır. Aynı kart iki kez eklenmez.", parent=self.parent):
            return
        self.app.hl_worker = HighlightWorker(self.lib, self.app.events)
        self.app.hl_worker.start()

    def on_highlights_done(self, added, sources, stopped):
        self.refresh()
        msg = (f"{sources} kaynaktaki {added} işaretleme alıntı kartı olarak eklendi." if added
               else "Yeni işaretleme bulunamadı.")
        self.app.toast(("Durduruldu. " if stopped else "") + msg)
        self.app._log("success" if added else "info", "PDF işaretlemeleri: " + msg)

    def _mark_all_reviewed(self):
        """Listede görünen bütün 'yeni' kaynakları tek seferde incelendi sayar."""
        new = [self.by_id[int(i)] for i in self.tree.get_children()
               if int(i) in self.by_id and self.by_id[int(i)]["is_new"]]
        if not new:
            messagebox.showinfo(APP_NAME, "Listede 'yeni' işaretli kaynak yok.", parent=self.parent)
            return
        total_new = sum(1 for i in self.items if i["is_new"])
        scope = "Listede görünen" if len(new) < total_new else "Bütün"
        if not messagebox.askokcancel(
                APP_NAME, f"{scope} {len(new)} yeni kaynak 'incelendi' sayılacak: kalın yazı ve ● işareti kalkar.\n\n"
                          "Künye, PDF ve etiketler değişmez; kaynaklar kütüphanede kalır."
                          + (f"\n\n(Listede görünmeyen {total_new - len(new)} yeni kaynağa dokunulmaz.)"
                             if len(new) < total_new else ""), parent=self.parent):
            return
        self.lib.mark_reviewed([i["id"] for i in new])
        self.refresh()
        self.app.toast(f"{len(new)} kaynak incelendi sayıldı.")

    def _remove(self):
        items = self.selected_items()
        if not items:
            return
        with_pdf = [i for i in items if i["file_path"] and Path(i["file_path"]).is_file()]
        msg = f"{len(items)} kaynak kütüphaneden çıkarılsın mı?"
        if with_pdf:
            msg += f"\n\n{len(with_pdf)} tanesinin PDF dosyası da silinsin mi?\nEvet: PDF'ler de silinir · Hayır: PDF'ler klasörde kalır"
            answer = messagebox.askyesnocancel(APP_NAME, msg, parent=self.parent)
            if answer is None:
                return
        else:
            if not messagebox.askyesno(APP_NAME, msg, parent=self.parent):
                return
            answer = False
        for item in items:
            if answer and item in with_pdf:
                try:
                    Path(item["file_path"]).unlink()
                except OSError:
                    pass
            self.lib.delete(item["id"])
        self.refresh(keep_selection=False)

    def _add_pdfs(self):
        paths = filedialog.askopenfilenames(parent=self.parent, title="Kütüphaneye eklenecek PDF'ler ve e-kitaplar",
                                            filetypes=[("PDF ve e-kitap", "*.pdf *.epub *.acsm"), ("PDF", "*.pdf"),
                                                       ("E-kitap (EPUB, ödünç bileti ACSM)", "*.epub *.acsm")])
        if paths:
            self._start_import(paths)

    def _pdfless_lists(self):
        """(tüm PDF'sizler, listede görünen PDF'sizlerin kimlikleri, seçili PDF'sizler) — numara sırasıyla."""
        nopdf = sorted((i for i in self.items if not i.get("has_pdf")), key=lambda i: i.get("no") or 0)
        visible = {int(i) for i in self.tree.get_children()}
        chosen = self.selected_items()
        chosen = [i for i in nopdf if i["id"] in {c["id"] for c in chosen}] if len(chosen) > 1 else []
        return nopdf, visible, chosen

    def _ask_range(self, purpose, on_start):
        """Hangi kayıt numaralarının işleneceğini soran pencereyi açar."""
        nopdf, visible, chosen = self._pdfless_lists()
        if not nopdf:
            messagebox.showinfo(APP_NAME, "Kütüphanede PDF'i olmayan kaynak yok.", parent=self.parent)
            return
        old = getattr(self, "range_dialog", None)
        if old is not None and old.winfo_exists():
            old.destroy()
        self.range_dialog = RangeDialog(self.app, purpose, nopdf, visible, chosen, on_start)

    def _retry_pdfs(self):
        """PDF'siz kaynakların PDF'ini tek tuşla yeniden arar (açık erişim, yayıncı sayfası, YÖK)."""
        worker = getattr(self, "retry_worker", None)
        if worker and worker.is_alive():
            worker.cancel.set()
            self.retry_btn.configure(text="Durduruluyor…", state="disabled")
            return
        if not self.app.library_folder():
            self.app.choose_library_folder()
            if not self.app.library_folder():
                return
        self._ask_range("retry", self._start_retry)

    def _start_retry(self, items, label, rng):
        self._retry_run = (label, rng)
        email = self.app.email_entry.get().strip()
        self.retry_worker = PdfRetryWorker(items, self.lib, self.app.events, self.app.library_folder(), email,
                                           label=label)
        self.retry_btn.configure(text="Durdur", fg_color="#C9353A", hover_color="#A42A2E")
        self.app._log("info", f"PDF yeniden arama başladı: {label} ({len(items)} kaynak).")
        self.retry_worker.start()

    def on_retry_done(self, found, tried, stopped, found_nos=(), tried_nos=(), deferred_nos=(), report=""):
        self.retry_btn.configure(text="PDF'leri Yeniden Ara", state="normal", fg_color="#1F8F4E",
                                 hover_color="#18723E")
        label, rng = getattr(self, "_retry_run", ("", None))
        last = max(tried_nos, default=0)
        if rng:                                      # bir sonraki sefer kalınan yerden başlasın
            remember_setting("retry_next_no", (last + 1) if stopped and last else rng[1] + 1)
        self.refresh()
        where = f"{label}: " if label else ""
        msg = f"{where}{tried} kaynak denendi, {found} tanesinin PDF'i bulunup bağlandı"
        msg += f" (No {no_ranges_text(found_nos, 8)})." if found_nos else "."
        if stopped:
            msg = f"Durduruldu — No {last}'e kadar denendi. " + msg if last else "Durduruldu. " + msg
        if deferred_nos:
            msg += (f" {len(deferred_nos)} kaynakta site 'çok fazla istek' dediği için arama ertelendi "
                    f"(No {no_ranges_text(deferred_nos, 6)}); bunlar 'denenmedi' sayılır, bir süre sonra "
                    "aynı aralıkla yeniden başlatın.")
        if tried - found - len(deferred_nos) > 0:
            msg += " Kalanlar için 'PDF'sizleri Sırayla Aç'ı aynı aralıkla kullanabilirsiniz."
        self.app.toast(msg)
        missing = sorted(set(tried_nos) - set(found_nos))
        self.app._log("success" if found else "info", "PDF yeniden arama: " + msg +
                      (f" Bulunamayanlar: No {no_ranges_text(missing)}." if missing else ""))
        if report and Path(report).is_file():
            self.app._log("muted", f"Rapor: {report}")
            self.app.notify_report(report, f"PDF arama: {tried} arandı, {found} bulundu")
        left = [i for i in self.items if (i.get("no") or 0) in set(missing) - set(deferred_nos)
                and not i.get("has_pdf")]
        queue_open = getattr(self.app, "pdf_queue", None) is not None and self.app.pdf_queue.winfo_exists()
        if left and not stopped and not queue_open and messagebox.askyesno(
                APP_NAME, f"{msg}\n\nBulunamayan {len(left)} kaynak (No {no_ranges_text([i.get('no') for i in left], 6)}) "
                          "Google Akademik'te başlıkla sırayla açılsın mı?\n\nGoogle otomatik aramaya izin "
                          "vermediği için bu adımı siz yaparsınız: sonuçlarda [PDF] bağlantısı varsa tıklayıp "
                          "indirin, program dosyayı kaynağa bağlayıp bir sonrakini açar; yoksa 'Atla'.",
                parent=self.parent):
            self.app.pdf_queue = PdfQueuePanel(self.app, left, f"{label} · Google Akademik", open_mode="scholar")

    def _open_queue(self):
        """Seçilen numara aralığındaki PDF'siz kaynakları sırayla açar."""
        if getattr(self.app, "pdf_queue", None) is not None and self.app.pdf_queue.winfo_exists():
            self.app.pdf_queue.lift()
            return
        if not self.app.library_folder():
            self.app.choose_library_folder()
            if not self.app.library_folder():
                return
        self._ask_range("queue", lambda items, label, rng: setattr(
            self.app, "pdf_queue", PdfQueuePanel(self.app, items, label,
                                                 open_mode=getattr(self.range_dialog, "open_mode_value", "page"))))

    def _add_isbn(self):
        """Kitap ekleme: ISBN ya da çevrimiçi okunan kitabın bağlantısı (bağlantı kayıtta kalır)."""
        dialog = ctk.CTkInputDialog(title="Kitap ekle (ISBN ya da bağlantı)",
                                    text="Kitabın ISBN'ini ya da çevrimiçi okunduğu sayfanın adresini yapıştırın "
                                         "(birden çok olabilir).\nKünye bulunur, bağlantı kayıtta kalır; herkese açık "
                                         "kitapların dosyası ya da metni de alınır.\nGiriş isteyen platformlarda "
                                         "bağlantıyla birlikte ISBN'i de yazarsanız künye ISBN'den gelir.")
        set_window_icon(dialog, delay=260)
        text = dialog.get_input()
        if not text:
            return
        urls = list(dict.fromkeys(u.rstrip(".,;)") for u in re.findall(r"https?://\S+", text)))
        isbns = find_isbns(re.sub(r"https?://\S+", " ", text))
        if not isbns and not urls:
            messagebox.showwarning(APP_NAME, "Geçerli bir ISBN ya da bağlantı bulunamadı. ISBN'i 10 ya da 13 haneli, "
                                             "bağlantıyı https:// ile başlayarak yazın.", parent=self.parent)
            return
        answer = import_dialog(self.app, len(isbns) + len(urls), self.lib.all_tags(), show_move=False, unit="kitap")
        if answer is None:
            return
        _, tags, auto = answer
        self.isbn_btn.configure(state="disabled", text="Aranıyor…")
        lib, events, folder = self.lib, self.app.events, self.app.library_folder()

        def work():
            added, existing, missing = [], [], []
            session = make_session()
            try:
                pair = isbns[0] if len(urls) == 1 and len(isbns) == 1 else ""     # bağlantı + ISBN: aynı kitap
                for url in urls:
                    try:
                        item_id, created, access = add_online_book(lib, session, url, tags, folder, auto, isbn=pair)
                        (added if created else existing).append(item_id)
                        events.put(("log", "info", f"Kitap bağlantısı eklendi ({access}): {url}"))
                    except Exception as exc:
                        missing.append(shorten(url, 50))
                        diag(f"kitap bağlantısı {url}: {describe_error(exc)}")
                for isbn in ([] if pair else isbns):
                    rec = book_record_by_isbn(session, isbn)
                    if not rec.get("title"):
                        missing.append(isbn)
                        continue
                    found = lib.find_by_doi(rec.get("doi")) or lib.find_by_title(rec["title"])
                    if found:
                        lib.add_tags(found, tags)
                        existing.append(found)
                        continue
                    item_id, _ = lib.add(rec, tags=list(tags) + auto_group_tags(rec, "", auto), source="elle")
                    lib.update(item_id, {"notes": f"ISBN: {isbn}"})
                    added.append(item_id)
            except Exception:
                diag_exception("ISBN ile ekleme")
            finally:
                session.close()
            events.put(("isbn_done", added, existing, missing))

        threading.Thread(target=work, daemon=True).start()

    def on_isbn_done(self, added, existing, missing):
        self.isbn_btn.configure(state="normal", text="Kitap Ekle (ISBN / Bağlantı)…")
        self.refresh()
        if added:
            self.select(added[0])
        parts = [f"{len(added)} kitap eklendi"]
        if existing:
            parts.append(f"{len(existing)} tanesi zaten kütüphanedeydi")
        if missing:
            parts.append("bulunamayan: " + ", ".join(missing))
        self.app.toast("; ".join(parts) + ".")

    def _import_refs(self):
        paths = filedialog.askopenfilenames(
            parent=self.parent, title="Kaynakça dosyası seçin (Piri, Google Akademik, Zotero, EndNote…)",
            filetypes=[("Kaynakça (RIS, BibTeX)", "*.ris *.bib *.txt *.nbib *.enw"), ("Tüm dosyalar", "*.*")])
        if not paths:
            return
        answer = import_dialog(self.app, len(paths), self.lib.all_tags(), title="Kaynakça içe aktarılacak",
                               show_move=False, unit="dosya")
        if answer is None:
            return
        _, tags, auto = answer
        total_added = total_existing = 0
        errors = []
        for path in paths:
            try:
                added, existing, _ = import_references(self.lib, path, tags, auto)
                total_added += added
                total_existing += existing
            except Exception as exc:
                diag_exception(f"içe aktarma: {path}")
                errors.append(f"{Path(path).name}: {exc}")
        self.refresh()
        msg = f"{total_added} kaynak eklendi, {total_existing} tanesi zaten kütüphanedeydi."
        if total_added:
            msg += ("\n\nEklenenler PDF'siz durur. PDF'i için kaynağı seçip 'Makaleyi Aç'a basın (ya da 'PDF'sizleri Sırayla Aç'ı kullanın); "
                    "indirdiğiniz PDF İndirilenler'den kendiliğinden bağlanır. Açık erişimli olanların PDF'ini "
                    "geçmişe dönük tarama da yeniden dener.")
        if errors:
            msg += "\n\nOkunamayanlar:\n" + "\n".join(errors)
        messagebox.showinfo(APP_NAME, msg, parent=self.parent)

    def _scan_folder(self):
        folder = filedialog.askdirectory(parent=self.parent, title="PDF'lerin bulunduğu klasörü seçin")
        if not folder:
            return
        lib_folder = self.app.library_folder()
        pages = [p for p in sorted(Path(folder).rglob("*.htm*")) if p.suffix.lower() in (".html", ".htm")
                 and HTML_ARCHIVE_DIR not in p.parts]
        if pages and messagebox.askyesno(
                APP_NAME, f"Bu klasörde {len(pages)} kaydedilmiş web sayfası (.html) var.\n\n"
                          "Bunlar da kaynak olarak kütüphaneye eklensin ve PDF'leri yeniden aransın mı? "
                          f"Sayfalar kütüphane klasöründeki '{HTML_ARCHIVE_DIR}' klasörüne taşınır.",
                parent=self.parent):
            self._start_html(pages)
        paths = sorted(p for p in Path(folder).rglob("*") if p.suffix.lower() in (".pdf", ".epub")
                       and p.is_file())
        lib_folder = self.app.library_folder()
        if lib_folder:
            paths = [p for p in paths if Path(lib_folder) not in p.parents]
        if not paths:
            if not pages:
                messagebox.showinfo(APP_NAME, "Bu klasörde (kütüphane klasörü dışında) PDF ya da EPUB bulunamadı.",
                                    parent=self.parent)
            return
        self._start_import(paths, report_folders=[folder])

    def _start_html(self, pages):
        if not self.app.library_folder():
            self.app.choose_library_folder()
            if not self.app.library_folder():
                return
        answer = import_dialog(self.app, len(pages), self.lib.all_tags(), show_move=False, unit="web sayfası")
        if answer is None:
            return
        _, tags, auto = answer
        self.count_label.configure(text=f"{len(pages)} web sayfası işleniyor…")
        HtmlImportWorker(pages, self.lib, self.app.events, self.app.library_folder(),
                         email=self.app.email_entry.get().strip(), tags=tags, auto_tags=auto).start()

    def _start_import(self, paths, report_folders=()):
        answer = import_dialog(self.app, len(paths), self.lib.all_tags())
        if answer is None:
            return
        move, tags, auto = answer
        self.app.start_import(paths, tags, move, report_folders, auto_tags=auto)

    def _autotag(self):
        items = self.selected_items()
        scope = f"seçili {len(items)} kaynağa" if items else "kütüphanedeki tüm kaynaklara"
        if not messagebox.askyesno(
                APP_NAME, f"Anahtar kelimeler (PDF'lerden) ve grup etiketleri {scope} eklensin mi?\n\n"
                          "Elle verdiğiniz etiketler silinmez; yalnızca eşleşen grup adları eklenir.",
                parent=self.parent):
            return
        self.autotag_btn.configure(state="disabled", text="Etiketleniyor…")
        AutoTagWorker(self.lib, self.app.events, [i["id"] for i in items] if items else None).start()

    def _complete(self):
        """Bölüm sayfaları, kitap adı, editör, yayınevi, cilt/sayı gibi eksik alanları toplu tamamlar."""
        worker = getattr(self, "complete_worker", None)
        if worker and worker.is_alive():
            worker.cancel.set()
            self.complete_btn.configure(text="Durduruluyor…", state="disabled")
            return
        chosen = self.selected_items()
        pool = chosen if len(chosen) > 1 else [self.by_id[int(i)] for i in self.tree.get_children()
                                                if int(i) in self.by_id]
        items = [i for i in pool if missing_fields(i)]
        if not items:
            messagebox.showinfo(APP_NAME, "Listede eksik künye bilgisi olan kaynak yok.", parent=self.parent)
            return
        counts = {}
        for i in items:
            for f in missing_fields(i):
                counts[f] = counts.get(f, 0) + 1
        names = {"pages": "sayfa aralığı", "container": "dergi/kitap adı", "editors": "editör",
                 "publisher": "yayınevi", "volume": "cilt"}
        detail = ", ".join(f"{names.get(k, k)}: {v}" for k, v in sorted(counts.items(), key=lambda kv: -kv[1]))
        scope = "seçili" if len(chosen) > 1 else "listede görünen"
        if not messagebox.askokcancel(
                APP_NAME, f"{scope.capitalize()} {len(items)} kaynakta eksik künye bilgisi var ({detail}).\n\n"
                          "Eksikler Crossref'ten (DOI ya da başlık+yazar+yıl ile), bölümlerde üst kitabın "
                          "kaydından ve PDF'in sayfa numaralarından tamamlanacak. Doldurduğunuz alanlara "
                          "dokunulmaz.", parent=self.parent):
            return
        self.complete_worker = CompleteWorker(items, self.lib, self.app.events)
        self._complete_style = {k: self.complete_btn.cget(k) for k in ("fg_color", "hover_color", "text_color")}
        self.complete_btn.configure(text="Durdur", fg_color="#C9353A", hover_color="#A42A2E", text_color="#ffffff")
        self.complete_worker.start()

    def on_complete_done(self, updated, counts, tried, stopped):
        self.complete_btn.configure(text="Eksik Künyeleri Tamamla", state="normal",
                                    **getattr(self, "_complete_style", {}))
        self.refresh()
        names = {"pages": "sayfa", "container": "dergi/kitap adı", "editors": "editör", "publisher": "yayınevi",
                 "volume": "cilt", "issue": "sayı", "doi": "DOI", "issn": "ISSN", "year": "yıl", "type": "tür"}
        detail = ", ".join(f"{v} {names.get(k, k)}" for k, v in sorted(counts.items(), key=lambda kv: -kv[1]))
        msg = (f"{tried} kaynağa bakıldı, {len(updated)} tanesi tamamlandı"
               + (f" ({detail}; No {no_ranges_text(updated, 8)})." if updated else "."))
        if stopped:
            msg = "Durduruldu. " + msg
        if tried > len(updated):
            msg += " Bulunamayanlar Crossref'te kayıtlı değil; onları künye alanlarından elle doldurabilirsiniz."
        self.app.toast(msg)
        self.app._log("success" if updated else "info", "Künye tamamlama: " + msg)

    def autotag_finished(self, total, tagged, kw_added):
        self.autotag_btn.configure(state="normal", text="Otomatik Etiketle")
        self.refresh()
        self.app.toast(f"{total} kaynak incelendi: {tagged} tanesine grup etiketi, {kw_added} tanesine anahtar kelime eklendi.")

    def _bibliography(self, selected=True):
        items = self.selected_items() if selected else [self.by_id[int(i)] for i in self.tree.get_children()]
        if not items:
            messagebox.showinfo(APP_NAME, "Önce tablodan kaynak seçin.", parent=self.parent)
            return
        self.bib_dialog = BibliographyDialog(self.parent, [self.lib.get(i["id"]) for i in items])

    def _export(self):
        items = self.selected_items() or [self.by_id[int(i)] for i in self.tree.get_children()]
        if not items:
            return
        path = filedialog.asksaveasfilename(
            parent=self.parent, title=f"{len(items)} kaynağı dışa aktar", initialfile="kutuphanem.bib",
            defaultextension=".bib", filetypes=[("BibTeX (Jenni, Zotero, Overleaf)", "*.bib"),
                                                ("RIS (Zotero, Mendeley, EndNote)", "*.ris")])
        if not path:
            return
        records = [self.lib.get(i["id"]) for i in items]
        text = to_ris(records) if path.lower().endswith(".ris") else to_bibtex(records)
        Path(path).write_text(text, encoding="utf-8")
        self.app.toast(f"{len(items)} kaynak dışa aktarıldı: {Path(path).name}")


class ScanTab:
    """'Tarama' sekmesi: anahtar kelime grupları, haftalık tarama, rapor ve ayarlar."""

    HOURS = [f"{h:02d}:00" for h in range(6, 24)]

    def __init__(self, parent, app):
        self.app = app
        self.parent = parent
        self.worker = None
        self.cancel = threading.Event()
        parent.grid_columnconfigure(0, weight=3)
        parent.grid_columnconfigure(1, weight=2)
        parent.grid_rowconfigure(0, weight=1)
        self._build_keywords()
        self._build_side()
        self.update_info()

    def _build_keywords(self):
        card = ctk.CTkFrame(self.parent, corner_radius=12)
        card.grid(row=0, column=0, sticky="nsew", padx=(8, 6), pady=4)
        card.grid_columnconfigure(0, weight=1)
        card.grid_rowconfigure(2, weight=1)
        ctk.CTkLabel(card, text="Anahtar kelime grupları", font=self.app.font_section,
                     anchor="w").grid(row=0, column=0, sticky="ew", padx=16, pady=(14, 0))
        ctk.CTkLabel(card, text="[Grup adı] ile yeni grup başlar; her satır bir terim. 'bağlam:' satırı çok anlamlı "
                                "terimler için yanında geçmesi gereken kelimeleri belirtir. Grup adı, bulunan "
                                "yayınlara etiket olarak verilir.", text_color=MUTED, font=ctk.CTkFont(size=12),
                     wraplength=560, justify="left", anchor="w").grid(row=1, column=0, sticky="ew", padx=16)
        self.kw_box = ctk.CTkTextbox(card, font=self.app.font_log, wrap="none", border_width=1)
        self.kw_box.grid(row=2, column=0, sticky="nsew", padx=16, pady=8)
        self.kw_box.insert("1.0", load_keywords_text())
        self.kw_box.bind("<KeyRelease>", lambda _: self._count_terms())
        row = ctk.CTkFrame(card, fg_color="transparent")
        row.grid(row=3, column=0, sticky="ew", padx=16, pady=(0, 14))
        ctk.CTkButton(row, text="Kaydet", width=90, command=self._save_keywords).pack(side="left")
        ctk.CTkButton(row, text="Varsayılana Dön", width=130, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=self._reset_keywords).pack(side="left", padx=8)
        self.kw_info = ctk.CTkLabel(row, text="", text_color=MUTED, font=ctk.CTkFont(size=12))
        self.kw_info.pack(side="left", padx=8)
        self._count_terms()

    def _build_side(self):
        side = ctk.CTkScrollableFrame(self.parent, corner_radius=12)
        side.grid(row=0, column=1, sticky="nsew", padx=(6, 8), pady=4)
        side.grid_columnconfigure(0, weight=1)
        s = self.app.settings
        r = 0

        def section(text):
            nonlocal r
            ctk.CTkLabel(side, text=text, font=self.app.font_section, anchor="w").grid(
                row=r, column=0, sticky="ew", padx=10, pady=(14 if r else 6, 4))
            r += 1

        section("Haftalık tarama")
        self.info_label = ctk.CTkLabel(side, text="", anchor="w", justify="left", wraplength=330)
        self.info_label.grid(row=r, column=0, sticky="ew", padx=10); r += 1
        btns = ctk.CTkFrame(side, fg_color="transparent")
        btns.grid(row=r, column=0, sticky="ew", padx=10, pady=6); r += 1
        btns.grid_columnconfigure(0, weight=1)
        self.scan_btn = ctk.CTkButton(btns, text="Şimdi Tara", height=36, fg_color="#1F8F4E",
                                      hover_color="#18723E", command=self.start_scan)
        self.scan_btn.grid(row=0, column=0, sticky="ew")
        self.stop_btn = ctk.CTkButton(btns, text="Durdur", width=80, height=36, fg_color="#C9353A",
                                      hover_color="#A42A2E", state="disabled", command=self.stop_scan)
        self.stop_btn.grid(row=0, column=1, padx=(8, 0))
        self.progress = ctk.CTkProgressBar(side, height=10)
        self.progress.grid(row=r, column=0, sticky="ew", padx=10, pady=(2, 4)); r += 1
        self.progress.set(0)
        self.status_label = ctk.CTkLabel(side, text="", text_color=MUTED, anchor="w", justify="left",
                                         wraplength=330, font=ctk.CTkFont(size=12))
        self.status_label.grid(row=r, column=0, sticky="ew", padx=10); r += 1
        rep = ctk.CTkFrame(side, fg_color="transparent")
        rep.grid(row=r, column=0, sticky="ew", padx=10, pady=6); r += 1
        ctk.CTkButton(rep, text="Son Raporu Aç", width=130, command=self.open_last_report).pack(side="left")
        ctk.CTkButton(rep, text="Rapor Klasörü", width=110, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=self.open_report_folder).pack(side="left", padx=8)
        extra = ctk.CTkFrame(side, fg_color="transparent")
        extra.grid(row=r, column=0, sticky="w", padx=10); r += 1
        ctk.CTkButton(extra, text="Son 7 Günü Yeniden Tara", height=26, width=170, fg_color="transparent",
                      border_width=1, text_color=TEXT, font=ctk.CTkFont(size=12),
                      command=self.rescan_week).pack(side="left")
        ctk.CTkButton(extra, text="Tanılama Kaydını Aç", height=26, width=150, fg_color="transparent",
                      border_width=1, text_color=MUTED, font=ctk.CTkFont(size=12),
                      command=self.app.open_diagnostics).pack(side="left", padx=8)
        self.retro_btn = ctk.CTkButton(side, text="Geçmişe Dönük Tarama… (tüm literatür)", height=32,
                                       fg_color="#1F6F8B", hover_color="#185A71", command=self.open_retro)
        self.retro_btn.grid(row=r, column=0, sticky="ew", padx=10, pady=(8, 0)); r += 1

        section("Kendiliğinden çalışma")
        ctk.CTkLabel(side, text="Uygulama açıkken ya da açıldığında son taramanın üzerinden 7 gün "
                                "geçmişse tarama kendiliğinden başlar. Uygulama kapalıyken de taraması "
                                "için gün ve saati seçip kurulum komutunu bir kez Komut İstemi'nde "
                                "çalıştırın (isteğe bağlı).", text_color=MUTED,
                     font=ctk.CTkFont(size=12), wraplength=330, justify="left",
                     anchor="w").grid(row=r, column=0, sticky="ew", padx=10); r += 1
        when = ctk.CTkFrame(side, fg_color="transparent")
        when.grid(row=r, column=0, sticky="ew", padx=10, pady=6); r += 1
        self.day_menu = ctk.CTkOptionMenu(when, values=list(WEEKDAYS), width=118)
        self.day_menu.set(s.get("scan_day", "Pazartesi"))
        self.day_menu.grid(row=0, column=0)
        self.hour_menu = ctk.CTkOptionMenu(when, values=self.HOURS, width=84)
        self.hour_menu.set(s.get("scan_hour", "09:00"))
        self.hour_menu.grid(row=0, column=1, padx=6)
        ctk.CTkButton(when, text="Kurulum Komutunu Kopyala", width=208, command=self.schedule).grid(
            row=1, column=0, columnspan=2, pady=(6, 0), sticky="w")
        ctk.CTkButton(when, text="Kaldırma Komutu", width=118, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=self.unschedule).grid(row=2, column=0, pady=(6, 0), sticky="w")
        self.sched_label = ctk.CTkLabel(side, text="", text_color=MUTED, font=ctk.CTkFont(size=12),
                                        anchor="w", justify="left", wraplength=330)
        self.sched_label.grid(row=r, column=0, sticky="ew", padx=10); r += 1
        self.auto_var = ctk.BooleanVar(value=s.get("auto_scan", True))
        ctk.CTkCheckBox(side, text="Açılışta 7 gün geçmişse kendiliğinden tara", variable=self.auto_var,
                        command=self.app.save_all_settings).grid(row=r, column=0, sticky="w", padx=10, pady=3); r += 1
        self.open_report_var = ctk.BooleanVar(value=s.get("open_report", True))
        ctk.CTkCheckBox(side, text="Rapor hazır olunca tarayıcıda aç", variable=self.open_report_var,
                        command=self.app.save_all_settings).grid(row=r, column=0, sticky="w", padx=10, pady=3); r += 1

        section("Taranacak kaynaklar")
        self.src_dp = ctk.BooleanVar(value=s.get("scan_dergipark", True))
        self.src_cr = ctk.BooleanVar(value=s.get("scan_crossref", True))
        ctk.CTkCheckBox(side, text="DergiPark (Türkçe dergiler, resmî veri kapısı)", variable=self.src_dp,
                        command=self.app.save_all_settings).grid(row=r, column=0, sticky="w", padx=10, pady=3); r += 1
        ctk.CTkCheckBox(side, text="Crossref (uluslararası, DOI'li yayınlar)", variable=self.src_cr,
                        command=self.app.save_all_settings).grid(row=r, column=0, sticky="w", padx=10, pady=3); r += 1
        self.src_oa = ctk.BooleanVar(value=s.get("scan_openalex", True))
        ctk.CTkCheckBox(side, text="OpenAlex (kitap, bölüm, tez, kurum arşivleri)",
                        variable=self.src_oa, command=self.app.save_all_settings).grid(
            row=r, column=0, sticky="w", padx=10, pady=3); r += 1
        oak = ctk.CTkFrame(side, fg_color="transparent")
        oak.grid(row=r, column=0, sticky="w", padx=34, pady=(0, 3)); r += 1
        ctk.CTkLabel(oak, text="Ücretsiz anahtar:", text_color=MUTED, font=ctk.CTkFont(size=12)).pack(side="left")
        self.oa_key = ctk.CTkEntry(oak, width=130, height=26, show="•", placeholder_text="isteğe bağlı")
        self.oa_key.pack(side="left", padx=6)
        if s.get("openalex_api_key"):
            self.oa_key.insert(0, s["openalex_api_key"])
        for ev in ("<FocusOut>", "<Return>"):
            self.oa_key.bind(ev, lambda _e: self.app.save_all_settings())
        ctk.CTkButton(oak, text="Al", width=40, height=26, fg_color="transparent", border_width=1, text_color=TEXT,
                      command=lambda: webbrowser.open_new_tab(OPENALEX_KEY_PAGE)).pack(side="left")
        self.src_eric = ctk.BooleanVar(value=s.get("scan_eric", True))
        ctk.CTkCheckBox(side, text="ERIC (eğitim araştırmaları; çoğunun PDF'i açık)", variable=self.src_eric,
                        command=self.app.save_all_settings).grid(row=r, column=0, sticky="w", padx=10, pady=3); r += 1
        self.src_yok = ctk.BooleanVar(value=s.get("scan_yok", True))
        ctk.CTkCheckBox(side, text="YÖK Ulusal Tez Merkezi (yeni tezler, izinli olanların PDF'i)",
                        variable=self.src_yok, command=self.app.save_all_settings).grid(
            row=r, column=0, sticky="w", padx=10, pady=3); r += 1
        self.yok_skip_closed = ctk.BooleanVar(value=s.get("yok_skip_closed", True))
        ctk.CTkCheckBox(side, text="PDF'i yayımlanmamış tezleri kütüphaneye ekleme", variable=self.yok_skip_closed,
                        command=self.app.save_all_settings, font=ctk.CTkFont(size=12)).grid(
            row=r, column=0, sticky="w", padx=34, pady=(0, 3)); r += 1
        self.thesis_btn = ctk.CTkButton(side, text="PDF'siz tezleri kütüphaneden çıkar…", height=26, width=230,
                                        fg_color="transparent", border_width=1, text_color=TEXT,
                                        font=ctk.CTkFont(size=12), command=self.check_theses)
        self.thesis_btn.grid(row=r, column=0, sticky="w", padx=34, pady=(0, 6)); r += 1
        ctk.CTkLabel(side, text="Google Scholar uyarı e-postalarını İndir sekmesine yapıştırırsanız "
                                "içindeki makaleler de iner ve kütüphaneye girer.", text_color=MUTED,
                     font=ctk.CTkFont(size=12), wraplength=330, justify="left",
                     anchor="w").grid(row=r, column=0, sticky="ew", padx=10, pady=(2, 0)); r += 1

        section("Scopus listesi")
        ctk.CTkLabel(side, text="Elsevier'in Scopus kaynak listesini (Excel) bir kez yükleyin; dergisi Scopus'ta "
                                "olan kaynaklar kütüphanede ve raporlarda işaretlenir. Liste yılda iki kez "
                                "güncellenir.", text_color=MUTED, font=ctk.CTkFont(size=12), wraplength=330,
                     justify="left", anchor="w").grid(row=r, column=0, sticky="ew", padx=10); r += 1
        sc = ctk.CTkFrame(side, fg_color="transparent")
        sc.grid(row=r, column=0, sticky="w", padx=10, pady=6); r += 1
        self.scopus_btn = ctk.CTkButton(sc, text="Listeyi Yükle…", width=130, command=self.load_scopus_list)
        self.scopus_btn.pack(side="left")
        ctk.CTkButton(sc, text="İndirme Sayfası", width=120, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=lambda: webbrowser.open(SCOPUS_LIST_PAGE)).pack(side="left", padx=8)
        self.scopus_label = ctk.CTkLabel(side, text="", text_color=MUTED, font=ctk.CTkFont(size=12),
                                         anchor="w", justify="left", wraplength=330)
        self.scopus_label.grid(row=r, column=0, sticky="ew", padx=10); r += 1
        self.refresh_scopus_label()

        section("Claude bağlantısı")
        ctk.CTkLabel(side, text="Claude masaüstü uygulaması kütüphanenizde arama, etiketleme, alıntı kartı, "
                                "kaynakça ve PDF okuma yapabilir. Bağladıktan sonra Claude'u tamamen kapatıp "
                                "(sistem tepsisi → Quit) yeniden açın.", text_color=MUTED,
                     font=ctk.CTkFont(size=12), wraplength=330, justify="left",
                     anchor="w").grid(row=r, column=0, sticky="ew", padx=10); r += 1
        cl = ctk.CTkFrame(side, fg_color="transparent")
        cl.grid(row=r, column=0, sticky="w", padx=10, pady=6); r += 1
        ctk.CTkButton(cl, text="Claude'a Bağla", width=130, fg_color="#C15F3C", hover_color="#A34E30",
                      command=self.connect_claude).pack(side="left")
        ctk.CTkButton(cl, text="Ayarı Kopyala", width=110, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=self.copy_claude_config).pack(side="left", padx=8)
        self.index_label = ctk.CTkLabel(side, text="Claude için metin dizini: açılıştan kısa süre sonra denetlenir.",
                                        text_color=MUTED, font=ctk.CTkFont(size=12), wraplength=330,
                                        justify="left", anchor="w")
        self.index_label.grid(row=r, column=0, sticky="ew", padx=10); r += 1
        self.index_btn = ctk.CTkButton(side, text="Dizini Şimdi Güncelle", height=26, width=170,
                                       fg_color="transparent", border_width=1, text_color=TEXT,
                                       font=ctk.CTkFont(size=12), command=self.update_index_clicked)
        self.index_btn.grid(row=r, column=0, sticky="w", padx=10, pady=(4, 6)); r += 1

        section("Kütüphane ayarları")
        lf = ctk.CTkFrame(side, fg_color="transparent")
        lf.grid(row=r, column=0, sticky="ew", padx=10); r += 1
        lf.grid_columnconfigure(0, weight=1)
        ctk.CTkEntry(lf, textvariable=self.app.folder_var, height=30).grid(row=0, column=0, sticky="ew")
        ctk.CTkButton(lf, text="Seç…", width=60, command=self.app.choose_library_folder).grid(row=0, column=1, padx=(6, 0))
        self.shared_var = ctk.BooleanVar(value=bool(s.get("shared_library")))
        ctk.CTkCheckBox(side, text="Ortak kütüphane (Google Drive: tüm bilgisayarlarımda)",
                        variable=self.shared_var, command=self.toggle_shared).grid(
            row=r, column=0, sticky="w", padx=10, pady=(8, 3)); r += 1
        sh = ctk.CTkFrame(side, fg_color="transparent")
        sh.grid(row=r, column=0, sticky="ew", padx=10); r += 1
        sh.grid_columnconfigure(0, weight=1)
        self.sync_label = ctk.CTkLabel(sh, text="", text_color=MUTED, font=ctk.CTkFont(size=12), anchor="w",
                                       justify="left", wraplength=240)
        self.sync_label.grid(row=0, column=0, sticky="ew")
        self.sync_btn = ctk.CTkButton(sh, text="Şimdi Eşitle", width=100, height=26, font=ctk.CTkFont(size=12),
                                      command=self.sync_clicked)
        self.sync_btn.grid(row=0, column=1, padx=(6, 0))
        self.refresh_sync_label()
        self.update_var = ctk.BooleanVar(value=s.get("auto_update", True))
        ctk.CTkCheckBox(side, text=f"Açılışta güncellemeleri al (şu an v{APP_VERSION})", variable=self.update_var,
                        command=self.app.save_all_settings).grid(row=r, column=0, sticky="w", padx=10, pady=(8, 3))
        r += 1
        self.autotag_var = ctk.BooleanVar(value=s.get("auto_tag", True))
        ctk.CTkCheckBox(side, text="Yeni gelen kaynaklara anahtar kelime ve grup etiketini otomatik ekle",
                        variable=self.autotag_var, command=self.app.save_all_settings).grid(
            row=r, column=0, sticky="w", padx=10, pady=(8, 3)); r += 1
        self.watch_var = ctk.BooleanVar(value=s.get("watch_downloads", True))
        ctk.CTkCheckBox(side, text="İndirilenler klasörünü izle (indirdiğim PDF'i doğru kaynağa bağla)",
                        variable=self.watch_var, command=self.app.save_all_settings).grid(
            row=r, column=0, sticky="w", padx=10, pady=(8, 3)); r += 1
        dlf = ctk.CTkFrame(side, fg_color="transparent")
        dlf.grid(row=r, column=0, sticky="ew", padx=10); r += 1
        dlf.grid_columnconfigure(0, weight=1)
        self.dl_label = ctk.CTkLabel(dlf, text="", text_color=MUTED, font=ctk.CTkFont(size=11), anchor="w",
                                     justify="left", wraplength=260)
        self.dl_label.grid(row=0, column=0, sticky="ew")
        ctk.CTkButton(dlf, text="Değiştir…", width=80, height=24, font=ctk.CTkFont(size=11),
                      fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.change_downloads).grid(row=0, column=1, padx=(6, 0))
        self.refresh_downloads_label()
        ctk.CTkLabel(side, text="Kurum erişim sayfası", font=ctk.CTkFont(size=12), text_color=MUTED,
                     anchor="w").grid(row=r, column=0, sticky="ew", padx=10, pady=(6, 0)); r += 1
        self.inst_entry = ctk.CTkEntry(side, height=30)
        self.inst_entry.insert(0, s.get("institution_url") or DEFAULT_INSTITUTION_URL)
        self.inst_entry.grid(row=r, column=0, sticky="ew", padx=10, pady=(0, 10)); r += 1
        self.inst_entry.bind("<FocusOut>", lambda _: self.app.save_all_settings())
        self.refresh_schedule_label()

    # ── anahtar kelimeler ───────────────────────────────────────────────────
    def _count_terms(self):
        groups = parse_keyword_groups(self.kw_box.get("1.0", "end"))
        text = f"{len(groups)} grup · {sum(len(g['terms']) for g in groups)} terim"
        if keywords_customized():
            text += " · v2.4'te daraltılmış yeni varsayılan liste var ('Varsayılana Dön')"
        self.kw_info.configure(text=text)

    def _save_keywords(self):
        text = self.kw_box.get("1.0", "end").rstrip() + "\n"
        if not parse_keyword_groups(text):
            messagebox.showwarning(APP_NAME, "En az bir [Grup] ve bir terim olmalı.", parent=self.parent)
            return
        save_keywords_text(text)
        self.app.toast("Anahtar kelimeler kaydedildi.")

    def _reset_keywords(self):
        if messagebox.askyesno(APP_NAME, "Anahtar kelimeler varsayılan listeye dönsün mü?", parent=self.parent):
            self.kw_box.delete("1.0", "end")
            self.kw_box.insert("1.0", DEFAULT_KEYWORDS)
            self._count_terms()

    # ── tarama ──────────────────────────────────────────────────────────────
    def update_info(self):
        s = load_settings()
        last = s.get("last_scan")
        if last:
            try:
                local = datetime.fromisoformat(last).replace(tzinfo=timezone.utc).astimezone()
                due = local + timedelta(days=SCAN_INTERVAL_DAYS)
                text = f"Son tarama: {local:%d.%m.%Y %H:%M} · sıradaki: {due:%d.%m.%Y}"
            except ValueError:
                text = "Son tarama: bilinmiyor"
        else:
            text = "Henüz tarama yapılmadı. İlk tarama son 7 günü kapsar."
        self.info_label.configure(text=text)

    def rescan_week(self):
        if messagebox.askyesno(APP_NAME, "Son 7 gün baştan taransın mı?\n(Kütüphanede zaten olan yayınlar "
                                         "yeniden eklenmez.)", parent=self.parent):
            self.start_scan(force_days=7)

    def open_retro(self):
        if self.worker and self.worker.is_alive():
            messagebox.showinfo(APP_NAME, "Şu an bir tarama sürüyor; bitince yeniden deneyin.", parent=self.parent)
            return
        RetroScanDialog(self.app, self)

    def start_scan(self, automatic=False, force_days=None, retro=None):
        if self.worker and self.worker.is_alive():
            return
        unsaved = self.kw_box.get("1.0", "end").rstrip() + "\n"
        if unsaved != load_keywords_text() and parse_keyword_groups(unsaved):
            save_keywords_text(unsaved)
        if not self.app.library_folder():
            self.app.choose_library_folder()
        self.app.save_all_settings()
        self.cancel = threading.Event()
        self.scan_btn.configure(state="disabled", text="Taranıyor…")
        self.stop_btn.configure(state="normal")
        self.progress.set(0)
        self.status_label.configure(text="Tarama başlıyor…" + (" (açılışta otomatik)" if automatic else ""))
        settings = load_settings()
        if force_days:
            settings["force_days"] = force_days
        if retro:
            settings["retro"] = retro
            self.status_label.configure(text=f"Geçmişe dönük tarama başlıyor ({retro_period_label(retro['years'])})…")
            self.retro_btn.configure(state="disabled")
        self.worker = ScanWorker(self.app.library, settings, self.app.events, self.cancel)
        self.worker.start()

    def stop_scan(self):
        self.cancel.set()
        self.stop_btn.configure(state="disabled")
        self.status_label.configure(text="Durduruluyor…")

    def on_status(self, text):
        self.status_label.configure(text=text)

    def on_progress(self, value):
        self.progress.set(max(0.0, min(1.0, value)))

    def on_finished(self, report, summary):
        self.retro_btn.configure(state="normal")
        self.scan_btn.configure(state="normal", text="Şimdi Tara")
        self.stop_btn.configure(state="disabled")
        self.status_label.configure(text=summary)
        self.update_info()
        self.app.library_tab.refresh()
        if report:
            self.app.notify_report(report, summary)
            if self.open_report_var.get():
                webbrowser.open(Path(report).as_uri())
        failed = list(dict.fromkeys(getattr(self.worker, "failed_theses", []) or []))
        if failed:
            self.app.after(800, lambda: self._offer_thesis_retry(failed))

    def _offer_thesis_retry(self, ids):
        lib_tab = self.app.library_tab
        items = [i for i in (self.app.library.get(x) for x in ids) if i and not i["file_path"]]
        running = getattr(lib_tab, "retry_worker", None)
        if not items or (running and running.is_alive()):
            return
        if messagebox.askyesno(APP_NAME, f"Taramada {len(items)} izinli tezin PDF'i YÖK Tez Merkezi'nden "
                                         "indirilemedi (site o an hata ya da beklenmedik bir sayfa döndürdü). "
                                         "Şimdi yeniden denensin mi?", parent=self.parent):
            lib_tab._start_retry(items, f"inmeyen {len(items)} tez", None)

    def open_last_report(self):
        report = load_settings().get("last_report")
        if report and Path(report).is_file():
            webbrowser.open(Path(report).as_uri())
        else:
            messagebox.showinfo(APP_NAME, "Henüz rapor yok.", parent=self.parent)

    def open_report_folder(self):
        folder = Path(self.app.library_folder() or settings_path().parent) / "Tarama Raporları"
        folder.mkdir(parents=True, exist_ok=True)
        open_in_file_manager(folder)

    # ── indirme klasörü ─────────────────────────────────────────────────────
    def refresh_downloads_label(self):
        self.dl_label.configure(text="İzlenen: " + " · ".join(str(f) for f in downloads_folders()))

    def change_downloads(self):
        path = filedialog.askdirectory(parent=self.parent, title="Tarayıcının PDF'leri kaydettiği klasör")
        if not path:
            return
        current = _load_settings_raw()
        current["downloads_folder"] = os.path.normpath(path)
        save_settings(current)
        self.app.settings = load_settings()
        self.refresh_downloads_label()
        self.app.toast("İndirme klasörü kaydedildi.")

    # ── ortak kütüphane ─────────────────────────────────────────────────────
    def refresh_sync_label(self):
        s = _load_settings_raw()
        if not s.get("shared_library"):
            self.sync_label.configure(text="Kapalı: kütüphane yalnızca bu bilgisayarda.", text_color=MUTED)
            self.sync_btn.configure(state="disabled")
            return
        self.sync_btn.configure(state="normal")
        if shared_dir(s) is None:
            self.sync_label.configure(text="Bulut klasörüne ulaşılamıyor (Google Drive açık mı?). Bu bilgisayarda "
                                           "çalışmaya devam edebilirsiniz.", text_color=LOG_COLORS["warn"])
            return
        last = (s.get("sync") or {}).get("last_sync")
        meta = self.app.sync.meta()
        who = f" · son gönderen: {meta['machine']}" if meta.get("machine") else ""
        self.sync_label.configure(text=f"Açık · son eşitleme: {last or '—'}{who}", text_color=LOG_COLORS["success"])

    def update_index_clicked(self):
        if self.app.update_index(manual=True):
            self.index_label.configure(text="Claude için metin dizini güncelleniyor…")
        else:
            self.app.toast("Dizin zaten güncelleniyor.")

    def on_index_done(self, stats, stopped):
        if not stats:
            self.index_label.configure(text="Metin dizini kurulamadı; ayrıntı tanılama kaydında.")
            return
        mb = stats["karakter"] / 1_000_000
        text = (f"Claude için metin dizini: {stats['kaynak']}/{stats['toplam']} kaynak, {stats['parca']} parça "
                f"(~{mb:.0f} milyon karakter)" + (" · Drive'da ortak" if stats.get("ortak") else ""))
        if stats.get("baska_bilgisayar"):
            text += f" · şu an {stats['baska_bilgisayar']} bilgisayarı güncelliyor, buradan yalnızca okunuyor"
        if stats.get("ocr"):
            text += f" · {stats['ocr']} taranmış PDF metin tanımayla okundu"
        if stats.get("metinsiz"):
            text += f" · {stats['metinsiz']} PDF'te metin çıkmadı"
            if stats.get("ocr_yok"):
                text += f" (taranmış PDF okuma: {stats['ocr_yok']})"
        self.index_label.configure(text=text + (" · yarıda kaldı, sonra sürecek" if stopped else "") + ".")

    def check_theses(self):
        """Kütüphanedeki PDF'siz YÖK tezlerini Tez Merkezi'nde yoklar; sonra çıkarmak için onay ister."""
        worker = getattr(self, "thesis_worker", None)
        if worker and worker.is_alive():
            worker.cancel.set()
            self.thesis_btn.configure(text="Durduruluyor…", state="disabled")
            return
        lib = self.app.library
        items = [i for i in lib.items_without_file() if yok_tez_no(i)]
        if not items:
            messagebox.showinfo(APP_NAME, "Kütüphanede PDF'i olmayan YÖK tezi yok.", parent=self.parent)
            return
        minutes = max(1, round(len(items) * 3.5 / 60))
        if not messagebox.askokcancel(
                APP_NAME, f"Kütüphanede PDF'i olmayan {len(items)} YÖK tezi var.\n\nÖnce her biri Tez Merkezi'nde "
                          f"yeniden yoklanacak (~{minutes} dk): PDF'i sonradan açılmış olanlar indirilip bağlanır, "
                          "açılmamış olanların listesi size sorulur. Hiçbir şey sormadan silinmez.",
                parent=self.parent):
            return
        self.thesis_worker = ThesisCleanupWorker(items, lib, self.app.events, self.app.library_folder())
        self.thesis_btn.configure(text="Yoklanıyor… (durdur)")
        self.thesis_worker.start()

    def on_theses_checked(self, closed, attached, errors, stopped):
        self.thesis_btn.configure(text="PDF'siz tezleri kütüphaneden çıkar…", state="normal")
        lib, tab = self.app.library, self.app.library_tab
        tab.refresh()
        note = (f"{attached} tezin PDF'i sonradan açılmış; indirilip bağlandı. " if attached else "") + \
               (f"{errors} tez yoklanamadı (bağlantı sorunu); onlara dokunulmadı. " if errors else "") + \
               ("Yoklama yarıda durduruldu. " if stopped else "")
        cards = lib.card_counts()
        keep = [i for i in closed if cards.get(i["id"])]
        drop = [i for i in closed if not cards.get(i["id"])]
        if not drop:
            messagebox.showinfo(APP_NAME, (note or "") + ("PDF'i yayımlanmamış tez kalmadı." if not keep else
                                f"PDF'i yayımlanmamış {len(keep)} tezde alıntı kartınız var; onlar kütüphanede "
                                "bırakıldı."), parent=self.parent)
            return
        years = sorted(int(i["year"]) for i in drop if str(i.get("year") or "").isdigit())
        span = f" ({years[0]}–{years[-1]} arası)" if years else ""
        extra = f"\n\nAlıntı kartı olan {len(keep)} tez korunacak." if keep else ""
        if not messagebox.askyesno(
                APP_NAME, note + f"\n\nPDF'i Tez Merkezi'nde yayımlanmamış {len(drop)} tez{span} kütüphaneden "
                                 f"çıkarılsın mı? (No {no_ranges_text([i.get('no') for i in drop], 8)})" + extra +
                          "\n\nYeni taramalarda da PDF'i olmayan tezler eklenmez ('PDF'i yayımlanmamış tezleri "
                          "kütüphaneye ekleme' açık olduğu sürece).", parent=self.parent):
            return
        for item in drop:
            lib.delete(item["id"])
        tab.refresh(keep_selection=False)
        self.app.toast(f"{len(drop)} PDF'siz tez kütüphaneden çıkarıldı.")
        self.app._log("info", f"PDF'i yayımlanmamış {len(drop)} tez çıkarıldı: No {no_ranges_text([i.get('no') for i in drop])}")

    def sync_clicked(self):
        if self.app.sync_in_background(manual=True):
            self.app.toast("Ortak kütüphane eşitleniyor…")
        else:
            self.app.toast("Eşitleme zaten sürüyor.")

    def toggle_shared(self):
        app = self.app
        if not self.shared_var.get():
            self._disable_shared()
            return
        folder = app.library_folder()
        if not folder or not os.path.isdir(folder):
            messagebox.showwarning(APP_NAME, "Önce kütüphane klasörünü Google Drive içinde seçin "
                                             "(ör. G:\\Drive'ım\\Akademik Kütüphanem).", parent=self.parent)
            self.shared_var.set(False)
            return
        if not any(k in fold(folder) for k in ("drive", "onedrive", "dropbox", "icloud")):
            if not messagebox.askyesno(APP_NAME, f"Kütüphane klasörü bir bulut klasörü gibi görünmüyor:\n{folder}\n\n"
                                                 "Ortak kütüphane için klasörün Google Drive'da olması gerekir. "
                                                 "Yine de açılsın mı?", parent=self.parent):
                self.shared_var.set(False)
                return
        lib = app.library
        outside = [i for i in lib.all_items() if i["file_path"] and os.path.exists(i["file_path"])
                   and not os.path.normcase(os.path.abspath(i["file_path"])).startswith(
                       os.path.normcase(os.path.abspath(folder)).rstrip("\\/") + os.sep)]
        if outside and messagebox.askyesno(
                APP_NAME, f"{len(outside)} kaynağın PDF'i kütüphane klasörünün dışında duruyor; öbür "
                          "bilgisayarlar bunları göremez.\n\nKütüphane klasörüne taşınsınlar mı?", parent=self.parent):
            moved = 0
            for item in outside:
                try:
                    new = place_in_library(Path(item["file_path"]), item, folder)
                    lib.update(item["id"], {"file_path": str(new)})
                    moved += 1
                except OSError:
                    diag_exception(f"taşınamadı: {item['file_path']}")
            app.toast(f"{moved} PDF kütüphane klasörüne taşındı.")
        local_dir = settings_path().parent
        current = _load_settings_raw()
        current["shared_library"] = True
        current.pop("sync", None)
        save_settings(current)
        shared = shared_dir()
        shared.mkdir(parents=True, exist_ok=True)
        for name in ("anahtar_kelimeler.txt", "scopus_listesi.json", "indirme_gecmisi.json"):
            if (local_dir / name).is_file() and not (shared / name).exists():
                shutil.copy2(local_dir / name, shared / name)
        (shared / "BENİ OKU.txt").write_text(
            "Bu klasör Akademik Kaynak İndirici'nin ortak kütüphane verisidir (künyeler, etiketler, alıntı "
            "kartları, anahtar kelimeler).\nSilmeyin ve içindeki dosyaları elle değiştirmeyin.\n", encoding="utf-8")
        lib.configure_paths()
        lib.relativize_paths()
        if (shared / SHARED_DB_NAME).is_file():
            meta = app.sync.meta()
            if lib.count() == 0:
                app.sync.pull()
            else:
                choice = choice_dialog(
                    self.parent, "Bu klasörde başka bir kütüphane var",
                    f"{meta.get('machine', 'Başka bir bilgisayar')} bu klasöre {meta.get('items', '?')} kaynaklık "
                    f"bir kütüphane koymuş. Bu bilgisayarda da {lib.count()} kaynak var.\n\n"
                    "• Birleştir (önerilen): iki kütüphane toplanır.\n"
                    "• Ortaktakini kullan: bu bilgisayardaki kütüphane yedeklenip bırakılır.",
                    ["Birleştir", "Ortaktakini kullan"])
                if choice == 0:
                    added, updated = app.sync.merge()
                    app.toast(f"Birleştirildi: {added} kaynak eklendi, {updated} güncellendi.")
                elif choice == 1:
                    app.sync.pull()
                else:
                    self.shared_var.set(False)
                    self._disable_shared()
                    return
        else:
            app.sync.push(force=True)
        app.sync.heartbeat()
        app._write_phone_export()
        app.library_tab.refresh()
        self.refresh_sync_label()
        self.refresh_scopus_label()
        diag(f"ortak kütüphane açıldı: {shared}")
        messagebox.showinfo(APP_NAME, "Ortak kütüphane açıldı.\n\nÖbür bilgisayarda: Google Drive'ı kurun, programda "
                                      "kütüphane klasörü olarak aynı Drive klasörünü seçin ve bu kutuyu işaretleyin.\n\n"
                                      f"Telefonda: Drive'da '{PHONE_EXPORT_NAME}' dosyasını açın; PDF'ler aynı "
                                      "klasörde.", parent=self.parent)

    def _disable_shared(self):
        shared = shared_dir()
        if shared is not None:                            # son hâli gönder, ortak dosyaları buraya geri al
            self.app.sync_now(quiet=True)
            local_dir = settings_path().parent
            for name in ("anahtar_kelimeler.txt", "scopus_listesi.json", "indirme_gecmisi.json"):
                if (shared / name).is_file():
                    try:
                        shutil.copy2(shared / name, local_dir / name)
                    except OSError:
                        pass
            self.app.sync.heartbeat(closing=True)
        current = _load_settings_raw()
        current["shared_library"] = False
        save_settings(current)
        self.app.library.configure_paths()
        self.refresh_sync_label()

    # ── Scopus listesi ──────────────────────────────────────────────────────
    def refresh_scopus_label(self):
        data = load_scopus()
        if data:
            text = (f"Yüklü: {data.get('file', 'liste')} · {data.get('count', 0):,} kaynak · "
                    f"{data.get('imported', '')}").replace(",", ".")
            self.scopus_label.configure(text=text, text_color=LOG_COLORS["success"])
        else:
            self.scopus_label.configure(text="Liste yüklenmedi.", text_color=MUTED)

    def load_scopus_list(self):
        path = filedialog.askopenfilename(parent=self.parent, title="Scopus kaynak listesini seçin",
                                          filetypes=[("Excel", "*.xlsx"), ("Tüm dosyalar", "*.*")])
        if not path:
            return
        self.scopus_btn.configure(state="disabled")
        ScopusImportWorker(path, self.app.library, self.app.events, threading.Event()).start()

    def on_scopus(self, kind, text):
        color = {"error": LOG_COLORS["error"], "done": LOG_COLORS["success"]}.get(kind, MUTED)
        self.scopus_label.configure(text=text, text_color=color)
        if kind in ("done", "error"):
            self.scopus_btn.configure(state="normal")
        if kind == "error":
            messagebox.showerror(APP_NAME, text + "\n\nElsevier'in sitesinden indirdiğiniz .xlsx dosyasını "
                                                  "seçtiğinizden emin olun.", parent=self.parent)

    # ── Claude bağlantısı ───────────────────────────────────────────────────
    def _mcp_ready(self) -> bool:
        if mcp_exe_path().is_file():
            return True
        messagebox.showwarning(APP_NAME, f"{MCP_EXE_NAME}.exe bu programın klasöründe bulunamadı.\n\n"
                                         "GitHub'dan indirdiğiniz klasörün tamamını (içindeki _internal "
                                         "klasörüyle birlikte) aynı yerde tutun.", parent=self.parent)
        return False

    def connect_claude(self):
        if not self._mcp_ready():
            return
        try:
            written = connect_claude_desktop()
        except (OSError, ValueError) as exc:
            diag_exception("Claude bağlantısı")
            messagebox.showerror(APP_NAME, f"Bağlantı eklenemedi:\n{exc}\n\n"
                                           "'Ayarı Kopyala' ile elle ekleyebilirsiniz.", parent=self.parent)
            return
        if not written:
            messagebox.showinfo(APP_NAME, "Bu bilgisayarda Claude masaüstü uygulaması bulunamadı.\n\n"
                                          "claude.ai/download adresinden kurup bir kez açın, sonra bu düğmeye "
                                          "yeniden basın.", parent=self.parent)
            return
        diag(f"Claude bağlantısı eklendi: {', '.join(map(str, written))}")
        messagebox.showinfo(APP_NAME, "Bağlantı Claude'un ayarlarına eklendi.\n\n"
                                      "1. Claude'u tamamen kapatın: saatin yanındaki simgeye sağ tıklayıp Quit.\n"
                                      "2. Claude'u yeniden açın.\n"
                                      "3. Yazı kutusunun altındaki araçlar (+ ya da ayar simgesi) menüsünde "
                                      "\"akademik-kutuphane\" görünür.\n\n"
                                      "Deneyin: \"Kütüphanemde PDF'i olmayan kaynakları listele.\"\n\n"
                                      f"Ayar dosyası:\n{written[0]}", parent=self.parent)

    def copy_claude_config(self):
        if not self._mcp_ready():
            return
        snippet = claude_config_snippet()
        self.parent.clipboard_clear()
        self.parent.clipboard_append(snippet)
        messagebox.showinfo(APP_NAME, "Ayar panoya kopyalandı.\n\nClaude → Settings → Developer → Edit Config ile "
                                      "açılan dosya boşsa bunu yapıştırın; doluysa \"mcpServers\" içine "
                                      "yalnızca \"akademik-kutuphane\" bölümünü ekleyin.\n\n" + snippet,
                            parent=self.parent)

    # ── zamanlama ───────────────────────────────────────────────────────────
    def _copy_command(self, command, title, steps):
        self.parent.clipboard_clear()
        self.parent.clipboard_append(command)
        messagebox.showinfo(APP_NAME, f"{title} komutu panoya kopyalandı.\n\n{steps}\n\n{command}",
                            parent=self.parent)

    def schedule(self):
        if not getattr(sys, "frozen", False):
            messagebox.showinfo(APP_NAME, "Bu komut yalnızca .exe sürümünde hazırlanabilir.", parent=self.parent)
            return
        create, _ = task_commands(self.day_menu.get(), self.hour_menu.get())
        self._copy_command(create, "Kurulum",
                           "1. Başlat menüsüne cmd yazıp Komut İstemi'ni açın.\n"
                           "2. Pencereye sağ tıklayıp yapıştırın ve Enter'a basın.\n"
                           "3. \"BAŞARILI\" yazısını görünce kapatabilirsiniz.\n\n"
                           "Not: exe'nin yerini değiştirirseniz komutu yeniden çalıştırın.")
        current = load_settings()
        current["scan_task"] = f"{self.day_menu.get()} {self.hour_menu.get()}"
        save_settings(current)
        self.app.save_all_settings()
        self.refresh_schedule_label()

    def unschedule(self):
        _, delete = task_commands(self.day_menu.get(), self.hour_menu.get())
        self._copy_command(delete, "Kaldırma", "Başlat → cmd → yapıştırın ve Enter'a basın.")
        current = load_settings()
        current.pop("scan_task", None)
        save_settings(current)
        self.refresh_schedule_label()

    def refresh_schedule_label(self):
        task = load_settings().get("scan_task")
        if task:
            self.sched_label.configure(text=f"Kurulum komutu hazırlandı: her {task}",
                                       text_color=LOG_COLORS["success"])
        else:
            self.sched_label.configure(text="Windows görevi kurulmadı (isteğe bağlı).", text_color=MUTED)


class DownloadsWatcher(threading.Thread):
    """İndirilenler klasörüne yeni düşen PDF'leri PDF'i olmayan kaynaklarla eşleştirir."""

    def __init__(self, library, folder, since: float, library_folder, events):
        super().__init__(daemon=True)
        self.library = library
        self.folders = [Path(f) for f in (folder if isinstance(folder, (list, tuple)) else [folder])]
        self.since = since
        self.library_folder = library_folder
        self.events = events
        self.newest = since

    def run(self):
        try:
            candidates = [p for folder in self.folders for p in downloaded_docs(folder)
                          if p.is_file() and self.since < p.stat().st_mtime < time.time() - 5]
        except OSError:
            candidates = []
        if not candidates:
            self.events.put(("watch_done", self.newest))
            return
        missing = [i for i in self.library.items_without_file() if len(i["title"].split()) >= 3]
        for path in sorted(candidates, key=lambda p: p.stat().st_mtime):
            self.newest = max(self.newest, path.stat().st_mtime)
            try:
                sha = file_sha256(path)
                if self.library.find_by_sha(sha):
                    continue
                target = None
                if path.stem.isdigit():
                    target = next((i["id"] for i in missing if yok_tez_no(i) == path.stem), None)
                    if target:
                        placed = attach_pdf(self.library, target, path, self.library_folder, move=True)
                        missing = [i for i in missing if i["id"] != target]
                        self.events.put(("watch_attached", target, placed.name))
                        continue
                head = doc_head(path)
                m = DOI_RE.search(head)
                if m:
                    found = self.library.find_by_doi(clean_url(m.group(1)))
                    if found and any(i["id"] == found for i in missing):
                        target = found
                if not target:
                    for item in missing:
                        if title_matches_text(item["title"], head):
                            target = item["id"]
                            break
                if target:
                    placed = attach_pdf(self.library, target, path, self.library_folder, move=True)
                    missing = [i for i in missing if i["id"] != target]
                    self.events.put(("watch_attached", target, placed.name))
                elif (DOI_RE.search(head) or len(head) > 500) and missing:   # akademik PDF ama eşleşmedi
                    self.events.put(("watch_unmatched", path.name))
            except Exception:
                diag_exception(f"indirilenler izleyicisi: {path.name}")
                continue
        self.events.put(("watch_done", self.newest))


class App(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title(f"{APP_NAME}  v{APP_VERSION}")
        self.geometry("1280x820")
        self.minsize(1080, 700)

        self.events = queue.Queue()
        self.cancel_event = threading.Event()
        self.worker = None
        self.import_worker = None
        self.watcher = None
        self.failed_links = []
        self._file_bar_spinning = False
        self._toast_job = None
        self.started = time.time()

        settings = load_settings()
        self.settings = settings
        set_window_icon(self)
        self.library = Library()
        self.sync = LibrarySync(self.library)
        self._last_focus_sync = time.time()
        self.folder_var = ctk.StringVar(value=settings.get("library_folder") or settings.get("folder") or "")
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

        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)

        self._build_header()
        self.tabs = ctk.CTkTabview(self, corner_radius=14, command=self._on_tab)
        self.tabs.grid(row=1, column=0, sticky="nsew", padx=16, pady=(0, 16))
        download_tab = self.tabs.add("İndir")
        library_tab = self.tabs.add("Kütüphanem")
        scan_tab = self.tabs.add("Tarama")
        download_tab.grid_columnconfigure(0, weight=3, uniform="col")
        download_tab.grid_columnconfigure(1, weight=2, uniform="col")
        download_tab.grid_rowconfigure(0, weight=1)
        self._build_left_panel(download_tab)
        self._build_right_panel(download_tab)
        self.library_tab = LibraryTab(library_tab, self)
        self.scan_tab = ScanTab(scan_tab, self)
        if self.library.count():
            self.tabs.set("Kütüphanem")

        self._log("info", "Hazır. Metni yapıştırın ya da dosya ekleyin, sonra 'İndirmeyi Başlat'a basın.")
        self.after(80, self._poll_events)
        self.watchdog = FreezeWatchdog()
        self._watchdog_beat()
        self.watchdog.start()
        self.after(600, self._first_run)
        self.index_worker = None
        self.after(45_000, self._index_tick)
        self.after(25_000, self._warm_twins)
        self.after(15_000, self._watch_downloads)
        self._db_stamp = self._library_stamp()
        self.bind("<FocusIn>", self._on_focus, add="+")
        self.after(5 * 60_000, self._sync_tick)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    def _warm_twins(self):
        """İkiz kayıt listesini arka planda önceden hesaplar (PDF arama pencereleri beklemeden açılsın)."""
        def work():
            try:
                key = self.library.change_no()
                self._twins_cache = (key, find_pdf_twins(self.library))
            except Exception:
                diag_exception("ikiz kayıt ön hesabı")
        threading.Thread(target=work, daemon=True).start()

    def pdf_twins(self) -> dict:
        """PDF'i ikiz bir kayıtta duran PDF'siz kayıtlar (kütüphane değişmedikçe önbellekten)."""
        try:
            key = self.library.change_no()
        except Exception:
            key = None
        cache = getattr(self, "_twins_cache", None)
        if cache and key is not None and cache[0] == key:
            return cache[1]
        try:
            twins = find_pdf_twins(self.library)
        except Exception:
            diag_exception("ikiz kayıt tespiti")
            twins = {}
        self._twins_cache = (key, twins)
        return twins

    def _rebuild_citations_quietly(self):
        """Dizin güncellenince atıf ağını arka planda yeniden hesaplar (PDF açmaz, birkaç saniye)."""
        lib = self.library

        def work():
            try:
                idx = ShardedIndex(readonly=True)
                build_citation_graph(lib, idx)
                idx.close()
            except Exception:
                diag_exception("atıf ağı (arka plan)")
        threading.Thread(target=work, daemon=True).start()

    def _index_tick(self):
        """Metin dizinini 10 dakikada bir (yalnızca değişenler için) günceller."""
        try:
            self.update_index()
        finally:
            self.after(10 * 60_000, self._index_tick)

    def update_index(self, manual=False):
        if self.index_worker is not None and self.index_worker.is_alive():
            return False
        self.index_worker = IndexWorker(self.library, self.events)
        self.index_worker.manual = manual
        self.index_worker.start()
        return True

    def _watchdog_beat(self):
        self.watchdog.beat = time.monotonic()
        self.after(500, self._watchdog_beat)

    def _library_stamp(self):
        try:
            st = self.library.path.stat()
            return st.st_mtime_ns, st.st_size
        except OSError:
            return None

    def _on_focus(self, event):
        """Claude (ya da tarama görevi) kütüphaneyi değiştirdiyse pencereye dönünce listeyi tazele."""
        if self.sync.folder() is not None and time.time() - self._last_focus_sync > 60:
            self._last_focus_sync = time.time()
            self.sync_in_background(send=False)
        stamp = self._library_stamp()
        if stamp != self._db_stamp:
            self._db_stamp = stamp
            try:
                self.library_tab.refresh()
            except Exception:
                diag_exception("odak yenileme")

    # ── ortak kütüphane eşitlemesi ──────────────────────────────────────────────
    def sync_now(self, startup=False, closing=False, quiet=False):
        """Durumu yoklar: gerekirse gönderir, alır ya da çakışmada sorar. Dönüş: yapılan işlem."""
        sync = self.sync
        if sync.folder() is None:
            return "kapali"
        if startup:
            others = sync.other_sessions()
            if others:
                messagebox.showwarning(APP_NAME, f"Ortak kütüphane şu anda {', '.join(others)} bilgisayarında da "
                                                 "açık görünüyor.\n\nİkisinde birden değişiklik yaparsanız program "
                                                 "hangisini tutacağınızı sorar. Mümkünse öbür bilgisayardaki "
                                                 "programı kapatın.", parent=self)
            sync.heartbeat()
        done = ""
        try:
            state = sync.status()
            if state in ("ilk", "gonder"):
                done = sync.push()
            elif state == "al":
                done = sync.pull()
                if not closing:
                    self.library_tab.refresh()
                    meta = sync.meta()
                    self.toast(f"{meta.get('machine', 'Öbür bilgisayar')} bilgisayarındaki değişiklikler alındı.")
            elif state == "cakisma":
                done = self.resolve_conflict()
            if done in ("gonderildi", "alindi", "birlestirildi") and not closing:
                self._write_phone_export()
        except Exception as exc:
            diag_exception("eşitleme")
            if not quiet:
                messagebox.showwarning(APP_NAME, f"Ortak kütüphane eşitlenemedi:\n{exc}\n\nBulut klasörüne "
                                                 "ulaşılabildiğini kontrol edin. Çalışmanız bu bilgisayarda "
                                                 "güvende; bir sonraki eşitlemede yeniden denenir.", parent=self)
        self._db_stamp = self._library_stamp()
        try:
            self.scan_tab.refresh_sync_label()
        except Exception:
            pass
        return done or "esit"

    def _sync_tick(self):
        try:
            self.sync_in_background()
        finally:
            self.after(5 * 60_000, self._sync_tick)

    def sync_in_background(self, manual=False, startup=False, send=True) -> bool:
        """Ortak kütüphaneyi arayüzü dondurmadan eşitler (bulut klasörü yavaş olabilir).
        Çakışma olursa soru ana pencerede sorulur."""
        if self.sync.folder() is None:
            return False
        running = getattr(self, "_sync_thread", None)
        if running is not None and running.is_alive():
            return False
        sync, events = self.sync, self.events

        def work():
            result, machine, others = "hata", "", []
            try:
                if startup:
                    others = sync.other_sessions()
                sync.heartbeat()
                folder = sync.folder()
                if folder is not None:
                    shared_state(folder, max_age=0)          # son tarama bilgisini tazele
                state = sync.status()
                if state in ("ilk", "gonder") and not send:
                    result = "bekliyor"                       # bir sonraki 5 dakikalık turda gönderilir
                elif state in ("ilk", "gonder"):
                    result = sync.push()
                elif state == "al":
                    result = sync.pull()
                    machine = sync.meta().get("machine", "")
                elif state == "cakisma":
                    result = "cakisma"
                else:
                    result = "esit"
            except Exception:
                diag_exception("arka plan eşitleme")
            events.put(("sync_bg", result, machine, manual, others))

        self._sync_thread = threading.Thread(target=work, name="eşitleme", daemon=True)
        self._sync_thread.start()
        return True

    def on_sync_bg(self, result, machine, manual, others=()):
        self._db_stamp = self._library_stamp()
        if others:
            messagebox.showwarning(APP_NAME, f"Ortak kütüphane şu anda {', '.join(others)} bilgisayarında da "
                                             "açık görünüyor.\n\nİkisinde birden değişiklik yaparsanız program "
                                             "hangisini tutacağınızı sorar. Mümkünse öbür bilgisayardaki "
                                             "programı kapatın.", parent=self)
        if result == "cakisma":
            self.sync_now()                                    # hangisinin tutulacağını sorar
            return
        if result == "alindi":
            self.settings = load_settings()
            self.library_tab.refresh()
            self.toast(f"{machine or 'Öbür bilgisayar'} bilgisayarındaki değişiklikler alındı.")
        if result in ("gonderildi", "alindi", "birlestirildi") and \
                time.time() - getattr(self, "_last_phone_export", 0) > 30 * 60:
            self._last_phone_export = time.time()
            self._write_phone_export()
        try:
            self.scan_tab.refresh_sync_label()
        except Exception:
            pass
        if manual and result != "alindi":
            self.toast({"gonderildi": "Ortak kütüphaneye gönderildi.", "esit": "Ortak kütüphane zaten güncel.",
                        "birlestirildi": "Birleştirildi.",
                        "hata": "Ortak kütüphane eşitlenemedi; bulut klasörünü kontrol edin."}.get(result, "Tamam."))

    def _write_phone_export(self):
        folder = self.library_folder()
        if not folder:
            return

        def work():
            try:
                write_phone_export(self.library, folder)
            except Exception:
                diag_exception("telefon dökümü")
        threading.Thread(target=work, daemon=True).start()

    def resolve_conflict(self) -> str:
        meta = self.sync.meta()
        other = meta.get("machine") or "öbür bilgisayar"
        when = ""
        try:
            when = datetime.fromisoformat(meta["saved_at"]).astimezone().strftime("%d.%m.%Y %H:%M")
        except (KeyError, ValueError):
            pass
        choice = choice_dialog(self, "Ortak kütüphane: iki yerde değişiklik var",
                               f"Bu bilgisayarda yaptığınız değişiklikler henüz buluta gönderilmeden, {other} "
                               f"bilgisayarı da ortak kütüphaneyi güncellemiş ({when}).\n\n"
                               "• Birleştir: iki taraftaki kaynaklar, etiketler ve alıntı kartları toplanır "
                               "(önerilen). Bir tarafta silinen kaynak öbüründe duruyorsa geri gelir.\n"
                               f"• {other} kopyasını al: bu bilgisayardaki son değişiklikler bırakılır.\n"
                               "• Bu bilgisayarınkini kullan: öbür bilgisayarın son değişiklikleri bırakılır.\n\n"
                               "Hangisini seçerseniz seçin iki kopyanın da yedeği alınır.",
                               ["Birleştir", f"{other} kopyasını al", "Bu bilgisayarınkini kullan"])
        if choice == 0:
            added, updated = self.sync.merge()
            self.library_tab.refresh()
            self.toast(f"Birleştirildi: {added} kaynak eklendi, {updated} kaynak güncellendi.")
            return "birlestirildi"
        if choice == 1:
            self.sync.pull()
            self.library_tab.refresh()
            return "alindi"
        if choice == 2:
            return self.sync.push(force=True)
        return "ertelendi"

    # ── yerleşim ────────────────────────────────────────────────────────────────
    def _section(self, parent, text, row, pady=(16, 2)):
        ctk.CTkLabel(parent, text=text, font=self.font_section, anchor="w").grid(
            row=row, column=0, sticky="ew", padx=18, pady=pady)

    def _build_header(self):
        header = ctk.CTkFrame(self, fg_color="transparent")
        header.grid(row=0, column=0, columnspan=2, sticky="ew", padx=22, pady=(18, 8))
        header.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(header, text=APP_NAME, font=self.font_title).grid(row=0, column=0, sticky="w")
        self.subtitle = ctk.CTkLabel(
            header, font=self.font_small, text_color=MUTED, anchor="w",
            text="İndir · kütüphanende düzenle · haftalık taramayla yeni yayınlardan haberdar ol",
        )
        self.subtitle.grid(row=1, column=0, sticky="w")
        self.notice_btn = ctk.CTkButton(header, text="", height=30, fg_color="#1F8F4E", hover_color="#18723E",
                                        command=self._open_notice)
        self.notice_target = None
        self.theme_switch = ctk.CTkSwitch(header, text="Koyu tema", command=self._toggle_theme)
        self.theme_switch.grid(row=0, column=2, rowspan=2, sticky="e")
        if ctk.get_appearance_mode().lower() == "dark":
            self.theme_switch.select()

    def _build_left_panel(self, parent):
        card = ctk.CTkFrame(parent, corner_radius=14)
        card.grid(row=0, column=0, sticky="nsew", padx=(4, 8), pady=4)
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
        self._section(card, "2   Kütüphane klasörü", row=4, pady=(18, 6))
        folder_row = ctk.CTkFrame(card, fg_color="transparent")
        folder_row.grid(row=5, column=0, sticky="ew", padx=18)
        folder_row.grid_columnconfigure(0, weight=1)
        self.folder_entry = ctk.CTkEntry(folder_row, textvariable=self.folder_var, height=34)
        self.folder_entry.grid(row=0, column=0, sticky="ew", padx=(0, 8))
        self.folder_btn = ctk.CTkButton(folder_row, text="Klasör Seç", width=110,
                                        height=34, command=self.choose_library_folder)
        self.folder_btn.grid(row=0, column=1)

        # seçenekler
        self._section(card, "Seçenekler", row=6, pady=(18, 4))
        opts = ctk.CTkFrame(card, fg_color="transparent")
        opts.grid(row=7, column=0, sticky="ew", padx=18)
        self.option_boxes = []
        for i, (text, var) in enumerate([
            ("Çıplak DOI'leri de yakala  (doi:10.xxxx/…  →  https://doi.org/…)", self.opt_doi),
            ("Link bir makale sayfasına açılırsa PDF'i bul (sayfa, kurum arşivi, açık erişim)", self.opt_find_pdf),
            ("Daha önce indirdiklerimi tekrar indirme (dosyayı taşımış ya da silmiş olsam bile)", self.opt_skip_existing),
            ("PDF bulunamazsa web sayfasını .html olarak kaydet", self.opt_save_html),
        ]):
            box = ctk.CTkCheckBox(opts, text=text, variable=var, font=self.font_small,
                                  checkbox_width=20, checkbox_height=20)
            box.grid(row=i, column=0, sticky="w", pady=3)
            self.option_boxes.append(box)

        email_row = ctk.CTkFrame(card, fg_color="transparent")
        email_row.grid(row=8, column=0, sticky="ew", padx=18, pady=(8, 0))
        email_row.grid_columnconfigure(1, weight=1)
        email_row.grid_columnconfigure(3, weight=1)
        ctk.CTkLabel(email_row, text="E-posta:", font=self.font_small).grid(row=0, column=0, padx=(0, 8))
        self.email_entry = ctk.CTkEntry(email_row, height=30,
                                        placeholder_text="ad.soyad@universite.edu.tr")
        self.email_entry.grid(row=0, column=1, sticky="ew")
        if self.email_var.get():
            self.email_entry.insert(0, self.email_var.get())
        ctk.CTkLabel(email_row, text="Etiket:", font=self.font_small).grid(row=0, column=2, padx=(12, 8))
        self.tag_entry = ctk.CTkEntry(email_row, height=30, placeholder_text="elle: ör. tez bölüm 2")
        self.tag_entry.grid(row=0, column=3, sticky="ew")
        self.auto_tag_dl = ctk.BooleanVar(value=self.settings.get("auto_tag", True))
        ctk.CTkCheckBox(email_row, text="+ otomatik", variable=self.auto_tag_dl, width=20,
                        font=self.font_small).grid(row=0, column=4, padx=(8, 0))
        ctk.CTkLabel(
            card, font=ctk.CTkFont(size=11), text_color=MUTED, anchor="w", justify="left",
            wraplength=540,
            text="E-posta isteğe bağlı: girerseniz DOI'lerin yasal açık erişim kopyaları Unpaywall'da aranır "
                 "(adres yalnızca Unpaywall'a gönderilir). Elle yazılan etiket inen her kaynağa verilir; '+ otomatik' işaretliyse konusu uyanlara grup etiketleri de eklenir.",
        ).grid(row=9, column=0, sticky="ew", padx=18, pady=(4, 16))

    def _build_right_panel(self, parent):
        card = ctk.CTkFrame(parent, corner_radius=14)
        card.grid(row=0, column=1, sticky="nsew", padx=(8, 4), pady=4)
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
        self.after(50, self.library_tab.apply_style)

    def save_all_settings(self):
        current = load_settings()           # tarama tarihi gibi başka yerde yazılan alanlar korunur
        current.update({
            "library_folder": self.folder_var.get().strip(),
            "email": self.email_entry.get().strip(),
            "doi": self.opt_doi.get(),
            "find_pdf": self.opt_find_pdf.get(),
            "save_html": self.opt_save_html.get(),
            "skip_existing": self.opt_skip_existing.get(),
        })
        scan = getattr(self, "scan_tab", None)
        if scan is not None:
            current.update({
                "auto_scan": scan.auto_var.get(), "open_report": scan.open_report_var.get(),
                "scan_dergipark": scan.src_dp.get(), "scan_crossref": scan.src_cr.get(),
                "scan_openalex": scan.src_oa.get(), "scan_eric": scan.src_eric.get(),
                "openalex_api_key": scan.oa_key.get().strip(),
                "scan_yok": scan.src_yok.get(), "yok_skip_closed": scan.yok_skip_closed.get(),
                "watch_downloads": scan.watch_var.get(), "scan_day": scan.day_menu.get(),
                "auto_tag": scan.autotag_var.get(), "auto_update": scan.update_var.get(),
                "scan_hour": scan.hour_menu.get(),
                "institution_url": scan.inst_entry.get().strip() or DEFAULT_INSTITUTION_URL,
            })
        save_settings(current)
        self.settings = current

    _save_settings = save_all_settings

    # ── kütüphane / tarama ile ilgili ───────────────────────────────────────────
    def _first_run(self):
        if not self.folder_var.get().strip():
            messagebox.showinfo(
                APP_NAME, "Kütüphane klasörünüzü seçin.\n\nİndirilen ve eklenen bütün PDF'ler bu klasörde "
                          "'Soyad (Yıl) - Başlık.pdf' adıyla toplanacak. Örneğin Belgeler içinde "
                          "'Akademik Kütüphanem' adlı bir klasör olabilir.", parent=self)
            self.choose_library_folder()
        if self.sync.folder() is not None:          # ortak kütüphane: önce öbür bilgisayarlardakini al
            self._last_focus_sync = time.time()
            self.sync_in_background(startup=True)
            self.toast("Ortak kütüphane denetleniyor…")
        self._update_notices()
        report = self.settings.get("last_report")
        seen = self.settings.get("seen_report")
        if report and report != seen and Path(report).is_file():
            self.notify_report(report, "Yeni tarama raporu hazır")
        if self.settings.get("auto_scan", True) and scan_due(self.settings) and self.library_folder():
            self._log("info", "Son taramanın üzerinden 7 gün geçmiş; haftalık tarama arka planda başlıyor.")
            self.scan_tab.start_scan(automatic=True)

    def _update_notices(self):
        current = _load_settings_raw()
        if current.get("seen_version") != APP_VERSION:
            if current.get("seen_version"):
                self.toast(f"Program v{APP_VERSION} sürümüne güncellendi.")
                self._log("success", f"Program kendiliğinden v{APP_VERSION} sürümüne güncellendi.")
            current["seen_version"] = APP_VERSION
            save_settings(current)
        stale = os.environ.get("AKADEMIK_EXE_ESKI")
        if stale:
            self._log("warn", f"Yeni sürüm (v{stale}) hazır, ama yeni bir kütüphane gerektirdiği için programın "
                              "kendisinin (exe) bir kez güncellenmesi gerekiyor. GitHub'daki son derlemeyi "
                              "indirin; sonraki güncellemeler yine kendiliğinden gelir.")

    def notify_report(self, report, summary):
        self.notice_target = report
        self.notice_btn.configure(text=f"📰 {summary} — Raporu aç")
        self.notice_btn.grid(row=0, column=1, rowspan=2, padx=12)

    def _open_notice(self):
        if self.notice_target and Path(self.notice_target).is_file():
            webbrowser.open(Path(self.notice_target).as_uri())
            current = load_settings()
            current["seen_report"] = self.notice_target
            save_settings(current)
        self.notice_btn.grid_remove()

    def toast(self, text):
        self.subtitle.configure(text=f"✓ {text}", text_color=LOG_COLORS["success"])
        if self._toast_job:
            self.after_cancel(self._toast_job)
        self._toast_job = self.after(3500, lambda: self.subtitle.configure(
            text="İndir · kütüphanende düzenle · haftalık taramayla yeni yayınlardan haberdar ol",
            text_color=MUTED))

    def _on_tab(self):
        if self.tabs.get() == "Kütüphanem":
            self.library_tab.refresh()

    def start_import(self, paths, tags, move, report_folders=(), auto_tags=None):
        if self.import_worker and self.import_worker.is_alive():
            messagebox.showinfo(APP_NAME, "Önceki ekleme işlemi sürüyor.", parent=self)
            return
        self.import_worker = LibraryScanWorker(paths, self.library, self.events, threading.Event(),
                                               tags=tags, library_folder=self.library_folder(), move=move,
                                               report_folders=report_folders, auto_tags=auto_tags)
        self.library_tab.count_label.configure(text=f"{len(paths)} dosya kütüphaneye alınıyor…")
        self.import_worker.start()

    def _watch_downloads(self):
        try:
            queue_open = getattr(self, "pdf_queue", None) is not None and self.pdf_queue.winfo_exists()
            if (self.settings.get("watch_downloads", True) and self.library_folder() and not queue_open
                    and not (self.watcher and self.watcher.is_alive())):
                folders = [f for f in downloads_folders() if f.is_dir()]
                if folders:
                    since = max(self.settings.get("watch_since", 0) or 0, self.started - 3600)
                    self.watcher = DownloadsWatcher(self.library, folders, since,
                                                    self.library_folder(), self.events)
                    self.watcher.start()
        finally:
            self.after(20_000, self._watch_downloads)

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
        paths = list(filedialog.askopenfilenames(parent=self, title="Kaynak dosyası seçin",
                                                 filetypes=SUPPORTED_FILES))
        pdfs = [p for p in paths if p.lower().endswith(".pdf")]
        if pdfs:
            choice = choice_dialog(
                self, "PDF'lerle ne yapalım?",
                f"{len(pdfs)} PDF seçtiniz.\n\n"
                "• Kütüphaneye ekle: PDF'ler makalenin kendisiyse. Künyesi çıkarılır, kütüphane klasörüne "
                "alınır, etiketlenir.\n"
                "• İçindeki linkleri indir: PDF bir kaynakça ya da literatür özetiyse. İçindeki linkler ve "
                "DOI'ler bulunur, indirilmek üzere kutuya eklenir.",
                ["Kütüphaneye ekle", "İçindeki linkleri indir"])
            if choice is None:
                paths = [p for p in paths if p not in pdfs]
            elif choice == 0:
                paths = [p for p in paths if p not in pdfs]
                self.tabs.set("Kütüphanem")
                self.library_tab._start_import(pdfs)
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

    def library_folder(self):
        text = self.folder_var.get().strip()
        return str(Path(text).expanduser()) if text else None

    def choose_library_folder(self):
        initial = self.folder_var.get() or str(default_library_dir())
        if not os.path.isdir(initial):
            initial = str(Path(initial).parent if Path(initial).parent.is_dir() else Path.home())
        path = filedialog.askdirectory(parent=self, initialdir=initial,
                                       title="Kütüphane klasörünü seçin (tüm PDF'ler burada toplanır)")
        if path:
            self.folder_var.set(os.path.normpath(path))
            self._log("info", f"Kütüphane klasörü: {self.folder_var.get()}")
            self.save_all_settings()
            self.library.configure_paths()
        elif not self.folder_var.get():
            self.folder_var.set(str(default_library_dir()))
            self.save_all_settings()

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
        if not self.folder_var.get().strip():
            self.choose_library_folder()
        folder_text = self.folder_var.get().strip()
        if not folder_text:
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
                   "skip_existing": self.opt_skip_existing.get(), "email": email,
                   "library": self.library, "library_folder": str(folder),
                   "tags": clean_tags(self.tag_entry.get()), "auto_tags": bool(self.auto_tag_dl.get())}
        self._set_running(True)
        self.overall_bar.set(0)
        self.overall_label.configure(text=f"0 / {len(links)}")
        self._reset_file_progress()
        self._set_status("İndiriliyor…")
        self._log("info", f"İndirme başladı: {len(links)} link → {folder}")
        if self.opt_find_pdf.get() and not email:
            self._log("muted", "İpucu: Seçeneklere e-posta girerseniz açık erişim kopyaları da aranır.")
        diag(f"indirme başladı: {len(links)} link")
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
            parts.append(f"{counts['dup']} daha önce indirilmiş")
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
            self.library_tab.refresh()
        elif kind == "retry":
            n, total, title, no = message[1:]
            self.library_tab.count_label.configure(
                text=f"PDF aranıyor · No {no} ({n + 1}/{total}): {shorten(title, 44)}")
        elif kind == "files_checked":
            self.library_tab.refresh()
        elif kind == "sync_bg":
            self.on_sync_bg(*message[1:])
        elif kind == "complete":
            n, total, title, no = message[1:]
            self.library_tab.count_label.configure(
                text=f"Künye tamamlanıyor · No {no} ({n + 1}/{total}): {shorten(title, 44)}")
        elif kind == "complete_done":
            self.library_tab.on_complete_done(*message[1:])
        elif kind == "thesis_check":
            n, total = message[1:]
            self.scan_tab.thesis_btn.configure(text=f"Yoklanıyor {n + 1}/{total}… (durdur)")
        elif kind == "thesis_check_done":
            self.scan_tab.on_theses_checked(*message[1:])
        elif kind == "index":
            done, total = message[1:]
            self.scan_tab.index_label.configure(text=f"Claude için metin dizini hazırlanıyor: {done}/{total} kaynak "
                                                     "okundu (arka planda)…")
        elif kind == "index_done":
            self.scan_tab.on_index_done(*message[1:])
            if message[1] and not message[2]:
                self._rebuild_citations_quietly()
        elif kind == "cite_done":
            win = getattr(self.library_tab, "cite_win", None)
            if win is not None and win.winfo_exists():
                win.on_built(message[1])
        elif kind == "cite_links":
            win = getattr(self.library_tab, "cite_win", None)
            if win is not None and win.winfo_exists():
                win.on_links(*message[1:])
            elif len(message) > 3 and message[3] and message[1] and not (self.worker and self.worker.is_alive()):
                self.input_box.insert("end", "\n──── Eksik temel kaynaklar ────\n" + "\n".join(message[1]) + "\n")
                self.tabs.set("İndir")
                self._start()
        elif kind == "cite_prog":
            win = getattr(self.library_tab, "cite_win", None)
            if win is not None and win.winfo_exists():
                win.on_progress(*message[1:])
        elif kind == "hl":
            n, total = message[1:]
            self.library_tab.count_label.configure(text=f"PDF işaretlemeleri okunuyor {n}/{total}…")
        elif kind == "rx":
            n, total = message[1:]
            self.library_tab.count_label.configure(text=f"Künyeler PDF'ten çıkarılıyor {n}/{total}…")
        elif kind == "rx_done":
            self.library_tab.on_reextract_done(*message[1:])
        elif kind == "hl_done":
            self.library_tab.on_highlights_done(*message[1:])
        elif kind == "isbn_done":
            self.library_tab.on_isbn_done(*message[1:])
        elif kind == "retry_wait":
            secs, count = message[1:]
            self.library_tab.count_label.configure(
                text=f"{count} kaynakta site 'çok fazla istek' dedi; site dinlensin diye "
                     f"{max(1, round(secs / 60))} dk bekleniyor, sonra yeniden denenecek…")
        elif kind == "retry_done":
            self.library_tab.on_retry_done(*message[1:])
        elif kind == "html_done":
            added, pdfs, existing = message[1:]
            self.library_tab.refresh()
            self.toast(f"Web sayfaları: {added} kaynak eklendi, {pdfs} tanesinin PDF'i bulundu, "
                       f"{existing} tanesi zaten vardı.")
            self._log("success", f"Web sayfaları kütüphaneye işlendi: {added} yeni, {pdfs} PDF, {existing} zaten vardı. "
                                 "PDF'i bulunamayanlar için Kütüphanem → 'PDF'sizleri Sırayla Aç'.")
        elif kind == "scopus":
            self.scan_tab.on_scopus(message[1], message[2])
            if message[1] in ("done", "error"):
                self.library_tab.refresh()
        elif kind == "scan_status":
            self.scan_tab.on_status(message[1])
        elif kind == "scan_progress":
            self.scan_tab.on_progress(message[1])
        elif kind == "scan_finished":
            self.scan_tab.on_finished(message[1], message[2])
        elif kind == "scan":               # klasörden/PDF'ten kütüphaneye alma
            done, total, name = message[1:]
            if name:
                self.library_tab.count_label.configure(text=f"Kütüphaneye alınıyor {done + 1}/{total}: {shorten(name, 50)}")
        elif kind == "scan_done":
            added, updated, skipped, pending = (list(message[1:]) + [0])[:4]
            self.library_tab.refresh()
            extra = f" İnmemiş {pending} kaynak da PDF'siz olarak eklendi." if pending else ""
            self.toast(f"{added} kaynak eklendi, {updated} güncellendi, {skipped} zaten vardı.{extra}")
        elif kind == "watch_attached":
            item_id, name = message[1:]
            self.library_tab.refresh()
            self.toast(f"İndirilen PDF kütüphanedeki kaynağına bağlandı: {shorten(name, 60)}")
        elif kind == "watch_unmatched":
            name = message[1]
            self.toast(f"İndirilenler'deki “{shorten(name, 40)}” hiçbir PDF'siz kaynakla eşleşmedi — "
                       "kaynağı seçip 'PDF Bağla…' ile bağlayın.")
            self._log("warn", f"İndirilen {name} kütüphanedeki bir kaynakla otomatik eşleşmedi. Kütüphanem'de "
                              "kaynağı seçip 'PDF Bağla…' düğmesiyle bu dosyayı gösterin.")
        elif kind == "watch_done":
            newest = message[1]
            if newest > (self.settings.get("watch_since") or 0):
                current = load_settings()
                current["watch_since"] = newest
                save_settings(current)
                self.settings["watch_since"] = newest
        elif kind == "autotag":
            n, total = message[1:]
            self.library_tab.count_label.configure(text=f"Otomatik etiketleniyor {n}/{total}…")
        elif kind == "autotag_done":
            self.library_tab.autotag_finished(*message[1:])
        elif kind == "crossref_done":
            self.library_tab.crossref_done(message[1], message[2])

    def _on_close(self):
        if self.worker and self.worker.is_alive():
            if not messagebox.askyesno(APP_NAME, "İndirme devam ediyor. Durdurup çıkmak istiyor musunuz?",
                                       parent=self):
                return
            self.cancel_event.set()
            self.worker.join(timeout=3)
        scan = self.scan_tab.worker
        if scan and scan.is_alive():
            if not messagebox.askyesno(APP_NAME, "Haftalık tarama sürüyor. Durdurup çıkmak istiyor musunuz?\n"
                                                 "(Bir sonraki açılışta yeniden denenir.)", parent=self):
                return
            self.scan_tab.cancel.set()
            scan.join(timeout=5)
        self.save_all_settings()
        if getattr(self, "index_worker", None) is not None and self.index_worker.is_alive():
            self.index_worker.cancel.set()
            self.index_worker.join(timeout=5)
        running = getattr(self, "_sync_thread", None)
        if running is not None and running.is_alive():
            running.join(timeout=120)
        if self.sync.folder() is not None:
            self.sync_now(closing=True, quiet=True)
            self.sync.heartbeat(closing=True)
        try:
            self.library.close()
        except Exception:
            pass
        diag("uygulama kullanıcı tarafından kapatıldı")
        self.destroy()

    def report_callback_exception(self, exc_type, exc, tb):
        import traceback
        diag("ARAYÜZ HATASI:\n" + "".join(traceback.format_exception(exc_type, exc, tb)))
        try:
            self._log("error", f"Beklenmeyen hata: {exc_type.__name__}: {exc} (ayrıntı tanılama kaydında)")
        except Exception:
            pass

    def open_diagnostics(self):
        path = diag_path()
        if path.exists():
            open_file(path)
        else:
            messagebox.showinfo(APP_NAME, "Henüz tanılama kaydı yok.", parent=self)


def main():
    if "--ocr-selftest" in sys.argv:
        print(ocr_selftest())
        return
    if "--mcpb-pack" in sys.argv:            # derleme sırasında: .mcpb uzantı paketini üret
        i = sys.argv.index("--mcpb-pack")
        print(pack_mcpb(sys.argv[i + 1], sys.argv[i + 2]))
        return
    install_crash_logging()
    if updates_enabled() and not os.environ.get(UPDATE_ENV):
        if "--mcp" not in sys.argv:          # Claude bağlantısı ağı beklemesin; arayüzün indirdiğini kullanır
            try:
                fetch_update()
            except Exception:
                diag_exception("güncelleme denetimi")
        if run_updated_code():
            return
    if "--mcp" in sys.argv:                  # Claude masaüstü uygulaması bağlantısı
        run_mcp_server()
        return
    if "--tara" in sys.argv:              # Windows görev zamanlayıcısından: arayüzsüz tarama
        try:
            run_headless_scan()
        except Exception:
            diag_exception("arayüzsüz tarama")
        return
    ctk.set_appearance_mode("system")
    ctk.set_default_color_theme("blue")
    app = App()
    app.mainloop()


if __name__ == "__main__":
    main()
