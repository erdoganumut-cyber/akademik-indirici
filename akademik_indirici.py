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
- Haftada bir, düzenlenebilir anahtar kelime gruplarıyla DergiPark (OAI-PMH) ve Crossref'i
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
APP_VERSION = "2.0"

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
    # kütüphane künyesi için
    "citation_journal_title", "citation_volume", "citation_issue", "citation_firstpage",
    "citation_lastpage", "citation_publisher", "citation_language", "citation_book_title",
    "citation_inbook_title", "citation_conference_title", "citation_dissertation_institution",
    "citation_technical_report_institution", "citation_isbn", "dc.publisher", "dc.language",
}


def parse_attrs(tag: str) -> dict:
    attrs = {}
    for m in _ATTR_RE.finditer(tag):
        value = next(v for v in m.groups()[1:] if v is not None)
        attrs.setdefault(m.group(1).lower(), html.unescape(value).strip())
    return attrs


def parse_citation_meta(page: str) -> dict:
    """Google Scholar / Dublin Core <meta> etiketlerini okur (ilk değer geçerli).
    Tüm yazarlar ayrıca meta["_authors"] listesinde tutulur."""
    meta, authors = {}, []
    for tag in _META_TAG_RE.findall(page):
        attrs = parse_attrs(tag)
        key = (attrs.get("name") or attrs.get("property") or "").lower()
        if key == "dc.identifier" and not normalize_doi(attrs.get("content")):
            continue  # yalnızca DOI olan dc.identifier işimize yarar
        if key == "citation_author" and attrs.get("content"):
            authors.append(attrs["content"])
        if key in _WANTED_META and attrs.get("content") and key not in meta:
            meta[key] = attrs["content"]
    if authors:
        meta["_authors"] = authors
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


class WrongPdf(Exception):
    """İnen PDF'in başlığı makale sayfasındaki başlıkla uyuşmuyor (başka bir yayın)."""


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


def history_key(url: str) -> str:
    return "|".join(_dedupe_key(url))


def history_path() -> Path:
    return settings_path().parent / "indirme_gecmisi.json"


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
                                     source="indirme")
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
                 "publisher", "doi", "url", "editors", "institution", "language")

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


def tr_sort_key(text: str):
    return [_TR_RANK.get(c, 100 + ord(c)) for c in tr_lower(text)]


def looks_turkish(text: str, language: str = "") -> bool:
    return (language or "").lower().startswith("tr") or bool(re.search(r"[çğıöşüÇĞİÖŞÜ]", text or ""))


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
    }


def crossref_record(session, doi: str):
    """DOI'nin künyesini Crossref'ten alır (APA için en güvenilir kaynak)."""
    try:
        r = session.get(CROSSREF_API + quote(doi, safe="/:;()._-"), timeout=API_TIMEOUT,
                        headers={"Accept": "application/json"})
        if r.status_code != 200:
            return None
        return record_from_crossref(r.json().get("message") or {})
    except (requests.RequestException, ValueError, AttributeError, IndexError, TypeError):
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


def pdf_info(path) -> dict:
    try:
        from pypdf import PdfReader
        info = PdfReader(str(path)).metadata or {}
        return {"title": str(info.get("/Title") or ""), "author": str(info.get("/Author") or "")}
    except Exception:
        return {}


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
        add(f" [{w[kind]}{', ' + inst if inst else ''}]. ")
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
                   ("keywords", ", ".join(rec.get("tags") or []))]
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
        lines += [f"KW  - {t}" for t in rec.get("tags") or []]
        lines.append("ER  - ")
        out.append("\n".join(lines))
    return "\n\n".join(out) + "\n"


# ── Tek kütüphane klasörü ───────────────────────────────────────────────────

def library_filename(rec: dict, ext: str = ".pdf") -> str:
    """Kütüphane klasöründeki standart ad: 'Soyad (Yıl) - Başlık.pdf'"""
    people = rec.get("authors") or []
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
"""

# Sonradan eklenen sütunlar (eski veritabanları da açılabilsin diye)
_EXTRA_COLUMNS = {
    "is_new": "INTEGER DEFAULT 0",      # haftalık taramadan gelip henüz incelenmedi
    "source": "TEXT DEFAULT ''",        # indirme / tarama / klasör / elle
    "matched": "TEXT DEFAULT ''",       # taramada eşleşen grup ve kelimeler
}


def clean_tags(text_or_list) -> list:
    items = text_or_list if isinstance(text_or_list, (list, tuple)) else re.split(r"[,;\n]", text_or_list or "")
    seen, out = set(), []
    for tag in items:
        tag = re.sub(r"\s+", " ", str(tag)).strip()
        if tag and fold(tag) not in seen:
            seen.add(fold(tag))
            out.append(tag)
    return out


class Library:
    """Kaynakların künyesi, etiketleri, notları ve PDF tam metni (dosyalar yerinde kalır)."""

    def __init__(self, path=None):
        self.path = Path(path) if path else settings_path().parent / "kutuphane.db"
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.lock = threading.RLock()
        self.db = sqlite3.connect(str(self.path), check_same_thread=False, timeout=30)
        self.db.row_factory = sqlite3.Row
        with self.lock, self.db:
            self.db.executescript(_SCHEMA)
            have = {r[1] for r in self.db.execute("PRAGMA table_info(items)")}
            for column, decl in _EXTRA_COLUMNS.items():
                if column not in have:
                    self.db.execute(f"ALTER TABLE items ADD COLUMN {column} {decl}")

    # --- okuma ---------------------------------------------------------------
    def _to_item(self, row) -> dict:
        item = dict(row)
        for key in ("authors", "editors"):
            try:
                item[key] = json.loads(item[key] or "[]")
            except ValueError:
                item[key] = []
        return item

    def get(self, item_id: int):
        with self.lock:
            row = self.db.execute("SELECT * FROM items WHERE id=?", (item_id,)).fetchone()
            if not row:
                return None
            item = self._to_item(row)
            item["tags"] = sorted((r[0] for r in self.db.execute(
                "SELECT tag FROM tags WHERE item_id=?", (item_id,))), key=tr_sort_key)
            return item

    def all_items(self) -> list:
        with self.lock:
            items = {row["id"]: self._to_item(row) for row in self.db.execute("SELECT * FROM items")}
            for item in items.values():
                item["tags"] = []
            for item_id, tag in self.db.execute("SELECT item_id, tag FROM tags ORDER BY tag"):
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

    def find_by_path(self, path):
        with self.lock:
            row = self.db.execute("SELECT id FROM items WHERE file_path=?", (str(path),)).fetchone()
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
                "source, is_new, matched) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (rec["title"], json.dumps(rec["authors"], ensure_ascii=False), rec["year"], rec["type"],
                 rec["container"], rec["volume"], rec["issue"], rec["pages"], rec["publisher"],
                 rec["doi"], rec["url"], json.dumps(rec["editors"], ensure_ascii=False),
                 rec["institution"], rec["language"], str(file_path or ""), sha,
                 datetime.now().strftime("%Y-%m-%d"), source, 1 if is_new else 0, matched))
            item_id = cur.lastrowid
            if fulltext:
                self.set_fulltext(item_id, fulltext)
            self.add_tags(item_id, tags)
            return item_id, True

    def update(self, item_id: int, fields: dict):
        allowed = set(RECORD_FIELDS) | {"file_path", "sha256", "notes", "is_new", "source", "matched"}
        values = {}
        for key, value in fields.items():
            if key not in allowed:
                continue
            values[key] = json.dumps(value, ensure_ascii=False) if key in ("authors", "editors") else value
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
                matched=""):
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
    info = pdf_info(path) if not (cr or page_rec.get("title")) else {}
    info_rec = {}
    if info.get("title") and len(info["title"]) > 10 and not re.search(r"\.docx?$|untitled|microsoft", info["title"], re.I):
        info_rec = {"title": info["title"], "authors": text_to_people(info.get("author", ""))}
    record = merge_records(cr or {}, merge_records(page_rec, merge_records(
        file_rec if " - " in path.stem else {}, merge_records(info_rec, file_rec))))
    if doi and not record.get("doi"):
        record["doi"] = doi
    if url and not record.get("url") and not is_doi_host(url):
        record["url"] = url
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


class LibraryScanWorker(threading.Thread):
    """Seçilen PDF'leri (ya da bir klasördeki tüm PDF'leri) kütüphaneye alır.
    Mesajlar: ("scan", sıra, toplam, ad) · ("log", seviye, metin) · ("scan_done", eklenen, güncellenen, atlanan)"""

    def __init__(self, paths, library, events, cancel_event, tags=(), library_folder=None, move=False):
        super().__init__(daemon=True)
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
                    url = links.get(str(path), "")
                    _, created = catalog_pdf(self.library, session, path, sha, url=url,
                                             doi=doi_from_url(url) if url else None, tags=self.tags,
                                             library_folder=self.library_folder, move=self.move,
                                             source="klasör")
                    if created:
                        added += 1
                    else:
                        updated += 1
                except Exception as exc:
                    self.events.put(("log", "error", f"{path.name} eklenemedi: {describe_error(exc)}"))
        finally:
            session.close()
            self.events.put(("scan", total, total, ""))
            self.events.put(("scan_done", added, updated, skipped))


def attach_pdf(library, item_id: int, path, library_folder=None, move=True):
    """PDF'i olmayan bir kaynağa sonradan PDF bağlar (elle ya da İndirilenler izleyiciyle)."""
    item = library.get(item_id)
    path = Path(path)
    sha = file_sha256(path)
    target = place_in_library(path, item, library_folder, move=move)
    library.update(item_id, {"file_path": str(target), "sha256": sha})
    library.set_fulltext(item_id, pdf_text(target))
    return target


# ════════════════════════════════════════════════════════════════════════════
#  6) HAFTALIK TARAMA: anahtar kelimeler, DergiPark (OAI-PMH), Crossref, rapor
# ════════════════════════════════════════════════════════════════════════════

DERGIPARK_OAI = "https://dergipark.org.tr/api/public/oai/"
CROSSREF_SEARCH = "https://api.crossref.org/works"
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
# terimle birlikte bu kelimelerden biri de geçmelidir (çok anlamlı kısa terimler için).
# '#' ile başlayan satırlar açıklamadır.

[Halk dansları ve sahneleme]
bağlam: halk, oyun, dans, dance, folklor, folklore, folk
halk oyun
halk dans
folk dance
folklore on stage
spectacularization of folklore
staging folk
sahneleme
koreografi
choreograph
kültürel performans
cultural performance

[Etnokoreoloji ve notasyon]
etnokoreoloji
ethnochoreolog
koreoloji
choreolog
dans notasyon
dance notation
hareket notasyon
movement notation
labanotation
laban notasyon
kinetografi
kinetography
benesh
laban hareket analiz
laban movement analysis

[Dijital dönüşüm, MR ve hareket yakalama]
bağlam: dans, dance, oyun, folklor, folklore, miras, heritage, kültür, cultur, gelenek, tradition
hareket yakalama
motion capture
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
poz tahmin
markerless

[Somut olmayan kültürel miras]
bağlam: miras, heritage, dans, dance, gelenek, tradition, kültür, cultur
somut olmayan kültürel miras
intangible cultural heritage
yaşayan insan hazine
living human treasure
miras statüsü
heritage status
dans belgeleme
dance documentation
safeguarding

[Geleneksel sohbet toplantıları ve kültürel bellek]
geleneksel sohbet toplantı
sohbet toplantı
traditional sohbet
sohbet meeting
kültürel bellek
cultural memory
toplumsal bellek
collective memory
birikme gece
ateş gezme
sıra gecesi
ritual gathering
yaren ; bağlam: sohbet, toplantı, gelenek, folklor, halk, tradition
barana ; bağlam: sohbet, toplantı, gelenek, folklor, halk, tradition
gezek ; bağlam: sohbet, toplantı, gelenek, folklor, halk, tradition
oturak ; bağlam: sohbet, toplantı, gelenek, folklor, abdal, kırşehir, eğlence

[Dijital kültür]
dijital kültür
digital culture
e-kültürle
dijital kültürlenme
kültürel aktarım
cultural transmission
algoritmik kültür
algorithmic culture
platform kültür
platform culture

[Gelenek, icra ve yorum]
bağlam: dans, dance, oyun, müzik, music, halk, folk, gelenek, tradition, sanat, art
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
dans eğitim
dance education
dans pedagoji
dance pedagogy
halk oyunları öğretim
halk oyunları eğitim
folk dance teaching
ritim eğitim
rhythm education
ritim dikte
rhythmic dictation
aksak usul
aksak ritim
asma davul

[Dans, kimlik ve kültür politikası]
bağlam: dans, dance, oyun, folklor, folklore, müzik, music, halk, folk
kimlik
identity
ulus inşa
nation-building
nation building
kültür politika
cultural policy
kültürel diplomasi
cultural diplomacy
göç
migration
diaspora
milliyetçilik
nationalism

[Yöresel oyunlar]
bağlam: oyun, dans, halk, folk, dance, yöre, folklor
zeybek
horon
halay
bar
teke
kılıç kalkan
kaşık oyun
karşılama

[Dans ve bedenlenmiş biliş]
bedenlenmiş biliş
embodied cognition
embodiment ; bağlam: dance, dans
interpersonal coordination ; bağlam: dance, dans, movement
interactional synchrony
topluluk dans
community dance
community-based dance
dance improvisation
dans doğaçlama
distributed creativity
kinesthetic empathy
"""


def keywords_path() -> Path:
    return settings_path().parent / "anahtar_kelimeler.txt"


def load_keywords_text() -> str:
    try:
        return keywords_path().read_text(encoding="utf-8")
    except OSError:
        return DEFAULT_KEYWORDS


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
        if term.strip():
            current["terms"].append({"term": term.strip(), "context": ctx})
    return [g for g in groups if g["terms"]]


def _word_start(word: str):
    return re.compile(r"(?<!\w)" + re.escape(fold(word)))


class KeywordMatcher:
    """Metinde hangi grup/terimlerin geçtiğini bulur (Türkçe ekleri tolere eder)."""

    def __init__(self, groups):
        self.groups = []
        for g in groups:
            group_ctx = [_word_start(w) for w in g.get("context") or []]
            terms = []
            for t in g["terms"]:
                ctx = [_word_start(w) for w in t["context"]] if t.get("context") is not None else group_ctx
                terms.append((t["term"], _word_start(t["term"]), ctx))
            self.groups.append((g["name"], terms))

    def match(self, text: str) -> dict:
        """{grup adı: [eşleşen terimler]}"""
        body = fold(text)
        hits = {}
        for name, terms in self.groups:
            for term, rx, ctx in terms:
                if rx.search(body) and (not ctx or any(c.search(body) for c in ctx)):
                    hits.setdefault(name, []).append(term)
        return hits

    def search_terms(self) -> list:
        """Crossref'te aranacak sorgular (kısa/çok anlamlı terimlere bağlam eklenir)."""
        out = []
        for name, terms in self.groups:
            for term, _, ctx in terms:
                query = term
                if ctx and len(term) < 9:
                    continue          # 'bar', 'teke' gibi terimler Crossref'te anlamsız sonuç verir
                out.append((name, query))
        return out


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
        })
    token_el = root.find(".//oai:resumptionToken", _NS)
    token = token_el.text.strip() if token_el is not None and token_el.text and token_el.text.strip() else None
    total = 0
    if token_el is not None and (token_el.get("completeListSize") or "").isdigit():
        total = int(token_el.get("completeListSize"))
    return records, token, total, None


def harvest_dergipark(session, since: datetime, until: datetime, progress=None, cancel=None):
    """DergiPark'a 'since' tarihinden beri eklenen/güncellenen makaleleri sayfa sayfa getirir."""
    params = {"verb": "ListRecords", "metadataPrefix": "oai_dc",
              "from": since.strftime("%Y-%m-%dT%H:%M:%SZ"), "until": until.strftime("%Y-%m-%dT%H:%M:%SZ")}
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


def search_crossref(session, query: str, since: datetime, rows: int = 100):
    params = {"query.bibliographic": query, "rows": rows,
              "filter": f"from-created-date:{since.strftime('%Y-%m-%d')}",
              "select": "DOI,title,subtitle,author,editor,container-title,issued,published-print,"
                        "published-online,type,abstract,subject,language,URL,publisher,volume,issue,page"}
    r = session.get(CROSSREF_SEARCH, params=params, timeout=(15, 60), headers={"Accept": "application/json"})
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


# ── Tarama raporu (HTML) ────────────────────────────────────────────────────

def _h(text) -> str:
    return html.escape(str(text or ""))


def write_scan_report(path: Path, info: dict, found: list, added_items: list) -> Path:
    """found: [{"record", "hits", "status", "item_id"}] · added_items: o hafta eklenen kaynaklar"""
    groups = {}
    for entry in found:
        for group in entry["hits"]:
            groups.setdefault(group, []).append(entry)
    status_label = {"pdf": ("PDF indirildi", "ok"), "nopdf": ("PDF yok", "warn"),
                    "institution": ("Kurum erişimi gerekebilir", "inst"), "known": ("Zaten kütüphanede", "muted")}

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
        title = _h(rec.get("title") or "(başlıksız)")
        title_html = f'<a href="{_h(link)}">{title}</a>' if link else title
        return (f'<li><div class="t">{title_html}</div><div class="m">{_h(meta)}</div>'
                f'<div class="c"><span class="chip {cls}">{_h(label)}{" · " + _h(db) if db else ""}</span>'
                f'<span class="chip">{_h(rec.get("source", ""))}</span>'
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
        f'<div class="m">{_h({"tarama": "Taramadan", "indirme": "İndirmeden", "klasör": "Klasörden"}.get(i.get("source"), "Elle"))}'
        f'{" · PDF var" if i.get("file_path") else " · PDF yok"}</div></li>'
        for i in added_items)
    errors = "".join(f"<li>{_h(e)}</li>" for e in info.get("errors", []))
    pdf_count = sum(1 for e in found if e["status"] == "pdf")
    new_count = sum(1 for e in found if e["status"] != "known")
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
.chip.inst{{color:var(--inst);border-color:var(--inst)}}.kw{{font-size:12px;color:var(--muted)}}
.empty{{color:var(--muted)}}footer{{color:var(--muted);font-size:12px;margin-top:40px}}
</style></head><body><main>
<h1>Haftalık Tarama Raporu</h1>
<p class="sub">{_h(info['since'])} – {_h(info['until'])} arası · Kaynaklar: {_h(', '.join(info.get('sources', [])))}</p>
<div class="stats">
<div class="stat"><b>{new_count}</b><span>yeni yayın</span></div>
<div class="stat"><b>{pdf_count}</b><span>PDF indirildi</span></div>
<div class="stat"><b>{info.get('dergipark', 0)}</b><span>DergiPark kaydı tarandı</span></div>
<div class="stat"><b>{info.get('crossref', 0)}</b><span>Crossref kaydı tarandı</span></div>
<div class="stat"><b>{len(added_items)}</b><span>kütüphaneye eklendi (tümü)</span></div>
</div>
{''.join(sections)}
<section><h2>Bu dönemde kütüphaneye eklenen tüm kaynaklar <small>{len(added_items)}</small></h2>
<ul>{added_rows or '<p class="empty">Yok.</p>'}</ul></section>
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


def acquire_scan_lock() -> bool:
    """Aynı anda iki tarama (uygulama + zamanlanmış görev) çalışmasın."""
    path = scan_lock_path()
    try:
        if path.exists() and time.time() - path.stat().st_mtime < 3 * 3600:
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

    def log(self, level, text):
        self.events.put(("log", level, text))

    def run(self):
        if not acquire_scan_lock():
            self.summary = "Başka bir tarama zaten çalışıyor."
            self.events.put(("scan_finished", None, self.summary))
            return
        try:
            self._run()
        except Exception as exc:
            self.summary = f"Tarama yarıda kaldı: {describe_error(exc)}"
            self.log("error", self.summary)
            self.events.put(("scan_finished", None, self.summary))
        finally:
            release_scan_lock()

    def _run(self):
        now = utc_now()
        last = self.settings.get("last_scan")
        try:
            since = datetime.fromisoformat(last) if last else now - timedelta(days=SCAN_FIRST_WINDOW_DAYS)
        except ValueError:
            since = now - timedelta(days=SCAN_FIRST_WINDOW_DAYS)
        since = max(since, now - timedelta(days=60))       # çok uzun aralar için sınır
        matcher = KeywordMatcher(parse_keyword_groups(load_keywords_text()))
        session = make_session()
        info = {"since": since.strftime("%d.%m.%Y"), "until": now.strftime("%d.%m.%Y"),
                "sources": [], "errors": [], "dergipark": 0, "crossref": 0,
                "created": datetime.now().strftime("%d.%m.%Y %H:%M")}
        candidates = {}       # anahtar → {"record", "hits"}
        reached = []          # ulaşılabilen kaynaklar (hiçbiri yoksa tarama 'yapılmamış' sayılır)

        def key_of(rec):
            return (rec.get("doi") or "").lower() or rec.get("url") or fold(rec.get("title", ""))

        def consider(rec):
            # dergi adı bilerek dışarıda: 'Millî Folklor'da çıkan her makale 'folklor' bağlamı sayılmasın
            text = " ".join([rec.get("title", ""), " ".join(rec.get("all_titles", [])),
                             " ".join(rec.get("subjects", [])), rec.get("description", "")])
            hits = matcher.match(text)
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

        # 3) Kütüphaneye ekleme + açık erişim PDF
        found = []
        library_folder = self.settings.get("library_folder") or None
        if library_folder:
            try:
                Path(library_folder).mkdir(parents=True, exist_ok=True)
            except OSError as exc:
                info["errors"].append(f"Kütüphane klasörü oluşturulamadı: {describe_error(exc)}")
                library_folder = None
        downloader = DownloadWorker([], library_folder or str(Path.home()), {
            "find_pdf": True, "save_html": False, "email": self.settings.get("email", ""),
            "library": self.library, "library_folder": library_folder}, queue.Queue(), self.cancel)
        attempts = 0
        total = len(candidates)
        for n, entry in enumerate(candidates.values(), start=1):
            if self.cancel.is_set():
                break
            rec, hits = entry["record"], entry["hits"]
            self.events.put(("scan_progress", 0.85 + 0.15 * n / max(total, 1)))
            self.status(f"Yeni yayınlar kütüphaneye ekleniyor ({n}/{total})")
            known = (self.library.find_by_doi(rec.get("doi")) or self.library.find_by_url(rec.get("url"))
                     or self.library.find_by_title(rec.get("title")))
            if known:
                found.append({"record": rec, "hits": hits, "status": "known", "item_id": known})
                continue
            tags = list(hits)
            matched = describe_hits(hits)
            status, item_id = "nopdf", None
            link = ("https://doi.org/" + rec["doi"]) if rec.get("doi") else rec.get("url")
            if link and attempts < SCAN_MAX_DOWNLOADS and library_folder:
                attempts += 1
                try:
                    downloader._last_saved = None
                    downloader._tried = set()
                    result = downloader._download_one(session, link, n)
                    saved = downloader._last_saved
                    if result[0] == "ok" and saved:
                        item_id, _ = catalog_pdf(self.library, session, saved["path"], saved["sha"],
                                                 meta=saved["meta"], url=rec.get("url") or link,
                                                 doi=rec.get("doi") or None, tags=tags,
                                                 library_folder=library_folder, source="tarama",
                                                 is_new=True, matched=matched)
                        status = "pdf"
                except Exception as exc:
                    info["errors"].append(f"{rec.get('title', '')[:60]}: {describe_error(exc)}")
            if item_id is None:
                record = {k: rec.get(k) for k in RECORD_FIELDS if rec.get(k)}
                item_id, _ = self.library.add(record, tags=tags, source="tarama", is_new=True,
                                              matched=matched)
                if rec.get("doi") and database_for_doi(rec["doi"]):
                    status = "institution"
            else:
                self.library.update(item_id, {"is_new": 1, "matched": matched})
            found.append({"record": rec, "hits": hits, "status": status, "item_id": item_id})
        session.close()

        if not reached:
            self.summary = ("Hiçbir kaynağa ulaşılamadı (internet bağlantısını kontrol edin); "
                            "tarama bir sonraki açılışta yeniden denenecek.")
            self.log("warn", self.summary)
            self.events.put(("scan_progress", 0.0))
            self.events.put(("scan_finished", None, self.summary))
            return
        added_items = self.library.items_added_since(since.strftime("%Y-%m-%d"))
        folder = Path(library_folder or settings_path().parent) / "Tarama Raporları"
        self.report_path = write_scan_report(folder / f"Tarama_{datetime.now():%Y-%m-%d_%H%M%S}.html",
                                             info, found, added_items)
        new = sum(1 for e in found if e["status"] != "known")
        pdfs = sum(1 for e in found if e["status"] == "pdf")
        self.summary = f"{new} yeni yayın bulundu, {pdfs} tanesinin PDF'i indi."
        if not self.cancel.is_set():
            self.settings["last_scan"] = now.isoformat()
            self.settings["last_report"] = str(self.report_path)
            current = load_settings()
            current.update(last_scan=self.settings["last_scan"], last_report=self.settings["last_report"])
            save_settings(current)
        self.events.put(("scan_progress", 1.0))
        self.events.put(("scan_finished", str(self.report_path), self.summary))


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


def _run_quiet(args):
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
    return subprocess.run(args, capture_output=True, text=True, creationflags=flags)


def schedule_weekly_scan(day: str, hour: str):
    """Haftalık taramayı Windows görev zamanlayıcısına ekler. Dönüş: (başarılı_mı, mesaj)"""
    if not sys.platform.startswith("win"):
        return False, "Zamanlanmış görev yalnızca Windows'ta kurulabilir."
    if not getattr(sys, "frozen", False):
        return False, "Zamanlanmış görev yalnızca .exe sürümünden kurulabilir."
    command = f'"{sys.executable}" --tara'
    result = _run_quiet(["schtasks", "/Create", "/F", "/SC", "WEEKLY", "/D", WEEKDAYS.get(day, "MON"),
                         "/ST", hour, "/TN", TASK_NAME, "/TR", command])
    if result.returncode == 0:
        return True, f"Her {day} {hour}'da tarama yapılacak."
    return False, (result.stderr or result.stdout or "schtasks hata verdi").strip()


def unschedule_weekly_scan():
    if not sys.platform.startswith("win"):
        return False, "Yalnızca Windows'ta."
    result = _run_quiet(["schtasks", "/Delete", "/F", "/TN", TASK_NAME])
    return result.returncode == 0, (result.stderr or result.stdout).strip()


def weekly_scan_scheduled() -> bool:
    if not sys.platform.startswith("win"):
        return False
    try:
        return _run_quiet(["schtasks", "/Query", "/TN", TASK_NAME]).returncode == 0
    except OSError:
        return False


def run_headless_scan():
    """Zamanlanmış görev: arayüz açmadan tarar, raporu yazar ve tarayıcıda açar."""
    settings = load_settings()
    library = Library()
    events = queue.Queue()
    worker = ScanWorker(library, settings, events, threading.Event())
    worker.run()
    library.close()
    if worker.report_path and settings.get("open_report", True):
        webbrowser.open(Path(worker.report_path).as_uri())


# ════════════════════════════════════════════════════════════════════════════
#  7) AYARLAR (klasör, e-posta ve seçenekler bir sonraki açılışta hatırlanır)
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


def default_library_dir() -> Path:
    docs = Path.home() / "Documents"
    return (docs if docs.is_dir() else Path.home()) / "Akademik Kütüphanem"


def show_in_file_manager(path: Path):
    path = Path(path)
    if sys.platform.startswith("win"):
        subprocess.Popen(["explorer", "/select,", str(path)])
    else:
        open_in_file_manager(path.parent)


def open_file(path: Path):
    if sys.platform.startswith("win"):
        os.startfile(str(path))  # type: ignore[attr-defined]
    elif sys.platform == "darwin":
        subprocess.Popen(["open", str(path)])
    else:
        subprocess.Popen(["xdg-open", str(path)])


def add_italic_tag(textbox):
    """CTkTextbox'a, kutunun kendi yazısıyla aynı boyutta 'i' (italik) etiketi ekler."""
    from tkinter import font as tkfont
    inner = textbox._textbox
    try:
        actual = tkfont.Font(root=inner, font=inner.cget("font")).actual()
        inner.tag_configure("i", font=(actual["family"], actual["size"], "italic"))
    except Exception:
        inner.tag_configure("i", font=("TkDefaultFont", 10, "italic"))


class BibliographyDialog(ctk.CTkToplevel):
    """Seçilen kaynakların APA kaynakçası: panoya kopyala ya da Word olarak kaydet."""

    def __init__(self, master, records, lang="tr"):
        super().__init__(master)
        self.title(f"Kaynakça · {len(records)} kaynak")
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

    STATUS_FILTERS = ["Tümü", "Yeni (taramadan)", "PDF'i olanlar", "PDF'i olmayanlar", "Kartı olanlar"]

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
                                   placeholder_text="Ara: başlık, yazar, dergi, etiket, alıntı kartı…")
        self.search.grid(row=0, column=0, sticky="ew")
        self.search.bind("<KeyRelease>", lambda _: self._schedule_refresh())
        self.fulltext_var = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(bar, text="PDF içinde de ara", variable=self.fulltext_var, width=20,
                        command=self.refresh, font=ctk.CTkFont(size=12)).grid(row=0, column=1, padx=10)
        self.tag_menu = ctk.CTkOptionMenu(bar, values=["Tüm etiketler"], width=170,
                                          command=lambda _: self.refresh(), dynamic_resizing=False)
        self.tag_menu.grid(row=0, column=2, padx=(0, 8))
        self.status_menu = ctk.CTkOptionMenu(bar, values=self.STATUS_FILTERS, width=160,
                                             command=lambda _: self.refresh(), dynamic_resizing=False)
        self.status_menu.grid(row=0, column=3, padx=(0, 8))
        ctk.CTkButton(bar, text="PDF Ekle…", width=96, command=self._add_pdfs).grid(row=0, column=4, padx=(0, 8))
        ctk.CTkButton(bar, text="Klasör Tara…", width=110, fg_color="transparent", border_width=1,
                      text_color=TEXT, command=self._scan_folder).grid(row=0, column=5)

    def _build_table(self):
        from tkinter import ttk
        frame = ctk.CTkFrame(self.parent, corner_radius=12)
        frame.grid(row=1, column=0, sticky="nsew", padx=(8, 6))
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(0, weight=1)
        cols = ("pdf", "author", "year", "title", "tags")
        self.tree = ttk.Treeview(frame, columns=cols, show="headings", selectmode="extended",
                                 style="Lib.Treeview")
        for col, text, width, stretch in (("pdf", "", 34, False), ("author", "Yazar", 150, False),
                                          ("year", "Yıl", 52, False), ("title", "Başlık", 360, True),
                                          ("tags", "Etiketler", 150, False)):
            self.tree.heading(col, text=text, command=lambda c=col: self._sort(c))
            self.tree.column(col, width=width, minwidth=30, stretch=stretch,
                             anchor="center" if col in ("pdf", "year") else "w")
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
                ("institution", "Kurum (tez)", ""), ("doi", "DOI", "10.xxxx/…"), ("url", "Link", ""),
                ("tags", "Etiketler", "virgülle ayırın")], start=1):
            entry = ctk.CTkEntry(form, placeholder_text=hint, height=30)
            self._field(form, row, label, entry)
            self.f[key] = entry
        self.f_type = ctk.CTkOptionMenu(form, values=list(ITEM_TYPES.values()), height=30)
        self._field(form, 13, "Tür", self.f_type)
        self.matched_label = ctk.CTkLabel(form, text="", text_color=MUTED, font=ctk.CTkFont(size=11),
                                          anchor="w", justify="left", wraplength=360)
        self.matched_label.grid(row=14, column=0, columnspan=2, sticky="ew", padx=4, pady=(6, 0))

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
        self.inst_btn = ctk.CTkButton(btns, text="Kurum Erişimiyle Aç", command=self._open_institution,
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
        self.remove_btn.grid(row=2, column=1, columnspan=2, sticky="ew", padx=2, pady=2)

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
        for item in self.items:
            item["has_pdf"] = bool(item["file_path"]) and Path(item["file_path"]).is_file()
            item["cards"] = card_counts.get(item["id"], 0)
            item["_blob"] = fold(" ".join([item["title"], people_to_text(item["authors"]), item["container"],
                                           item["year"], item["notes"], " ".join(item["tags"]), item["doi"],
                                           item.get("matched", "")]))
        tags = self.lib.all_tags()
        current_tag = self.tag_menu.get()
        self.tag_menu.configure(values=["Tüm etiketler"] + tags)
        if current_tag not in tags:
            self.tag_menu.set("Tüm etiketler")

        words = [w for w in fold(self.search.get()).split() if w]
        extra = set()
        if words:
            extra |= self.lib.card_text_ids(words)
            if self.fulltext_var.get():
                extra |= self.lib.fulltext_ids(words)
        tag = self.tag_menu.get()
        status = self.status_menu.get()

        def visible(item):
            if words and not (all(w in item["_blob"] for w in words) or item["id"] in extra):
                return False
            if tag != "Tüm etiketler" and tag not in item["tags"]:
                return False
            return {"Tümü": True, "Yeni (taramadan)": item["is_new"], "PDF'i olanlar": item["has_pdf"],
                    "PDF'i olmayanlar": not item["has_pdf"], "Kartı olanlar": item["cards"] > 0}[status]

        shown = [i for i in self.items if visible(i)]
        keys = {"author": lambda i: tr_sort_key(first_author_label(i)), "year": lambda i: i["year"] or "0",
                "title": lambda i: tr_sort_key(i["title"]), "tags": lambda i: tr_sort_key(", ".join(i["tags"])),
                "pdf": lambda i: i["has_pdf"], "added": lambda i: (i["added"], i["id"])}
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
                             values=(mark, first_author_label(item), item["year"], title, ", ".join(item["tags"])))
        keep = [s for s in selected if self.tree.exists(s)]
        if keep:
            self.tree.selection_set(keep)
            self.tree.see(keep[0])
        new = sum(1 for i in self.items if i["is_new"])
        nopdf = sum(1 for i in self.items if not i["has_pdf"])
        self.count_label.configure(text=f"{len(shown)} / {len(self.items)} kaynak · {new} yeni · {nopdf} PDF'siz")
        if not keep:
            self._show(None)

    def _sort(self, col):
        if self.sort_col == col:
            self.sort_rev = not self.sort_rev
        else:
            self.sort_col, self.sort_rev = col, col in ("year", "pdf")
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
                    self.remove_btn, self.card_save):
            btn.configure(state=state)
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
        has_pdf = bool(item["file_path"]) and Path(item["file_path"]).is_file()
        self.open_btn.configure(state="normal" if has_pdf else "disabled")
        self.show_btn.configure(state="normal" if has_pdf else "disabled")
        self.attach_btn.configure(text="PDF'i Değiştir…" if has_pdf else "PDF Bağla…")
        if has_pdf:
            self.pdf_label.configure(text=f"📄 {Path(item['file_path']).name}", text_color=TEXT)
        else:
            db = database_for_doi(item["doi"])
            hint = f" · kurum erişimi: {db}" if db else ""
            self.pdf_label.configure(text=f"PDF yok{hint}", text_color=LOG_COLORS["warn"])
        self.f_title.insert("1.0", item["title"])
        values = dict(item, authors=people_to_text(item["authors"]), editors=people_to_text(item["editors"]),
                      tags=", ".join(item["tags"]))
        for key, entry in self.f.items():
            if values.get(key):
                entry.insert(0, values[key])
        self.f_type.set(ITEM_TYPES.get(item["type"], "Diğer"))
        info = []
        if item.get("source"):
            info.append({"tarama": "Haftalık taramadan", "indirme": "İndiriciden", "klasör": "Klasör taramasından",
                         "elle": "Elle eklendi"}.get(item["source"], item["source"]))
        if item.get("added"):
            info.append(f"eklendi: {item['added']}")
        if item.get("matched"):
            info.append(f"eşleşen: {item['matched']}")
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

    def _render_apa(self):
        if not self.current:
            return
        rec = self.lib.get(self.current["id"])
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
        item = self.current
        if not item:
            return
        link = ("https://doi.org/" + item["doi"]) if item["doi"] else item["url"]
        db = database_for_doi(item["doi"])
        if link:
            webbrowser.open_new_tab(link)
        portal = self.app.settings.get("institution_url") or DEFAULT_INSTITUTION_URL
        msg = ("Makale tarayıcıda açıldı. Kampüs ağındaysanız doğrudan PDF'i indirebilirsiniz.\n\n"
               "Kampüs dışındaysanız kurum erişim sayfasında (VETİS) giriş yapıp "
               + (f"listeden “{db}” veritabanını açın ve makaleyi orada arayın."
                  if db else "ilgili veritabanını açıp makaleyi orada arayın.")
               + "\n\nİndirdiğiniz PDF, İndirilenler klasörünüzden kendiliğinden bu kaynağa bağlanır.\n\n"
               "Kurum erişim sayfası da açılsın mı?")
        if messagebox.askyesno(APP_NAME, msg, parent=self.parent):
            webbrowser.open_new_tab(portal)

    def _attach_pdf(self):
        item = self.current
        if not item:
            return
        path = filedialog.askopenfilename(parent=self.parent, title="Bu kaynağın PDF'ini seçin",
                                          filetypes=[("PDF", "*.pdf"), ("Tüm dosyalar", "*.*")])
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
        for item in self.selected_items():
            self.lib.update(item["id"], {"is_new": 0})
        self.refresh()

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
        paths = filedialog.askopenfilenames(parent=self.parent, title="Kütüphaneye eklenecek PDF'ler",
                                            filetypes=[("PDF", "*.pdf")])
        if paths:
            self._start_import(paths)

    def _scan_folder(self):
        folder = filedialog.askdirectory(parent=self.parent, title="PDF'lerin bulunduğu klasörü seçin")
        if not folder:
            return
        paths = sorted(Path(folder).rglob("*.pdf"))
        lib_folder = self.app.library_folder()
        if lib_folder:
            paths = [p for p in paths if Path(lib_folder) not in p.parents]
        if not paths:
            messagebox.showinfo(APP_NAME, "Bu klasörde (kütüphane klasörü dışında) PDF bulunamadı.", parent=self.parent)
            return
        self._start_import(paths)

    def _start_import(self, paths):
        move = messagebox.askyesnocancel(
            APP_NAME, f"{len(paths)} PDF kütüphaneye alınacak.\n\n"
                      "Dosyalar kütüphane klasörüne TAŞINSIN mı?\n"
                      "Evet: taşınır (tek klasör) · Hayır: kopyalanır, asılları yerinde kalır", parent=self.parent)
        if move is None:
            return
        dialog = ctk.CTkInputDialog(text="Bu kaynaklara eklenecek etiket (isteğe bağlı, virgülle):",
                                    title="Etiket")
        tags = dialog.get_input() or ""
        self.app.start_import(paths, clean_tags(tags), move)

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

        section("Kendiliğinden çalışma")
        ctk.CTkLabel(side, text="Uygulama kapalıyken de taraması için Windows görev zamanlayıcısına "
                                "bir kez kurun. Bilgisayar o gün kapalıysa, uygulamayı açtığınızda "
                                "7 gün geçmişse tarama kendiliğinden başlar.", text_color=MUTED,
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
        ctk.CTkButton(when, text="Windows'a Kur", width=118, command=self.schedule).grid(
            row=1, column=0, pady=(6, 0), sticky="w")
        ctk.CTkButton(when, text="Kaldır", width=84, fg_color="transparent", border_width=1, text_color=TEXT,
                      command=self.unschedule).grid(row=1, column=1, padx=6, pady=(6, 0), sticky="w")
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
        ctk.CTkLabel(side, text="Google Scholar uyarı e-postalarını İndir sekmesine yapıştırırsanız "
                                "içindeki makaleler de iner ve kütüphaneye girer.", text_color=MUTED,
                     font=ctk.CTkFont(size=12), wraplength=330, justify="left",
                     anchor="w").grid(row=r, column=0, sticky="ew", padx=10, pady=(2, 0)); r += 1

        section("Kütüphane ayarları")
        lf = ctk.CTkFrame(side, fg_color="transparent")
        lf.grid(row=r, column=0, sticky="ew", padx=10); r += 1
        lf.grid_columnconfigure(0, weight=1)
        ctk.CTkEntry(lf, textvariable=self.app.folder_var, height=30).grid(row=0, column=0, sticky="ew")
        ctk.CTkButton(lf, text="Seç…", width=60, command=self.app.choose_library_folder).grid(row=0, column=1, padx=(6, 0))
        self.watch_var = ctk.BooleanVar(value=s.get("watch_downloads", True))
        ctk.CTkCheckBox(side, text="İndirilenler klasörünü izle (indirdiğim PDF'i doğru kaynağa bağla)",
                        variable=self.watch_var, command=self.app.save_all_settings).grid(
            row=r, column=0, sticky="w", padx=10, pady=(8, 3)); r += 1
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
        self.kw_info.configure(text=f"{len(groups)} grup · {sum(len(g['terms']) for g in groups)} terim")

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

    def start_scan(self, automatic=False):
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
        self.worker = ScanWorker(self.app.library, load_settings(), self.app.events, self.cancel)
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
        self.scan_btn.configure(state="normal", text="Şimdi Tara")
        self.stop_btn.configure(state="disabled")
        self.status_label.configure(text=summary)
        self.update_info()
        self.app.library_tab.refresh()
        if report:
            self.app.notify_report(report, summary)
            if self.open_report_var.get():
                webbrowser.open(Path(report).as_uri())

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

    # ── zamanlama ───────────────────────────────────────────────────────────
    def schedule(self):
        ok, msg = schedule_weekly_scan(self.day_menu.get(), self.hour_menu.get())
        self.app.save_all_settings()
        (messagebox.showinfo if ok else messagebox.showwarning)(APP_NAME, msg, parent=self.parent)
        self.refresh_schedule_label()

    def unschedule(self):
        ok, msg = unschedule_weekly_scan()
        if not ok and msg:
            messagebox.showwarning(APP_NAME, msg, parent=self.parent)
        self.refresh_schedule_label()

    def refresh_schedule_label(self):
        if weekly_scan_scheduled():
            self.sched_label.configure(text=f"✓ Kurulu: her {self.day_menu.get()} {self.hour_menu.get()}",
                                       text_color=LOG_COLORS["success"])
        else:
            self.sched_label.configure(text="Windows görevi kurulu değil.", text_color=MUTED)


class DownloadsWatcher(threading.Thread):
    """İndirilenler klasörüne yeni düşen PDF'leri PDF'i olmayan kaynaklarla eşleştirir."""

    def __init__(self, library, folder, since: float, library_folder, events):
        super().__init__(daemon=True)
        self.library = library
        self.folder = Path(folder)
        self.since = since
        self.library_folder = library_folder
        self.events = events
        self.newest = since

    def run(self):
        try:
            candidates = [p for p in self.folder.glob("*.pdf")
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
                head = pdf_text(path, max_pages=2, max_chars=20_000)
                target = None
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
            except Exception:
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
        self.library = Library()
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
        self.after(600, self._first_run)
        self.after(15_000, self._watch_downloads)
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
        self.tag_entry = ctk.CTkEntry(email_row, height=30, placeholder_text="ör. tez bölüm 2")
        self.tag_entry.grid(row=0, column=3, sticky="ew")
        ctk.CTkLabel(
            card, font=ctk.CTkFont(size=11), text_color=MUTED, anchor="w", justify="left",
            wraplength=540,
            text="E-posta isteğe bağlı: girerseniz DOI'lerin yasal açık erişim kopyaları Unpaywall'da aranır "
                 "(adres yalnızca Unpaywall'a gönderilir). Etiket, bu indirmede inen kaynaklara verilir.",
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
                "watch_downloads": scan.watch_var.get(), "scan_day": scan.day_menu.get(),
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
        report = self.settings.get("last_report")
        seen = self.settings.get("seen_report")
        if report and report != seen and Path(report).is_file():
            self.notify_report(report, "Yeni tarama raporu hazır")
        if self.settings.get("auto_scan", True) and scan_due(self.settings) and self.library_folder():
            self._log("info", "Son taramanın üzerinden 7 gün geçmiş; haftalık tarama arka planda başlıyor.")
            self.scan_tab.start_scan(automatic=True)

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

    def start_import(self, paths, tags, move):
        if self.import_worker and self.import_worker.is_alive():
            messagebox.showinfo(APP_NAME, "Önceki ekleme işlemi sürüyor.", parent=self)
            return
        self.import_worker = LibraryScanWorker(paths, self.library, self.events, threading.Event(),
                                               tags=tags, library_folder=self.library_folder(), move=move)
        self.library_tab.count_label.configure(text=f"{len(paths)} PDF kütüphaneye alınıyor…")
        self.import_worker.start()

    def _watch_downloads(self):
        try:
            if (self.settings.get("watch_downloads", True) and self.library_folder()
                    and not (self.watcher and self.watcher.is_alive())):
                downloads = Path.home() / "Downloads"
                if downloads.is_dir():
                    since = max(self.settings.get("watch_since", 0) or 0, self.started - 3600)
                    self.watcher = DownloadsWatcher(self.library, downloads, since,
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
                   "tags": clean_tags(self.tag_entry.get())}
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
            added, updated, skipped = message[1:]
            self.library_tab.refresh()
            self.toast(f"{added} kaynak eklendi, {updated} güncellendi, {skipped} zaten vardı.")
        elif kind == "watch_attached":
            item_id, name = message[1:]
            self.library_tab.refresh()
            self.toast(f"İndirilen PDF kütüphanedeki kaynağına bağlandı: {shorten(name, 60)}")
        elif kind == "watch_done":
            newest = message[1]
            if newest > (self.settings.get("watch_since") or 0):
                current = load_settings()
                current["watch_since"] = newest
                save_settings(current)
                self.settings["watch_since"] = newest
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
        try:
            self.library.close()
        except Exception:
            pass
        self.destroy()


def main():
    if "--tara" in sys.argv:              # Windows görev zamanlayıcısından: arayüzsüz tarama
        run_headless_scan()
        return
    ctk.set_appearance_mode("system")
    ctk.set_default_color_theme("blue")
    app = App()
    app.mainloop()


if __name__ == "__main__":
    main()
