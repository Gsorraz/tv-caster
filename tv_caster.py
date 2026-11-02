#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
TV Caster - envia áudio e vídeo do PC para a TV pela rede (DLNA/UPnP).

Alvo: Samsung UN43T5300 (Tizen 2020) e LG (webOS), mas funciona com qualquer
TV que seja "Media Renderer" DLNA (TCL, Philips, Sony...).
LG: ligue a TV (não em espera) e deixe o compartilhamento de mídia ativo.

Como funciona:
  1. Descobre a TV na rede via SSDP (multicast UDP 239.255.255.250:1900).
  2. Sobe um servidor HTTP local servindo o arquivo escolhido (com Range,
     para a TV conseguir avançar/voltar).
  3. Manda para a TV os comandos UPnP (SetAVTransportURI, Play, Pause,
     Seek, SetVolume...). A própria TV baixa e reproduz o arquivo.
  4. Legendas: acha o .srt/.ass/.vtt ao lado do vídeo, converte para SRT
     (UTF-8) e entrega à TV junto com o vídeo (extensão Samsung CaptionInfo).
  5. Controle pelo celular: o mesmo servidor entrega uma página de controle
     (botão "Celular" mostra o endereço e o QR code).

Só usa a biblioteca padrão do Python.
Transmitir (botão no topo): captura a tela, uma janela ou só o som do PC e manda
ao vivo para a TV (ffmpeg + captura de áudio WASAPI; usa a placa de vídeo quando
dá). A imagem chega à TV com alguns segundos de atraso, então não serve para
jogos de ação (nesses, use Win+K).

Legendas embutidas em MKV (texto/ASS/SRT): o programa lê as faixas, extrai a
escolhida para SRT e tira as embutidas do que vai para a TV (o arquivo em disco
não é alterado), então dá para escolher a faixa ou desligar de verdade.
Opcionais: ffmpeg (converter o vídeo) e segno (pip install segno) para o QR code.

Firewall do Windows: na primeira execução, permita o Python em
"Redes privadas", senão a TV (e o celular) não conseguem acessar o PC.
"""

import hashlib
import html
import json
import os
import queue
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import xml.etree.ElementTree as ET
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, filedialog

HTTP_PORT = 8765
SSDP_ADDR = ("239.255.255.250", 1900)
DLNA_FEATURES = ("DLNA.ORG_OP=01;DLNA.ORG_CI=0;"
                 "DLNA.ORG_FLAGS=01700000000000000000000000000000")


def _config_dir():
    """Script: ao lado do .py. Executável (PyInstaller): %APPDATA%\\TV Caster."""
    if getattr(sys, "frozen", False):
        d = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"), "TV Caster")
        try:
            os.makedirs(d, exist_ok=True)
        except OSError:
            pass
        return d
    return os.path.dirname(os.path.abspath(__file__))


def resource_path(name):
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, name)


CONFIG_PATH = os.path.join(_config_dir(), "tv_caster_config.json")

MIME = {
    # vídeo
    ".mp4": "video/mp4", ".m4v": "video/mp4", ".mkv": "video/x-matroska",
    ".avi": "video/x-msvideo", ".mov": "video/quicktime",
    ".wmv": "video/x-ms-wmv", ".ts": "video/mp2t", ".m2ts": "video/mp2t",
    ".mpg": "video/mpeg", ".mpeg": "video/mpeg", ".webm": "video/webm",
    ".flv": "video/x-flv", ".3gp": "video/3gpp",
    # áudio
    ".mp3": "audio/mpeg", ".m4a": "audio/mp4", ".aac": "audio/aac",
    ".flac": "audio/flac", ".wav": "audio/wav", ".ogg": "audio/ogg",
    ".opus": "audio/ogg", ".wma": "audio/x-ms-wma",
}
VIDEO_EXT = [e for e, m in MIME.items() if m.startswith("video")]
AUDIO_EXT = [e for e, m in MIME.items() if m.startswith("audio")]
SUB_EXT = (".srt", ".ass", ".ssa", ".vtt")
SUB_DIRS = ("subs", "sub", "subtitles", "legendas", "legenda")

STATE_PT = {
    "PLAYING": "Reproduzindo", "PAUSED_PLAYBACK": "Pausado",
    "STOPPED": "Parado", "TRANSITIONING": "Carregando",
    "NO_MEDIA_PRESENT": "Sem mídia",
}

# Paleta (dark, estilo Apple)
BG = "#1c1c1e"
CARD = "#2c2c2e"
CARD2 = "#3a3a3c"
CARD3 = "#48484a"
FG = "#f5f5f7"
FG2 = "#98989d"
ACC = "#0a84ff"
ACC_H = "#409cff"
GREEN = "#30d158"

SCALE = 1.0
F_UI = F_SMALL = F_BOLD = F_TITLE = F_NOW = F_LIST = None


def px(n):
    return max(1, int(round(n * SCALE)))


# --------------------------------------------------------------------------
# Utilitários
# --------------------------------------------------------------------------
def local_ip_for(host="8.8.8.8"):
    """IP da placa de rede do PC usada para alcançar 'host'."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect((host, 9))
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        s.close()


def hms_to_sec(t):
    if not t or "NOT_IMPLEMENTED" in t.upper():
        return 0
    try:
        parts = [int(p) for p in t.split(".")[0].split(":")]
    except ValueError:
        return 0
    while len(parts) < 3:
        parts.insert(0, 0)
    h, m, s = parts[-3:]
    return h * 3600 + m * 60 + s


def sec_to_hms(s, pad_hours=False):
    s = int(max(0, s))
    h = s // 3600
    return (f"{h:02d}" if pad_hours else f"{h}") + f":{s % 3600 // 60:02d}:{s % 60:02d}"


def _ln(tag):
    return tag.rsplit("}", 1)[-1]


def natkey(s):
    return [int(x) if x.isdigit() else x.lower() for x in re.split(r"(\d+)", s)]


def title_of(path):
    return os.path.splitext(os.path.basename(path))[0]


def scan_media(folder):
    """Todos os arquivos de mídia de uma pasta (recursivo), em ordem natural."""
    out = []
    for dp, dn, fn in os.walk(folder):
        dn[:] = sorted((d for d in dn if not d.startswith(".")), key=natkey)
        for f in sorted(fn, key=natkey):
            if not f.startswith(".") and os.path.splitext(f)[1].lower() in MIME:  # ignora ._lixo do macOS
                out.append(os.path.join(dp, f))
    return out


def load_config():
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            cfg = json.load(f)
    except (OSError, ValueError):
        cfg = {}
    if not isinstance(cfg, dict):
        cfg = {}
    cfg.setdefault("folders", [])
    if not cfg.get("remote_key"):
        cfg["remote_key"] = uuid.uuid4().hex[:12]
        save_config(cfg)
    return cfg


def save_config(cfg):
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
    except OSError:
        pass


def didl_metadata(title, url, mime, size, sub_url=None):
    if mime.startswith("audio"):
        upnp_class = "object.item.audioItem.musicTrack"
    else:
        upnp_class = "object.item.videoItem"
    esc = html.escape
    protocol = f"http-get:*:{mime}:{DLNA_FEATURES}"
    sub, pv = "", ""
    if sub_url:
        u = esc(sub_url)
        # LG/Philips/outras (PacketVideo): atributos no <res> do vídeo
        pv = f' pv:subtitleFileType="srt" pv:subtitleFileUri="{u}"'
        # Samsung: <res> extra + CaptionInfo(Ex)
        sub = (f'<res protocolInfo="http-get:*:text/srt:*">{u}</res>'
               f'<sec:CaptionInfoEx sec:type="srt">{u}</sec:CaptionInfoEx>'
               f'<sec:CaptionInfo sec:type="srt">{u}</sec:CaptionInfo>')
    return (
        '<DIDL-Lite xmlns="urn:schemas-upnp-org:metadata-1-0/DIDL-Lite/" '
        'xmlns:dc="http://purl.org/dc/elements/1.1/" '
        'xmlns:upnp="urn:schemas-upnp-org:metadata-1-0/upnp/" '
        'xmlns:dlna="urn:schemas-dlna-org:metadata-1-0/" '
        'xmlns:sec="http://www.sec.co.kr/" '
        'xmlns:pv="http://www.pv.com/pvns/">'
        '<item id="0" parentID="-1" restricted="1">'
        f"<dc:title>{esc(title)}</dc:title>"
        f"<upnp:class>{upnp_class}</upnp:class>"
        f'<res protocolInfo="{esc(protocol)}" size="{size}"{pv}>{esc(url)}</res>'
        f"{sub}"
        "</item></DIDL-Lite>"
    )


# --------------------------------------------------------------------------
# Legendas: localizar, converter para SRT (UTF-8)
# --------------------------------------------------------------------------
_TS = re.compile(r"(?:(\d+):)?(\d+):(\d+)[.,](\d+)")
_TS_LINE = re.compile(r"(\S+)\s*-->\s*(\S+)")


def _decode_text(raw):
    if raw[:2] in (b"\xff\xfe", b"\xfe\xff"):
        return raw.decode("utf-16", "replace")
    for enc in ("utf-8-sig", "cp1252"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            continue
    return raw.decode("latin-1")


def _ts_ms(text):
    m = _TS.match(text.strip())
    if not m:
        raise ValueError(text)
    h, mi, s, frac = int(m.group(1) or 0), int(m.group(2)), int(m.group(3)), m.group(4)
    return ((h * 60 + mi) * 60 + s) * 1000 + int((frac + "000")[:3])


def _fmt_ms(ms):
    h, r = divmod(int(ms), 3600000)
    m, r = divmod(r, 60000)
    s, ms = divmod(r, 1000)
    return f"{h:02d}:{m:02d}:{s:02d},{ms:03d}"


def _parse_blocks(text):
    """SRT e WebVTT têm o mesmo formato de bloco: linha de tempo + texto."""
    cues = []
    for block in re.split(r"\n\s*\n", text.replace("\r\n", "\n").replace("\r", "\n")):
        lines = block.strip("\n").split("\n")
        idx = next((i for i, l in enumerate(lines) if "-->" in l), None)
        if idx is None:
            continue
        m = _TS_LINE.search(lines[idx])
        if not m:
            continue
        try:
            a, b = _ts_ms(m.group(1)), _ts_ms(m.group(2))
        except ValueError:
            continue
        body = "\n".join(lines[idx + 1:])
        body = re.sub(r"<(?!/?[ibu]>)[^>]+>", "", body).strip()
        if body:
            cues.append((a, b, body))
    return cues


def _parse_ass(text):
    fmt, cues, in_events = None, [], False
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("["):
            in_events = s.lower() == "[events]"
            continue
        if not in_events:
            continue
        low = s.lower()
        if low.startswith("format:"):
            fmt = [x.strip().lower() for x in s[7:].split(",")]
        elif low.startswith("dialogue:") and fmt:
            parts = s[9:].lstrip().split(",", len(fmt) - 1)
            if len(parts) < len(fmt):
                continue
            d = dict(zip(fmt, parts))
            try:
                a, b = _ts_ms(d["start"]), _ts_ms(d["end"])
            except (ValueError, KeyError):
                continue
            t = re.sub(r"\{[^}]*\}", "", d.get("text", ""))
            t = t.replace("\\N", "\n").replace("\\n", "\n").replace("\\h", " ").strip()
            if t:
                cues.append((a, b, t))
    cues.sort(key=lambda c: c[0])
    return cues


def subtitle_to_srt(path, tmpdir):
    """Lê .srt/.ass/.ssa/.vtt (qualquer codificação) e grava um SRT UTF-8."""
    with open(path, "rb") as f:
        text = _decode_text(f.read())
    if os.path.splitext(path)[1].lower() in (".ass", ".ssa"):
        cues = _parse_ass(text)
    else:
        cues = _parse_blocks(text)
    if not cues:
        raise RuntimeError("legenda vazia ou em formato não reconhecido")
    out = os.path.join(tmpdir, uuid.uuid4().hex[:10] + ".srt")
    with open(out, "w", encoding="utf-8", newline="\r\n") as f:
        for i, (a, b, t) in enumerate(cues, 1):
            f.write(f"{i}\n{_fmt_ms(a)} --> {_fmt_ms(b)}\n{t}\n\n")
    return out


def _sub_rank(name):
    n = name.lower()
    if re.search(r"(pt[-_. ]?br|\bpt\b|por\b|portug|brazil|\bbr\b)", n):
        lang = 0
    elif re.search(r"(\ben\b|\beng\b|english)", n):
        lang = 1
    else:
        lang = 2
    return (lang, 0 if n.endswith(".srt") else 1, natkey(n))


def find_subtitles(video_path):
    """Legendas ao lado do vídeo (mesmo nome) ou em pastas Subs/Legendas."""
    d = os.path.dirname(video_path)
    base = title_of(video_path).lower()
    found = []

    def scan(folder, need_prefix):
        try:
            names = os.listdir(folder)
        except OSError:
            return
        for f in names:
            n, e = os.path.splitext(f)
            if e.lower() in SUB_EXT and (not need_prefix or n.lower().startswith(base)):
                found.append(os.path.join(folder, f))

    scan(d, True)
    try:
        subdirs = [x for x in os.listdir(d) if os.path.isdir(os.path.join(d, x))]
    except OSError:
        subdirs = []
    for x in subdirs:
        if x.lower() in SUB_DIRS:
            scan(os.path.join(d, x), True)
            for y in os.listdir(os.path.join(d, x)):     # Subs/<nome do vídeo>/*.srt
                yp = os.path.join(d, x, y)
                if os.path.isdir(yp) and y.lower().startswith(base):
                    scan(yp, False)
        elif x.lower().startswith(base):
            scan(os.path.join(d, x), False)
    return sorted(found, key=lambda p: _sub_rank(os.path.basename(p)))


# ---------------------------------------------------------------------------
# MKV: listar faixas, tirar legendas embutidas do que vai para a TV (sem mexer
# no arquivo) e extrair uma legenda embutida para SRT.
# ---------------------------------------------------------------------------
TEXT_SUB_CODECS = ("S_TEXT/UTF8", "S_TEXT/ASCII", "S_TEXT/ASS", "S_TEXT/SSA")
LANG_NAMES = {
    "por": "Português", "pt": "Português", "eng": "Inglês", "en": "Inglês",
    "spa": "Espanhol", "es": "Espanhol", "fre": "Francês", "fra": "Francês", "fr": "Francês",
    "ger": "Alemão", "deu": "Alemão", "de": "Alemão", "ita": "Italiano", "it": "Italiano",
    "jpn": "Japonês", "ja": "Japonês", "kor": "Coreano", "chi": "Chinês", "zho": "Chinês",
    "rus": "Russo", "ara": "Árabe", "und": "Idioma não informado",
}


def _vint(buf, i, keep_marker):
    b = buf[i]
    length, mask = 1, 0x80
    while length <= 8 and not b & mask:
        length += 1
        mask >>= 1
    if length > 8:
        raise ValueError("vint inválido")
    if i + length > len(buf):
        raise IndexError("fim do buffer")
    v = b if keep_marker else b & (mask - 1)
    for k in range(1, length):
        v = (v << 8) | buf[i + k]
    return v, length


class MkvInfo:
    def __init__(self):
        self.tracks = []          # dicts: number, uid, type, codec, lang, name, start, end
        self.segment_body = 0
        self.timescale = 1000000  # ns por tick
        self.size = 0

    def subs(self):
        return [t for t in self.tracks if t["type"] == 17]


def mkv_info(path):
    """Cabeçalho de um MKV/WebM (faixas, escala de tempo). None se não for MKV legível."""
    if os.path.splitext(path)[1].lower() not in (".mkv", ".webm"):
        return None
    try:
        with open(path, "rb") as f:
            buf = f.read(8 * 1024 * 1024)
        size = os.path.getsize(path)
    except OSError:
        return None
    info = MkvInfo()
    info.size = size

    def entry(i, end, start, stop):
        tr = {"number": 0, "uid": 0, "type": 0, "codec": "", "lang": "", "name": "",
              "start": start, "end": stop}
        while i < end:
            try:
                eid, l1 = _vint(buf, i, True)
                sz, l2 = _vint(buf, i + l1, False)
            except (ValueError, IndexError):
                break
            body = i + l1 + l2
            nxt = min(body + sz, end)
            raw = buf[body:nxt]
            if eid == 0xD7:
                tr["number"] = int.from_bytes(raw, "big")
            elif eid == 0x73C5:
                tr["uid"] = int.from_bytes(raw, "big")
            elif eid == 0x83:
                tr["type"] = int.from_bytes(raw, "big")
            elif eid == 0x86:
                tr["codec"] = raw.decode("ascii", "ignore").strip("\0")
            elif eid == 0x22B59C:
                tr["lang"] = raw.decode("ascii", "ignore").strip("\0")
            elif eid == 0x22B59D and not tr["lang"]:
                tr["lang"] = raw.decode("ascii", "ignore").strip("\0")
            elif eid == 0x536E:
                tr["name"] = raw.decode("utf-8", "replace").strip("\0")
            i = nxt
        return tr

    def walk(i, end):
        while i < end:
            try:
                eid, l1 = _vint(buf, i, True)
                sz, l2 = _vint(buf, i + l1, False)
            except (ValueError, IndexError):
                return False
            body = i + l1 + l2
            unknown = sz == (1 << (7 * l2)) - 1
            stop = end if unknown else min(body + sz, end)
            if eid == 0x18538067:                                  # Segment
                info.segment_body = body
                if walk(body, stop) is False:
                    return False
            elif eid in (0x1549A966, 0x1654AE6B):                  # Info, Tracks
                if walk(body, stop) is False:
                    return False
            elif eid == 0x2AD7B1:                                  # TimestampScale
                info.timescale = int.from_bytes(buf[body:stop], "big") or 1000000
            elif eid == 0xAE:                                      # TrackEntry
                info.tracks.append(entry(body, stop, i, body + sz))
            elif eid == 0x1F43B675:                                # Cluster: acabou o cabeçalho
                return False
            i = stop
        return True

    walk(0, len(buf))
    return info if info.tracks else None


def mkv_subtitle_tracks(path):
    """Idiomas das faixas de legenda embutidas (lista vazia se não houver)."""
    info = mkv_info(path)
    return [t["lang"] or "und" for t in info.subs()] if info else []


def _cues_to_srt_file(cues, tmpdir):
    out = os.path.join(tmpdir, uuid.uuid4().hex[:10] + ".srt")
    with open(out, "w", encoding="utf-8", newline="\r\n") as f:
        for i, (a, b, t) in enumerate(cues, 1):
            f.write(f"{i}\n{_fmt_ms(a)} --> {_fmt_ms(b)}\n{t}\n\n")
    return out


def mkv_extract_subtitle(path, info, track, tmpdir, progress=None):
    """Extrai uma legenda de TEXTO embutida (SRT/ASS/SSA) para um .srt UTF-8."""
    codec = track["codec"]
    if codec not in TEXT_SUB_CODECS:
        raise RuntimeError("essa legenda embutida é uma imagem (PGS/VobSub) e não pode ser convertida")
    tnum, scale = track["number"], info.timescale
    is_ass = codec in ("S_TEXT/ASS", "S_TEXT/SSA")
    raw_cues, cl_time, pending = [], 0, None
    pos, total = info.segment_body, info.size
    win, win_pos = b"", 0

    with open(path, "rb", buffering=0) as f:
        def rd(at, n):
            """Leitura em janelas de 8 MB (sequencial: bem mais rápida que saltos pequenos)."""
            nonlocal win, win_pos
            if not (win_pos <= at and at + n <= win_pos + len(win)):
                f.seek(at)
                win, win_pos = f.read(max(n, 8 * 1024 * 1024)), at
            return win[at - win_pos: at - win_pos + n]

        last_report = 0
        while pos < total:
            h = rd(pos, 24)
            if len(h) < 3:
                break
            try:
                eid, l1 = _vint(h, 0, True)
                sz, l2 = _vint(h, l1, False)
            except (ValueError, IndexError):
                break
            body = pos + l1 + l2
            if eid in (0x1F43B675, 0xA0):                    # Cluster, BlockGroup: entra
                pos = body
                continue
            unknown = sz == (1 << (7 * l2)) - 1
            if unknown:
                break
            head = h[l1 + l2:]
            if eid == 0xE7:                                  # Timecode do cluster
                cl_time = int.from_bytes(head[:sz], "big") if sz <= len(head) else 0
                if progress and pos - last_report > 64 * 1024 * 1024:
                    last_report = pos
                    progress(pos / total)
            elif eid in (0xA3, 0xA1):                        # SimpleBlock, Block
                pending = None
                try:
                    tn, lt = _vint(head, 0, False)
                except (ValueError, IndexError):
                    tn, lt = -1, 0
                if tn == tnum and len(head) >= lt + 3:
                    rel = int.from_bytes(head[lt:lt + 2], "big", signed=True)
                    data = rd(body + lt + 3, sz - lt - 3)
                    start_ms = (cl_time + rel) * scale / 1e6
                    pending = [start_ms, None, data]
                    raw_cues.append(pending)
            elif eid == 0x9B and pending is not None:        # BlockDuration do bloco anterior
                d = int.from_bytes(head[:sz], "big") if sz <= len(head) else 0
                pending[1] = pending[0] + d * scale / 1e6
                pending = None
            pos = body + sz
    cues = []
    for a, b, data in raw_cues:
        try:
            txt = data.decode("utf-8")
        except UnicodeDecodeError:       # muxers antigos gravam Windows-1252 no MKV
            txt = data.decode("cp1252", "replace")
        if is_ass:
            parts = txt.split(",", 8)
            txt = parts[8] if len(parts) == 9 else ""
            txt = re.sub(r"\{[^}]*\}", "", txt)
            txt = txt.replace("\\N", "\n").replace("\\n", "\n").replace("\\h", " ")
        txt = txt.strip()
        if txt:
            cues.append((int(a), int(b if b is not None else a + 3000), txt))
    cues.sort(key=lambda c: c[0])
    if not cues:
        raise RuntimeError("nenhuma fala encontrada nessa faixa de legenda")
    return _cues_to_srt_file(cues, tmpdir)


# --------------------------------------------------------------------------
# TV (Media Renderer UPnP)
# --------------------------------------------------------------------------
class Renderer:
    def __init__(self, name, location, av, rc):
        self.name = name
        self.location = location
        self.av = av            # (serviceType, controlURL) do AVTransport
        self.rc = rc            # (serviceType, controlURL) do RenderingControl
        self.host = urllib.parse.urlparse(location).hostname

    def __str__(self):
        return f"{self.name}  ({self.host})"

    # ---- SOAP ----
    def _soap(self, svc, action, args=()):
        if not svc:
            raise RuntimeError(f"A TV não oferece o serviço para '{action}'.")
        stype, url = svc
        body = "".join(f"<{k}>{html.escape(str(v))}</{k}>" for k, v in args)
        envelope = (
            '<?xml version="1.0" encoding="utf-8"?>'
            '<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" '
            's:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">'
            f'<s:Body><u:{action} xmlns:u="{stype}">{body}</u:{action}>'
            "</s:Body></s:Envelope>"
        )
        req = urllib.request.Request(
            url, data=envelope.encode("utf-8"), method="POST",
            headers={"Content-Type": 'text/xml; charset="utf-8"',
                     "SOAPAction": f'"{stype}#{action}"'})
        try:
            with urllib.request.urlopen(req, timeout=6) as r:
                return r.read().decode("utf-8", "ignore")
        except urllib.error.HTTPError as e:
            txt = e.read().decode("utf-8", "ignore")
            code = self._get(txt, "errorCode")
            desc = self._get(txt, "errorDescription")
            raise RuntimeError(f"{action} recusado pela TV ({code} {desc})".strip())
        except (urllib.error.URLError, OSError) as e:
            raise RuntimeError(f"Sem resposta da TV em {action}: {e}")

    @staticmethod
    def _get(xml_text, tag):
        m = re.search(rf"<(?:\w+:)?{tag}>(.*?)</(?:\w+:)?{tag}>", xml_text, re.S)
        return html.unescape(m.group(1)).strip() if m else ""

    # ---- comandos ----
    def set_uri(self, url, meta):
        self._soap(self.av, "SetAVTransportURI",
                   [("InstanceID", 0), ("CurrentURI", url), ("CurrentURIMetaData", meta)])

    def play(self):
        self._soap(self.av, "Play", [("InstanceID", 0), ("Speed", "1")])

    def pause(self):
        self._soap(self.av, "Pause", [("InstanceID", 0)])

    def stop(self):
        self._soap(self.av, "Stop", [("InstanceID", 0)])

    def seek(self, seconds):
        target = sec_to_hms(seconds, pad_hours=True)
        try:
            self._soap(self.av, "Seek", [("InstanceID", 0), ("Unit", "REL_TIME"),
                                         ("Target", target)])
        except RuntimeError as first:
            try:   # algumas TVs só aceitam ABS_TIME
                self._soap(self.av, "Seek", [("InstanceID", 0), ("Unit", "ABS_TIME"),
                                             ("Target", target)])
            except RuntimeError:
                raise first

    def transport_state(self):
        x = self._soap(self.av, "GetTransportInfo", [("InstanceID", 0)])
        return self._get(x, "CurrentTransportState")

    def position(self):
        x = self._soap(self.av, "GetPositionInfo", [("InstanceID", 0)])
        return hms_to_sec(self._get(x, "RelTime")), hms_to_sec(self._get(x, "TrackDuration"))

    def get_volume(self):
        x = self._soap(self.rc, "GetVolume", [("InstanceID", 0), ("Channel", "Master")])
        try:
            return int(self._get(x, "CurrentVolume"))
        except ValueError:
            return 0

    def set_volume(self, v):
        self._soap(self.rc, "SetVolume", [("InstanceID", 0), ("Channel", "Master"),
                                          ("DesiredVolume", int(v))])

    def set_mute(self, mute):
        self._soap(self.rc, "SetMute", [("InstanceID", 0), ("Channel", "Master"),
                                        ("DesiredMute", 1 if mute else 0)])


def load_renderer(location):
    """Lê o XML de descrição do dispositivo e monta um Renderer."""
    with urllib.request.urlopen(location, timeout=5) as r:
        root = ET.fromstring(r.read())
    base, name = location, None
    for el in root.iter():
        t = _ln(el.tag)
        if t == "URLBase" and el.text:
            base = el.text.strip()
        elif t == "friendlyName" and name is None and el.text:
            name = el.text.strip()
    av = rc = None
    for el in root.iter():
        if _ln(el.tag) != "service":
            continue
        info = {_ln(c.tag): (c.text or "").strip() for c in el}
        st, ctrl = info.get("serviceType", ""), info.get("controlURL", "")
        if not ctrl:
            continue
        full = urllib.parse.urljoin(base, ctrl)
        if ":AVTransport:" in st and not av:
            av = (st, full)
        elif ":RenderingControl:" in st and not rc:
            rc = (st, full)
    if not av:
        return None
    return Renderer(name or location, location, av, rc)


SSDP_TARGETS = ("urn:schemas-upnp-org:device:MediaRenderer:1",
                "urn:schemas-upnp-org:service:AVTransport:1")  # LG/outras respondem a um dos dois


def ssdp_locations(dest=SSDP_ADDR, timeout=4.0):
    """M-SEARCH (multicast, ou unicast se 'dest' for o IP da TV) -> URLs de descrição."""
    ip = local_ip_for(dest[0] if dest != SSDP_ADDR else "8.8.8.8")
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
    sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_TTL, 4)
    try:
        sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_IF, socket.inet_aton(ip))
        sock.bind((ip, 0))
    except OSError:
        pass
    sock.settimeout(0.5)
    locations = set()
    try:
        for _ in range(2):
            for st in SSDP_TARGETS:
                msg = ("M-SEARCH * HTTP/1.1\r\n"
                       f"HOST: {dest[0]}:{dest[1]}\r\n"
                       'MAN: "ssdp:discover"\r\n'
                       "MX: 3\r\n"
                       f"ST: {st}\r\n\r\n").encode()
                try:
                    sock.sendto(msg, dest)
                except OSError:
                    pass
        end = time.time() + timeout
        while time.time() < end:
            try:
                data, _ = sock.recvfrom(65507)
            except socket.timeout:
                continue
            except OSError:
                break
            m = re.search(rb"(?im)^location:\s*(\S+)", data)
            if m:
                locations.add(m.group(1).decode(errors="ignore"))
    finally:
        sock.close()
    return locations


def discover(timeout=4.0):
    """Procura TVs (MediaRenderer) na rede local via SSDP."""
    found, seen = [], set()
    for loc in sorted(ssdp_locations(SSDP_ADDR, timeout)):
        try:
            r = load_renderer(loc)
        except Exception:
            continue
        if r and (r.host, r.name) not in seen:
            seen.add((r.host, r.name))
            found.append(r)
    return found


def connect_ip(ip):
    """TV pelo IP: SSDP direto (LG webOS usa portas aleatórias) e portas conhecidas da Samsung."""
    locs = sorted(ssdp_locations((ip, 1900), 3.0))
    locs += [f"http://{ip}:9197/dmr", f"http://{ip}:7676/smp_15_"]
    for loc in locs:
        try:
            r = load_renderer(loc)
        except Exception:
            continue
        if r:
            return r
    raise RuntimeError(f"Nenhum renderizador DLNA respondeu em {ip}. "
                       "Na LG, ligue em Configurações > Conexão > Compartilhamento de mídia/Miracast e "
                       "deixe a TV ligada (não em espera).")


# --------------------------------------------------------------------------
# Servidor HTTP: entrega arquivos para a TV e a página de controle do celular
# --------------------------------------------------------------------------
class _QuietServer(ThreadingHTTPServer):
    def handle_error(self, request, client_address):
        pass  # TV/celular fecharam a conexão no meio (seek, stop, página fechada) - normal


class MediaServer:
    def __init__(self):
        self.files = {}   # token -> (caminho, mime, cabeçalhos extras)
        self.remote = None  # callable(handler, "GET"|"POST") para /r/...
        self.live = None    # LiveStream atual (rota /live/...)
        handler = self._make_handler()
        self.httpd = None
        for port in range(HTTP_PORT, HTTP_PORT + 20):
            try:
                self.httpd = _QuietServer(("0.0.0.0", port), handler)
                break
            except OSError:
                continue
        if not self.httpd:
            raise RuntimeError("Não foi possível abrir uma porta para o servidor de mídia.")
        self.httpd.daemon_threads = True
        self.port = self.httpd.server_address[1]
        threading.Thread(target=self.httpd.serve_forever, daemon=True).start()

    def publish(self, path, mime, ip, headers=None):
        token = uuid.uuid4().hex[:12]
        self.files[token] = (path, mime, headers or {})
        ext = os.path.splitext(path)[1].lower()
        return f"http://{ip}:{self.port}/m/{token}/media{ext}"

    def shutdown(self):
        try:
            self.httpd.shutdown()
            self.httpd.server_close()
        except Exception:
            pass

    def _make_handler(server):
        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, *args):
                pass

            def do_HEAD(self):
                if self.path.startswith("/live/") and server.live:
                    server.live.serve(self, head=True)
                else:
                    self._serve(head=True)

            def do_GET(self):
                if self.path.startswith("/r/") and server.remote:
                    server.remote(self, "GET")
                elif self.path.startswith("/live/") and server.live:
                    server.live.serve(self)
                else:
                    self._serve(head=False)

            def do_POST(self):
                if self.path.startswith("/r/") and server.remote:
                    server.remote(self, "POST")
                else:
                    self.send_error(404)

            def _serve(self, head):
                m = re.match(r"^/m/([0-9a-f]+)/", self.path)
                item = server.files.get(m.group(1)) if m else None
                if not item or not os.path.isfile(item[0]):
                    self.send_error(404)
                    return
                path, mime, extra = item
                size = os.path.getsize(path)
                start, end, status = 0, size - 1, 200

                rng = self.headers.get("Range")
                if rng:
                    m = re.match(r"bytes=(\d*)-(\d*)", rng.strip())
                    if m:
                        s, e = m.groups()
                        if s:
                            start = int(s)
                            end = int(e) if e else size - 1
                        elif e:
                            start, end = max(0, size - int(e)), size - 1
                        if start >= size:
                            self.send_response(416)
                            self.send_header("Content-Range", f"bytes */{size}")
                            self.send_header("Content-Length", "0")
                            self.end_headers()
                            return
                        end = min(end, size - 1)
                        status = 206

                length = end - start + 1
                self.send_response(status)
                self.send_header("Content-Type", mime)
                self.send_header("Content-Length", str(length))
                self.send_header("Accept-Ranges", "bytes")
                self.send_header("transferMode.dlna.org", "Streaming")
                self.send_header("contentFeatures.dlna.org", DLNA_FEATURES)
                for k, v in extra.items():
                    self.send_header(k, v)
                if status == 206:
                    self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
                self.end_headers()
                if head:
                    return
                try:
                    with open(path, "rb") as f:
                        f.seek(start)
                        remaining = length
                        while remaining > 0:
                            chunk = f.read(min(262144, remaining))
                            if not chunk:
                                break
                            self.wfile.write(chunk)
                            remaining -= len(chunk)
                except OSError:
                    pass  # TV fechou a conexão (seek, stop...) - normal
        return Handler


# ---------------------------------------------------------------------------
# Modo compatibilidade: converte para MP4/MP3 com o ffmpeg (embutido no .exe)
# ---------------------------------------------------------------------------
class ConversionCancelled(Exception):
    pass


def find_ffmpeg():
    """ffmpeg embutido no executável (ou em bin/), senão o que estiver no PATH."""
    for rel in ("ffmpeg.exe", os.path.join("bin", "ffmpeg.exe")):
        p = resource_path(rel)
        if os.path.isfile(p):
            return p
    return shutil.which("ffmpeg")


def _probe(ff, path):
    """Duração (s) e codec do vídeo, lidos da saída de 'ffmpeg -i'."""
    flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
    try:
        p = subprocess.run([ff, "-hide_banner", "-i", path], stdout=subprocess.DEVNULL,
                           stderr=subprocess.PIPE, creationflags=flags, timeout=60)
        txt = p.stderr.decode("utf-8", "ignore")
    except (subprocess.TimeoutExpired, OSError):
        return {"duration": 0, "vcodec": ""}
    d = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", txt)
    v = re.search(r"Video:\s*(\w+)", txt)
    dur = int(d.group(1)) * 3600 + int(d.group(2)) * 60 + float(d.group(3)) if d else 0
    return {"duration": dur, "vcodec": v.group(1).lower() if v else ""}


def convert_media(path, is_audio, tmpdir, progress=None, cancelled=None):
    """MP4 (H.264+AAC) ou MP3. Vídeo já em H.264: só o áudio é convertido (rápido)."""
    ff = find_ffmpeg()
    if not ff:
        raise RuntimeError("o conversor (ffmpeg) não está disponível nesta cópia do programa")
    info = _probe(ff, path)
    out = os.path.join(tmpdir, uuid.uuid4().hex + (".mp3" if is_audio else ".mp4"))
    if is_audio:
        enc = ["-vn", "-c:a", "libmp3lame", "-b:a", "256k"]
    else:
        vid = (["-c:v", "copy"] if info["vcodec"] == "h264" else
               ["-c:v", "libx264", "-preset", "veryfast", "-crf", "21", "-pix_fmt", "yuv420p"])
        enc = ["-map", "0:v:0", "-map", "0:a:0?", *vid,
               "-c:a", "aac", "-b:a", "192k", "-ac", "2", "-movflags", "+faststart"]
    return _run_ffmpeg(ff, path, enc, out, info["duration"], tmpdir, progress, cancelled)


def mkv_without_subs(path, tmpdir, progress=None, cancelled=None):
    """Cópia do MKV sem as faixas de legenda (só copia os dados, não recodifica).

    Tirar só a faixa do cabeçalho não serve: os blocos de legenda continuam dentro do
    vídeo e a TV perde quadros (pixelado/pulando) a cada fala. Exige espaço livre ~ tamanho do arquivo.
    """
    ff = find_ffmpeg()
    if not ff:
        raise RuntimeError("o conversor (ffmpeg) não está disponível nesta cópia do programa")
    if shutil.disk_usage(tmpdir).free < os.path.getsize(path) * 1.05 + (256 << 20):
        raise RuntimeError("sem espaço livre no disco temporário")
    out = os.path.join(tmpdir, uuid.uuid4().hex + ".mkv")
    enc = ["-map", "0:v", "-map", "0:a?", "-map_chapters", "0", "-sn", "-dn", "-c", "copy"]
    return _run_ffmpeg(ff, path, enc, out, _probe(ff, path)["duration"], tmpdir, progress, cancelled)


def _run_ffmpeg(ff, path, enc, out, duration, tmpdir, progress, cancelled):
    """Roda o ffmpeg com progresso (0..1) e cancelamento; devolve 'out' ou levanta erro."""
    info = {"duration": duration}
    cmd = [ff, "-hide_banner", "-nostats", "-progress", "pipe:1", "-y", "-i", path, *enc, out]
    flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
    log_path = os.path.join(tmpdir, "ffmpeg_" + uuid.uuid4().hex[:6] + ".log")
    with open(log_path, "wb") as log:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=log, creationflags=flags)
        try:
            for raw in p.stdout:
                if cancelled and cancelled():
                    p.kill()
                    p.wait()
                    raise ConversionCancelled()
                line = raw.decode("ascii", "ignore").strip()
                if progress and info["duration"] and line.startswith("out_time_ms="):
                    try:
                        progress(min(0.99, int(line[12:]) / 1e6 / info["duration"]))
                    except ValueError:
                        pass
            rc = p.wait()
        except BaseException:
            if p.poll() is None:
                p.kill()
                p.wait()
            for junk in (out,):
                try:
                    os.remove(junk)
                except OSError:
                    pass
            raise
    if rc != 0:
        try:
            tail = open(log_path, "rb").read()[-300:].decode("utf-8", "ignore")
        except OSError:
            tail = ""
        raise RuntimeError("ffmpeg falhou: " + tail)
    return out


# ---------------------------------------------------------------------------
# Transmissão ao vivo: tela / janela / som do PC -> TV
# ---------------------------------------------------------------------------
LIVE_QUALITY = {      # chave: (rótulo, largura, altura, fps, bitrate)
    # taxas altas encurtam a espera da TV (ela só começa a mostrar depois de receber ~1,5 MB)
    "leve": ("Leve · 720p", 1280, 720, 30, "8M"),
    "normal": ("Equilibrada · 1080p", 1920, 1080, 30, "16M"),
    "alta": ("Alta · 1080p 60", 1920, 1080, 60, "24M"),
}
LIVE_FLAGS = "DLNA.ORG_OP=00;DLNA.ORG_CI=0;DLNA.ORG_FLAGS=01700000000000000000000000000000"
_ENCODER = {}


def detect_encoder(ff):
    """Melhor codificador H.264 disponível: placa de vídeo (NVENC/AMF/QSV) ou CPU (x264)."""
    if "enc" in _ENCODER:
        return _ENCODER["enc"]
    flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
    choice = "libx264"
    for enc in ("h264_nvenc", "h264_amf", "h264_qsv"):
        try:
            p = subprocess.run([ff, "-hide_banner", "-loglevel", "error", "-f", "lavfi", "-i",
                                "color=c=black:s=256x256:r=10", "-frames:v", "2", "-c:v", enc,
                                "-f", "null", "-"], capture_output=True, creationflags=flags,
                               timeout=25)
        except (OSError, subprocess.TimeoutExpired):
            continue
        if p.returncode == 0:
            choice = enc
            break
    _ENCODER["enc"] = choice
    return choice


def window_rects():
    """{título: (x, y, largura, altura)} das janelas abertas e visíveis (área real, sem a sombra)."""
    if os.name != "nt":
        return {}
    import ctypes
    from ctypes import wintypes
    u32, dwm = ctypes.windll.user32, ctypes.windll.dwmapi
    for fn in (u32.IsWindowVisible, u32.IsIconic, u32.GetWindowTextLengthW, u32.GetWindowRect):
        fn.argtypes = [wintypes.HWND] + ([ctypes.POINTER(wintypes.RECT)] if fn is u32.GetWindowRect else [])
    u32.GetWindowTextW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    u32.GetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int]
    dwm.DwmGetWindowAttribute.argtypes = [wintypes.HWND, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD]
    out = {}
    proc_t = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)

    def cb(hwnd, _):
        try:
            if not u32.IsWindowVisible(hwnd) or u32.IsIconic(hwnd):
                return True
            n = u32.GetWindowTextLengthW(hwnd)
            if n == 0 or u32.GetWindowLongW(hwnd, -20) & 0x80:      # sem título / janela de ferramenta
                return True
            cloaked = ctypes.c_int(0)
            dwm.DwmGetWindowAttribute(hwnd, 14, ctypes.byref(cloaked), 4)
            if cloaked.value:                                       # janela "escondida" do Windows
                return True
            r = wintypes.RECT()
            if dwm.DwmGetWindowAttribute(hwnd, 9, ctypes.byref(r), ctypes.sizeof(r)) != 0:
                u32.GetWindowRect(hwnd, ctypes.byref(r))            # 9 = limites reais (sem sombra)
            if r.right - r.left < 120 or r.bottom - r.top < 80:
                return True
            buf = ctypes.create_unicode_buffer(n + 1)
            u32.GetWindowTextW(hwnd, buf, n + 1)
            if buf.value not in ("Program Manager", "TV Caster"):
                out[buf.value] = (r.left, r.top, r.right - r.left, r.bottom - r.top)
        except Exception:
            pass
        return True
    u32.EnumWindows(proc_t(cb), 0)
    return out


def list_windows():
    """Títulos das janelas abertas e visíveis (para escolher qual transmitir)."""
    return sorted(window_rects(), key=str.lower)


def bring_to_front(title):
    try:
        import ctypes
        u32 = ctypes.windll.user32
        u32.FindWindowW.restype = ctypes.c_void_p
        u32.SetForegroundWindow.argtypes = [ctypes.c_void_p]
        hwnd = u32.FindWindowW(None, title)
        if hwnd:
            u32.SetForegroundWindow(hwnd)
    except Exception:
        pass


def clamp_region(r):
    """Recorta o retângulo para dentro da área das telas e deixa largura/altura pares."""
    if os.name != "nt" or not r:
        return None
    import ctypes
    u32 = ctypes.windll.user32
    vx, vy, vw, vh = (u32.GetSystemMetrics(i) for i in (76, 77, 78, 79))
    x, y, w, h = r
    x0, y0, x1, y1 = max(x, vx), max(y, vy), min(x + w, vx + vw), min(y + h, vy + vh)
    w, h = (x1 - x0) // 2 * 2, (y1 - y0) // 2 * 2
    return (x0, y0, w, h) if w >= 64 and h >= 64 else None


def list_screens(ff):
    """[(índice, largura, altura)] das telas que a captura por GPU enxerga (na ordem dela)."""
    flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
    out = []
    for i in range(8):
        try:
            p = subprocess.run([ff, "-hide_banner", "-v", "verbose", "-f", "lavfi", "-i",
                                f"ddagrab=output_idx={i}:framerate=2", "-frames:v", "1", "-f", "null", "-"],
                               capture_output=True, creationflags=flags, timeout=20)
        except (OSError, subprocess.TimeoutExpired):
            break
        m = re.search(rb"Opened dxgi output (\d+) with dimensions (\d+)x(\d+)", p.stderr)
        if p.returncode != 0 or not m:
            break
        out.append((i, int(m.group(2)), int(m.group(3))))
    return out


def primary_size():
    """Tamanho (px) da tela principal; o programa é DPI-aware, então vem em pixels reais."""
    try:
        import ctypes
        u32 = ctypes.windll.user32
        return u32.GetSystemMetrics(0), u32.GetSystemMetrics(1)
    except Exception:
        return (0, 0)


def screen_labels(screens):
    """Rótulos das telas: 'Tela 1 · 3440×1440 (principal)'."""
    psz, marked, out = primary_size(), False, []
    for i, w, h in screens:
        tag = ""
        if not marked and (w, h) == psz:
            tag, marked = " (principal)", True
        out.append(f"Tela {i + 1} · {w}×{h}{tag}")
    return out


def build_live_cmd(ff, mode, title, quality, with_audio, enc, audio_fmt=None, br=None, gop=None,
                   region=None, screen=0):
    """Linha de comando do ffmpeg. mode: 'screen' | 'window' | 'audio'."""
    _, w, h, fps, br0 = LIVE_QUALITY[quality]
    br = br or br0
    gop = gop or max(1, fps // 2)              # quadro-chave a cada 0,5 s: a TV entra rápido
    cmd = [ff, "-hide_banner", "-loglevel", "error", "-nostats"]
    if mode == "screen":
        cmd += ["-f", "lavfi", "-i", f"ddagrab=output_idx={screen}:framerate={fps}:draw_mouse=1"]
        pre = "hwdownload,format=bgra,"
    elif mode == "window":
        cmd += ["-f", "gdigrab", "-framerate", str(fps), "-draw_mouse", "1", "-i", "title=" + title]
        pre = ""
    elif mode == "region":                        # área da janela na tela (apps com vídeo por GPU)
        x, y, rw, rh = region
        cmd += ["-f", "gdigrab", "-framerate", str(fps), "-draw_mouse", "1", "-offset_x", str(x),
                "-offset_y", str(y), "-video_size", f"{rw}x{rh}", "-i", "desktop"]
        pre = ""
    elif mode == "desktop":                       # plano B da captura de tela (todas as telas)
        cmd += ["-f", "gdigrab", "-framerate", str(fps), "-i", "desktop"]
        pre = ""
    else:
        pre = None
    if with_audio and audio_fmt:
        rate, ch = audio_fmt
        cmd += ["-thread_queue_size", "1024", "-f", "s16le", "-ar", str(rate), "-ac", str(ch),
                "-use_wallclock_as_timestamps", "1", "-i", "pipe:0"]
    if mode == "audio":
        return cmd + ["-vn", "-c:a", "libmp3lame", "-b:a", "192k", "-ar", "44100", "-ac", "2",
                      "-write_xing", "0", "-id3v2_version", "0", "-f", "mp3", "pipe:1"]
    vf = (pre + f"scale={w}:{h}:force_original_aspect_ratio=decrease,"
          f"pad={w}:{h}:(ow-iw)/2:(oh-ih)/2,format=yuv420p")
    cmd += ["-map", "0:v:0"] + (["-map", "1:a:0"] if with_audio and audio_fmt else [])
    cmd += ["-vf", vf, "-r", str(fps), "-g", str(gop), "-bf", "0"]
    if enc == "h264_nvenc":
        cmd += ["-c:v", enc, "-preset", "p1", "-tune", "ll", "-zerolatency", "1", "-rc", "cbr",
                "-b:v", br, "-maxrate", br, "-bufsize", br, "-profile:v", "high"]
    elif enc == "libx264":
        cmd += ["-c:v", enc, "-preset", "ultrafast", "-tune", "zerolatency", "-b:v", br,
                "-maxrate", br, "-bufsize", br, "-profile:v", "high"]
    else:
        cmd += ["-c:v", enc, "-b:v", br, "-maxrate", br]
    if with_audio and audio_fmt:
        cmd += ["-af", "aresample=async=1000:first_pts=0", "-c:a", "aac", "-b:a", "160k",
                "-ar", "48000", "-ac", "2"]
    cmd += ["-f", "mpegts", "-mpegts_flags", "+resend_headers", "-pat_period", "0.5",
            "-flush_packets", "1", "-muxdelay", "0", "-muxpreload", "0", "pipe:1"]
    return cmd


_AUDIO_LOCK = threading.RLock()


class AudioLoopback:
    """Captura o som que sai do PC (loopback WASAPI) em blocos de 20 ms."""

    def __init__(self):
        self.rate, self.channels = 48000, 2
        self.q = queue.Queue(maxsize=300)
        self._pa = self._stream = None

    def open(self):
        import pyaudiowpatch as pa
        with _AUDIO_LOCK:
            self._open(pa)

    def _open(self, pa):
        self._pa = pa.PyAudio()
        try:
            wasapi = self._pa.get_host_api_info_by_type(pa.paWASAPI)
            spk = self._pa.get_device_info_by_index(wasapi["defaultOutputDevice"])
            dev = spk if spk.get("isLoopbackDevice") else None
            if dev is None:
                for d in self._pa.get_loopback_device_info_generator():
                    if spk["name"] in d["name"]:
                        dev = d
                        break
            if dev is None:
                raise RuntimeError("não achei a saída de áudio do PC para capturar")
            self.rate, self.channels = int(dev["defaultSampleRate"]), int(dev["maxInputChannels"])

            def cb(data, frames, ti, status):
                try:
                    self.q.put_nowait(data)
                except queue.Full:
                    pass
                return (None, pa.paContinue)
            self._stream = self._pa.open(format=pa.paInt16, channels=self.channels, rate=self.rate,
                                         input=True, input_device_index=dev["index"],
                                         frames_per_buffer=int(self.rate * 0.02), stream_callback=cb)
        except Exception:
            self.close()
            raise

    def silence(self):
        return bytes(int(self.rate * 0.02) * self.channels * 2)

    def close(self):
        with _AUDIO_LOCK:
            try:
                if self._stream:
                    self._stream.stop_stream()
                    self._stream.close()
                if self._pa:
                    self._pa.terminate()
            except Exception:
                pass
            self._stream = self._pa = None


class LiveStream:
    """Roda o ffmpeg de captura e entrega o resultado, ao vivo, para quem pedir (a TV)."""
    MAX_BUF = 16 * 1024 * 1024

    def __init__(self, ff, tmpdir):
        self.ff, self.tmpdir = ff, tmpdir
        self.token = uuid.uuid4().hex[:12]
        self.proc, self.audio = None, None
        self.chunks, self.first, self.count, self.size = [], 0, 0, 0
        self.cond = threading.Condition()
        self.alive = False
        self.mode, self.title, self.encoder = "", "", ""
        self.audio_only = False
        self.warning = ""
        self.bytes_per_sec = 1_000_000
        self.kf = []                      # índices dos blocos que começam um quadro-chave
        self.video_pid = 0x100            # 1º stream do mpegts do ffmpeg
        self.start_mode = "kf"            # 'kf' = entra no último quadro-chave; 'back' = ~1 s atrás
        self.transfer_mode = "Streaming"
        self.bitrate = None
        self.gop = None
        self.pad_bytes = 0                # enchimento inicial (pacotes nulos do TS) para a TV

    @property
    def mime(self):
        return "audio/mpeg" if self.audio_only else "video/mpeg"

    def path(self):
        return f"/live/{self.token}.{'mp3' if self.audio_only else 'ts'}"

    def start(self, mode, title="", quality="normal", with_audio=True, screen=0):
        self.mode, self.title, self.audio_only = mode, title, mode == "audio"
        self.screen = screen
        self.encoder = "" if self.audio_only else detect_encoder(self.ff)
        audio_fmt = None
        if with_audio or self.audio_only:
            try:
                self.audio = AudioLoopback()
                self.audio.open()
                audio_fmt = (self.audio.rate, self.audio.channels)
            except Exception as e:
                self.audio = None
                if self.audio_only:
                    raise RuntimeError(f"não consegui capturar o som do PC ({e})")
                self.warning = f"Sem som: {e}"
        br = self.bitrate or LIVE_QUALITY[quality][4]
        self.bytes_per_sec = int(br[:-1]) * 125_000 + 20_000
        cap, region = mode, None
        if mode == "window" and self._window_black(title):
            rect = clamp_region(window_rects().get(title))
            if rect:                       # Spotify, navegadores...: a captura direta sai preta
                bring_to_front(title)
                cap, region = "region", rect
                self.warning = ("Essa janela usa vídeo acelerado por GPU (como o Spotify): estou "
                                "transmitindo a área dela na tela. Mantenha-a visível e no mesmo lugar.")
        attempts = [cap]
        if cap == "screen" and screen == 0:
            attempts.append("desktop")        # plano B (gdigrab) só para a tela 1
        last_err = ""
        for m in attempts:
            cmd = build_live_cmd(self.ff, m, title, quality, bool(audio_fmt), self.encoder, audio_fmt,
                                 self.bitrate, self.gop, region, screen)
            ok, last_err = self._spawn(cmd)
            if ok:
                if m != cap:
                    self.warning = "Captura por GPU indisponível; usando o modo compatível."
                return
            self._kill()
        if self.audio:
            self.audio.close()
        raise RuntimeError("a captura não iniciou: " + (last_err or "erro desconhecido"))

    def _window_black(self, title):
        """A captura direta dessa janela sai toda preta? (acontece com apps desenhados pela GPU)"""
        flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
        try:
            p = subprocess.run([self.ff, "-hide_banner", "-loglevel", "error", "-f", "gdigrab",
                                "-framerate", "5", "-i", "title=" + title, "-frames:v", "4", "-vf",
                                "scale=48:27,format=rgb24", "-f", "rawvideo", "-"],
                               capture_output=True, creationflags=flags, timeout=15)
        except (OSError, subprocess.TimeoutExpired):
            return False
        data = p.stdout[-48 * 27 * 3:]
        # captura que falha vem em preto exato (0,0,0); uma interface escura de verdade fica acima disso
        return p.returncode == 0 and len(data) == 48 * 27 * 3 and max(data) < 4

    def _spawn(self, cmd):
        flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
        self.log_path = os.path.join(self.tmpdir, "live_" + uuid.uuid4().hex[:6] + ".log")
        self._log = open(self.log_path, "wb")
        self.proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=self._log, creationflags=flags)
        self.alive = True
        self.chunks, self.first, self.count, self.size, self.kf = [], 0, 0, 0, []
        self.times, self.start_age = [], 0.0
        threading.Thread(target=self._read, daemon=True).start()
        if self.audio:
            threading.Thread(target=self._feed_audio, daemon=True).start()
        else:
            try:
                self.proc.stdin.close()
            except OSError:
                pass
        end = time.time() + 12
        while time.time() < end:
            with self.cond:
                if self.count >= 3:
                    return True, ""
            if self.proc.poll() is not None:
                break
            time.sleep(0.1)
        try:
            err = open(self.log_path, "rb").read()[-400:].decode("utf-8", "ignore").strip()
        except OSError:
            err = ""
        return False, err

    def _feed_audio(self):
        audio, proc = self.audio, self.proc
        try:
            while self.alive and proc is self.proc:
                try:
                    data = audio.q.get(timeout=0.05)
                except queue.Empty:
                    data = audio.silence()          # PC mudo: mantém o relógio do áudio andando
                proc.stdin.write(data)
        except (OSError, ValueError, AttributeError):
            pass

    def _read(self):
        proc, step = self.proc, (4096 if self.audio_only else 188 * 21)
        try:
            while True:
                data = proc.stdout.read(step) if self.audio_only else proc.stdout.read(step)
                if not data:
                    break
                with self.cond:
                    self.chunks.append(data)
                    self.times.append(time.time())
                    self.count += 1
                    self.size += len(data)
                    if not self.audio_only and self._has_keyframe(data):
                        self.kf.append(self.count - 1)
                        self.kf = self.kf[-64:]
                    while self.size > self.MAX_BUF and len(self.chunks) > 1:
                        self.size -= len(self.chunks.pop(0))
                        self.times.pop(0)
                        self.first += 1
                    self.cond.notify_all()
        except (OSError, ValueError):
            pass
        if proc is self.proc:
            self.alive = False
        with self.cond:
            self.cond.notify_all()

    def _has_keyframe(self, data):
        """Algum pacote TS do vídeo neste bloco tem o 'random access indicator' (quadro-chave)?"""
        pid = self.video_pid
        for o in range(0, len(data) - 187, 188):
            if (data[o] == 0x47 and ((data[o + 1] & 0x1F) << 8 | data[o + 2]) == pid
                    and data[o + 3] & 0x20 and data[o + 4] > 0 and data[o + 5] & 0x40):
                return True
        return False

    def _kill(self):
        self.alive = False
        p = self.proc
        if p and p.poll() is None:
            try:
                p.kill()
                p.wait(timeout=5)
            except Exception:
                pass
        with self.cond:
            self.cond.notify_all()

    def stop(self):
        self._kill()
        if self.audio:
            self.audio.close()
            self.audio = None

    def running(self):
        return bool(self.alive and self.proc and self.proc.poll() is None)

    def serve(self, h, head=False):
        """Atende a TV: manda o fluxo ao vivo, a partir de ~1 s atrás, até ela desconectar."""
        if h.path.split("?")[0] != self.path() or not self.alive:
            h.send_error(404)
            return
        h.send_response(200)
        h.send_header("Content-Type", self.mime)
        h.send_header("Cache-Control", "no-cache, no-store")
        h.send_header("Connection", "close")
        h.send_header("transferMode.dlna.org", self.transfer_mode)
        h.send_header("contentFeatures.dlna.org", LIVE_FLAGS)
        h.end_headers()
        h.close_connection = True
        if head:
            return
        with self.cond:
            ci = self.count
            if self.start_mode == "back":
                back = int(self.bytes_per_sec * 1.0)
                while ci > self.first and back > 0:
                    ci -= 1
                    back -= len(self.chunks[ci - self.first])
            elif not self.audio_only:
                seen, deadline = len(self.kf), time.time() + 2.5
                while self.alive and len(self.kf) <= seen and time.time() < deadline:
                    self.cond.wait(0.1)            # espera o próximo quadro-chave (<= 0,5 s)
                if len(self.kf) > seen:
                    ci = max(self.first, self.kf[-1] - 1)   # 1 bloco antes: leva o PAT/PMT junto
            if self.times and self.first <= ci < self.count:
                self.start_age = time.time() - self.times[ci - self.first]   # idade do 1º bloco enviado
        try:
            if self.pad_bytes and not self.audio_only:
                null = b"\x47\x1f\xff\x10" + b"\xff" * 184      # pacote nulo (PID 0x1FFF): o decodificador ignora
                h.wfile.write(null * (self.pad_bytes // 188))
            while self.alive:
                with self.cond:
                    while self.alive and ci >= self.count:
                        self.cond.wait(1.0)
                    if not self.alive:
                        break
                    if ci < self.first:                  # TV ficou para trás: pula para o presente
                        ci = max(self.first, self.count - 20)
                    batch = self.chunks[ci - self.first:]
                    ci = self.count
                h.wfile.write(b"".join(batch))
        except OSError:
            pass


def didl_live(title, url, audio_only):
    cls = "object.item.audioItem.musicTrack" if audio_only else "object.item.videoItem"
    mime = "audio/mpeg" if audio_only else "video/mpeg"
    esc = html.escape
    return (
        '<DIDL-Lite xmlns="urn:schemas-upnp-org:metadata-1-0/DIDL-Lite/" '
        'xmlns:dc="http://purl.org/dc/elements/1.1/" '
        'xmlns:upnp="urn:schemas-upnp-org:metadata-1-0/upnp/" '
        'xmlns:dlna="urn:schemas-dlna-org:metadata-1-0/">'
        '<item id="0" parentID="-1" restricted="1">'
        f"<dc:title>{esc(title)}</dc:title><upnp:class>{cls}</upnp:class>"
        f'<res protocolInfo="{esc(f"http-get:*:{mime}:{LIVE_FLAGS}")}">{esc(url)}</res>'
        "</item></DIDL-Lite>"
    )


# --------------------------------------------------------------------------
# Widgets (tema escuro estilo Apple)
# --------------------------------------------------------------------------
def rrect(cv, x1, y1, x2, y2, r, **kw):
    r = max(0, min(r, (x2 - x1) / 2, (y2 - y1) / 2))
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2,
           x2 - r, y2, x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return cv.create_polygon(pts, smooth=True, **kw)


def dark_titlebar(win):
    """Barra de título escura no Windows 10/11."""
    try:
        import ctypes
        win.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(win.winfo_id())
        dwm = ctypes.windll.dwmapi
        one = ctypes.c_int(1)
        for attr in (20, 19):
            if dwm.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(one), 4) == 0:
                break
        cap, txt = ctypes.c_int(0x001e1c1c), ctypes.c_int(0x00f7f5f5)
        dwm.DwmSetWindowAttribute(hwnd, 35, ctypes.byref(cap), 4)
        dwm.DwmSetWindowAttribute(hwnd, 36, ctypes.byref(txt), 4)
    except Exception:
        pass


class Btn(tk.Canvas):
    STYLES = {
        "default": (CARD2, CARD3, FG),
        "accent": (ACC, ACC_H, "#ffffff"),
        "ghost": (None, CARD2, FG),
    }

    def __init__(self, master, text, command, style="default", height=34, pad=16):
        self.h = px(height)
        self.pad = px(pad)
        super().__init__(master, height=self.h, bg=master.cget("bg"),
                         highlightthickness=0, bd=0, cursor="hand2")
        self.text, self.command, self.style, self.hover = text, command, style, False
        self.bind("<Enter>", lambda e: self._set_hover(True))
        self.bind("<Leave>", lambda e: self._set_hover(False))
        self.bind("<ButtonRelease-1>", self._click)
        self._layout()

    def _layout(self):
        self.w = F_UI.measure(self.text) + 2 * self.pad
        self.config(width=self.w)
        self._draw()

    def _set_hover(self, v):
        self.hover = v
        self._draw()

    def _click(self, e):
        if 0 <= e.x <= self.w and 0 <= e.y <= self.h and self.command:
            self.command()

    def set_text(self, text):
        self.text = text
        self._layout()

    def _draw(self):
        self.delete("all")
        base, hov, fg = self.STYLES[self.style]
        fill = hov if self.hover else base
        if fill:
            rrect(self, 1, 1, self.w - 1, self.h - 1, self.h / 2, fill=fill, outline="")
        self.create_text(self.w / 2, self.h / 2, text=self.text, fill=fg, font=F_UI)


def draw_icon(cv, name, cx, cy, r, color):
    k = dict(fill=color, outline="")
    if name == "play":
        cv.create_polygon(cx - r * .6, cy - r, cx - r * .6, cy + r, cx + r * .95, cy, **k)
    elif name == "pause":
        cv.create_rectangle(cx - r * .75, cy - r, cx - r * .15, cy + r, **k)
        cv.create_rectangle(cx + r * .15, cy - r, cx + r * .75, cy + r, **k)
    elif name == "stop":
        rrect(cv, cx - r * .8, cy - r * .8, cx + r * .8, cy + r * .8, r * .2, **k)
    elif name == "next":
        cv.create_polygon(cx - r, cy - r * .8, cx - r, cy + r * .8, cx, cy, **k)
        cv.create_polygon(cx, cy - r * .8, cx, cy + r * .8, cx + r, cy, **k)
    elif name == "prev":
        cv.create_polygon(cx + r, cy - r * .8, cx + r, cy + r * .8, cx, cy, **k)
        cv.create_polygon(cx, cy - r * .8, cx, cy + r * .8, cx - r, cy, **k)
    elif name in ("vol", "mute"):
        cv.create_polygon(cx - r, cy - r * .35, cx - r * .5, cy - r * .35, cx, cy - r * .8,
                          cx, cy + r * .8, cx - r * .5, cy + r * .35, cx - r, cy + r * .35, **k)
        if name == "vol":
            for rr in (.55, .95):
                cv.create_arc(cx - r * rr + r * .1, cy - r * rr, cx + r * rr + r * .1, cy + r * rr,
                              start=-40, extent=80, style="arc", outline=color, width=px(2))
        else:
            w = px(2)
            cv.create_line(cx + r * .3, cy - r * .4, cx + r * 1.0, cy + r * .4, fill=color, width=w)
            cv.create_line(cx + r * .3, cy + r * .4, cx + r * 1.0, cy - r * .4, fill=color, width=w)


class IconBtn(tk.Canvas):
    def __init__(self, master, icon, command, size=44, primary=False, glyph=.34):
        s = px(size)
        super().__init__(master, width=s, height=s, bg=master.cget("bg"),
                         highlightthickness=0, bd=0, cursor="hand2")
        self.s, self.icon, self.command = s, icon, command
        self.primary, self.glyph, self.hover = primary, glyph, False
        self.bind("<Enter>", lambda e: self._set_hover(True))
        self.bind("<Leave>", lambda e: self._set_hover(False))
        self.bind("<ButtonRelease-1>", self._click)
        self._draw()

    def _set_hover(self, v):
        self.hover = v
        self._draw()

    def _click(self, e):
        if 0 <= e.x <= self.s and 0 <= e.y <= self.s and self.command:
            self.command()

    def set_icon(self, icon):
        if icon != self.icon:
            self.icon = icon
            self._draw()

    def _draw(self):
        self.delete("all")
        c = self.s / 2
        if self.primary:
            self.create_oval(1, 1, self.s - 1, self.s - 1,
                             fill="#d1d1d6" if self.hover else "#ffffff", outline="")
            col = BG
        else:
            if self.hover:
                self.create_oval(1, 1, self.s - 1, self.s - 1, fill=CARD2, outline="")
            col = FG
        draw_icon(self, self.icon, c, c, self.s * self.glyph, col)


class Slider(tk.Canvas):
    """Barra estilo Apple: o valor vem da posição exata do mouse."""

    def __init__(self, master, on_change=None, on_release=None, fill=FG, height=22, width=None):
        kw = {"width": px(width)} if width else {}
        super().__init__(master, height=px(height), bg=master.cget("bg"),
                         highlightthickness=0, bd=0, cursor="hand2", **kw)
        self.frac, self.dragging, self.enabled, self.hover = 0.0, False, True, False
        self.on_change, self.on_release, self.fillc = on_change, on_release, fill
        self.bind("<Configure>", lambda e: self._draw())
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<B1-Motion>", self._move)
        self.bind("<ButtonRelease-1>", self._release)
        self.bind("<Enter>", lambda e: self._set_hover(True))
        self.bind("<Leave>", lambda e: self._set_hover(False))

    def _set_hover(self, v):
        self.hover = v
        self._draw()

    def _frac_at(self, x):
        pad = px(8)
        return min(1.0, max(0.0, (x - pad) / max(1, self.winfo_width() - 2 * pad)))

    def set(self, f):
        if self.dragging:
            return
        self.frac = min(1.0, max(0.0, f))
        self._draw()

    def set_enabled(self, v):
        self.enabled = v
        self.config(cursor="hand2" if v else "arrow")
        self._draw()

    def _press(self, e):
        if not self.enabled:
            return
        self.dragging = True
        self._move(e)

    def _move(self, e):
        if not self.dragging:
            return
        self.frac = self._frac_at(e.x)
        self._draw()
        if self.on_change:
            self.on_change(self.frac)

    def _release(self, e):
        if not self.dragging:
            return
        self.frac = self._frac_at(e.x)
        self.dragging = False
        self._draw()
        if self.on_release:
            self.on_release(self.frac)

    def _draw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        pad, cy, th = px(8), h / 2, px(4)
        x1, x2 = pad, max(pad + 1, w - pad)
        rrect(self, x1, cy - th / 2, x2, cy + th / 2, th / 2, fill=CARD3, outline="")
        xe = x1 + (x2 - x1) * self.frac
        if self.enabled and xe > x1 + 1:
            rrect(self, x1, cy - th / 2, xe, cy + th / 2, th / 2, fill=self.fillc, outline="")
        if self.enabled and (self.hover or self.dragging):
            r = px(7)
            self.create_oval(xe - r, cy - r, xe + r, cy + r, fill="#ffffff", outline="")


class Switch(tk.Canvas):
    def __init__(self, master, value=False, command=None):
        super().__init__(master, width=px(42), height=px(24), bg=master.cget("bg"),
                         highlightthickness=0, bd=0, cursor="hand2")
        self.value, self.command = value, command
        self.bind("<Button-1>", lambda e: self.toggle())
        self._draw()

    def get(self):
        return self.value

    def toggle(self):
        self.value = not self.value
        self._draw()
        if self.command:
            self.command(self.value)

    def _draw(self):
        self.delete("all")
        w, h = px(42), px(24)
        rrect(self, 1, 1, w - 1, h - 1, h / 2, fill=GREEN if self.value else CARD3, outline="")
        m = px(3)
        x = w - m - (h - 2 * m) if self.value else m
        self.create_oval(x, m, x + h - 2 * m, h - m, fill="#ffffff", outline="")


class Tip:
    """Dica que aparece ao passar o mouse."""

    def __init__(self, widget, text):
        self.widget, self.text, self.win, self.job = widget, text, None, None
        widget.bind("<Enter>", self._enter, add="+")
        widget.bind("<Leave>", self._leave, add="+")
        widget.bind("<ButtonPress>", self._leave, add="+")

    def _enter(self, _):
        self.job = self.widget.after(450, self._show)

    def _leave(self, _):
        if self.job:
            self.widget.after_cancel(self.job)
            self.job = None
        if self.win:
            self.win.destroy()
            self.win = None

    def _show(self):
        self.win = w = tk.Toplevel(self.widget)
        w.overrideredirect(True)
        w.attributes("-topmost", True)
        tk.Label(w, text=self.text, bg=CARD2, fg=FG, font=F_SMALL, justify="left",
                 wraplength=px(320), padx=px(12), pady=px(8)).pack()
        w.geometry(f"+{self.widget.winfo_rootx()}+{self.widget.winfo_rooty() - w.winfo_reqheight() - 6}")


COMPAT_HELP = (
    "Modo compatibilidade\n\n"
    "Use só quando a TV não consegue tocar um arquivo: fica sem imagem, sem som "
    "ou mostra \"formato não suportado\".\n\n"
    "O que acontece: o programa converte o arquivo aqui no PC, para MP4 (vídeo) ou "
    "MP3 (música), antes de enviar para a TV. O arquivo original não é alterado.\n\n"
    "• Vídeo já em H.264: só o áudio é convertido. É rápido (poucos minutos num filme).\n"
    "• Outros formatos (HEVC, AVI antigo etc.): o vídeo é recodificado. Pode levar "
    "vários minutos; acompanhe a porcentagem na barra de status, embaixo.\n"
    "• Trocar de item cancela a conversão em andamento.\n\n"
    "Se a TV já toca o arquivo normalmente, deixe desligado: converter só atrasa e "
    "pode reduzir um pouco a qualidade.\n\n"
    "Depois de ligar, toque o item de novo para valer a conversão."
)


def make_dialog(root, title):
    d = tk.Toplevel(root)
    d.title(title)
    d.configure(bg=BG)
    d.transient(root)
    d.resizable(False, False)
    dark_titlebar(d)
    return d


def center_on(d, root):
    d.update_idletasks()
    x = root.winfo_rootx() + (root.winfo_width() - d.winfo_width()) // 2
    y = root.winfo_rooty() + (root.winfo_height() - d.winfo_height()) // 3
    d.geometry(f"+{max(0, x)}+{max(0, y)}")


def show_info(root, title, msg):
    d = make_dialog(root, title)
    tk.Label(d, text=msg, bg=BG, fg=FG, font=F_UI, wraplength=px(380),
             justify="left").pack(padx=px(24), pady=(px(22), px(14)))
    Btn(d, "OK", d.destroy, "accent").pack(pady=(0, px(18)))
    center_on(d, root)
    d.grab_set()


def ask_text(root, title, prompt, callback):
    d = make_dialog(root, title)
    tk.Label(d, text=prompt, bg=BG, fg=FG, font=F_UI, wraplength=px(380),
             justify="left").pack(padx=px(24), pady=(px(22), px(8)), anchor="w")
    var = tk.StringVar()
    e = tk.Entry(d, textvariable=var, bg=CARD, fg=FG, insertbackground=FG, relief="flat",
                 font=F_LIST, highlightthickness=1, highlightbackground=CARD3,
                 highlightcolor=ACC)
    e.pack(fill="x", padx=px(24), ipady=px(6))

    def ok(*_):
        v = var.get().strip()
        d.destroy()
        if v:
            callback(v)
    row = tk.Frame(d, bg=BG)
    row.pack(pady=px(16))
    Btn(row, "Cancelar", d.destroy).pack(side="left", padx=4)
    Btn(row, "Conectar", ok, "accent").pack(side="left", padx=4)
    e.bind("<Return>", ok)
    center_on(d, root)
    d.grab_set()
    e.focus_set()


# --------------------------------------------------------------------------
# Controle pelo celular (página web servida pelo próprio programa)
# --------------------------------------------------------------------------
REMOTE_HTML = r"""<!doctype html>
<html lang="pt-BR"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#1c1c1e">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<title>TV Caster</title>
<style>
:root{--bg:#1c1c1e;--card:#2c2c2e;--card2:#3a3a3c;--fg:#f5f5f7;--fg2:#98989d;--acc:#0a84ff;--sep:#38383a}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html{background:var(--bg)}
body{margin:0;background:var(--bg);color:var(--fg);font:16px/1.35 -apple-system,BlinkMacSystemFont,"SF Pro Text","Segoe UI",Roboto,sans-serif;
 padding:calc(14px + env(safe-area-inset-top)) 16px calc(28px + env(safe-area-inset-bottom));max-width:560px;margin:0 auto}
h1{font-size:28px;margin:6px 0 14px;letter-spacing:-.5px}
#off{background:#5b2020;color:#ffd7d7;border-radius:12px;padding:10px 14px;margin-bottom:12px;font-size:14px}
select{width:100%;background:var(--card);color:var(--fg);border:0;border-radius:12px;padding:13px 14px;font-size:16px;margin-bottom:14px;appearance:none;-webkit-appearance:none}
.card{background:var(--card);border-radius:20px;padding:18px 16px 14px;margin-bottom:16px}
#now{font-size:19px;font-weight:600;word-break:break-word;min-height:26px}
.sub{color:var(--fg2);font-size:13px;margin-top:2px;min-height:18px}
.times{display:flex;justify-content:space-between;color:var(--fg2);font-size:12px;font-variant-numeric:tabular-nums}
input[type=range]{-webkit-appearance:none;appearance:none;width:100%;height:30px;background:transparent;margin:6px 0 0}
input[type=range]::-webkit-slider-runnable-track{height:5px;border-radius:3px;background:linear-gradient(to right,#fff var(--p,0%),#48484a var(--p,0%))}
input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:20px;height:20px;border-radius:50%;background:#fff;margin-top:-7.5px;box-shadow:0 1px 4px #0006}
input[type=range]::-moz-range-track{height:5px;border-radius:3px;background:#48484a}
input[type=range]::-moz-range-progress{height:5px;border-radius:3px;background:#fff}
input[type=range]::-moz-range-thumb{width:20px;height:20px;border:0;border-radius:50%;background:#fff}
input[type=range]:disabled{opacity:.4}
.ctl{display:flex;justify-content:center;align-items:center;gap:22px;margin:8px 0 12px}
.ctl button,.mute{background:none;border:0;color:var(--fg);width:54px;height:54px;border-radius:50%;display:grid;place-items:center;padding:0}
.ctl button:active,.mute:active{background:var(--card2)}
.ctl svg{width:28px;height:28px;fill:currentColor}
.ctl #play{background:#fff;color:#1c1c1e;width:68px;height:68px}
.ctl #play svg{width:32px;height:32px}
.ctl #play:active{background:#d1d1d6}
.volrow{display:flex;align-items:center;gap:6px}
.mute{width:40px;height:40px}.mute svg{width:24px;height:24px;fill:currentColor}
.skip{display:flex;justify-content:center;gap:12px;margin:10px 0 2px}
.skip button{min-width:104px;height:44px;border:0;border-radius:999px;background:var(--card2);color:var(--fg);font-size:15px;font-weight:600;padding:0 16px;touch-action:manipulation}
.skip button:active{background:#48484a}
.skip button:disabled{opacity:.4}
.volrow .mute{width:38px;height:38px}
.vb{flex:none;width:40px;height:40px;border-radius:50%;border:0;background:var(--card2);color:var(--fg);font-size:26px;line-height:1;padding:0 0 3px;display:grid;place-items:center;touch-action:manipulation}
.vb:active{background:#48484a}
.volrow input[type=range]{flex:1;min-width:0}
#vn{width:28px;text-align:right;color:var(--fg2);font-size:13px;font-variant-numeric:tabular-nums}
.seg{display:flex;background:var(--card);border-radius:12px;padding:3px;margin-bottom:12px}
.seg button{flex:1;border:0;background:none;color:var(--fg2);font-size:15px;padding:9px;border-radius:9px;font-weight:600}
.seg button.on{background:var(--card2);color:var(--fg)}
ul{list-style:none;margin:0;padding:0;background:var(--card);border-radius:16px;overflow:hidden}
li{display:flex;align-items:center;border-bottom:1px solid var(--sep)}
li:last-child{border-bottom:0}
li.cur .t{color:var(--acc);font-weight:600}
.row{flex:1;text-align:left;background:none;border:0;color:var(--fg);font-size:15px;padding:14px 16px;min-width:0;word-break:break-word}
.row small{display:block;color:var(--fg2);font-size:12px}
.x,.mini{background:none;border:0;color:var(--fg2);font-size:22px;width:46px;height:46px;flex:none}
.mini{color:var(--acc);font-size:15px;font-weight:600;width:auto;padding:0 14px}
.empty{color:var(--fg2);text-align:center;padding:26px 10px;font-size:14px}
.bar{display:flex;gap:8px;align-items:center;margin-bottom:10px}
.bar .path{flex:1;color:var(--fg2);font-size:13px;word-break:break-all}
.pill{background:var(--card2);color:var(--fg);border:0;border-radius:999px;padding:8px 14px;font-size:14px}
#toast{position:fixed;left:50%;bottom:calc(24px + env(safe-area-inset-bottom));transform:translateX(-50%);background:#48484aee;color:#fff;padding:10px 18px;border-radius:999px;font-size:14px;opacity:0;transition:opacity .2s;pointer-events:none}
#toast.on{opacity:1}
</style></head><body>
<h1>TV Caster</h1>
<div id="off" hidden>Sem conexão com o PC. Confira se o TV Caster está aberto.</div>
<select id="tv"></select>
<div class="card">
  <div id="now">Nada tocando</div>
  <div class="sub" id="st"></div>
  <input type="range" id="seek" min="0" max="1" step="1" value="0" disabled>
  <div class="times"><span id="t1">0:00</span><span id="t2">0:00</span></div>
  <div class="skip">
    <button id="sbk" aria-label="Voltar 10 segundos" disabled>&minus;10 s</button>
    <button id="sfw" aria-label="Avançar 10 segundos" disabled>+10 s</button>
  </div>
  <div class="ctl">
    <button id="prev" aria-label="Anterior"></button>
    <button id="play" aria-label="Play/Pausa"></button>
    <button id="stop" aria-label="Parar"></button>
    <button id="next" aria-label="Próximo"></button>
  </div>
  <div class="volrow">
    <button class="mute" id="mute" aria-label="Mudo"></button>
    <button class="vb" id="vdn" aria-label="Diminuir volume">&minus;</button>
    <input type="range" id="vol" min="0" max="100" step="1" value="15">
    <button class="vb" id="vup" aria-label="Aumentar volume">+</button>
    <span id="vn">15</span>
  </div>
  <div class="sub" id="subinfo" style="margin-top:8px"></div>
</div>
<div class="seg"><button id="tq" class="on">Fila</button><button id="tl">Biblioteca</button><button id="ts">Legendas</button><button id="tw">Ao vivo</button></div>
<section id="sq"><ul id="queue"></ul><div class="empty" id="empty">A fila está vazia. Adicione itens na Biblioteca.</div></section>
<section id="sl" hidden></section>
<section id="sv" hidden></section>
<div id="toast"></div>
<script>
const $=s=>document.querySelector(s);
const ICON={
 play:'<svg viewBox="0 0 24 24"><path d="M7 4.5v15l13-7.5z"/></svg>',
 pause:'<svg viewBox="0 0 24 24"><path d="M6 4h4v16H6zM14 4h4v16h-4z"/></svg>',
 stop:'<svg viewBox="0 0 24 24"><rect x="6" y="6" width="12" height="12" rx="2"/></svg>',
 prev:'<svg viewBox="0 0 24 24"><path d="M11 5v14L2.5 12zM21.5 5v14L13 12z"/></svg>',
 next:'<svg viewBox="0 0 24 24"><path d="M13 5v14l8.5-7zM2.5 5v14L11 12z"/></svg>',
 vol:'<svg viewBox="0 0 24 24"><path d="M3 9v6h4l5 4V5L7 9z"/><path d="M15.5 8.5a5 5 0 0 1 0 7M18.2 5.8a9 9 0 0 1 0 12.4" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"/></svg>',
 mute:'<svg viewBox="0 0 24 24"><path d="M3 9v6h4l5 4V5L7 9z"/><path d="M16 9l5 6M21 9l-5 6" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"/></svg>'};
const PT={PLAYING:'Reproduzindo',PAUSED_PLAYBACK:'Pausado',STOPPED:'Parado',TRANSITIONING:'Carregando',NO_MEDIA_PRESENT:'Sem mídia'};
const fmt=s=>{s=Math.max(0,Math.floor(s||0));const h=Math.floor(s/3600),m=Math.floor(s%3600/60),x=s%60;return(h?h+':'+String(m).padStart(2,'0'):m)+':'+String(x).padStart(2,'0')};
const prog=r=>r.style.setProperty('--p',(r.max>0?r.value/r.max*100:0)+'%');
let S=null,drag=false,hold=0,vhold=0,qsig='',br={root:null,path:''},tab='q',tt;
['prev','play','stop','next'].forEach(k=>$('#'+k).innerHTML=ICON[k]);
$('#mute').innerHTML=ICON.vol;
function toast(t){const e=$('#toast');e.textContent=t;e.classList.add('on');clearTimeout(tt);tt=setTimeout(()=>e.classList.remove('on'),1800)}
async function api(p,b){const r=await fetch(p,b?{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(b)}:undefined);if(!r.ok)throw 0;return r.json()}
function send(c,x){return api('api/cmd',Object.assign({cmd:c},x||{})).then(()=>setTimeout(poll,250)).catch(()=>toast('Falha ao enviar'))}
async function poll(){try{S=await api('api/state');$('#off').hidden=true;render()}catch(e){$('#off').hidden=false}}
function render(){
 const s=S,sel=$('#tv'),k=s.tvs.join('|');
 if(sel.dataset.k!==k){sel.dataset.k=k;sel.replaceChildren();s.tvs.forEach((t,i)=>sel.append(new Option(t,i)));if(!s.tvs.length)sel.append(new Option('Nenhuma TV encontrada',''))}
 if(s.tv>=0)sel.value=s.tv;
 $('#now').textContent=s.now;$('#st').textContent=s.loading?'Carregando…':(PT[s.state]||s.state||'');
 $('#play').innerHTML=s.state==='PLAYING'?ICON.pause:ICON.play;
 const r=$('#seek');
 if(!drag&&Date.now()>hold){r.max=s.dur||1;r.value=Math.min(s.pos,s.dur||1);r.disabled=!s.dur;$('#sbk').disabled=$('#sfw').disabled=r.disabled;prog(r);$('#t1').textContent=fmt(s.pos)}
 $('#t2').textContent=fmt(s.dur);
 if(Date.now()>vhold){$('#vol').value=s.volume;prog($('#vol'));$('#vn').textContent=s.volume}
 $('#mute').innerHTML=s.muted?ICON.mute:ICON.vol;
 $('#subinfo').textContent=s.subdesc||(s.subs?'':'Legendas desligadas');
 const q=JSON.stringify([s.playlist,s.current]);if(q!==qsig){qsig=q;drawQueue()}
 if(tab==='s')drawSubs();if(tab==='w')renderLive();
}
function drawQueue(){const ul=$('#queue');ul.replaceChildren();S.playlist.forEach((t,i)=>{const li=document.createElement('li');if(i===S.current)li.className='cur';
 const b=document.createElement('button');b.className='row';const sp=document.createElement('span');sp.className='t';sp.textContent=t;b.append(sp);b.onclick=()=>send('play_index',{i});
 const x=document.createElement('button');x.className='x';x.textContent='×';x.onclick=()=>send('remove',{i});li.append(b,x);ul.append(li)});$('#empty').hidden=S.playlist.length>0}
function drawSubs(){const box=$('#ss');if(!box)return;const k=JSON.stringify([S.subs,S.subopts]);if(box.dataset.k===k)return;box.dataset.k=k;box.replaceChildren();
 const bar=document.createElement('div');bar.className='bar';const p=document.createElement('div');p.className='path';p.textContent=S.subs?'Legendas ligadas':'Legendas desligadas';
 const b=document.createElement('button');b.className='pill';b.textContent=S.subs?'Desligar tudo':'Ligar';b.onclick=()=>send('subs');bar.append(p,b);box.append(bar);
 if(!S.subopts.length){const e=document.createElement('div');e.className='empty';e.textContent='Toque algo para escolher a legenda.';box.append(e);return}
 const ul=document.createElement('ul');S.subopts.forEach((o,i)=>{const li=document.createElement('li');if(o.sel)li.className='cur';const r=document.createElement('button');r.className='row';r.disabled=!o.ok;if(!o.ok)r.style.opacity='.45';
  const sp=document.createElement('span');sp.className='t';sp.textContent=(o.sel?'●  ':'○  ')+o.label;r.append(sp);r.onclick=()=>{send('sub_choice',{i});toast('Aplicando legenda…')};li.append(r);ul.append(li)});
 box.append(ul)}
async function browse(){
 const box=$('#sl');box.replaceChildren();
 if(br.root===null){const ul=document.createElement('ul');S.folders.forEach((f,i)=>{const li=document.createElement('li');const b=document.createElement('button');b.className='row';b.textContent='📁  '+f;b.onclick=()=>{br={root:i,path:''};browse()};li.append(b);ul.append(li)});
  if(!S.folders.length){const e=document.createElement('div');e.className='empty';e.textContent='Nenhuma pasta compartilhada. No PC, use "+ Pasta" para adicionar uma.';box.append(e)}else box.append(ul);return}
 let d;try{d=await api('api/browse?root='+br.root+'&path='+encodeURIComponent(br.path))}catch(e){toast('Pasta indisponível');br={root:null,path:''};return browse()}
 const bar=document.createElement('div');bar.className='bar';
 const back=document.createElement('button');back.className='pill';back.textContent='‹ Voltar';back.onclick=()=>{if(!br.path)br={root:null,path:''};else{const i=br.path.lastIndexOf('/');br.path=i<0?'':br.path.slice(0,i)}browse()};
 const p=document.createElement('div');p.className='path';p.textContent=S.folders[br.root]+(br.path?' / '+br.path.split('/').join(' / '):'');
 const all=document.createElement('button');all.className='pill';all.textContent='+ Tudo';all.onclick=()=>{send('add_dir',{root:br.root,path:br.path});toast('Pasta adicionada à fila')};
 bar.append(back,p,all);box.append(bar);
 const ul=document.createElement('ul');
 d.dirs.forEach(n=>{const li=document.createElement('li');const b=document.createElement('button');b.className='row';b.textContent='📁  '+n;b.onclick=()=>{br.path=br.path?br.path+'/'+n:n;browse()};li.append(b);ul.append(li)});
 d.files.forEach(n=>{const rel=br.path?br.path+'/'+n:n;const li=document.createElement('li');const b=document.createElement('button');b.className='row';b.textContent=n;b.onclick=()=>{send('add_file',{root:br.root,path:rel,play:true})};
  const a=document.createElement('button');a.className='mini';a.textContent='+';a.onclick=()=>{send('add_file',{root:br.root,path:rel});toast('Adicionado à fila')};li.append(b,a);ul.append(li)});
 if(!ul.children.length){const e=document.createElement('div');e.className='empty';e.textContent='Pasta sem vídeos ou músicas.';box.append(e)}else box.append(ul)}
function setTab(t){tab=t;['q','l','s','w'].forEach(k=>{const e=$('#t'+k);if(e)e.className=t===k?'on':''});
 $('#sq').hidden=t!=='q';$('#sl').hidden=t!=='l';$('#sv').hidden=t!=='w';
 let ss=$('#ss');if(!ss){ss=document.createElement('section');ss.id='ss';document.body.insertBefore(ss,$('#toast'))}ss.hidden=t!=='s';
 if(t==='l')browse();if(t==='s'){ss.dataset.k='';drawSubs()}if(t==='w')openLive()}
$('#tq').onclick=()=>setTab('q');$('#tl').onclick=()=>setTab('l');$('#ts').onclick=()=>setTab('s');$('#tw').onclick=()=>setTab('w');
function pill(t,fn){const b=document.createElement('button');b.className='pill';b.textContent=t;b.onclick=fn;return b}
function renderLive(){const e=$('#lvst');if(e)e.textContent=S.live&&S.live.on?('● Transmitindo: '+S.live.label):'Nada sendo transmitido. A imagem chega à TV com alguns segundos de atraso (ótimo para vídeo e música; ruim para jogos de ação).'}
async function openLive(){const box=$('#sv');box.replaceChildren();
 const st=document.createElement('div');st.className='sub';st.id='lvst';st.style.marginBottom='10px';box.append(st);
 const bar=document.createElement('div');bar.className='bar';
 (S.screens&&S.screens.length>1?S.screens.map((l,i)=>pill('Tela '+(i+1),()=>{send('live_start',{mode:'screen',screen:i});toast('Iniciando…')})):[pill('Tela inteira',()=>{send('live_start',{mode:'screen'});toast('Iniciando…')})]).forEach(b=>bar.append(b));bar.append(pill('Só o som do PC',()=>{send('live_start',{mode:'audio'});toast('Iniciando…')}),pill('Parar',()=>send('live_stop')));box.append(bar);
 const h=document.createElement('div');h.className='sub';h.textContent='Ou escolha uma janela aberta no PC:';h.style.margin='6px 0';box.append(h);
 const ul=document.createElement('ul');box.append(ul);
 try{const w=await api('api/windows');w.forEach(t=>{const li=document.createElement('li');const r=document.createElement('button');r.className='row';r.textContent=t;r.onclick=()=>{send('live_start',{mode:'window',title:t});toast('Iniciando…')};li.append(r);ul.append(li)});
  if(!w.length){const e=document.createElement('div');e.className='empty';e.textContent='Nenhuma janela encontrada.';box.append(e)}}catch(e){}
 renderLive()}
$('#play').onclick=()=>send(S&&S.state==='PLAYING'?'pause':'play');
$('#prev').onclick=()=>send('prev');$('#next').onclick=()=>send('next');$('#stop').onclick=()=>send('stop');
$('#mute').onclick=()=>send('mute');
$('#tv').onchange=e=>send('select_tv',{i:+e.target.value});
const seek=$('#seek');
seek.addEventListener('input',()=>{drag=true;prog(seek);$('#t1').textContent=fmt(seek.value)});
seek.addEventListener('change',()=>{drag=false;hold=Date.now()+5000;send('seek',{sec:+seek.value})});
let kt;
function skip(d){if(seek.disabled)return;const v=Math.max(0,Math.min(+seek.max-1,(+seek.value||0)+d));seek.value=v;prog(seek);$('#t1').textContent=fmt(v);hold=Date.now()+5000;
 clearTimeout(kt);kt=setTimeout(()=>send('seek',{sec:v}),400)}   // toques seguidos acumulam e viram um só salto
$('#sbk').onclick=()=>skip(-10);$('#sfw').onclick=()=>skip(10);
const vol=$('#vol');
vol.addEventListener('input',()=>{vhold=Date.now()+2500;prog(vol);$('#vn').textContent=vol.value});
vol.addEventListener('change',()=>{vhold=Date.now()+2500;send('volume',{v:+vol.value})});
let vt;
function volStep(d){const v=Math.max(0,Math.min(100,(+vol.value||0)+d));vol.value=v;prog(vol);$('#vn').textContent=v;vhold=Date.now()+2500;
 clearTimeout(vt);vt=setTimeout(()=>send('volume',{v}),300)}   // vários toques seguidos viram um só envio
$('#vdn').onclick=()=>volStep(-1);$('#vup').onclick=()=>volStep(1);
setInterval(poll,1000);poll();
</script></body></html>
"""


class Remote:
    """Atende /r/<chave>/... no servidor HTTP (página + API JSON)."""

    def __init__(self, app):
        self.app = app

    @property
    def key(self):
        return self.app.cfg["remote_key"]

    def _send(self, h, code, body, ctype, extra=None):
        h.send_response(code)
        h.send_header("Content-Type", ctype)
        h.send_header("Content-Length", str(len(body)))
        h.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            h.send_header(k, v)
        h.end_headers()
        h.wfile.write(body)

    def _json(self, h, obj, code=200):
        self._send(h, code, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                   "application/json; charset=utf-8")

    def __call__(self, h, method):
        try:
            self._handle(h, method)
        except (OSError, ValueError, KeyError, IndexError, TypeError):
            try:
                self._json(h, {"ok": False}, 400)
            except OSError:
                pass

    def _handle(self, h, method):
        u = urllib.parse.urlparse(h.path)
        prefix = f"/r/{self.key}"
        if u.path == prefix:
            self._send(h, 301, b"", "text/plain", {"Location": prefix + "/"})
            return
        if not u.path.startswith(prefix + "/"):
            self._send(h, 404, b"404", "text/plain")
            return
        route = u.path[len(prefix) + 1:]
        q = urllib.parse.parse_qs(u.query)
        if method == "GET" and route in ("", "index.html"):
            self._send(h, 200, REMOTE_HTML.encode("utf-8"), "text/html; charset=utf-8")
        elif method == "GET" and route == "api/state":
            self._json(h, self.app.snapshot())
        elif method == "GET" and route == "api/windows":
            self._json(h, list_windows())
        elif method == "GET" and route == "api/browse":
            self._json(h, self._browse(int(q["root"][0]), q.get("path", [""])[0]))
        elif method == "POST" and route == "api/cmd":
            n = min(int(h.headers.get("Content-Length") or 0), 65536)
            data = json.loads(h.rfile.read(n).decode("utf-8") or "{}")
            def run():
                try:
                    self.app.remote_cmd(data)
                except (ValueError, KeyError, IndexError, TypeError, OSError):
                    pass   # comando inválido ou fora das pastas compartilhadas
            self.app.root.after(0, run)
            self._json(h, {"ok": True})
        else:
            self._send(h, 404, b"404", "text/plain")

    def resolve(self, root_i, rel):
        """Caminho absoluto dentro de uma pasta compartilhada (nunca fora dela)."""
        folders = self.app.cfg.get("folders", [])
        base = os.path.realpath(folders[root_i])
        rel = (rel or "").replace("\\", "/").strip("/")
        full = os.path.realpath(os.path.join(base, *[p for p in rel.split("/") if p]))
        if os.path.commonpath([base, full]) != base:
            raise ValueError("fora da pasta")
        return full

    def _browse(self, root_i, rel):
        full = self.resolve(root_i, rel)
        dirs, files = [], []
        for n in sorted(os.listdir(full), key=natkey)[:3000]:
            if n.startswith("."):
                continue
            p = os.path.join(full, n)
            if os.path.isdir(p):
                dirs.append(n)
            elif os.path.splitext(n)[1].lower() in MIME:
                files.append(n)
        return {"dirs": dirs, "files": files}


# --------------------------------------------------------------------------
# Interface
# --------------------------------------------------------------------------
class App:
    def __init__(self, root):
        self.root = root
        root.title("TV Caster")
        root.geometry(f"{px(860)}x{px(740)}")
        root.minsize(px(740), px(600))
        root.configure(bg=BG)

        self.cfg = load_config()
        self.server = MediaServer()
        self.remote = Remote(self)
        self.server.remote = self.remote
        self.tmpdir = tempfile.mkdtemp(prefix="tvcaster_")
        self.renderers = []
        self.dev = None
        self.playlist = []
        self.current = -1
        self.duration = 0
        self.pos = 0
        self.state = ""
        self.vol_value = 15
        self.now_text = "Nada tocando"
        self.status_text = ""
        self.sub_name = ""
        self.sub_text = ""
        self.sub_choice = {}      # caminho -> 'auto' | 'off' | ('ext', arquivo) | ('emb', nº da faixa)
        self.sub_custom = {}      # caminho -> arquivo de legenda escolhido à mão
        self.mkv_cache = {}
        self.tv_lock = threading.Lock()
        self.live = None
        self.screens = []                 # [(índice, largura, altura)] da captura por GPU
        self.live_label = ""
        self.live_seen = False
        self.live_dialog = None
        self.sub_cache = {}
        self.seek_target = None
        self.seek_until = 0
        self.loading = False
        self.load_gen = 0
        self.expect_end = False
        self.was_playing = False
        self.user_stopped = False
        self.muted = False
        self.converted = {}
        self.stripped = {}        # caminho -> cópia sem legendas embutidas (na pasta temporária)
        self.alive = True

        self._build_ui()
        root.after(60, lambda: enable_file_drop(root, self._on_drop))
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        root.after(30, lambda: dark_titlebar(root))
        _ff = find_ffmpeg()
        if _ff:
            self.run_bg(lambda: list_screens(_ff), lambda s: setattr(self, "screens", s))
        self.discover()
        threading.Thread(target=self._poll_loop, daemon=True).start()

    # ---------------- UI ----------------
    def _build_ui(self):
        r = self.root
        side = px(24)

        # barra de status (embaixo)
        bar = tk.Frame(r, bg=BG)
        bar.pack(fill="x", side="bottom", padx=side, pady=(0, px(10)))
        self.state_lbl = tk.Label(bar, text="", bg=BG, fg=FG2, font=F_SMALL, anchor="e")
        self.state_lbl.pack(side="right")
        self.status = tk.Label(bar, text="", bg=BG, fg=FG2, font=F_SMALL, anchor="w")
        self.status.pack(side="left", fill="x", expand=True)

        # cabeçalho
        head = tk.Frame(r, bg=BG)
        head.pack(fill="x", padx=side, pady=(px(20), px(12)))
        tk.Label(head, text="TV Caster", bg=BG, fg=FG, font=F_TITLE).pack(side="left")
        Btn(head, "Celular", self.show_remote).pack(side="right")
        Btn(head, "Transmitir", self.show_live).pack(side="right", padx=(0, px(8)))
        self.tv_btn = Btn(head, "Procurando TVs…", self._open_tv_menu)
        self.tv_btn.pack(side="right", padx=(0, px(8)))
        self.tv_menu = tk.Menu(r, tearoff=0, bg=CARD, fg=FG, activebackground=ACC,
                               activeforeground="#ffffff", bd=0, relief="flat", font=F_UI)

        # fila
        lib = tk.Frame(r, bg=CARD)
        lib.pack(fill="both", expand=True, padx=side)
        top = tk.Frame(lib, bg=CARD)
        top.pack(fill="x", padx=px(16), pady=(px(14), px(4)))
        tk.Label(top, text="Fila de reprodução", bg=CARD, fg=FG, font=F_BOLD).pack(side="left")
        self.count_lbl = tk.Label(top, text="Arraste vídeos ou músicas para cá", bg=CARD, fg=FG2,
                                  font=F_SMALL)
        self.count_lbl.pack(side="right")

        body = tk.Frame(lib, bg=CARD)
        body.pack(fill="both", expand=True, padx=(px(8), px(4)))
        self.lb = tk.Listbox(body, bg=CARD, fg=FG, selectbackground=CARD2, selectforeground=FG,
                             activestyle="none", bd=0, highlightthickness=0, relief="flat",
                             font=F_LIST, selectmode="extended")
        sb = ttk.Scrollbar(body, style="Dark.Vertical.TScrollbar", orient="vertical",
                           command=self.lb.yview)
        self.lb.configure(yscrollcommand=sb.set)
        self.lb.pack(side="left", fill="both", expand=True, padx=(px(8), 0), pady=px(4))
        sb.pack(side="left", fill="y", pady=px(6))
        self.lb.bind("<Double-Button-1>", self._on_double_click)

        acts = tk.Frame(lib, bg=CARD)
        acts.pack(fill="x", padx=px(10), pady=(px(2), px(12)))
        for txt, cmd in (("+ Arquivos", self.add_files), ("+ Pasta", self.add_folder),
                         ("Legenda…", self._open_sub_menu), ("Remover", self.remove_sel),
                         ("Limpar", self.clear_list)):
            b = Btn(acts, txt, cmd, "ghost")
            b.pack(side="left", padx=2)
            if txt == "Legenda…":
                self.sub_btn = b
        Btn(acts, "↓", lambda: self.move(1), "ghost", pad=12).pack(side="right", padx=2)
        Btn(acts, "↑", lambda: self.move(-1), "ghost", pad=12).pack(side="right", padx=2)

        # player
        pl = tk.Frame(r, bg=CARD)
        pl.pack(fill="x", side="bottom", before=lib, padx=side, pady=(px(12), px(10)))
        self.now = tk.Label(pl, text="Nada tocando", bg=CARD, fg=FG, font=F_NOW, anchor="w")
        self.now.pack(fill="x", padx=px(18), pady=(px(14), 0))
        self.sub_lbl = tk.Label(pl, text="", bg=CARD, fg=FG2, font=F_SMALL, anchor="w")
        self.sub_lbl.pack(fill="x", padx=px(18))

        prog = tk.Frame(pl, bg=CARD)
        prog.pack(fill="x", padx=px(12), pady=(px(8), 0))
        self.pos_lbl = tk.Label(prog, text="0:00:00", bg=CARD, fg=FG2, font=F_SMALL, width=7)
        self.pos_lbl.pack(side="left")
        self.progress = Slider(prog, on_change=self._on_seek_drag, on_release=self._on_seek_release)
        self.progress.pack(side="left", fill="x", expand=True)
        self.progress.set_enabled(False)
        self.dur_lbl = tk.Label(prog, text="0:00:00", bg=CARD, fg=FG2, font=F_SMALL, width=7)
        self.dur_lbl.pack(side="left")

        ctl = tk.Frame(pl, bg=CARD)
        ctl.pack(fill="x", padx=px(18), pady=(px(4), px(6)))
        ctl.columnconfigure(0, weight=1, uniform="c")
        ctl.columnconfigure(2, weight=1, uniform="c")
        self.state_big = tk.Label(ctl, text="", bg=CARD, fg=FG2, font=F_SMALL)
        self.state_big.grid(row=0, column=0, sticky="w")
        mid = tk.Frame(ctl, bg=CARD)
        mid.grid(row=0, column=1)
        IconBtn(mid, "prev", self.prev).pack(side="left", padx=4)
        self.btn_play = IconBtn(mid, "play", self.toggle_play, size=56, primary=True, glyph=.3)
        self.btn_play.pack(side="left", padx=8)
        IconBtn(mid, "stop", self.stop, glyph=.28).pack(side="left", padx=4)
        IconBtn(mid, "next", self.next).pack(side="left", padx=4)
        volf = tk.Frame(ctl, bg=CARD)
        volf.grid(row=0, column=2, sticky="e")
        self.mute_btn = IconBtn(volf, "vol", self.toggle_mute, size=34, glyph=.4)
        self.mute_btn.pack(side="left")
        self.vol = Slider(volf, on_change=self._on_vol_drag, on_release=self._on_vol_release,
                          width=110)
        self.vol.pack(side="left")
        self.vol.set(self.vol_value / 100)
        self.vol_lbl = tk.Label(volf, text="15", bg=CARD, fg=FG2, font=F_SMALL, width=3)
        self.vol_lbl.pack(side="left")

        opt = tk.Frame(pl, bg=CARD)
        opt.pack(fill="x", padx=px(18), pady=(px(4), px(14)))
        self.auto_var = Switch(opt, True)
        self.auto_var.pack(side="left")
        self._switch_label(opt, "Avançar na fila", self.auto_var)
        self.sub_var = Switch(opt, True, lambda v: self._subs_toggled())
        self.sub_var.pack(side="left", padx=(px(22), 0))
        self._switch_label(opt, "Legendas", self.sub_var)
        self.has_ffmpeg = bool(find_ffmpeg())
        self.conv_var = Switch(opt, False, self._compat_toggled)
        self.conv_var.pack(side="left", padx=(px(22), 0))
        lb = self._switch_label(opt, "Modo compatibilidade", self.conv_var)
        tip = ("Converte o arquivo para MP4/MP3 antes de enviar. Use só se a TV não "
               "tocar um arquivo (sem imagem, sem som ou erro). Clique em ? para detalhes.")
        Tip(lb, tip)
        helpb = Btn(opt, "?", lambda: show_info(self.root, "Modo compatibilidade", COMPAT_HELP),
                    "ghost", height=26, pad=8)
        helpb.pack(side="left", padx=(px(4), 0))
        Tip(helpb, tip)

    def _switch_label(self, parent, text, sw):
        lb = tk.Label(parent, text=text, bg=CARD, fg=FG, font=F_UI, cursor="hand2")
        lb.pack(side="left", padx=(px(8), 0))
        lb.bind("<Button-1>", lambda e: sw.toggle())
        return lb

    def _compat_toggled(self, on):
        if on and not self.has_ffmpeg:
            self.conv_var.value = False
            self.conv_var._draw()
            show_info(self.root, "Modo compatibilidade",
                      "O conversor (ffmpeg) não está disponível nesta cópia do programa.\n\n"
                      "Use o TV Caster.exe completo, ou instale o ffmpeg e coloque-o no PATH.")
            return
        self.set_status("Modo compatibilidade ligado: toque o item de novo para converter."
                        if on else "Modo compatibilidade desligado.")

    # ---------------- helpers ----------------
    def set_status(self, msg):
        self.status_text = msg
        self.root.after(0, lambda: self.status.config(text=msg))

    def run_bg(self, fn, ok=None, fail=None):
        def worker():
            try:
                res = fn()
            except Exception as e:
                err = str(e)
                self.set_status("Erro: " + err)
                if fail:
                    self.root.after(0, lambda: fail(err))
                return
            if ok:
                self.root.after(0, lambda: ok(res))
        threading.Thread(target=worker, daemon=True).start()

    def need_dev(self):
        if not self.dev:
            self.set_status("Selecione uma TV primeiro.")
            show_info(self.root, "TV Caster", "Selecione uma TV primeiro.")
            return False
        return True

    def snapshot(self):
        """Estado para a página do celular (lido de outra thread)."""
        rs = list(self.renderers)          # cópia: a lista pode ser trocada pela interface
        tv = rs.index(self.dev) if self.dev in rs else -1
        return {
            "tvs": [self.tv_label(i, rs) for i in range(len(rs))], "tv": tv,
            "playlist": [title_of(p) for p in list(self.playlist)],
            "current": self.current, "state": self.state, "loading": self.loading,
            "pos": self.pos, "dur": self.duration, "volume": self.vol_value,
            "muted": self.muted, "now": self.now_text, "status": self.status_text,
            "folders": [os.path.basename(f.rstrip("\\/")) or f for f in self.cfg["folders"]],
            "live": {"on": bool(self.live), "label": self.live_label if self.live else ""},
            "screens": screen_labels(self.screens),
            "subs": self.sub_var.get(), "subdesc": self.sub_text,
            "subopts": self._snap_subopts(),
        }

    def _snap_subopts(self):
        cur = self.current
        if not 0 <= cur < len(self.playlist):
            return []
        p = self.playlist[cur]
        eff = self.sub_effective(p)
        return [{"label": label, "ok": ok, "sel": c == eff} for c, label, ok in self.sub_options(p)]

    # ---------------- TVs ----------------
    def discover(self):
        self.set_status("Procurando TVs na rede…")
        self.tv_btn.set_text("Procurando TVs…")

        def done(found):
            found.sort(key=lambda r: natkey(r.host or ""))   # numeração estável (por IP)
            known = {(r.host, r.name) for r in found}
            for r in self.renderers:          # mantém as adicionadas manualmente
                if (r.host, r.name) not in known:
                    found.append(r)
            self.renderers = found
            if found:
                last = self.cfg.get("last_tv")
                idx = next((i for i, r in enumerate(found) if r.host == last), None)
                if idx is None:
                    idx = next((i for i, r in enumerate(found)
                                if re.search(r"samsung|\blg\b|webos|\[tv\]", r.name.lower())), 0)
                self.select_tv(idx)
                n = len(found)
                if n == 1:
                    self.set_status("1 dispositivo encontrado.")
                else:
                    self.set_status(f"{n} dispositivos encontrados — usando o nº {idx + 1}. "
                                    "Troque pelo botão da TV (canto superior direito).")
            else:
                self._rebuild_tv_menu()
                self.tv_btn.set_text("Nenhuma TV")
                self.set_status("Nenhuma TV encontrada. Confira firewall/Wi-Fi ou use 'IP manual'.")
        self.run_bg(discover, done)

    def tv_label(self, i, rs=None):
        """'1 · nome (ip)' quando há mais de uma TV, para não confundir."""
        rs = self.renderers if rs is None else rs
        return f"{i + 1} · {rs[i]}" if len(rs) > 1 else str(rs[i])

    def _rebuild_tv_menu(self):
        m = self.tv_menu
        m.delete(0, "end")
        for i, r in enumerate(self.renderers):
            mark = "✓  " if r is self.dev else "     "
            m.add_command(label=mark + self.tv_label(i), command=lambda i=i: self.select_tv(i))
        if self.renderers:
            m.add_separator()
        m.add_command(label="Procurar TVs", command=self.discover)
        m.add_command(label="IP manual…", command=self.manual_ip)

    def _open_tv_menu(self):
        b = self.tv_btn
        try:
            self.tv_menu.tk_popup(b.winfo_rootx(), b.winfo_rooty() + b.winfo_height() + 4)
        finally:
            self.tv_menu.grab_release()

    def manual_ip(self):
        def go(ip):
            self.set_status(f"Conectando em {ip}…")

            def done(r):
                self.renderers.append(r)
                self._rebuild_tv_menu()
                self.select_tv(len(self.renderers) - 1)
                self.set_status(f"Conectado: {r}")
            self.run_bg(lambda: connect_ip(ip), done)
        ask_text(self.root, "IP da TV",
                 "IP da TV (Samsung ou LG: Configurações > Rede > Status da rede):", go)

    def select_tv(self, i):
        if not 0 <= i < len(self.renderers):
            return
        self.dev = dev = self.renderers[i]
        self._rebuild_tv_menu()
        name = self.tv_label(i)
        self.tv_btn.set_text(name if len(name) <= 38 else name[:36] + "…")
        self.cfg["last_tv"] = dev.host
        save_config(self.cfg)

        def done(v):
            self._show_volume(v)
        if dev.rc:
            self.run_bg(dev.get_volume, done)

    # ---------------- fila ----------------
    def add_files(self):
        pats = lambda exts: " ".join("*" + e for e in exts)
        paths = filedialog.askopenfilenames(
            title="Escolha vídeos ou músicas",
            filetypes=[("Mídia", pats(VIDEO_EXT + AUDIO_EXT)),
                       ("Vídeo", pats(VIDEO_EXT)), ("Áudio", pats(AUDIO_EXT)),
                       ("Todos os arquivos", "*.*")])
        self._append(paths)

    def add_folder(self):
        folder = filedialog.askdirectory(title="Escolha uma pasta com vídeos ou músicas")
        if folder:
            self._add_folder_path(os.path.normpath(folder), share=True)

    def _add_folder_path(self, folder, share=False):
        self.set_status("Lendo a pasta…")
        if share and folder not in self.cfg["folders"]:
            self.cfg["folders"].append(folder)
            save_config(self.cfg)

        def done(paths):
            if not paths:
                self.set_status("Nenhum vídeo ou música encontrado nessa pasta.")
                show_info(self.root, "TV Caster", "Nenhum vídeo ou música encontrado nessa pasta.")
                return
            self._append(paths)
            self.set_status(f"{len(paths)} arquivo(s) adicionados da pasta.")
        self.run_bg(lambda: scan_media(folder), done)

    def _append(self, paths):
        self.playlist.extend(paths)
        self._refresh_list()

    def remove_sel(self):
        for i in sorted(self.lb.curselection(), reverse=True):
            del self.playlist[i]
            if i < self.current:
                self.current -= 1
            elif i == self.current:
                self.current = -1
        self._refresh_list()

    def clear_list(self):
        self.playlist.clear()
        self.current = -1
        self._refresh_list()

    def move(self, d):
        sel = self.lb.curselection()
        if len(sel) != 1:
            return
        i, j = sel[0], sel[0] + d
        if not 0 <= j < len(self.playlist):
            return
        self.playlist[i], self.playlist[j] = self.playlist[j], self.playlist[i]
        if self.current in (i, j):
            self.current = j if self.current == i else i
        self._refresh_list()
        self.lb.selection_set(j)

    def _refresh_list(self):
        self.lb.delete(0, "end")
        for n, p in enumerate(self.playlist, 1):
            self.lb.insert("end", f"{n:>3}    {title_of(p)}")
        for k in range(len(self.playlist)):
            if k == self.current:
                self.lb.itemconfig(k, foreground=ACC)
        n = len(self.playlist)
        self.count_lbl.config(text=f"{n} item" if n == 1 else f"{n} itens" if n
                              else "Arraste vídeos ou músicas para cá")

    def _on_drop(self, paths):
        """Arquivos/pastas soltos na janela: entram na fila e o primeiro arquivo já toca."""
        files, folders = [], []
        for p in paths:
            p = os.path.normpath(p)
            if os.path.isdir(p):
                folders.append(p)
            elif os.path.splitext(p)[1].lower() in MIME:
                files.append(p)
        if not files and not folders:
            self.set_status("Arraste vídeos ou músicas (ou uma pasta com eles).")
            return
        if files:
            first = len(self.playlist)
            self._append(sorted(files, key=natkey))
            if self.dev:
                self.play_index(first)
            else:
                self.set_status("Adicionado à fila. Selecione uma TV para reproduzir.")
        for f in folders:
            self._add_folder_path(f, share=True)

    def _on_double_click(self, _):
        sel = self.lb.curselection()
        if sel:
            self.play_index(sel[0])

    # ---------------- legendas ----------------
    def _mkv(self, path):
        if path not in self.mkv_cache:
            self.mkv_cache[path] = mkv_info(path)
        return self.mkv_cache[path]

    def sub_options(self, path):
        """Opções de legenda do item: [(escolha, texto, habilitada)]."""
        opts = [("auto", "Automática (padrão do arquivo)", True), ("off", "Sem legenda", True)]
        info = self._mkv(path)
        for tr in (info.subs() if info else []):
            ok = tr["codec"] in TEXT_SUB_CODECS
            lang = LANG_NAMES.get((tr["lang"] or "und").lower(), tr["lang"] or "Idioma não informado")
            kind = tr["codec"].replace("S_TEXT/", "").replace("S_", "").lower()
            label = f"Embutida: {lang}" + (f" — {tr['name']}" if tr["name"] else "") + f" ({kind})"
            if not ok:
                label += " — imagem, não suportada"
            opts.append((("emb", tr["number"]), label, ok))
        files = find_subtitles(path)
        extra = [self.sub_custom.get(path)]
        cur = self.sub_choice.get(path)
        if isinstance(cur, tuple) and cur[0] == "ext":
            extra.append(cur[1])           # a escolhida sempre aparece (e marcada) na lista
        for e in extra:
            if e and e not in files:
                files.append(e)
        for p in files:
            opts.append((("ext", p), "Arquivo: " + os.path.basename(p), True))
        return opts

    def sub_effective(self, path):
        """Escolha valendo agora para o item (a chave 'Legendas' desligada vence)."""
        return self.sub_choice.get(path, "auto") if self.sub_var.get() else "off"

    def choose_sub(self, path, choice):
        self.sub_choice[path] = choice
        if choice != "off" and not self.sub_var.get():      # escolher uma legenda liga a chave
            self.sub_var.value = True
            self.sub_var._draw()
        if (0 <= self.current < len(self.playlist) and self.playlist[self.current] == path
                and self._is_active()):
            self.play_index(self.current, start_at=self.pos)
        else:
            self.set_status("Legenda definida para: " + title_of(path))

    def _open_sub_menu(self):
        sel = self.lb.curselection()
        i = self.current if self.current >= 0 else (sel[0] if sel else -1)
        if not 0 <= i < len(self.playlist):
            show_info(self.root, "Legenda", "Selecione um item da fila primeiro.")
            return
        path = self.playlist[i]
        m = tk.Menu(self.root, tearoff=0, bg=CARD, fg=FG, activebackground=ACC,
                    activeforeground="#ffffff", disabledforeground=FG2, bd=0,
                    relief="flat", font=F_UI)
        eff = self.sub_effective(path)
        for choice, label, ok in self.sub_options(path):
            mark = "✓  " if choice == eff else "     "
            m.add_command(label=mark + label, state="normal" if ok else "disabled",
                          command=lambda c=choice: self.choose_sub(path, c))
            if choice == "off":
                m.add_separator()
        m.add_separator()
        m.add_command(label="     Escolher arquivo de legenda…",
                      command=lambda: self._pick_sub_file(path))
        b = self.sub_btn
        try:
            m.tk_popup(b.winfo_rootx(), b.winfo_rooty() + b.winfo_height() + 4)
        finally:
            m.grab_release()

    def _pick_sub_file(self, path):
        f = filedialog.askopenfilename(
            title="Escolha a legenda",
            filetypes=[("Legendas", " ".join("*" + e for e in SUB_EXT)), ("Todos", "*.*")])
        if f:
            self.sub_custom[path] = f
            self.choose_sub(path, ("ext", f))

    def _set_sub_text(self, txt):
        self.sub_text = txt
        self.sub_lbl.config(text=txt)

    def _ext_srt(self, file):
        key = ("ext", file, os.path.getmtime(file))
        if key not in self.sub_cache:
            self.sub_cache[key] = subtitle_to_srt(file, self.tmpdir)
        return self.sub_cache[key]

    def _emb_srt(self, path, info, tr):
        """SRT de uma legenda embutida; guarda em disco (extrair 4 GB leva alguns segundos)."""
        st = os.stat(path)
        key = hashlib.sha1(f"{path}|{st.st_size}|{st.st_mtime}|{tr['number']}".encode()).hexdigest()[:20]
        if key in self.sub_cache:
            return self.sub_cache[key]
        cdir = os.path.join(_config_dir(), "subcache")
        cached = os.path.join(cdir, key + ".srt")
        if not (os.path.isfile(cached) and os.path.getsize(cached) > 0):
            self.set_status("Extraindo a legenda embutida do arquivo…")
            last = [0]

            def prog(f):
                if f - last[0] >= 0.1:
                    last[0] = f
                    self.set_status(f"Extraindo a legenda embutida do arquivo… {int(f * 100)}%")
            tmp = mkv_extract_subtitle(path, info, tr, self.tmpdir, prog)
            try:
                os.makedirs(cdir, exist_ok=True)
                shutil.copyfile(tmp, cached)
            except OSError:
                cached = tmp
        self.sub_cache[key] = cached
        return cached

    def resolve_subs(self, path, choice, warn):
        """-> (srt ou None, tirar_legendas_embutidas, descrição). Roda fora da thread da interface."""
        info = self._mkv(path)
        has_emb = bool(info and info.subs())
        if choice == "off":
            return None, has_emb, "Sem legenda"
        try:
            if choice == "auto":
                cands = find_subtitles(path)
                if not cands:
                    return None, False, ("Legenda embutida (padrão do arquivo)" if has_emb else "")
                return self._ext_srt(cands[0]), has_emb, "Legenda: " + os.path.basename(cands[0])
            kind, val = choice
            if kind == "ext":
                return self._ext_srt(val), has_emb, "Legenda: " + os.path.basename(val)
            tr = next(t for t in info.subs() if t["number"] == val)
            lang = LANG_NAMES.get((tr["lang"] or "und").lower(), tr["lang"] or "idioma não informado")
            return self._emb_srt(path, info, tr), True, f"Legenda embutida: {lang}"
        except Exception as e:
            warn.append(f"Legenda não aplicada: {e}")
            return None, False, ""

    def _is_active(self):
        """Há algo carregado/tocando na TV agora?"""
        return self.current >= 0 and (
            self.loading or self.state in ("PLAYING", "PAUSED_PLAYBACK", "TRANSITIONING"))

    def _subs_toggled(self):
        if self.dev and self._is_active():     # recarrega o item mantendo a posição
            self.play_index(self.current, start_at=self.pos)

    def _send_to_tv(self, dev, title, url, meta, src, mime, warn):
        """Stop + SetAVTransportURI (com plano B de metadados) + Play (com novas tentativas)."""
        try:
            dev.stop()
            time.sleep(0.4)
        except Exception:
            pass
        try:
            dev.set_uri(url, meta)
        except RuntimeError:               # TV rígida (ex.: LG): tenta metadados mais simples
            plain = didl_metadata(title, url, mime, os.path.getsize(src)) if src else ""
            try:
                dev.set_uri(url, plain)
            except RuntimeError:
                dev.set_uri(url, "")
                warn.append("A TV recusou os metadados: tocando sem legenda externa.")
                self.set_status(warn[-1])
        last = None
        for _ in range(5):                 # a Samsung às vezes demora a aceitar o Play
            try:
                dev.play()
                return
            except RuntimeError as e:
                last = e
                time.sleep(0.8)
        raise last

    @staticmethod
    def _confirm_started(dev, timeout=14):
        """True = tocando; False = a TV desistiu (parou/erro); None = sem resposta clara."""
        bad, t0 = 0, time.time()
        while time.time() - t0 < timeout:
            time.sleep(0.8)
            try:
                st = dev.transport_state()
            except RuntimeError:
                continue
            if st == "PLAYING":
                return True
            bad = bad + 1 if st in ("STOPPED", "NO_MEDIA_PRESENT") else 0
            if bad >= 4:
                return False
        return None

    # ---------------- reprodução ----------------
    def play_index(self, i, start_at=0):
        if not self.need_dev() or not 0 <= i < len(self.playlist):
            return
        self.live_stop(quiet=True)
        self.current = i
        self._refresh_list()
        self.load_gen += 1
        gen = self.load_gen
        self.loading = True
        self.expect_end = False
        self.was_playing = False
        self.user_stopped = False
        self.seek_target = None
        self.duration = 0
        self.progress.set_enabled(False)
        self.progress.set(0)
        self.dur_lbl.config(text="0:00:00")
        self.sub_name = ""
        path, dev, convert = self.playlist[i], self.dev, self.conv_var.get()
        choice = self.sub_effective(path)
        is_audio = MIME.get(os.path.splitext(path)[1].lower(), "").startswith("audio")
        title = title_of(path)
        self.now_text = f"Carregando: {title}"
        self.now.config(text=self.now_text)
        self._set_sub_text("")
        self.set_status("Enviando para a TV…")
        warn = []                          # avisos que devem sobreviver ao "Reproduzindo…"

        def work():
            mime = MIME.get(os.path.splitext(path)[1].lower(), "video/mp4")
            src = path
            if convert:
                if path not in self.converted:
                    self.set_status("Convertendo para compatibilidade… 0%")
                    try:
                        self.converted[path] = convert_media(
                            path, is_audio, self.tmpdir,
                            lambda f: self.set_status(f"Convertendo para compatibilidade… {int(f * 100)}%"),
                            lambda: gen != self.load_gen)
                    except ConversionCancelled:
                        return
                src = self.converted[path]
                mime = "audio/mpeg" if is_audio else "video/mp4"
            ip = local_ip_for(dev.host)
            sub_url = None
            if not is_audio:
                srt, strip, self.sub_name = self.resolve_subs(path, choice, warn)
                if srt:
                    sub_url = self.server.publish(srt, "text/srt;charset=utf-8", ip)
                if strip and src == path:  # manda à TV uma cópia sem as legendas embutidas
                    if path not in self.stripped:
                        self.set_status("Preparando o arquivo sem legendas embutidas… 0%")
                        try:
                            self.stripped[path] = mkv_without_subs(
                                path, self.tmpdir,
                                lambda f: self.set_status(
                                    f"Preparando o arquivo sem legendas embutidas… {int(f * 100)}%"),
                                lambda: gen != self.load_gen)
                        except ConversionCancelled:
                            return
                        except Exception as e:
                            warn.append(f"Não deu para tirar as legendas embutidas ({e}); "
                                        "tocando o original.")
                            self.set_status(warn[-1])
                    src = self.stripped.get(path, path)

            u = self.server.publish(src, mime, ip, {"CaptionInfo.sec": sub_url} if sub_url else None)
            url, meta = u, didl_metadata(title, u, mime, os.path.getsize(src), sub_url)
            with self.tv_lock:             # um envio por vez; só o último clique vale
                if gen != self.load_gen:
                    return
                self._send_to_tv(dev, title, url, meta, src, mime, warn)
                if start_at > 5:           # retoma de onde estava (troca de legenda)
                    for _ in range(12):
                        time.sleep(0.7)
                        try:
                            if dev.transport_state() == "PLAYING":
                                dev.seek(start_at)
                                break
                        except RuntimeError:
                            pass

        def done(_):
            if gen != self.load_gen:
                return
            self.loading = False
            self.expect_end = True
            self.now_text = f"▶ {title}"
            self.now.config(text=self.now_text)
            if not is_audio:
                self._set_sub_text(self.sub_name or ("Sem legenda encontrada" if choice == "auto" else ""))
            self.set_status(warn[0] if warn else "Reproduzindo na TV.")

        def fail(_):
            if gen == self.load_gen:
                self.loading = False
                self.now_text = f"Falhou: {title}"
                self.now.config(text=self.now_text)
        self.run_bg(work, done, fail)

    def toggle_play(self):
        if self.live:
            self.live_stop()
            return
        if self.state == "PLAYING":
            self.pause()
        else:
            self.play()

    def play(self):
        if not self.need_dev():
            return
        if self.current < 0:
            sel = self.lb.curselection()
            if sel or self.playlist:
                self.play_index(sel[0] if sel else 0)
            return
        if self.state in ("STOPPED", "NO_MEDIA_PRESENT", ""):
            self.play_index(self.current)
            return
        self.user_stopped = False
        self.run_bg(self.dev.play)

    def pause(self):
        if self.need_dev():
            self.run_bg(self.dev.pause)

    def stop(self):
        if self.live:
            self.live_stop()
            return
        if not self.need_dev():
            return
        self.user_stopped = True
        self.expect_end = False
        self.run_bg(self.dev.stop)
        self.now_text = "Parado"
        self.now.config(text=self.now_text)

    def next(self):
        if self.current + 1 < len(self.playlist):
            self.play_index(self.current + 1)

    def prev(self):
        if self.current > 0:
            self.play_index(self.current - 1)

    # ---- avançar / voltar ----
    def _on_seek_drag(self, frac):
        self.pos_lbl.config(text=sec_to_hms(frac * self.duration))

    def _on_seek_release(self, frac):
        self.seek_to(frac * self.duration)

    def seek_to(self, sec):
        if not self.dev or not self.duration:
            self.set_status("A TV ainda não informou a duração do vídeo.")
            return
        sec = max(0, min(sec, self.duration - 1))
        self.seek_target = sec
        self.seek_until = time.time() + 8
        self.pos = sec
        self.pos_lbl.config(text=sec_to_hms(sec))
        self.progress.set(sec / self.duration)
        dev = self.dev
        self.set_status(f"Indo para {sec_to_hms(sec)}…")

        def fail(_):
            self.seek_target = None
        self.run_bg(lambda: dev.seek(sec),
                    lambda _: self.set_status(f"Posição: {sec_to_hms(sec)}"), fail)

    # ---- volume ----
    def _show_volume(self, v):
        self.vol_value = int(v)
        self.vol.set(v / 100)
        self.vol_lbl.config(text=str(int(v)))

    def _on_vol_drag(self, frac):
        self.vol_lbl.config(text=str(int(frac * 100)))

    def _on_vol_release(self, frac):
        self.set_volume(int(frac * 100))

    def set_volume(self, v):
        v = max(0, min(100, int(v)))
        self._show_volume(v)
        if self.dev and self.dev.rc:
            dev = self.dev
            self.run_bg(lambda: dev.set_volume(v))

    def toggle_mute(self):
        if not self.need_dev() or not self.dev.rc:
            return
        self.muted = not self.muted
        m = self.muted
        dev = self.dev
        self.run_bg(lambda: dev.set_mute(m))
        self.mute_btn.set_icon("mute" if m else "vol")

    # ---------------- transmissão ao vivo ----------------
    ENC_NAMES = {"h264_nvenc": "placa de vídeo NVIDIA (NVENC)", "h264_amf": "placa de vídeo AMD",
                 "h264_qsv": "Intel Quick Sync", "libx264": "processador (usa mais CPU)"}

    def live_start(self, mode, title="", quality="normal", with_audio=True, screen=0):
        """Começa a transmitir tela / janela / som do PC para a TV (thread da interface)."""
        if not self.need_dev():
            return
        ff = find_ffmpeg()
        if not ff:
            show_info(self.root, "Transmitir", "O conversor/captura (ffmpeg) não está disponível "
                                               "nesta cópia do programa.")
            return
        self.live_stop(quiet=True)                   # uma transmissão por vez
        self.load_gen += 1
        gen = self.load_gen
        self.loading = True
        self.expect_end = False
        self.was_playing = False
        self.user_stopped = False
        self.seek_target = None
        self.duration = 0
        self.live_seen = False
        self.progress.set_enabled(False)
        self.progress.set(0)
        self.dur_lbl.config(text="ao vivo")
        if not 0 <= screen < max(1, len(self.screens)):
            screen = 0
        label = {"screen": f"Tela {screen + 1}" if len(self.screens) > 1 else "Tela",
                 "audio": "Som do PC"}.get(mode, title)
        self.live_label = label
        self.now_text = f"Iniciando a transmissão: {label}"
        self.now.config(text=self.now_text)
        self._set_sub_text("")
        self.set_status("Iniciando a captura…")
        dev, live, warn = self.dev, LiveStream(ff, self.tmpdir), []
        self.live = live

        def work():
            prev = getattr(self, "_live_stop_thread", None)
            if prev is not None:
                prev.join(15)                      # a captura anterior precisa ter fechado
            live.start(mode, title, quality, with_audio, screen)
            if live.warning:
                warn.append(live.warning)
            ip = local_ip_for(dev.host)
            url = f"http://{ip}:{self.server.port}{live.path()}"
            self.server.live = live
            meta = didl_live(f"TV Caster · {label}", url, live.audio_only)
            with self.tv_lock:
                if gen != self.load_gen or self.live is not live:
                    live.stop()
                    return
                self._send_to_tv(dev, label, url, meta, None, live.mime, warn)
                if self._confirm_started(dev, 20) is False:
                    raise RuntimeError("a TV não aceitou a transmissão")

        def done(_):
            if gen != self.load_gen or self.live is not live:
                return
            self.loading = False
            self.now_text = f"● Transmitindo: {label}"
            self.now.config(text=self.now_text)
            self._set_sub_text("Ao vivo — a imagem chega à TV com alguns segundos de atraso")
            self.set_status(warn[0] if warn else "Transmitindo para a TV.")

        def fail(err):
            if self.live is live:
                self.live_stop(quiet=True)
                if self.dev:
                    self.run_bg(self.dev.stop)
                self.loading = False
                self.now_text = "Falhou a transmissão"
                self.now.config(text=self.now_text)
                show_info(self.root, "Transmitir", err)
        self.run_bg(work, done, fail)

    def live_stop(self, quiet=False):
        live, self.live = self.live, None
        if live is None:
            return False
        if self.server.live is live:
            self.server.live = None
        self._live_stop_thread = threading.Thread(target=live.stop, daemon=True)   # sem travar a tela
        self._live_stop_thread.start()
        self.loading = False
        if not quiet:
            if self.dev:
                dev = self.dev
                self.run_bg(dev.stop)
            self.now_text = "Transmissão encerrada"
            self.now.config(text=self.now_text)
            self._set_sub_text("")
            self.dur_lbl.config(text="0:00:00")
            self.set_status("Transmissão encerrada.")
        return True

    def show_live(self):
        old = getattr(self, "live_dialog", None)
        if old is not None and old.winfo_exists():
            old.lift()
            old.focus_force()
            return
        d = self.live_dialog = make_dialog(self.root, "Transmitir para a TV")
        st = {"mode": "screen", "quality": "normal", "screen": 0}
        pad = px(26)
        tk.Label(d, text="Transmitir para a TV", bg=BG, fg=FG, font=F_NOW).pack(
            padx=pad, pady=(px(22), px(4)), anchor="w")
        tk.Label(d, text="Envia ao vivo o que está no PC. A imagem chega à TV com alguns segundos "
                         "de atraso: ótimo para vídeos, apresentações e música; ruim para jogos de "
                         "ação (nesses, use o espelhamento do Windows: Win+K).",
                 bg=BG, fg=FG2, font=F_SMALL, wraplength=px(470), justify="left").pack(
            padx=pad, anchor="w")

        def segment(parent, items, key, on_change=None):
            btns = {}

            def pick(v):
                st[key] = v
                for k, b in btns.items():
                    b.style = "accent" if k == v else "default"
                    b._draw()
                if on_change:
                    on_change(v)
            for v, text in items:
                b = Btn(parent, text, lambda v=v: pick(v), "accent" if st[key] == v else "default")
                b.pack(side="left", padx=(0, px(6)))
                btns[v] = b
            return pick

        tk.Label(d, text="O que transmitir", bg=BG, fg=FG, font=F_BOLD).pack(
            padx=pad, pady=(px(16), px(6)), anchor="w")
        r1 = tk.Frame(d, bg=BG)
        r1.pack(padx=pad, anchor="w")

        # blocos que aparecem/somem: ficam direto na janela e entram sempre antes de 'enc'
        wf = tk.Frame(d, bg=BG)
        lb = tk.Listbox(wf, bg=CARD, fg=FG, selectbackground=ACC, selectforeground="#ffffff",
                        bd=0, highlightthickness=0, font=F_UI, height=7, activestyle="none",
                        exportselection=False)
        lb.pack(fill="x", pady=(px(8), px(4)))

        def refresh_windows():
            lb.delete(0, "end")
            for title in list_windows():
                lb.insert("end", title)
        Btn(wf, "Atualizar lista", refresh_windows, "ghost").pack(anchor="w")
        tk.Label(wf, text="Para Spotify e outros apps de música, prefira “Só o som do PC”. Apps com "
                          "vídeo acelerado por GPU (Spotify, navegadores) são capturados pela área "
                          "da janela: não a mova.", bg=BG, fg=FG2, font=F_SMALL, wraplength=px(470),
                 justify="left").pack(anchor="w", pady=(px(4), 0))
        srow = tk.Frame(d, bg=BG)             # qual tela (só aparece com 2 ou mais)
        tk.Label(srow, text="Qual tela", bg=BG, fg=FG, font=F_BOLD).pack(anchor="w", pady=(px(16), px(6)))
        sb = tk.Frame(srow, bg=BG)
        sb.pack(anchor="w")
        screens_done = {"n": -1}

        def fill_screens():
            if screens_done["n"] == len(self.screens):
                return
            screens_done["n"] = len(self.screens)
            for w in sb.winfo_children():
                w.destroy()
            if len(self.screens) > 1:
                segment(sb, list(enumerate(screen_labels(self.screens))), "screen")
            on_mode(st["mode"])
        qrow = tk.Frame(d, bg=BG)
        tk.Label(qrow, text="Qualidade", bg=BG, fg=FG, font=F_BOLD).pack(anchor="w", pady=(px(16), px(6)))
        qb = tk.Frame(qrow, bg=BG)
        qb.pack(anchor="w")
        segment(qb, [(k, v[0]) for k, v in LIVE_QUALITY.items()], "quality")
        arow = tk.Frame(d, bg=BG)
        audio_sw = Switch(arow, True)
        audio_sw.pack(side="left", pady=(px(14), 0))
        al = tk.Label(arow, text="Incluir o som do PC (continua saindo no PC também)", bg=BG, fg=FG,
                      font=F_UI, cursor="hand2")
        al.pack(side="left", padx=(px(8), 0), pady=(px(14), 0))
        al.bind("<Button-1>", lambda e: audio_sw.toggle())
        enc = tk.Label(d, text="", bg=BG, fg=FG2, font=F_SMALL, anchor="w")
        enc.pack(fill="x", padx=pad, pady=(px(14), 0))
        msg = tk.Label(d, text="", bg=BG, fg=FG, font=F_UI, anchor="w", wraplength=px(470),
                       justify="left")
        msg.pack(fill="x", padx=pad, pady=(px(6), 0))

        def on_mode(v):
            for w in (wf, srow, qrow, arow):
                w.pack_forget()
            if v == "window":
                refresh_windows()
                wf.pack(fill="x", padx=pad, before=enc)
            if v == "screen" and len(self.screens) > 1:
                srow.pack(anchor="w", padx=pad, before=enc)
            if v != "audio":
                qrow.pack(anchor="w", padx=pad, before=enc)
                arow.pack(anchor="w", padx=pad, before=enc)
        pick_mode = segment(r1, [("screen", "Tela"), ("window", "Uma janela"),
                                 ("audio", "Só o som do PC")], "mode", on_mode)
        pick_mode("screen")

        ff = find_ffmpeg()
        if ff:
            self.run_bg(lambda: detect_encoder(ff),
                        lambda e: enc.config(text="Codificação: " + self.ENC_NAMES.get(e, e)))

        def go_click():
            title = ""
            if st["mode"] == "window":
                sel = lb.curselection()
                if not sel:
                    msg.config(text="Escolha uma janela da lista.")
                    return
                title = lb.get(sel[0])
            # com uma transmissão ativa, isto TROCA: a anterior é encerrada e a nova começa
            self.live_start(st["mode"], title, st["quality"], audio_sw.get(), st["screen"])
        row = tk.Frame(d, bg=BG)
        row.pack(pady=px(16))
        go = Btn(row, "Iniciar transmissão", go_click, "accent")
        go.pack(side="left", padx=4)
        stop_btn = Btn(row, "Parar", lambda: self.live_stop())
        close_btn = Btn(row, "Fechar", d.destroy)
        close_btn.pack(side="left", padx=4)

        def tick():
            if not d.winfo_exists():
                return
            fill_screens()
            live = bool(self.live)
            want = "Trocar para esta seleção" if live else "Iniciar transmissão"
            if go.text != want:
                go.set_text(want)
            if live and not stop_btn.winfo_ismapped():
                stop_btn.pack(side="left", padx=4, before=close_btn)
            elif not live and stop_btn.winfo_ismapped():
                stop_btn.pack_forget()
            if live:
                if self.loading:
                    msg.config(text=self.status_text)
                else:
                    extra = self.status_text if self.status_text not in ("", "Transmitindo para a TV.") else ""
                    msg.config(text="● Transmitindo: " + self.live_label + ("\n" + extra if extra else ""))
            elif msg.cget("text").startswith("●"):
                msg.config(text="")
            d.after(500, tick)
        tick()
        center_on(d, self.root)

    # ---------------- celular ----------------
    def remote_url(self):
        ip = local_ip_for(self.dev.host) if self.dev else local_ip_for()
        return f"http://{ip}:{self.server.port}/r/{self.cfg['remote_key']}/"

    def remote_cmd(self, d):
        """Comandos vindos da página do celular (executa na thread da interface)."""
        c = d.get("cmd")
        if c == "play":
            self.play()
        elif c == "pause":
            self.pause()
        elif c == "stop":
            self.stop()
        elif c == "next":
            self.next()
        elif c == "prev":
            self.prev()
        elif c == "seek":
            self.seek_to(float(d["sec"]))
        elif c == "volume":
            self.set_volume(int(d["v"]))
        elif c == "mute":
            self.toggle_mute()
        elif c == "subs":
            self.sub_var.toggle()
        elif c == "play_index":
            self.play_index(int(d["i"]))
        elif c == "select_tv":
            self.select_tv(int(d["i"]))
        elif c == "remove":
            i = int(d["i"])
            if 0 <= i < len(self.playlist):
                del self.playlist[i]
                if i < self.current:
                    self.current -= 1
                elif i == self.current:
                    self.current = -1
                self._refresh_list()
        elif c == "live_start":
            mode = d.get("mode")
            if mode in ("screen", "audio"):
                self.live_start(mode, screen=int(d.get("screen", 0)))
            elif mode == "window" and d.get("title") in list_windows():
                self.live_start("window", d["title"])
        elif c == "live_stop":
            self.live_stop()
        elif c == "sub_choice":
            if 0 <= self.current < len(self.playlist):
                p = self.playlist[self.current]
                opts = self.sub_options(p)
                i = int(d["i"])
                if 0 <= i < len(opts) and opts[i][2]:
                    self.choose_sub(p, opts[i][0])
        elif c in ("add_file", "add_dir"):
            full = self.remote.resolve(int(d["root"]), d.get("path", ""))
            if c == "add_dir":
                if os.path.isdir(full):
                    self._append(scan_media(full))
            elif os.path.isfile(full) and os.path.splitext(full)[1].lower() in MIME:
                self._append([full])
                if d.get("play"):
                    self.play_index(len(self.playlist) - 1)

    def show_remote(self):
        d = make_dialog(self.root, "Controle pelo celular")
        url = self.remote_url()
        tk.Label(d, text="Controle pelo celular", bg=BG, fg=FG, font=F_NOW).pack(
            padx=px(26), pady=(px(22), px(4)), anchor="w")
        tk.Label(d, text="Com o celular no mesmo Wi-Fi, abra o endereço abaixo no navegador "
                         "(ou aponte a câmera para o QR code).",
                 bg=BG, fg=FG2, font=F_UI, wraplength=px(420), justify="left").pack(
            padx=px(26), anchor="w")

        qr_ok = False
        try:
            import segno
            m = [list(row) for row in segno.make(url, micro=False, error="m").matrix]
            n, cell, quiet = len(m), px(6), 4
            size = (n + 2 * quiet) * cell
            cv = tk.Canvas(d, width=size, height=size, bg="#ffffff", highlightthickness=0, bd=0)
            for y, row in enumerate(m):
                for x, v in enumerate(row):
                    if v:
                        cv.create_rectangle((x + quiet) * cell, (y + quiet) * cell,
                                            (x + quiet + 1) * cell, (y + quiet + 1) * cell,
                                            fill="#000000", outline="")
            cv.pack(pady=px(14))
            qr_ok = True
        except Exception:
            pass
        if not qr_ok:
            tk.Label(d, text="(para ver o QR code: pip install segno)", bg=BG, fg=FG2,
                     font=F_SMALL).pack(pady=(px(10), 0))

        e = tk.Entry(d, bg=CARD, fg=FG, readonlybackground=CARD, relief="flat", font=F_LIST,
                     justify="center", highlightthickness=1, highlightbackground=CARD3)
        e.insert(0, url)
        e.config(state="readonly")
        e.pack(fill="x", padx=px(26), ipady=px(6), pady=(px(6), px(8)))

        def copy():
            self.root.clipboard_clear()
            self.root.clipboard_append(url)
            cp.set_text("Copiado ✓")
        cp = Btn(d, "Copiar endereço", copy, "accent")
        cp.pack()

        tk.Label(d, text="Pastas visíveis no celular (as que você adicionou com “+ Pasta”):",
                 bg=BG, fg=FG2, font=F_SMALL, wraplength=px(420), justify="left").pack(
            padx=px(26), pady=(px(16), px(4)), anchor="w")
        lb = tk.Listbox(d, bg=CARD, fg=FG, selectbackground=CARD2, selectforeground=FG,
                        bd=0, highlightthickness=0, font=F_UI, height=4, activestyle="none")
        for f in self.cfg["folders"]:
            lb.insert("end", f)
        lb.pack(fill="x", padx=px(26))

        def unshare():
            for i in reversed(lb.curselection()):
                del self.cfg["folders"][i]
                lb.delete(i)
            save_config(self.cfg)
        row = tk.Frame(d, bg=BG)
        row.pack(pady=px(14))
        Btn(row, "Parar de compartilhar", unshare).pack(side="left", padx=4)
        Btn(row, "Fechar", d.destroy).pack(side="left", padx=4)
        center_on(d, self.root)

    # ---------------- acompanhamento ----------------
    def _poll_loop(self):
        while self.alive:
            dev = self.dev
            if dev and not self.loading:
                try:
                    state = dev.transport_state()
                    rel, dur = dev.position()
                    if self.alive:
                        self.root.after(0, self._on_poll, state, rel, dur)
                except Exception:
                    pass
            time.sleep(1)

    def _on_poll(self, state, rel, dur):
        if self.live and not self.loading:
            if not self.live.running():            # janela fechada, erro de captura...
                self.live_stop(quiet=True)
                self.now_text = "Transmissão terminou"
                self.now.config(text=self.now_text)
                self.set_status("A captura terminou (a janela foi fechada?).")
            elif state == "PLAYING":
                self.live_seen = True
            elif state in ("STOPPED", "NO_MEDIA_PRESENT") and self.live_seen:
                self.live_stop(quiet=True)         # você parou pelo controle da TV
                self.now_text = "Transmissão encerrada na TV"
                self.now.config(text=self.now_text)
                self.set_status("Transmissão encerrada na TV.")
        self.state = state
        txt = STATE_PT.get(state, state or "")
        self.state_lbl.config(text=txt)
        self.state_big.config(text=txt)
        self.btn_play.set_icon("pause" if state == "PLAYING" else "play")
        if dur:
            self.duration = dur
            self.dur_lbl.config(text=sec_to_hms(dur))
            self.progress.set_enabled(True)

        if self.seek_target is not None:      # mostra o destino até a TV confirmar
            if (time.time() > self.seek_until
                    or self.seek_target - 2 <= rel <= self.seek_target + 15):
                self.seek_target = None
        if self.seek_target is None and not self.progress.dragging:
            self.pos = rel
            self.pos_lbl.config(text=sec_to_hms(rel))
            self.progress.set(rel / self.duration if self.duration else 0)

        if state == "PLAYING":
            self.was_playing = True
        elif (state in ("STOPPED", "NO_MEDIA_PRESENT") and self.expect_end
              and self.was_playing and not self.user_stopped and not self.loading):
            self.expect_end = False
            self.was_playing = False
            if self.auto_var.get() and self.current + 1 < len(self.playlist):
                self.play_index(self.current + 1)
            else:
                self.now_text = "Fim da reprodução"
                self.now.config(text=self.now_text)

    def on_close(self):
        self.alive = False
        if self.live:
            self.live.stop()
        self.server.shutdown()
        shutil.rmtree(self.tmpdir, ignore_errors=True)
        self.root.destroy()


def init_theme(root):
    global SCALE, F_UI, F_SMALL, F_BOLD, F_TITLE, F_NOW, F_LIST
    SCALE = root.winfo_fpixels("1i") / 96.0
    fam = "Segoe UI Variable Text" if "Segoe UI Variable Text" in tkfont.families(root) else "Segoe UI"
    F_UI = tkfont.Font(root=root, family=fam, size=10)
    F_SMALL = tkfont.Font(root=root, family=fam, size=9)
    F_BOLD = tkfont.Font(root=root, family=fam, size=11, weight="bold")
    F_TITLE = tkfont.Font(root=root, family=fam, size=20, weight="bold")
    F_NOW = tkfont.Font(root=root, family=fam, size=13, weight="bold")
    F_LIST = tkfont.Font(root=root, family=fam, size=11)
    st = ttk.Style(root)
    try:
        st.theme_use("clam")
    except tk.TclError:
        pass
    st.layout("Dark.Vertical.TScrollbar",
              [("Vertical.Scrollbar.trough", {"sticky": "ns", "children": [
                  ("Vertical.Scrollbar.thumb", {"expand": "1", "sticky": "nswe"})]})])
    st.configure("Dark.Vertical.TScrollbar", troughcolor=CARD, background=CARD3,
                 bordercolor=CARD, lightcolor=CARD3, darkcolor=CARD3, gripcount=0, width=px(10))
    st.map("Dark.Vertical.TScrollbar", background=[("active", "#636366")])


def hide_own_console():
    """Esconde o prompt preto se ele foi aberto só para este programa
    (duplo clique no .py). Se rodou de um terminal, não mexe nele."""
    try:
        import ctypes
        k32 = ctypes.windll.kernel32
        hwnd = k32.GetConsoleWindow()
        if hwnd and k32.GetConsoleProcessList((ctypes.c_uint * 4)(), 4) <= 1:
            ctypes.windll.user32.ShowWindow(hwnd, 0)
    except Exception:
        pass


def set_app_icon(root):
    """Ícone no canto da janela (pequeno) e na barra de tarefas (grande)."""
    ico = resource_path("play-button.ico")
    if not os.path.isfile(ico):
        return
    try:
        root.iconbitmap(default=ico)       # também vale para as janelas de diálogo
    except tk.TclError:
        pass
    if os.name != "nt":
        return
    try:
        import ctypes
        from ctypes import c_void_p, c_uint, c_int, c_wchar_p
        u32 = ctypes.windll.user32
        u32.GetParent.restype, u32.GetParent.argtypes = c_void_p, [c_void_p]
        u32.LoadImageW.restype = c_void_p
        u32.LoadImageW.argtypes = [c_void_p, c_wchar_p, c_uint, c_int, c_int, c_uint]
        u32.SendMessageW.restype = c_void_p
        u32.SendMessageW.argtypes = [c_void_p, c_uint, c_void_p, c_void_p]
        root.update_idletasks()
        hwnd = u32.GetParent(root.winfo_id())
        for which, metric in ((1, 11), (0, 49)):   # ICON_BIG/SM_CXICON, ICON_SMALL/SM_CXSMICON
            size = u32.GetSystemMetrics(metric)
            h = u32.LoadImageW(None, ico, 1, size, size, 0x10)   # IMAGE_ICON, LR_LOADFROMFILE
            if h:
                u32.SendMessageW(hwnd, 0x80, which, h)           # WM_SETICON
    except Exception:
        pass


def enable_file_drop(root, on_drop):
    """Aceita arquivos e pastas arrastados do Explorer para a janela (WM_DROPFILES,
    sem biblioteca extra). on_drop(lista de caminhos) roda na thread da interface.
    Devolve True se ativou."""
    if os.name != "nt":
        return False
    try:
        import ctypes
        from ctypes import wintypes
        u32, s32 = ctypes.windll.user32, ctypes.windll.shell32
        WM_DROPFILES, WM_COPYGLOBALDATA, GWL_WNDPROC = 0x233, 0x49, -4
        LRESULT = ctypes.c_ssize_t
        WNDPROC = ctypes.WINFUNCTYPE(LRESULT, wintypes.HWND, wintypes.UINT,
                                     wintypes.WPARAM, wintypes.LPARAM)
        u32.GetParent.restype, u32.GetParent.argtypes = ctypes.c_void_p, [ctypes.c_void_p]
        set_proc = getattr(u32, "SetWindowLongPtrW", None) or u32.SetWindowLongW
        set_proc.restype = ctypes.c_void_p
        set_proc.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p]
        u32.CallWindowProcW.restype = LRESULT
        u32.CallWindowProcW.argtypes = [ctypes.c_void_p, wintypes.HWND, wintypes.UINT,
                                        wintypes.WPARAM, wintypes.LPARAM]
        s32.DragQueryFileW.restype = wintypes.UINT
        s32.DragQueryFileW.argtypes = [ctypes.c_void_p, wintypes.UINT, wintypes.LPWSTR, wintypes.UINT]
        s32.DragFinish.argtypes = [ctypes.c_void_p]
        s32.DragAcceptFiles.argtypes = [ctypes.c_void_p, wintypes.BOOL]

        root.update_idletasks()
        top = u32.GetParent(root.winfo_id()) or root.winfo_id()

        def dropped(hdrop):
            out = []
            for i in range(s32.DragQueryFileW(hdrop, 0xFFFFFFFF, None, 0)):
                n = s32.DragQueryFileW(hdrop, i, None, 0)
                buf = ctypes.create_unicode_buffer(n + 1)
                s32.DragQueryFileW(hdrop, i, buf, n + 1)
                out.append(buf.value)
            return out

        old = None
        pending = queue.Queue()

        def proc(hwnd, msg, wp, lp):
            # Aqui dentro NÃO se pode chamar o tkinter (derruba o interpretador):
            # só guarda os caminhos; quem trata é o pump(), no laço normal do Tk.
            if msg == WM_DROPFILES:
                try:
                    paths = dropped(wp)
                except Exception:
                    paths = []
                finally:
                    s32.DragFinish(wp)
                if paths:
                    pending.put(paths)
                return 0
            return u32.CallWindowProcW(old, hwnd, msg, wp, lp)

        def pump():
            try:
                while True:
                    on_drop(pending.get_nowait())
            except queue.Empty:
                pass
            try:
                root.after(150, pump)
            except tk.TclError:
                pass                    # janela fechada

        cb = WNDPROC(proc)
        old = set_proc(top, GWL_WNDPROC, ctypes.cast(cb, ctypes.c_void_p).value)
        if not old:
            return False
        root._drop_proc = cb            # a referência precisa viver tanto quanto a janela
        pump()
        s32.DragAcceptFiles(top, True)
        try:                            # permite arrastar mesmo se o programa rodar como administrador
            flt = u32.ChangeWindowMessageFilterEx
            flt.argtypes = [ctypes.c_void_p, wintypes.UINT, wintypes.DWORD, ctypes.c_void_p]
            for m in (WM_DROPFILES, WM_COPYGLOBALDATA):
                flt(top, m, 1, None)    # MSGFLT_ALLOW
        except Exception:
            pass
        return True
    except Exception:
        return False


def selftest():
    """'TV Caster.exe --selftest': confere o ffmpeg embutido e grava o resultado em %TEMP%."""
    ff, line = find_ffmpeg(), ""
    if ff:
        try:
            flags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
            p = subprocess.run([ff, "-hide_banner", "-version"], capture_output=True,
                               creationflags=flags, timeout=30)
            line = p.stdout.decode("utf-8", "ignore").splitlines()[0]
        except (OSError, subprocess.TimeoutExpired, IndexError):
            line = "falhou ao executar"
    with open(os.path.join(tempfile.gettempdir(), "tvcaster_selftest.txt"), "w",
              encoding="utf-8") as f:
        f.write(f"ffmpeg={ff}\n{line}\nicone={os.path.isfile(resource_path('play-button.ico'))}\n")


def main():
    if "--selftest" in sys.argv:
        selftest()
        return
    if os.name == "nt":
        hide_own_console()
    try:  # texto nítido em telas com escala no Windows
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    try:  # identidade própria na barra de tarefas (senão agrupa como "Python")
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("Gian.TVCaster")
    except Exception:
        pass
    root = tk.Tk()
    init_theme(root)
    set_app_icon(root)
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
