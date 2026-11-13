"""Testes da seleção de faixa de áudio de MKV (TV Caster). Sem janelas: não cria tk.Tk.

Uso: py -3.8 testes\\teste_mkv_audio.py
Grava um registro em testes\\logs\\execucoes.jsonl.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
TV = os.path.dirname(HERE)
sys.path.insert(0, TV)
import tv_caster as tc  # noqa: E402  (import não abre janela: o App só é criado em __main__)

SCR = r"C:\Users\Gian\AppData\Local\Temp\claude\f--Backups-Pythonprojeto-Tv\84e4f518-1223-4cb0-85a2-16d5ab239516\scratchpad"
HEAD = os.path.join(SCR, "head", "coyote_head.mkv")
OUT = os.path.join(SCR, "saida_mkv_audio")
os.makedirs(OUT, exist_ok=True)
FF = tc.find_ffmpeg()

OK = 0
FAIL = []
T0 = time.time()


def chk(cond, desc):
    global OK
    if cond:
        OK += 1
        print("  ok     " + desc)
    else:
        FAIL.append(desc)
        print("  FALHA  " + desc)


def bloco(nome, fn):
    """Roda um bloco; exceção vira falha (teste que não terminou não é 'passou')."""
    print(">>> " + nome)
    try:
        fn()
    except Exception as e:  # noqa: BLE001
        FAIL.append(f"{nome}: exceção {type(e).__name__}: {e}")
        print("  FALHA  exceção: " + repr(e))


def ff_info(p):
    r = subprocess.run([FF, "-hide_banner", "-i", p], stdout=subprocess.DEVNULL,
                       stderr=subprocess.PIPE, timeout=300)
    t = r.stderr.decode("utf-8", "ignore")
    return (re.findall(r"Stream #\S+: Audio:[^\r\n]*", t),
            re.findall(r"Stream #\S+: Subtitle:[^\r\n]*", t))


def avisos_demux(p):
    """Lê todos os pacotes sem decodificar (-c copy) e devolve o stderr do ffmpeg."""
    r = subprocess.run([FF, "-v", "warning", "-hide_banner", "-i", p, "-c", "copy", "-f", "null", "-"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=900)
    return r.stderr.decode("utf-8", "ignore")


def volume_medio(p, idx=None):
    cmd = [FF, "-hide_banner", "-i", p, "-map", f"0:a:{idx or 0}", "-ac", "2",
           "-af", "volumedetect", "-vn", "-f", "null", "-"]
    r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=600)
    m = re.search(r"mean_volume:\s*(-?[\d.]+) dB", r.stderr.decode("utf-8", "ignore"))
    return float(m.group(1)) if m else None


def bloco_js():
    html = tc.REMOTE_HTML
    scripts = re.findall(r"<script[^>]*>(.*?)</script>", html, re.S)
    chk(len(scripts) >= 1, f"página do celular tem <script> (achados: {len(scripts)})")
    for i, js in enumerate(scripts):
        arq = os.path.join(SCR, f"remote_script_{i}.js")
        with open(arq, "w", encoding="utf-8") as f:
            f.write(js)
        r = subprocess.run(["node", "--check", arq], capture_output=True, text=True, timeout=60)
        chk(r.returncode == 0, f"node --check do <script> {i} da página do celular"
            + ("" if r.returncode == 0 else ": " + r.stderr.strip()[:300]))


def bloco_logica():
    info = tc.mkv_info(HEAD)
    chk(info is not None, "mkv_info lê o cabeçalho do arquivo de teste")
    aud = info.audios() if info else []
    chk(len(aud) == 2, f"mkv_info acha 2 faixas de áudio (achou {len(aud)})")
    for t in aud:
        print(f"         faixa nº{t['number']}: lang={t['lang']!r} codec={t['codec']} "
              f"canais={t['channels']} default={t['default']} nome={t['name']!r}")
    if len(aud) == 2:
        chk(aud[0]["lang"] == "por" and aud[0]["channels"] == 2 and aud[0]["default"],
            "faixa 1 = por, 2.0, padrão")
        chk(aud[1]["channels"] == 6 and not aud[1]["lang"], "faixa 2 = 6 canais, sem idioma")

    # Métodos do App, sem criar a janela (object.__new__ não roda __init__ do Tk).
    app_cls = next(v for v in vars(tc).values() if isinstance(v, type) and hasattr(v, "audio_options"))
    obj = object.__new__(app_cls)
    obj.audio_choice = {}
    obj._mkv = lambda p: tc.mkv_info(p)
    opts = obj.audio_options(HEAD)
    for n, txt in opts:
        print(f"         opção nº{n}: {txt}")
    chk(len(opts) == 2, "audio_options devolve 2 opções")
    if len(opts) == 2:
        chk("Português" in opts[0][1] or "por" in opts[0][1].lower(), "rótulo da faixa por está em português")
        chk("Inglês" in opts[1][1], "faixa sem idioma cai em Inglês")
        chk("(padrão)" in opts[0][1] and "(padrão)" not in opts[1][1], "só a faixa por é marcada (padrão)")
    chk(obj.audio_default(HEAD) == (aud[0]["number"] if aud else None), "audio_default = faixa marcada como padrão")
    obj.audio_choice[HEAD] = aud[1]["number"]
    chk(obj.audio_index(HEAD) == 1, "audio_index da faixa escolhida (2ª) = 1")
    obj.audio_choice[HEAD] = 9999
    chk(obj.audio_effective(HEAD) == obj.audio_default(HEAD), "escolha inválida cai na faixa padrão")
    chk(obj.audio_index(HEAD) is None, "sem escolha válida, audio_index = None")


def bloco_remux():
    t = time.time()
    r1 = tc.mkv_remux(HEAD, OUT, audio=1, keep_subs=False)
    a, s = ff_info(r1)
    print(f"         (a) {len(a)} áudio(s), {len(s)} legenda(s) em {time.time() - t:.0f}s")
    chk(len(a) == 1 and re.search(r"6 channels|5\.1", a[0]) is not None,
        "(b) audio=1 sem legendas: 1 áudio, é a 5.1 (6 canais)")
    chk(len(s) == 0, "(b) audio=1 sem legendas: 0 legendas")

    r2 = tc.mkv_remux(HEAD, OUT, audio=1, keep_subs=True)
    a2, s2 = ff_info(r2)
    chk(len(a2) == 1 and re.search(r"6 channels|5\.1", a2[0]) is not None,
        "(c) audio=1 keep_subs=True: 1 áudio, 5.1")
    chk(len(s2) == 3, f"(c) audio=1 keep_subs=True mantém 3 legendas (achou {len(s2)})")

    r3 = tc.mkv_remux(HEAD, OUT, audio=None, keep_subs=False)
    a3, s3 = ff_info(r3)
    chk(len(a3) == 2, f"(d) audio=None sem legendas mantém as 2 áudios (achou {len(a3)})")
    chk(len(s3) == 0, "(d) audio=None sem legendas: 0 legendas")

    for nome, r in (("audio=1", r1), ("audio=1+legendas", r2), ("audio=None", r3)):
        w = avisos_demux(r)
        chk("Invalid track number" not in w,
            f"(e) {nome}: sem 'Invalid track number' ao ler os pacotes"
            + ("" if "Invalid track number" not in w else " — " + w.strip()[:200]))


def bloco_convert():
    clip = os.path.join(OUT, "clip20.mkv")
    subprocess.run([FF, "-hide_banner", "-y", "-t", "20", "-i", HEAD, "-map", "0", "-c", "copy", clip],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=600, check=True)
    v0, v1 = volume_medio(clip, 0), volume_medio(clip, 1)
    print(f"         volume médio fonte: faixa a:0={v0} dB, a:1={v1} dB")
    if v0 is None or v1 is None or abs(v0 - v1) < 1.0:
        print("         (faixas com volume parecido: teste de identidade pelo volume fica inconclusivo)")
    res = {}
    for idx in (0, 1):
        t = time.time()
        out = tc.convert_media(clip, False, OUT, audio=idx)
        a, _ = ff_info(out)
        vo = volume_medio(out)
        res[idx] = (out, a, vo)
        print(f"         convert audio={idx}: {len(a)} áudio(s) em {time.time() - t:.0f}s, volume {vo} dB")
        chk(len(a) == 1, f"(f) convert_media audio={idx} gera 1 faixa de áudio")
    # Identidade da faixa pelo idioma: o ffmpeg copia o idioma da faixa de origem para a saida.
    # (O volume medio nao serve: o downmix 5.1->estereo mede diferente na fonte e na saida.)
    for idx, esperado in ((0, "por"), (1, "eng")):
        a_out = res[idx][1]
        m = re.search(r"\((\w+)\)", a_out[0]) if a_out else None
        lang = m.group(1) if m else None
        chk(lang == esperado, f"(f) convert_media audio={idx} usa a faixa de idioma {esperado} (saida: {lang})")


def gravar_log(tempo):
    fonte = open(os.path.join(TV, "tv_caster.py"), "rb").read()
    reg = {
        "quando": time.strftime("%Y-%m-%d %H:%M:%S"),
        "arquivo": "tv_caster.py",
        "versao": hashlib.sha1(fonte).hexdigest()[:10],
        "motivo": "seleção de faixa de áudio MKV (parser, remux, convert, página do celular)",
        "ok": OK,
        "falhas": FAIL,
        "tempo_s": round(tempo, 1),
    }
    pasta = os.path.join(HERE, "logs")
    os.makedirs(pasta, exist_ok=True)
    with open(os.path.join(pasta, "execucoes.jsonl"), "a", encoding="utf-8") as f:
        f.write(json.dumps(reg, ensure_ascii=False) + "\n")
    return reg


if __name__ == "__main__":
    print("ffmpeg usado: " + str(FF))
    print(">>> compilação")
    import py_compile
    try:
        py_compile.compile(os.path.join(TV, "tv_caster.py"), doraise=True)
        chk(True, "py_compile tv_caster.py")
    except py_compile.PyCompileError as e:
        chk(False, "py_compile tv_caster.py: " + str(e))
    bloco("JS da página do celular", bloco_js)
    bloco("lógica (mkv_info e métodos de áudio)", bloco_logica)
    bloco("remux (a–e)", bloco_remux)
    bloco("convert_media (f)", bloco_convert)
    tempo = time.time() - T0
    reg = gravar_log(tempo)
    print(f"\nRESULTADO: {'TUDO OK' if not FAIL else str(len(FAIL)) + ' falha(s)'} | ok={OK} | "
          f"versão={reg['versao']} | {tempo:.0f}s")
    for f_ in FAIL:
        print("  - " + f_)
    sys.exit(0 if not FAIL else 1)
