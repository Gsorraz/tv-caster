# TV Caster

Envia vídeo, áudio e a tela do PC para a TV pela rede (DLNA/UPnP). Testado em Samsung (Tizen 2020) e LG (webOS);
funciona com qualquer TV *Media Renderer*.

- Descobre a TV via SSDP e serve o arquivo por HTTP local (com Range para avançar/voltar).
- Legendas `.srt/.ass/.vtt` convertidas e enviadas junto.
- Controle pelo celular (página web + QR Code).
- **Transmitir:** captura tela, janela ou só o som do PC e manda ao vivo (ffmpeg + WASAPI).

## Rodar
Só biblioteca padrão. Opcionais: `ffmpeg` (conversão/transmissão) e `pip install segno` (QR Code).
```bash
python tv_caster.py
```
Ou dê duplo clique em `TV Caster.pyw` (abre sem console).

> `bin/ffmpeg.exe` (88 MB) fica fora do Git: baixe em https://www.gyan.dev/ffmpeg/builds/ e coloque em `bin/`.
> As preferências ficam em `tv_caster_config.json` (gerado na execução).
