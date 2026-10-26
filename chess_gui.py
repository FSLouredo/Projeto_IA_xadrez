#!/usr/bin/env python3
"""Xadrez + Stockfish + importação de PGN.

Requisitos:  py -m pip install chess pillow
             (Tkinter já vem com o Python. O Pillow é opcional, mas necessário
              para skins em .webp/.jpg, sprite sheets e redimensionamento suave.)
Stockfish:   baixe em https://stockfishchess.org e extraia dentro desta pasta
             (o app o encontra sozinho) ou use o botão "Stockfish...".
Skins:       botão "Pasta de skins" (veja o LEIA-ME.txt que ele cria).
Setas:       botão direito no tabuleiro: arrastar = seta, clique = círculo
             (Shift = vermelho, Ctrl = azul, Alt = laranja).
Execução:    py chess_gui.py
"""
import json
import math
import os
import random
import re
import shutil
import statistics
import struct
import subprocess
import sys
import threading
import time
import unicodedata
import tkinter as tk
import wave
from tkinter import ttk, filedialog, messagebox, simpledialog

import chess
import chess.engine
import chess.pgn

try:
    from PIL import Image, ImageOps, ImageTk
except ImportError:                          # Pillow é opcional
    Image = ImageOps = ImageTk = None

# Pasta do programa: ao lado do .py ou, se virar .exe (PyInstaller), ao lado do .exe.
HERE = os.path.dirname(sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__))
CFG = os.path.join(HERE, "chess_gui.json")
SKIN_DIR = os.path.join(HERE, "skins")
SELFPLAY_DIR = os.path.join(HERE, "selfplay")

CAP = 1000                                   # teto de avaliação (cp); mate = CAP
MODES = ("2 jogadores (sem IA)", "Eu de brancas vs IA", "Eu de pretas vs IA")
VECTOR, FROM_SKIN, DEFAULT_THEME = "Vetorial (padrão)", "Da skin", "Clássico"
BOARD_THEMES = {
    "Clássico": ("#f0d9b5", "#b58863"),
    "Verde": ("#eeeed2", "#769656"),
    "Azul": ("#dee3e6", "#8ca2ad"),
    "Madeira escura": ("#e0c9a6", "#8b5a2b"),
    "Roxo": ("#e8e0f0", "#8877b3"),
    "Cinza": ("#e6e6e6", "#9a9a9a"),
}
HL_YELLOW, HL_CHECK, HL_MOVE = "#f7ec59", "#e8665d", "#6f9c4f"
HL_PREMOVE = "#d9534f"
PREMOVE_COST = 0.1                         # segundos descontados do relógio ao executar um premove

# Classificação de lances (nome, símbolo na tabela, cor, descrição) - estilo chess.com
CLASSES = {
    "brilliant":  ("Brilhante", "!!", "#1baca6", "Um sacrifício forte e sólido"),
    "great":      ("Ótimo", "!", "#5c8bb0", "Um lance crítico para a partida"),
    "best":       ("Melhor jogada", "", "#81b64c", "O melhor lance da posição"),
    "excellent":  ("Excelente", "", "#81b64c", "Quase tão bom quanto o melhor"),
    "good":       ("Bom", "", "#95b776", "Um lance sólido"),
    "inaccuracy": ("Imprecisão", "?!", "#f7c631", "Havia algo um pouco melhor"),
    "mistake":    ("Erro", "?", "#e58f2a", "Um erro que custa vantagem"),
    "blunder":    ("Erro grave", "??", "#ca3431", "Um erro muito caro"),
}
CLASS_ORDER = tuple(CLASSES)

SKIN_HELP = """SKINS DE PEÇAS E TABULEIRO
==========================

Cada skin é uma SUBPASTA aqui dentro. Exemplo:

    skins/
      minha_skin/
        wP.png  wN.png  wB.png  wR.png  wQ.png  wK.png     (brancas)
        bP.png  bN.png  bB.png  bR.png  bQ.png  bK.png     (pretas)
        board.png                                           (opcional: imagem do tabuleiro)
        skin.json                                           (opcional: cores do tabuleiro)

Nomes aceitos (maiúsculas/minúsculas não importam):
  wP, bK, w_p, white_pawn, pawn_white, branca_peao ...
  P=peão N=cavalo B=bispo R=torre Q=dama K=rei

Pixel art (imagens pequenas, ex.: 16x16) é ampliada sem ficar borrada.

Formato: PNG com fundo transparente (e .gif). Com o Pillow instalado
(py -m pip install pillow) também funcionam .webp, .jpg e .bmp.
SVG não é suportado: converta para PNG antes.

SPRITE SHEET: se a pasta tiver só UMA imagem larga (6 colunas x 2 linhas,
brancas em cima, pretas embaixo, ordem Rei, Dama, Bispo, Cavalo, Torre, Peão),
ela é fatiada automaticamente (precisa do Pillow).

skin.json (opcional), exemplo:
    {"light": "#eeeed2", "dark": "#769656", "board": "board.png"}

Depois de colocar a pasta aqui, abra a lista "Peças" no app: ela é atualizada
sozinha. Se a skin trouxer tabuleiro/cores, a opção "Da skin" é ativada.
"""


# --------------------------------------------------------------------------
# Utilidades
# --------------------------------------------------------------------------
def mix(c1, c2, t):
    a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(round(x + (y - x) * t) for x, y in zip(a, b))


def valid_color(c):
    return c if isinstance(c, str) and re.fullmatch(r"#[0-9a-fA-F]{6}", c) else None


def load_cfg():
    try:
        with open(CFG, encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def save_cfg(**kw):
    d = load_cfg()
    d.update(kw)
    try:
        with open(CFG, "w", encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False, indent=1)
    except OSError:
        pass


def find_stockfish():
    """Procura o Stockfish: caminho salvo, PATH ou subpastas do projeto."""
    p = load_cfg().get("stockfish", "")
    if p and os.path.isfile(p):
        return p
    p = shutil.which("stockfish")
    if p:
        return p
    for root, dirs, files in os.walk(HERE):
        if root[len(HERE):].count(os.sep) >= 2:
            dirs.clear()
        for f in files:
            n = f.lower()
            if n.startswith("stockfish") and (n.endswith(".exe") if os.name == "nt" else "." not in n):
                return os.path.join(root, f)
    return None


def fmt_cp(cp):
    if abs(cp) >= CAP:
        return "+10 ou mais" if cp > 0 else "-10 ou menos"      # vantagem decisiva (teto)
    return f"{cp / 100:+.2f}"


def mate_in(ev):
    """(vencedor, lances) se o Stockfish achou mate forçado; lances=0 = já é xeque-mate; senão None."""
    if not ev:
        return None
    if ev[4]:
        return ev[4] > 0, abs(ev[4])
    if ev[1] is None and abs(ev[0]) >= CAP:
        return ev[0] > 0, 0
    return None


def fmt_ev(ev, short=False):
    """Texto da avaliação de uma entrada do cache (inclui 'Mate em N')."""
    m = mate_in(ev)
    if m:
        win, n = m
        if short:
            return f"M{n}" if n else "#"
        return f"Mate em {n} ({'brancas' if win else 'pretas'})" if n else \
            f"Xeque-mate ({'brancas' if win else 'pretas'} vencem)"
    return fmt_cp(ev[0])


def winp(cp):
    """Chance de vitória (0..1) a partir de centipeões (curva logística do Lichess)."""
    return 1 / (1 + math.exp(-0.00368208 * cp))


def result_text(b):
    o = b.outcome()
    if o is None:
        return None
    if o.termination == chess.Termination.CHECKMATE:
        return f"Xeque-mate! {'Brancas' if o.winner else 'Pretas'} vencem ({b.result()})"
    return f"Empate ({o.termination.name.lower()}) 1/2-1/2"


# --------------------------------------------------------------------------
# Peças vetoriais (padrão, não dependem de fontes nem de arquivos)
# --------------------------------------------------------------------------
_BASE = ("poly", [(22, 92), (22, 82), (78, 82), (78, 92)])
PIECE_SHAPES = {
    chess.PAWN: [("poly", [(42, 42), (58, 42), (64, 66), (70, 82), (30, 82), (36, 66)]),
                 ("oval", (50, 30, 13, 13)), _BASE],
    chess.ROOK: [("poly", [(28, 18), (28, 38), (34, 44), (34, 66), (28, 82), (72, 82), (66, 66),
                           (66, 44), (72, 38), (72, 18), (62, 18), (62, 26), (55, 26), (55, 18),
                           (45, 18), (45, 26), (38, 26), (38, 18)]), _BASE],
    chess.KNIGHT: [("poly", [(28, 82), (34, 62), (42, 50), (30, 52), (16, 46), (18, 38), (34, 22),
                             (42, 10), (48, 18), (58, 18), (72, 34), (78, 60), (74, 82)]),
                   ("dot", (40, 32, 3)), _BASE],
    chess.BISHOP: [("poly", [(40, 54), (60, 54), (64, 70), (72, 82), (28, 82), (36, 70)]),
                   ("oval", (50, 38, 13, 19)), ("oval", (50, 14, 5, 5)), _BASE],
    chess.QUEEN: [("poly", [(28, 84), (18, 32), (27, 56), (34, 24), (42, 50), (50, 20), (58, 50),
                            (66, 24), (73, 56), (82, 32), (72, 84)]),
                  ("oval", (18, 30, 5, 5)), ("oval", (34, 22, 5, 5)), ("oval", (50, 18, 5, 5)),
                  ("oval", (66, 22, 5, 5)), ("oval", (82, 30, 5, 5)), _BASE],
    chess.KING: [("poly", [(30, 84), (26, 62), (36, 44), (64, 44), (74, 62), (70, 84)]),
                 ("poly", [(46, 8), (54, 8), (54, 16), (62, 16), (62, 24), (54, 24), (54, 44),
                           (46, 44), (46, 24), (38, 24), (38, 16), (46, 16)]), _BASE],
}


def paint_piece(c, cx, cy, size, piece):
    """Desenha a peça vetorial (centro cx, cy) no canvas c."""
    fill, edge = ("#fafafa", "#1a1a1a") if piece.color else ("#2b2b2b", "#e8e8e8")
    k, ox, oy = size / 100, cx - size / 2, cy - size / 2
    for kind, d in PIECE_SHAPES[piece.piece_type]:
        if kind == "poly":
            c.create_polygon([v for x, y in d for v in (ox + x * k, oy + y * k)],
                             fill=fill, outline=edge, width=2)
        elif kind == "oval":
            x, y, rx, ry = d
            c.create_oval(ox + (x - rx) * k, oy + (y - ry) * k, ox + (x + rx) * k, oy + (y + ry) * k,
                          fill=fill, outline=edge, width=2)
        else:
            x, y, r = d
            c.create_oval(ox + (x - r) * k, oy + (y - r) * k, ox + (x + r) * k, oy + (y + r) * k,
                          fill=edge, outline="")


def paint_badge(c, cx, cy, r, key):
    """Selo redondo da classificação do lance (como no chess.com)."""
    _, sym, col, _ = CLASSES[key]
    c.create_oval(cx - r, cy - r, cx + r, cy + r, fill=col, outline="#ffffff", width=max(1, int(r / 9)))
    if key == "best":                                           # estrela
        pts = []
        for i in range(10):
            ang = -math.pi / 2 + i * math.pi / 5
            rad = r * (0.62 if i % 2 == 0 else 0.26)
            pts += [cx + rad * math.cos(ang), cy + rad * math.sin(ang)]
        c.create_polygon(pts, fill="#ffffff", outline="")
    elif not sym:                                               # excelente / bom: visto
        c.create_line(cx - r * .42, cy + r * .02, cx - r * .1, cy + r * .36, cx + r * .46, cy - r * .34,
                      fill="#ffffff", width=max(2, int(r / 4)), capstyle="round", joinstyle="round")
    else:
        c.create_text(cx, cy, text=sym, fill="#ffffff", font=("Arial", max(7, int(r * 0.95)), "bold"))


# --------------------------------------------------------------------------
# Skins (pastas com PNGs das peças / imagem do tabuleiro)
# --------------------------------------------------------------------------
_PT = {"p": chess.PAWN, "n": chess.KNIGHT, "b": chess.BISHOP, "r": chess.ROOK, "q": chess.QUEEN, "k": chess.KING}
_WORDS = {"pawn": "p", "knight": "n", "bishop": "b", "rook": "r", "queen": "q", "king": "k",
          "peao": "p", "cavalo": "n", "bispo": "b", "torre": "r", "dama": "q", "rainha": "q", "rei": "k"}
_SIDES = {"w": chess.WHITE, "white": chess.WHITE, "branca": chess.WHITE, "branco": chess.WHITE,
          "b": chess.BLACK, "black": chess.BLACK, "preta": chess.BLACK, "preto": chess.BLACK}
_WA = "|".join(sorted(_WORDS, key=len, reverse=True))
_SA = "|".join(sorted(_SIDES, key=len, reverse=True))
IMG_EXT = {".png", ".gif"} | ({".webp", ".jpg", ".jpeg", ".bmp"} if Image else set())


def parse_piece_name(stem):
    """'wP', 'white_pawn', 'pawn_black'... -> (cor, tipo) ou None."""
    s = unicodedata.normalize("NFKD", stem.lower()).encode("ascii", "ignore").decode()
    s = re.sub(r"[^a-z]", "", s)
    m = re.fullmatch(r"(w|b)([pnbrqk])", s)
    if m:
        return _SIDES[m[1]], _PT[m[2]]
    m = re.fullmatch(rf"({_SA})({_WA})", s)
    if m:
        return _SIDES[m[1]], _PT[_WORDS[m[2]]]
    m = re.fullmatch(rf"({_WA})({_SA})", s)
    if m:
        return _SIDES[m[2]], _PT[_WORDS[m[1]]]
    m = re.fullmatch(r"([pnbrqk])(w|b)", s)
    if m:
        return _SIDES[m[2]], _PT[m[1]]
    return None


def _tk_scaled(path, size):
    """Redimensiona sem Pillow (só fatores inteiros, aproximado)."""
    img = tk.PhotoImage(file=path)
    w = max(img.width(), img.height())
    if w > size:
        img = img.subsample(max(1, round(w / size)))
    elif w * 2 <= size:
        img = img.zoom(max(1, round(size / w)))
    return img


class Skin:
    SHEET = (chess.KING, chess.QUEEN, chess.BISHOP, chess.KNIGHT, chess.ROOK, chess.PAWN)

    def __init__(self, folder):
        self.folder, self.name = folder, os.path.basename(folder)
        self.files, self.sheet, self.board_file = {}, None, None
        self.unrecognized = []
        self._img, self._board, self._sheet_im = {}, {}, None
        others = []
        for fn in sorted(os.listdir(folder)):
            stem, ext = os.path.splitext(fn)
            path = os.path.join(folder, fn)
            if ext.lower() not in IMG_EXT:
                continue
            key = parse_piece_name(stem)
            if key:
                self.files[key] = path
            elif re.sub(r"[^a-z]", "", stem.lower()) in ("board", "tabuleiro"):
                self.board_file = path
            else:
                others.append(path)
        self.unrecognized = others
        if not self.files and Image and len(others) == 1:     # sprite sheet 6x2?
            try:
                w, h = Image.open(others[0]).size
                if 2.4 <= w / h <= 3.6:
                    self.sheet = others[0]
            except Exception:
                pass
        cfg = {}
        try:
            with open(os.path.join(folder, "skin.json"), encoding="utf-8") as f:
                cfg = json.load(f)
        except (OSError, ValueError):
            pass
        cfg = cfg if isinstance(cfg, dict) else {}
        self.light, self.dark = valid_color(cfg.get("light")), valid_color(cfg.get("dark"))
        if isinstance(cfg.get("board"), str):
            p = os.path.join(folder, cfg["board"])
            if os.path.isfile(p):
                self.board_file = p

    @property
    def has_pieces(self):
        return bool(self.sheet) or len(self.files) == 12

    @property
    def has_board(self):
        return bool(self.board_file or (self.light and self.dark))

    def missing(self):
        names = {chess.PAWN: "P", chess.KNIGHT: "N", chess.BISHOP: "B", chess.ROOK: "R", chess.QUEEN: "Q", chess.KING: "K"}
        return [("w" if c else "b") + names[t] for c in (True, False) for t in names if (c, t) not in self.files]

    def _pil(self, piece):
        if self.sheet:
            if self._sheet_im is None:
                self._sheet_im = Image.open(self.sheet).convert("RGBA")
            im = self._sheet_im
            w, h = im.size
            col, row = self.SHEET.index(piece.piece_type), 0 if piece.color else 1
            return im.crop((round(col * w / 6), round(row * h / 2), round((col + 1) * w / 6), round((row + 1) * h / 2)))
        return Image.open(self.files[(piece.color, piece.piece_type)]).convert("RGBA")

    def image(self, piece, size):
        k = (piece.color, piece.piece_type, size)
        if k not in self._img:
            if Image:
                src = self._pil(piece)
                if max(src.size) <= 64:                      # pixel art: amplia sem borrar e depois ajusta
                    f = -(-size // max(src.size))
                    src = src.resize((src.width * f, src.height * f), Image.Resampling.NEAREST)
                im = ImageOps.contain(src, (size, size), Image.Resampling.LANCZOS)
                out = Image.new("RGBA", (size, size), (0, 0, 0, 0))
                out.paste(im, ((size - im.width) // 2, (size - im.height) // 2), im)
                self._img[k] = ImageTk.PhotoImage(out)
            else:
                self._img[k] = _tk_scaled(self.files[(piece.color, piece.piece_type)], size)
        return self._img[k]

    def board_image(self, size, flipped):
        k = (size, flipped)
        if k not in self._board:
            if Image:
                im = Image.open(self.board_file).convert("RGB").resize((size, size), Image.Resampling.LANCZOS)
                self._board[k] = ImageTk.PhotoImage(im.rotate(180) if flipped else im)
            else:
                self._board[k] = _tk_scaled(self.board_file, size)
        return self._board[k]


def scan_skins():
    out = {}
    if os.path.isdir(SKIN_DIR):
        for d in sorted(os.listdir(SKIN_DIR)):
            p = os.path.join(SKIN_DIR, d)
            if os.path.isdir(p):
                try:
                    s = Skin(p)
                except Exception:
                    continue
                if s.files or s.sheet or s.has_board or s.unrecognized:
                    out[s.name] = s
    return out


# --------------------------------------------------------------------------
# Classificação de lances (pontos esperados, como no chess.com)
# --------------------------------------------------------------------------
VAL = {chess.PAWN: 1, chess.KNIGHT: 3, chess.BISHOP: 3, chess.ROOK: 5, chess.QUEEN: 9, chess.KING: 0}


def mat_diff(b, color):
    return sum(VAL[p.piece_type] if p.color == color else -VAL[p.piece_type] for p in b.piece_map().values())


def qsearch(b, alpha, beta, depth):
    """Só capturas; devolve o saldo de material do ponto de vista de quem joga."""
    stand = mat_diff(b, b.turn)
    if depth == 0 or stand >= beta:
        return stand
    alpha = max(alpha, stand)
    caps = [m for m in b.legal_moves if b.is_capture(m)]
    caps.sort(key=lambda m: -(VAL[b.piece_type_at(m.to_square)] if b.piece_at(m.to_square) else 1))
    for m in caps:
        b.push(m)
        sc = -qsearch(b, -beta, -alpha, depth - 1)
        b.pop()
        if sc >= beta:
            return sc
        alpha = max(alpha, sc)
    return alpha


def sac_amount(board, move):
    """Pontos de material que o lance entrega em relação ao melhor que havia (após as capturas)."""
    b0 = board.copy(stack=False)
    before = qsearch(b0, -1000, 1000, 6)
    b1 = board.copy(stack=False)
    b1.push(move)
    after = -qsearch(b1, -1000, 1000, 6)
    return before - after


def is_sacrifice(board, move):
    return sac_amount(board, move) >= 2


def _gives_mate(board, move):
    b = board.copy(stack=False)
    b.push(move)
    return b.is_checkmate()


def classify_move(board, move, a, b, prev=None):
    """a, b = (cp das brancas, melhor lance, cp do 2º melhor) antes e depois do lance."""
    sign = 1 if board.turn == chess.WHITE else -1
    wp_b, wp_a = winp(sign * a[0]), winp(sign * b[0])
    loss = max(0.0, wp_b - wp_a)                       # pontos esperados perdidos
    if loss > 0.20:
        return "blunder"
    if loss > 0.10:
        return "mistake"
    if loss > 0.05:
        return "inaccuracy"
    if loss > 0.02:
        return "good"
    if wp_a >= 0.45 and wp_b <= 0.85 and is_sacrifice(board, move):
        return "brilliant"
    if a[1] == move and a[2] is not None:
        wp_2 = winp(sign * a[2])
        recapture = prev is not None and board.is_capture(move) and prev.to_square == move.to_square
        zone = lambda w: 2 if w >= 0.70 else 1 if w >= 0.30 else 0      # ganhando / igual / perdendo
        if (not recapture and not _gives_mate(board, move)
                and wp_b - wp_2 >= 0.10 and zone(wp_b) > zone(wp_2)):
            return "great"            # único lance que mantém a vantagem (ou o empate)
    return "best" if a[1] == move else "excellent"


# --------------------------------------------------------------------------
# Texto da análise detalhada de um lance
# --------------------------------------------------------------------------
PIECE_PT = {chess.PAWN: "um peão", chess.KNIGHT: "um cavalo", chess.BISHOP: "um bispo",
            chess.ROOK: "uma torre", chess.QUEEN: "a dama", chess.KING: "o rei"}
BAD = ("inaccuracy", "mistake", "blunder")


def ev_text(cp, mate, sign, final=False):
    """Avaliação do ponto de vista de quem jogou (sign=+1 brancas, -1 pretas)."""
    if mate is not None:
        return f"mate em {abs(mate)} para as {'brancas' if mate > 0 else 'pretas'}"
    if abs(cp) >= CAP:
        return "xeque-mate" if final else f"{'+' if sign * cp > 0 else '-'}10 ou mais"
    return f"{sign * cp / 100:+.2f}"


def explain_move(board, move, a, b, key, who):
    """Explicação de um lance já analisado: lista de (trecho, tag) para um Text."""
    mover = board.turn
    sign = 1 if mover else -1
    side = "brancas" if mover else "pretas"
    after = board.copy(stack=False)
    after.push(move)
    label, _, _, desc = CLASSES[key]
    wpb, wpa = winp(sign * a[0]) * 100, winp(sign * b[0]) * 100
    num = f"{board.fullmove_number}{'.' if mover else '...'}"
    out = [(f"{num} {board.san(move)}", "title"), (f"   {label}\n", key),
           (f"{who}\n\n", "muted"), (desc + ".\n\n", None),
           ("Números ", "h"), (f"(do ponto de vista das {side})\n", "muted"),
           (f"  Antes do lance:   {ev_text(a[0], a[4], sign, a[1] is None)}   ({wpb:.0f}% de chance de vitória)\n", None),
           (f"  Depois do lance:  {ev_text(b[0], b[4], sign, b[1] is None)}   ({wpa:.0f}% de chance de vitória)\n", None),
           (f"  Perda: {max(0, sign * (a[0] - b[0]))} cp  (cerca de {max(0, wpb - wpa):.0f} pontos "
            "percentuais de chance de vitória)\n\n", None)]
    if a[1] is not None and a[1] != move:
        out += [("Melhor lance segundo o Stockfish\n", "h"),
                (f"  {board.san(a[1])}   (avaliação {ev_text(a[0], a[4], sign, a[1] is None)})\n", None)]
        if a[3]:
            out.append((f"  Linha sugerida: {board.variation_san(list(a[3][:5]))}\n", None))
        out.append(("\n", None))
    elif a[3]:
        out += [("Você jogou o lance preferido do Stockfish\n", "h"),
                (f"  Continuação provável: {board.variation_san(list(a[3][:5]))}\n\n", None)]

    notes = []
    if key in BAD:
        reply = b[3][0] if b[3] else None
        if b[4] is not None and (b[4] > 0) != mover:
            notes.append(f"Seu lance permite mate em {abs(b[4])} para o adversário.")
        elif reply is not None and after.is_capture(reply):
            target = after.piece_at(reply.to_square)
            name = PIECE_PT[target.piece_type] if target else "um peão"
            same = " (justamente a peça que você acabou de mover)" if reply.to_square == move.to_square else ""
            notes.append(f"O adversário pode responder {after.san(reply)}, capturando {name}{same}.")
        elif b[3]:
            notes.append("Depois do seu lance, a linha mais forte do adversário é "
                         f"{after.variation_san(list(b[3][:4]))}.")
        if a[4] is not None and (a[4] > 0) == mover and not (b[4] is not None and (b[4] > 0) == mover):
            notes.append(f"Você tinha mate em {abs(a[4])} com {board.san(a[1])}.")
        if key == "blunder":
            notes.append("Dica: antes de mover, liste os xeques, as capturas e as ameaças do adversário.")
    elif key == "brilliant":
        notes.append(f"Você entregou cerca de {sac_amount(board, move)} ponto(s) de material e, mesmo assim, "
                     "o Stockfish confirma que sua posição continua boa.")
    elif key == "great":
        if a[5] is not None and a[2] is not None:
            notes.append(f"O segundo melhor lance ({board.san(a[5])}) levaria a {ev_text(a[2], None, sign)}; "
                         "por isso este era praticamente obrigatório.")
    else:
        notes.append("Você manteve a avaliação da posição.")
    if notes:
        out.append(("O que aconteceu\n", "h"))
        out += [("  " + n + "\n", None) for n in notes]
    return out


# --------------------------------------------------------------------------
# Relógio de xadrez
# --------------------------------------------------------------------------
CLOCK_PRESETS = {"Sem relógio": None, "1 min": (60, 0), "2+1": (120, 1), "3 min": (180, 0), "3+2": (180, 2),
                 "5 min": (300, 0), "5+3": (300, 3), "10 min": (600, 0), "10+5": (600, 5),
                 "15+10": (900, 10), "30 min": (1800, 0), "Personalizado...": "custom"}


def fmt_clock(sec):
    sec = max(0.0, sec)
    if sec < 20:
        return f"0:{sec:04.1f}"
    m, s = divmod(int(sec), 60)
    h, m = divmod(m, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


class Clock:
    """Dois relógios com incremento. Só começam a contar depois do 1º lance das brancas."""

    def __init__(self):
        self.set(None)

    def set(self, cfg):
        self.cfg = cfg
        self.reset()

    def reset(self):
        base = float(self.cfg[0]) if self.cfg else 0.0
        self.left = {True: base, False: base}
        self.turn, self.running, self.paused, self.flag = chess.WHITE, False, False, None
        self._t = None

    @property
    def enabled(self):
        return self.cfg is not None

    def tick(self):
        now = time.monotonic()
        if self.enabled and self.running and not self.paused and self.flag is None and self._t is not None:
            self.left[self.turn] -= now - self._t
            if self.left[self.turn] <= 0:
                self.left[self.turn], self.flag, self.running = 0.0, self.turn, False
        self._t = now

    def moved(self, color, nplies):
        """Chamar depois de um lance de `color`; nplies = total de lances já jogados."""
        self.tick()
        if not self.enabled or self.flag is not None:
            return
        if self.running:
            self.left[color] += self.cfg[1]                  # incremento
        self.turn, self.running = not color, nplies >= 1
        self._t = time.monotonic()

    def penalty(self, color, secs):
        """Desconta `secs` do relógio de `color` (usado nos premoves)."""
        if not self.enabled or self.flag is not None:
            return
        self.left[color] -= secs
        if self.left[color] <= 0:
            self.left[color], self.flag, self.running = 0.0, color, False

    def sync(self, turn, nplies):
        """Depois de desfazer lances / trocar o relógio."""
        self.tick()
        if self.flag is not None:
            self.left[self.flag] = max(self.left[self.flag], 15.0)
            self.flag = None
        self.turn, self.running = turn, self.enabled and nplies >= 1
        self._t = time.monotonic()


# --------------------------------------------------------------------------
# Paletas da interface (claro / escuro)
# --------------------------------------------------------------------------
PALETTES = {
    "Claro": dict(dark=False, bg="#f0f0f0", fg="#1b1b1b", field="#ffffff", btn="#e1e1e1", btn_active="#d0d0d0",
                  sel="#3d6a99", sel_fg="#ffffff", head="#dadada", border="#b0b0b0", muted="#606060"),
    "Escuro": dict(dark=True, bg="#2b2b2b", fg="#e6e6e6", field="#1e1e1e", btn="#3c3f41", btn_active="#4d5154",
                   sel="#3d6a99", sel_fg="#ffffff", head="#383838", border="#555555", muted="#a0a0a0"),
}
CLOCK_ON, CLOCK_LOW = "#3b7d3b", "#b3261e"
ARROW_GREEN, ARROW_RED, ARROW_BLUE, ARROW_ORANGE = "#2e8b47", "#c0392b", "#2b6cb0", "#e08a00"


# --------------------------------------------------------------------------
# Stockfish: avalia posições em segundo plano e guarda tudo num cache por FEN
# --------------------------------------------------------------------------
# --------------------------------------------------------------------------
# Força da IA. O Stockfish só aceita Elo >= 1320 (UCI_Elo); abaixo disso usamos
# "Skill Level 0" + busca rasa + uma chance de jogar um lance aleatório (erro).
# É uma aproximação: os números abaixo de 1350 não foram calibrados contra humanos.
# --------------------------------------------------------------------------
ELO_MIN, ELO_MAX, UCI_ELO_MIN = 300, 3000, 1350


def set_strength(engine, elo):
    try:
        if elo >= UCI_ELO_MIN:
            engine.configure({"UCI_LimitStrength": True, "UCI_Elo": int(elo)})
        else:
            engine.configure({"UCI_LimitStrength": False, "Skill Level": 0})
    except chess.engine.EngineError:
        pass


def blunder_chance(elo):
    """Chance de jogar um lance aleatório (0 em 1350, 80% em 300)."""
    return 0.0 if elo >= UCI_ELO_MIN else 0.8 * (UCI_ELO_MIN - elo) / (UCI_ELO_MIN - ELO_MIN)


def strength_move(engine, board, elo, secs):
    if elo < UCI_ELO_MIN:
        if random.random() < blunder_chance(elo):
            return random.choice(list(board.legal_moves))
        return engine.play(board, chess.engine.Limit(time=min(0.2, max(0.02, secs)), depth=2)).move
    return engine.play(board, chess.engine.Limit(time=max(0.02, secs))).move


class Analyzer:
    def __init__(self):
        self.path = find_stockfish()
        self.depth = 12
        # fen -> (cp das brancas, melhor lance, cp do 2º melhor, linha principal, mate, 2º melhor lance)
        self.cache = {}
        self.running = False
        self.error = None

    def _evaluate(self, engine, b):
        if b.is_game_over():
            o = b.outcome()
            return (0 if o.winner is None else (CAP if o.winner else -CAP)), None, None, (), None, None
        infos = engine.analyse(b, chess.engine.Limit(depth=self.depth), multipv=2)

        def cpw(i):
            return max(-CAP, min(CAP, i["score"].white().score(mate_score=10_000)))
        pv = infos[0].get("pv") or []
        pv2 = (infos[1].get("pv") or []) if len(infos) > 1 else []
        mate = infos[0]["score"].white().mate()
        keep = max(6, 2 * abs(mate)) if mate else 6          # mostra a sequência inteira do mate
        return (cpw(infos[0]), (pv[0] if pv else None), (cpw(infos[1]) if len(infos) > 1 else None),
                tuple(pv[:keep]), mate, (pv2[0] if pv2 else None))

    def run(self, boards):          # roda em thread
        try:
            engine = chess.engine.SimpleEngine.popen_uci(self.path)
            try:
                engine.configure({"Threads": min(4, os.cpu_count() or 1), "Hash": 64})
                for b in boards:
                    k = b.fen()
                    if k not in self.cache:
                        self.cache[k] = self._evaluate(engine, b)
            finally:
                engine.quit()
        except Exception as e:      # caminho inválido, engine travou, etc.
            self.error = str(e)
        finally:
            self.running = False

    def best_move(self, board, elo, secs=0.6):
        """Lance da IA (Stockfish com força limitada pelo Elo)."""
        engine = chess.engine.SimpleEngine.popen_uci(self.path)
        try:
            set_strength(engine, elo)
            return strength_move(engine, board, elo, secs)
        finally:
            engine.quit()

    def judge(self, boards, k):
        """Julga o lance k (de boards[k] para boards[k+1]) -> (perda_em_cp, melhor_lance)."""
        a, b = self.cache.get(boards[k].fen()), self.cache.get(boards[k + 1].fen())
        if not a or not b:
            return None
        sign = 1 if boards[k].turn == chess.WHITE else -1
        return max(0, sign * (a[0] - b[0])), a[1]


# --------------------------------------------------------------------------
# Banco de partidas PGN (lê só os cabeçalhos; carrega a partida sob demanda)
# --------------------------------------------------------------------------
class Library(tk.Toplevel):
    LIMIT = 20000

    def __init__(self, app, path):
        super().__init__(app)
        self.app = app
        self.f = open(path, encoding="utf-8", errors="replace")
        self.items = []
        while len(self.items) < self.LIMIT:
            off = self.f.tell()
            h = chess.pgn.read_headers(self.f)
            if h is None:
                break
            self.items.append((off, f"{h.get('White', '?')} vs {h.get('Black', '?')}  "
                                    f"[{h.get('Result', '*')}]  {h.get('Event', '')} {h.get('Date', '')}"))
        self.title(f"{os.path.basename(path)} - {len(self.items)} partidas (duplo clique para abrir)")
        self.q = tk.StringVar()
        self.q.trace_add("write", lambda *_: self.fill())
        ttk.Entry(self, textvariable=self.q).pack(fill="x", padx=6, pady=4)
        self.lb = tk.Listbox(self, width=95, height=24)
        self.lb.pack(fill="both", expand=True, padx=6, pady=(0, 6))
        self.lb.bind("<Double-Button-1>", self.open_game)
        self.protocol("WM_DELETE_WINDOW", self.close)
        app.subwins.append(self)
        self.retheme()
        self.fill()

    def retheme(self):
        p = self.app.pal
        self.configure(bg=p["bg"])
        self.lb.configure(bg=p["field"], fg=p["fg"], selectbackground=p["sel"], selectforeground=p["sel_fg"],
                          highlightthickness=0, relief="flat")

    def close(self):
        if self in self.app.subwins:
            self.app.subwins.remove(self)
        self.f.close()
        self.destroy()

    def fill(self):
        q = self.q.get().lower()
        self.shown = [i for i in self.items if q in i[1].lower()]
        self.lb.delete(0, "end")
        for _, text in self.shown[:3000]:
            self.lb.insert("end", text)

    def open_game(self, _):
        sel = self.lb.curselection()
        if sel:
            self.f.seek(self.shown[sel[0]][0])
            game = chess.pgn.read_game(self.f)
            if game:
                self.app.load_game(game)


# --------------------------------------------------------------------------
# Janela de registro de lances (histórico + explicação de cada lance)
# --------------------------------------------------------------------------
class MoveLog(tk.Toplevel):
    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("Registro de lances - análise do seu jogo")
        self.geometry("780x580")
        self.only_mine = tk.BooleanVar(value=True)
        self.follow = tk.BooleanVar(value=True)
        self._sig, self._busy = None, False

        top = ttk.Frame(self)
        top.pack(fill="x", padx=8, pady=(8, 4))
        ttk.Checkbutton(top, text="Só os meus lances (contra a IA)", variable=self.only_mine,
                        command=lambda: self.update_log(True)).pack(side="left")
        ttk.Checkbutton(top, text="Acompanhar o último lance", variable=self.follow,
                        command=lambda: self.update_log(True)).pack(side="left", padx=14)
        ttk.Button(top, text="Exportar...", command=self.export).pack(side="right")

        paned = ttk.PanedWindow(self, orient="vertical")
        paned.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        frm = ttk.Frame(paned)
        self.tree = ttk.Treeview(frm, columns=("n", "lance", "classe", "perda", "melhor"), show="headings",
                                 height=9, selectmode="browse")
        for c, t, w, anc in (("n", "#", 55, "center"), ("lance", "Lance", 90, "center"),
                             ("classe", "Classificação", 150, "w"), ("perda", "Perda", 80, "center"),
                             ("melhor", "Melhor lance", 110, "center")):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor=anc)
        sb = ttk.Scrollbar(frm, command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")
        self.text = tk.Text(paned, wrap="word", height=14, relief="flat", padx=12, pady=10,
                            font=("Arial", 10), cursor="arrow")
        self.text.configure(state="disabled")
        paned.add(frm, weight=1)
        paned.add(self.text, weight=2)
        self.tree.bind("<<TreeviewSelect>>", self.on_select)
        self.protocol("WM_DELETE_WINDOW", self.close)
        app.subwins.append(self)
        self.retheme()
        self.update_log(True)

    def retheme(self):
        p = self.app.pal
        self.configure(bg=p["bg"])
        self.text.configure(bg=p["field"], fg=p["fg"], insertbackground=p["fg"], highlightthickness=0)
        self.text.tag_configure("title", font=("Arial", 15, "bold"))
        self.text.tag_configure("h", font=("Arial", 10, "bold"), spacing1=2)
        self.text.tag_configure("muted", foreground=p["muted"])
        self.tree.tag_configure("none", foreground=p["muted"])
        for key, (_, _, col, _) in CLASSES.items():
            col = col if p["dark"] else mix(col, "#000000", 0.35)
            self.text.tag_configure(key, foreground=col, font=("Arial", 12, "bold"))
            self.tree.tag_configure(key, foreground=col)

    def close(self):
        if self in self.app.subwins:
            self.app.subwins.remove(self)
        self.app.log = None
        self.destroy()

    # ---- conteúdo ----
    def shown_moves(self):
        a = self.app
        return [k for k in range(len(a.moves))
                if not (self.only_mine.get() and a.ai_color is not None and a.boards[k].turn == a.ai_color)]

    def update_log(self, force=False):
        a = self.app
        rows = [(k, a.move_class(k)) for k in self.shown_moves()]
        sig = (a.game_id, len(a.moves), tuple(rows), self.follow.get())
        if sig == self._sig and not force:
            return
        self._sig = sig
        prev = self.tree.selection()
        self._busy = True
        self.tree.delete(*self.tree.get_children())
        for k, key in rows:
            board = a.boards[k]
            j = a.analyzer.judge(a.boards, k)
            best = board.san(j[1]) if key and j and j[1] and j[1] != a.moves[k] else ""
            self.tree.insert("", "end", iid=str(k), tags=(key or "none",),
                             values=(f"{board.fullmove_number}{'.' if board.turn else '...'}", a.sans[k],
                                     CLASSES[key][0] if key else "analisando...", f"{j[0]} cp" if j else "", best))
        chosen = None
        if rows:
            if self.follow.get():
                chosen = rows[-1][0]
            elif prev and self.tree.exists(prev[0]):
                chosen = int(prev[0])
        if chosen is not None:
            self.tree.selection_set(str(chosen))
            self.tree.see(str(chosen))
        self._busy = False
        self.show(chosen)

    def show(self, k):
        t = self.text
        t.configure(state="normal")
        t.delete("1.0", "end")
        if k is None:
            t.insert("end", "Faça um lance. Cada lance seu aparece nesta lista, com a explicação do Stockfish.\n"
                            "Clique num lance para revê-lo no tabuleiro.", "muted")
        else:
            exp = self.app.explain(k)
            if exp is None:
                t.insert("end", "Este lance ainda está sendo analisado pelo Stockfish...", "muted")
            else:
                for txt, tag in exp:
                    t.insert("end", txt, tag or ())
        t.configure(state="disabled")

    def on_select(self, _=None):
        if self._busy:
            return
        sel = self.tree.selection()
        if sel:
            self.follow.set(False)
            self.app.go(int(sel[0]) + 1)
            self.show(int(sel[0]))

    def select(self, k):
        if not self.tree.exists(str(k)):
            return
        self._busy = True
        self.tree.selection_set(str(k))
        self.tree.see(str(k))
        self._busy = False
        self.follow.set(False)
        self.app.go(k + 1)
        self.show(k)

    def export(self):
        p = filedialog.asksaveasfilename(parent=self, defaultextension=".txt", initialfile="analise_da_partida.txt",
                                         filetypes=[("Texto", "*.txt")])
        if not p:
            return
        parts = []
        for k in self.shown_moves():
            exp = self.app.explain(k)
            if exp:
                parts.append("".join(t for t, _ in exp))
        try:
            with open(p, "w", encoding="utf-8") as f:
                f.write(("\n" + "-" * 70 + "\n").join(parts) or "Sem lances analisados.")
        except OSError as e:
            messagebox.showerror("Exportar", f"Não foi possível salvar:\n{e}", parent=self)


# --------------------------------------------------------------------------
# Aplicação
# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# Editor de posição: monta um cenário personalizado para estudo
# --------------------------------------------------------------------------
STATUS_MSG = (
    ("STATUS_EMPTY", "o tabuleiro está vazio"),
    ("STATUS_NO_WHITE_KING", "falta o rei branco"),
    ("STATUS_NO_BLACK_KING", "falta o rei preto"),
    ("STATUS_TOO_MANY_KINGS", "há reis demais"),
    ("STATUS_TOO_MANY_WHITE_PAWNS", "as brancas têm mais de 8 peões"),
    ("STATUS_TOO_MANY_BLACK_PAWNS", "as pretas têm mais de 8 peões"),
    ("STATUS_PAWNS_ON_BACKRANK", "há peão na 1ª ou 8ª fileira"),
    ("STATUS_TOO_MANY_WHITE_PIECES", "as brancas têm mais de 16 peças"),
    ("STATUS_TOO_MANY_BLACK_PIECES", "as pretas têm mais de 16 peças"),
    ("STATUS_OPPOSITE_CHECK", "o lado que NÃO joga está em xeque (mude a vez ou mova o rei)"),
    ("STATUS_TOO_MANY_CHECKERS", "xeque impossível (peças demais dando xeque)"),
    ("STATUS_IMPOSSIBLE_CHECK", "xeque impossível nessa posição"),
)


class BoardEditor(tk.Toplevel):
    ORDER = (chess.KING, chess.QUEEN, chess.ROOK, chess.BISHOP, chess.KNIGHT, chess.PAWN)

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("Editor de posição")
        self.resizable(False, False)
        self.tool = "move"
        b = app.edit_board
        self.turn = tk.IntVar(value=1 if b.turn else 0)
        self.rights = {k: tk.BooleanVar() for k in ("K", "Q", "k", "q")}
        self.sync_vars()
        self.msg = tk.StringVar()
        self.tool_txt = tk.StringVar()
        self.cells = []

        ttk.Label(self, text="1) Escolha o que colocar (ou 'Mover'/'Apagar') e use o tabuleiro:").pack(
            anchor="w", padx=10, pady=(10, 4))
        pal = ttk.Frame(self)
        pal.pack(padx=10)
        for r, color in enumerate((chess.WHITE, chess.BLACK)):
            for c, t in enumerate(self.ORDER):
                cv = tk.Canvas(pal, width=48, height=48, highlightthickness=3, cursor="hand2")
                cv.grid(row=r, column=c, padx=1, pady=1)
                cv.bind("<Button-1>", lambda e, p=chess.Piece(t, color): self.pick(p))
                self.cells.append((cv, chess.Piece(t, color)))
        tools = ttk.Frame(self)
        tools.pack(fill="x", padx=10, pady=(6, 0))
        ttk.Button(tools, text="Mover peças", command=lambda: self.pick("move")).pack(side="left", padx=(0, 4))
        ttk.Button(tools, text="Apagar", command=lambda: self.pick("erase")).pack(side="left")
        ttk.Label(tools, textvariable=self.tool_txt).pack(side="left", padx=8)
        ttk.Label(self, justify="left", wraplength=330, text=(
            "Mover: arraste uma peça (solte fora do tabuleiro para apagar).\n"
            "Com uma peça escolhida: clique ou arraste sobre as casas para colocá-la.\n"
            "Botão direito numa casa: apaga a peça.")).pack(anchor="w", padx=10, pady=(6, 0))

        ttk.Label(self, text="2) Vez de jogar:").pack(anchor="w", padx=10, pady=(10, 0))
        row = ttk.Frame(self)
        row.pack(anchor="w", padx=10)
        for txt, v in (("Brancas", 1), ("Pretas", 0)):
            ttk.Radiobutton(row, text=txt, value=v, variable=self.turn, command=self.check).pack(side="left", padx=(0, 10))
        ttk.Label(self, text="Roques ainda permitidos:").pack(anchor="w", padx=10, pady=(6, 0))
        row = ttk.Frame(self)
        row.pack(anchor="w", padx=10)
        for k, txt in (("K", "O-O brancas"), ("Q", "O-O-O brancas"), ("k", "O-O pretas"), ("q", "O-O-O pretas")):
            ttk.Checkbutton(row, text=txt, variable=self.rights[k], command=self.check).pack(side="left", padx=(0, 6))

        row = ttk.Frame(self)
        row.pack(fill="x", padx=10, pady=(10, 0))
        for txt, cmd in (("Posição inicial", self.reset), ("Limpar tabuleiro", self.clear),
                         ("Copiar FEN", self.copy_fen), ("Colar FEN...", self.paste_fen)):
            ttk.Button(row, text=txt, command=cmd).pack(side="left", padx=(0, 4))
        ttk.Label(self, textvariable=self.msg, wraplength=330, justify="left").pack(anchor="w", padx=10, pady=8)
        row = ttk.Frame(self)
        row.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(row, text="Jogar a partir daqui", command=self.apply).pack(side="left", padx=(0, 6))
        ttk.Button(row, text="Cancelar", command=self.cancel).pack(side="left")

        self.protocol("WM_DELETE_WINDOW", self.cancel)
        app.subwins.append(self)
        self.retheme()
        self.pick("move")
        self.check()
        self.update_idletasks()
        try:
            self.geometry(f"+{app.winfo_rootx() + app.winfo_width() - 40}+{app.winfo_rooty() + 40}")
        except tk.TclError:
            pass

    def retheme(self):
        p = self.app.pal
        self.configure(bg=p["bg"])
        for cv, piece in self.cells:
            cv.configure(bg=self.app.light)                 # fundo claro: as peças brancas aparecem bem
            cv.delete("all")
            self.app.put_piece(cv, 27, 27, 42, piece)
        self.pick(self.tool)

    def pick(self, tool):
        self.tool = tool
        p = self.app.pal
        for cv, piece in self.cells:
            cv.configure(highlightbackground=p["sel"] if piece == tool else p["bg"],
                         highlightcolor=p["sel"])
        names = {chess.KING: "rei", chess.QUEEN: "dama", chess.ROOK: "torre", chess.BISHOP: "bispo",
                 chess.KNIGHT: "cavalo", chess.PAWN: "peão"}
        self.tool_txt.set("Ferramenta: mover" if tool == "move" else "Ferramenta: apagar" if tool == "erase" else
                          f"Colocando: {names[tool.piece_type]} {'branco' if tool.color else 'preto'}")

    def sync_vars(self):
        b = self.app.edit_board
        self.turn.set(1 if b.turn else 0)
        for k, bb in (("K", chess.BB_H1), ("Q", chess.BB_A1), ("k", chess.BB_H8), ("q", chess.BB_A8)):
            self.rights[k].set(bool(b.castling_rights & bb))

    def build(self):
        """Copia vez e roques da janela para o tabuleiro em edição."""
        b = self.app.edit_board
        b.turn = bool(self.turn.get())
        mask = 0
        for k, bb in (("K", chess.BB_H1), ("Q", chess.BB_A1), ("k", chess.BB_H8), ("q", chess.BB_A8)):
            if self.rights[k].get():
                mask |= bb
        b.castling_rights = mask
        b.castling_rights = b.clean_castling_rights()
        b.ep_square = None
        return b

    def problems(self):
        st = self.build().status()
        return [txt for name, txt in STATUS_MSG if st & getattr(chess, name, 0)]

    def check(self):
        pr = self.problems()
        self.msg.set("Posição válida." if not pr else "Ainda não dá para jogar: " + "; ".join(pr) + ".")
        self.app.draw()

    def place(self, sq, piece):
        b = self.app.edit_board
        if piece.piece_type == chess.PAWN and chess.square_rank(sq) in (0, 7):
            self.msg.set("Peões não podem ficar na 1ª nem na 8ª fileira.")
            return False
        if piece.piece_type == chess.KING:
            for s in list(b.pieces(chess.KING, piece.color)):
                if s != sq:
                    b.remove_piece_at(s)                   # só um rei por cor
        b.set_piece_at(sq, piece)
        self.check()
        return True

    def reset(self):
        self.app.edit_board.reset()
        self.sync_vars()
        self.check()

    def clear(self):
        b = self.app.edit_board
        b.clear_board()
        b.castling_rights = 0
        self.sync_vars()
        self.check()

    def copy_fen(self):
        fen = self.build().fen()
        self.clipboard_clear()
        self.clipboard_append(fen)
        self.msg.set("FEN copiado: " + fen)

    def paste_fen(self):
        try:
            init = self.clipboard_get().strip()
        except tk.TclError:
            init = ""
        fen = simpledialog.askstring("Colar FEN", "Cole o FEN da posição:", parent=self, initialvalue=init)
        if not fen:
            return
        try:
            chess.Board(fen.strip())
            self.app.edit_board.set_fen(fen.strip())
        except ValueError:
            self.msg.set("FEN inválido. Exemplo: rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1")
            return
        self.sync_vars()
        self.check()

    def apply(self):
        pr = self.problems()
        if pr:
            self.msg.set("Não dá para jogar: " + "; ".join(pr) + ".")
            return
        board = self.app.edit_board.copy(stack=False)
        self.sync_vars()
        self._close()
        self.app.start_from(board)

    def _close(self):
        a = self.app
        a.editing, a.editor, a.drag, a.hide_sq = False, None, None, None
        if self in a.subwins:
            a.subwins.remove(self)
        self.destroy()

    def cancel(self):
        a = self.app
        if not a.editing:
            return
        self._close()
        a.clock.paused = a._pre_paused
        a.refresh()


# --------------------------------------------------------------------------
# JOGADORES (IA vs IA). Cada jogador tem choose(board, secs) -> chess.Move.
# Para plugar a IA do grupo (rede neural, etc.), edite a classe MeuJogador
# mais abaixo: ela aparece na janela "IA vs IA" como "Minha IA".
# --------------------------------------------------------------------------
class Player:
    name = "?"

    def choose(self, board, secs):
        raise NotImplementedError

    def close(self):
        pass


class RandomPlayer(Player):
    name = "Aleatória"

    def choose(self, board, secs):
        return random.choice(list(board.legal_moves))


_VAL = {chess.PAWN: 100, chess.KNIGHT: 320, chess.BISHOP: 330, chess.ROOK: 500, chess.QUEEN: 900, chess.KING: 0}
_MATE = 100000


class _Timeout(Exception):
    pass


class MinimaxPlayer(Player):
    """Busca negamax com poda alfa-beta, aprofundamento iterativo e avaliação simples
    (material + centralização + avanço de peões). É o ponto de partida 'caseiro'."""

    def __init__(self, depth=2, positional=True):
        self.depth, self.positional = depth, positional
        self.name = f"Minimax (prof. {depth})" if positional else "Gulosa (material)"
        self.nodes, self.deadline = 0, 0.0

    def static(self, board):
        """Avaliação do ponto de vista de quem joga (centipeões)."""
        sc = 0
        for sq, p in board.piece_map().items():
            v = _VAL[p.piece_type]
            if self.positional:
                f, r = chess.square_file(sq), chess.square_rank(sq)
                if p.piece_type == chess.PAWN:
                    v += 6 * (r - 1 if p.color else 6 - r) + (4 if 2 <= f <= 5 else 0)
                elif p.piece_type != chess.KING:
                    v += 10 - 3 * (abs(f - 3.5) + abs(r - 3.5))          # centro vale mais
            sc += v if p.color else -v
        return sc if board.turn else -sc

    def quiesce(self, board, alpha, beta, depth):
        stand = self.static(board)
        if depth == 0 or stand >= beta:
            return max(stand, alpha) if stand < beta else stand
        alpha = max(alpha, stand)
        for m in sorted(board.generate_legal_captures(),
                        key=lambda m: -_VAL.get((board.piece_type_at(m.to_square) or chess.PAWN), 100)):
            board.push(m)
            sc = -self.quiesce(board, -beta, -alpha, depth - 1)
            board.pop()
            if sc >= beta:
                return sc
            alpha = max(alpha, sc)
        return alpha

    def order(self, board, moves):
        def key(m):
            k = 0
            if board.is_capture(m):
                k += 10 * _VAL.get(board.piece_type_at(m.to_square) or chess.PAWN, 100) - _VAL[board.piece_type_at(m.from_square)]
            if m.promotion:
                k += 800
            return -k
        return sorted(moves, key=key)

    def search(self, board, depth, alpha, beta, ply):
        self.nodes += 1
        if self.nodes & 127 == 0 and time.monotonic() > self.deadline:
            raise _Timeout
        if board.is_insufficient_material():
            return 0
        moves = list(board.legal_moves)
        if not moves:
            return -_MATE + ply if board.is_check() else 0
        if depth <= 0:
            return self.quiesce(board, alpha, beta, 4) if self.positional else self.static(board)
        best = -_MATE * 2
        for m in self.order(board, moves):
            board.push(m)
            sc = -self.search(board, depth - 1, -beta, -alpha, ply + 1)
            board.pop()
            if sc > best:
                best = sc
            alpha = max(alpha, sc)
            if alpha >= beta:
                break
        return best

    def choose(self, board, secs):
        b = board.copy(stack=False)
        moves = list(b.legal_moves)
        random.shuffle(moves)                      # variedade entre lances de mesmo valor
        best_move, self.nodes = moves[0], 0
        self.deadline = time.monotonic() + max(0.05, secs)
        for d in range(1, self.depth + 1):
            try:
                scores = []
                alpha = -_MATE * 2
                for m in self.order(b, moves):
                    b.push(m)
                    sc = -self.search(b, d - 1, -_MATE * 2, -alpha, 1)
                    b.pop()
                    scores.append((sc, m))
                    alpha = max(alpha, sc)
                scores.sort(key=lambda t: -t[0])
                best_move = scores[0][1]
                moves = [m for _, m in scores]      # melhor primeiro na próxima profundidade
                if scores[0][0] > _MATE - 100:
                    break                            # mate encontrado
            except _Timeout:
                break
        return best_move


class MeuJogador(Player):
    """>>> SUBSTITUA AQUI pela IA do grupo (rede neural em PyTorch, etc.). <<<
    Receba o tabuleiro (chess.Board) e devolva um chess.Move legal.
    Hoje ela só delega ao Minimax próprio, para a janela já funcionar."""

    def __init__(self, level=2):
        self.inner = MinimaxPlayer(level)
        self.name = f"Minha IA (nível {level})"

    def choose(self, board, secs):
        return self.inner.choose(board, secs)


class UciPlayer(Player):
    """Stockfish (com Elo limitado ou força total) ou qualquer outro motor UCI."""

    def __init__(self, path, elo=None, label=None):
        self.engine = chess.engine.SimpleEngine.popen_uci(path)
        try:
            self.engine.configure({"Threads": 1, "Hash": 16})
        except chess.engine.EngineError:
            pass
        self.elo = elo
        if elo:
            set_strength(self.engine, elo)
        self.name = label or (f"Stockfish {elo}" if elo else "Stockfish (total)")

    def choose(self, board, secs):
        if self.elo:
            return strength_move(self.engine, board, self.elo, secs)
        return self.engine.play(board, chess.engine.Limit(time=max(0.02, secs))).move

    def close(self):
        try:
            self.engine.quit()
        except Exception:
            pass


# tipo na janela -> (código, rótulo do nível, padrão, mín, máx)
SP_TYPES = {
    "Stockfish (Elo limitado)": ("stockfish", "Elo", 1500, ELO_MIN, ELO_MAX),
    "Stockfish (força total)": ("stockfish_full", "", 0, 0, 0),
    "Minimax própria": ("minimax", "Profundidade", 2, 1, 4),
    "Gulosa (só material)": ("greedy", "", 0, 0, 0),
    "Aleatória": ("random", "", 0, 0, 0),
    "Minha IA (classe MeuJogador)": ("mine", "Nível", 2, 1, 4),
    "Motor UCI externo...": ("uci", "", 0, 0, 0),
}


def make_player(spec, sf_path):
    kind, level = spec["kind"], spec.get("level", 0)
    if kind in ("stockfish", "stockfish_full"):
        if not sf_path:
            raise RuntimeError("Stockfish não configurado (botão 'Stockfish...').")
        return UciPlayer(sf_path, level if kind == "stockfish" else None)
    if kind == "uci":
        p = spec.get("path")
        return UciPlayer(p, None, "UCI: " + os.path.splitext(os.path.basename(p))[0])
    if kind == "minimax":
        return MinimaxPlayer(level)
    if kind == "greedy":
        return MinimaxPlayer(1, positional=False)
    if kind == "mine":
        return MeuJogador(level)
    return RandomPlayer()


TERM_PT = {"CHECKMATE": "xeque-mate", "STALEMATE": "afogamento", "INSUFFICIENT_MATERIAL": "material insuficiente",
           "SEVENTYFIVE_MOVES": "75 lances", "FIVEFOLD_REPETITION": "repetição", "FIFTY_MOVES": "50 lances",
           "THREEFOLD_REPETITION": "repetição", "LIMITE": "limite de lances"}


class SelfPlay(threading.Thread):
    """Roda uma série de partidas IA vs IA em segundo plano e grava PGN + dataset (JSONL)."""

    def __init__(self, cfg, analyzer, outdir):
        super().__init__(daemon=True)
        self.cfg, self.an, self.outdir = cfg, analyzer, outdir
        self.lock = threading.Lock()
        self.stop_ev, self.go = threading.Event(), threading.Event()
        self.go.set()
        self.game_no, self.start_board, self.moves = 0, chess.Board(), []
        self.results, self.error, self.status = [], None, "Preparando..."
        self.names = ("A", "B")
        self.base = None

    # ---- utilidades ----
    def wait_ok(self):
        while not self.go.wait(0.1):
            if self.stop_ev.is_set():
                return False
        return not self.stop_ev.is_set()

    def sleep(self, sec):
        end = time.monotonic() + sec
        while time.monotonic() < end and not self.stop_ev.is_set():
            time.sleep(0.03)

    def make_start(self):
        cfg = self.cfg
        for _ in range(50):
            b = cfg["start"].copy(stack=False)
            for _ in range(cfg["random_plies"]):
                mv = list(b.legal_moves)
                if not mv:
                    break
                b.push(random.choice(mv))
            if not b.is_game_over():
                b.clear_stack()
                return b
        return cfg["start"].copy(stack=False)

    # ---- laço principal ----
    def run(self):
        players = []
        try:
            A = make_player(self.cfg["A"], self.an.path)
            players.append(A)
            B = make_player(self.cfg["B"], self.an.path)
            players.append(B)
            self.names = (A.name, B.name)
            os.makedirs(self.outdir, exist_ok=True)
            self.base = os.path.join(self.outdir, "selfplay_" + time.strftime("%Y%m%d_%H%M%S"))
            for g in range(1, self.cfg["games"] + 1):
                if self.stop_ev.is_set():
                    break
                self.play_one(g, A, B)
        except Exception as e:
            self.error = str(e)
        finally:
            for p in players:
                p.close()
            self.status = "Erro: " + self.error if self.error else (
                "Interrompido." if self.stop_ev.is_set() else "Série concluída.")

    def play_one(self, g, A, B):
        cfg = self.cfg
        a_white = (g % 2 == 1) or not cfg["alternate"]
        white, black = (A, B) if a_white else (B, A)
        board = self.make_start()
        start = board.copy()
        played = []
        with self.lock:
            self.game_no, self.start_board, self.moves = g, start, []
        outcome = None
        while True:
            outcome = board.outcome(claim_draw=True)
            if outcome or len(played) >= cfg["max_plies"] or self.stop_ev.is_set():
                break
            if not self.wait_ok():
                break
            t0 = time.monotonic()
            p = white if board.turn else black
            mv = p.choose(board, cfg["secs"])
            if mv not in board.legal_moves:
                raise RuntimeError(f"{p.name} devolveu um lance ilegal: {mv}")
            board.push(mv)
            played.append(mv)
            with self.lock:
                self.moves.append(mv)
            self.status = f"Partida {g}/{cfg['games']}: {white.name} (brancas) x {black.name} (pretas) - lance {len(played)}"
            self.sleep(max(0.0, cfg["pause"] - (time.monotonic() - t0)))
        if outcome is None and not (len(played) >= cfg["max_plies"]):
            return                                           # interrompida: não registra
        result = outcome.result() if outcome else "1/2-1/2"
        reason = TERM_PT.get(outcome.termination.name, outcome.termination.name) if outcome else TERM_PT["LIMITE"]
        info = None
        if cfg["judge"] and self.an.path and played and not self.stop_ev.is_set():
            self.status = f"Partida {g}: julgando os lances com o Stockfish..."
            try:
                info = self.judge_game(start, played)
            except Exception as e:                           # motor falhou: grava sem avaliação
                self.status = "Falha ao julgar: " + str(e)
        a_pts = {"1-0": 1.0 if a_white else 0.0, "0-1": 0.0 if a_white else 1.0}.get(result, 0.5)
        res = dict(game=g, white=white.name, black=black.name, result=result, reason=reason, plies=len(played),
                   a_white=a_white, a_pts=a_pts,
                   acpl_w=info["acpl"][True] if info else None, acpl_b=info["acpl"][False] if info else None)
        self.save(res, start, played, info)
        with self.lock:
            self.results.append(res)

    # ---- julgamento pelo Stockfish ----
    def judge_game(self, start, moves):
        boards = [start.copy()]
        for m in moves:
            b = boards[-1].copy()
            b.push(m)
            boards.append(b)
        engine = chess.engine.SimpleEngine.popen_uci(self.an.path)
        try:
            engine.configure({"Threads": min(2, os.cpu_count() or 1), "Hash": 64})
            for b in boards:
                if self.stop_ev.is_set():
                    raise RuntimeError("interrompido")
                k = b.fen()
                if k not in self.an.cache:
                    self.an.cache[k] = self.an._evaluate(engine, b)
        finally:
            engine.quit()
        losses = {True: [], False: []}
        rows = []
        for k, m in enumerate(moves):
            j = self.an.judge(boards, k)
            loss = min(1000, j[0]) if j else None
            if loss is not None:
                losses[boards[k].turn].append(loss)
            rows.append(loss)
        acpl = {c: (sum(v) / len(v) if v else 0.0) for c, v in losses.items()}
        return dict(boards=boards, loss=rows, acpl=acpl)

    # ---- gravação: PGN + dataset ----
    def save(self, res, start, moves, info):
        game = chess.pgn.Game()
        h = game.headers
        h["Event"], h["Site"], h["Date"] = "IA vs IA", "chess_gui", time.strftime("%Y.%m.%d")
        h["Round"], h["White"], h["Black"] = str(res["game"]), res["white"], res["black"]
        h["Result"], h["Termination"] = res["result"], res["reason"]
        if start.fen() != chess.STARTING_FEN:
            game.setup(start)
        node = game
        for k, m in enumerate(moves):
            node = node.add_variation(m)
            if info:
                ev = self.an.cache.get(info["boards"][k + 1].fen())
                if ev:
                    node.comment = f"[%eval #{ev[4]}]" if ev[4] else f"[%eval {ev[0] / 100:.2f}]"
        with open(self.base + ".pgn", "a", encoding="utf-8") as f:
            print(game, file=f, end="\n\n")
        score = {"1-0": 1, "0-1": -1}.get(res["result"], 0)          # do ponto de vista das brancas
        b = start.copy()
        with open(self.base + ".jsonl", "a", encoding="utf-8") as f:
            for k, m in enumerate(moves):
                ev = self.an.cache.get(info["boards"][k].fen()) if info else None
                row = dict(game=res["game"], ply=k, fen=b.fen(), side="w" if b.turn else "b", move=m.uci(),
                           san=b.san(m), result_white=score, white=res["white"], black=res["black"],
                           cp_white=ev[0] if ev else None, mate_white=ev[4] if ev else None,
                           best=ev[1].uci() if ev and ev[1] else None,
                           loss=info["loss"][k] if info else None)
                f.write(json.dumps(row, ensure_ascii=False) + "\n")
                b.push(m)


class SelfPlayWindow(tk.Toplevel):
    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("IA vs IA - treino por partidas automáticas")
        self.geometry("820x640")
        self.uci = {"A": None, "B": None}
        self._last = {}
        self.vars, self.lvl_lbl, self.lvl_spin, self.type_var = {}, {}, {}, {}
        self.shown_game, self.shown_results = 0, 0
        self.saved_auto = None

        cfg = ttk.LabelFrame(self, text="Jogadores")
        cfg.pack(fill="x", padx=10, pady=(10, 4))
        for r, (key, title, default) in enumerate((("A", "IA A", "Stockfish (Elo limitado)"),
                                                   ("B", "IA B", "Minimax própria"))):
            ttk.Label(cfg, text=title + ":").grid(row=r, column=0, padx=6, pady=4, sticky="w")
            tv = tk.StringVar(value=default)
            self.type_var[key] = tv
            cb = app.combo(cfg, textvariable=tv, values=list(SP_TYPES), width=28)
            cb.grid(row=r, column=1, padx=4)
            cb.bind("<<ComboboxSelected>>", lambda e, k=key: self.on_type(k))
            self.lvl_lbl[key] = ttk.Label(cfg, text="")
            self.lvl_lbl[key].grid(row=r, column=2, padx=(10, 2))
            lv = tk.StringVar()
            self.vars[key] = lv
            self.lvl_spin[key] = ttk.Spinbox(cfg, from_=1, to=9, width=6, textvariable=lv)
            self.lvl_spin[key].grid(row=r, column=3)
            self.on_type(key, first=True)

        opt = ttk.LabelFrame(self, text="Partidas")
        opt.pack(fill="x", padx=10, pady=4)
        self.games = tk.StringVar(value="10")
        self.secs = tk.StringVar(value="0.3")
        self.pause = tk.StringVar(value="0.5")
        self.rnd = tk.StringVar(value="4")
        self.maxp = tk.StringVar(value="300")
        self.alt = tk.BooleanVar(value=True)
        self.judge = tk.BooleanVar(value=bool(app.analyzer.path))
        self.from_cur = tk.BooleanVar(value=False)
        items = (("Nº de partidas", self.games, 1, 1000, 1), ("Tempo por lance (s)", self.secs, 0.05, 30, 0.05),
                 ("Pausa entre lances (s)", self.pause, 0, 10, 0.1), ("Lances aleatórios na abertura", self.rnd, 0, 16, 1),
                 ("Limite de lances (plies)", self.maxp, 20, 1000, 10))
        for i, (txt, var, lo, hi, inc) in enumerate(items):
            ttk.Label(opt, text=txt + ":").grid(row=i // 3, column=(i % 3) * 2, padx=(8, 2), pady=3, sticky="e")
            ttk.Spinbox(opt, from_=lo, to=hi, increment=inc, width=6, textvariable=var).grid(
                row=i // 3, column=(i % 3) * 2 + 1, sticky="w")
        ttk.Checkbutton(opt, text="Alternar as cores a cada partida", variable=self.alt).grid(
            row=2, column=0, columnspan=2, padx=8, sticky="w")
        ttk.Checkbutton(opt, text="Julgar cada partida com o Stockfish (grava avaliação)", variable=self.judge).grid(
            row=2, column=2, columnspan=3, padx=8, sticky="w")
        ttk.Checkbutton(opt, text="Começar da posição que está no tabuleiro", variable=self.from_cur).grid(
            row=3, column=0, columnspan=3, padx=8, pady=(0, 4), sticky="w")

        row = ttk.Frame(self)
        row.pack(fill="x", padx=10, pady=4)
        self.b_start = ttk.Button(row, text="Iniciar", command=self.start)
        self.b_start.pack(side="left", padx=(0, 4))
        self.b_pause = ttk.Button(row, text="Pausar", command=self.toggle_pause, state="disabled")
        self.b_pause.pack(side="left", padx=4)
        self.b_stop = ttk.Button(row, text="Parar", command=self.stop, state="disabled")
        self.b_stop.pack(side="left", padx=4)
        ttk.Button(row, text="Abrir pasta dos arquivos", command=self.open_folder).pack(side="right")

        self.score = tk.StringVar(value="Placar: -")
        ttk.Label(self, textvariable=self.score, font=("Arial", 11, "bold")).pack(anchor="w", padx=10, pady=(6, 0))
        self.status = tk.StringVar(value="Pronto. Escolha os jogadores e clique em Iniciar.")
        ttk.Label(self, textvariable=self.status, wraplength=780).pack(anchor="w", padx=10)

        frm = ttk.Frame(self)
        frm.pack(fill="both", expand=True, padx=10, pady=8)
        cols = (("n", "#", 40), ("w", "Brancas", 170), ("b", "Pretas", 170), ("r", "Resultado", 85),
                ("m", "Lances", 60), ("e", "Fim", 115), ("pw", "Perda B", 70), ("pb", "Perda P", 70))
        self.tree = ttk.Treeview(frm, columns=[c[0] for c in cols], show="headings", height=10)
        for c, t, w in cols:
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="center")
        sb = ttk.Scrollbar(frm, command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")
        ttk.Label(self, wraplength=780, justify="left", text=(
            "'Perda' = perda média de centipeões por lance segundo o Stockfish (menor = joga melhor). "
            "Cada série grava um .pgn e um .jsonl (uma linha por posição: FEN, lance, avaliação, perda e resultado) "
            "na pasta selfplay, pronto para usar como dataset de treino.")).pack(anchor="w", padx=10, pady=(0, 8))

        self.protocol("WM_DELETE_WINDOW", self.close)
        app.subwins.append(self)
        self.retheme()
        try:                                              # ao lado do tabuleiro, sem cobri-lo
            x = min(app.winfo_rootx() + app.winfo_width() + 4, max(0, self.winfo_screenwidth() - 830))
            self.geometry(f"+{x}+{max(0, app.winfo_rooty())}")
        except tk.TclError:
            pass
        self.after(150, self.tick)

    def retheme(self):
        self.configure(bg=self.app.pal["bg"])

    # ---- configuração ----
    def on_type(self, key, first=False):
        name = self.type_var[key].get()
        kind, label, default, lo, hi = SP_TYPES[name]
        if kind == "uci":
            p = filedialog.askopenfilename(parent=self, title="Selecione o motor UCI (.exe)")
            if not p:
                if first:
                    self.type_var[key].set(next(iter(SP_TYPES)))
                    return self.on_type(key, True)
                self.type_var[key].set(self._last.get(key, next(iter(SP_TYPES))))
                return
            self.uci[key] = p
        self._last[key] = name
        self.lvl_lbl[key].config(text=label + (":" if label else ""))
        sp = self.lvl_spin[key]
        if label:
            sp.config(state="normal", from_=lo, to=hi, increment=50 if kind == "stockfish" else 1)
            self.vars[key].set(str(default))
        else:
            self.vars[key].set("")
            sp.config(state="disabled")

    def spec(self, key):
        kind = SP_TYPES[self.type_var[key].get()][0]
        try:
            level = int(float(self.vars[key].get() or 0))
        except ValueError:
            level = SP_TYPES[self.type_var[key].get()][2]
        return dict(kind=kind, level=level, path=self.uci[key])

    def num(self, var, lo, hi, default, cast=float):
        try:
            return max(lo, min(hi, cast(float(str(var.get()).replace(",", ".")))))
        except ValueError:
            return default

    # ---- controle ----
    def start(self):
        a = self.app
        if a.sp_active:
            return
        if a.editing:
            messagebox.showinfo("IA vs IA", "Feche o editor de posição antes de iniciar.", parent=self)
            return
        need_sf = any(self.spec(k)["kind"] in ("stockfish", "stockfish_full") for k in "AB")
        if (need_sf or self.judge.get()) and not a.analyzer.path:
            messagebox.showwarning("Stockfish", "Stockfish não encontrado. Use o botão 'Stockfish...' na janela principal "
                                   "ou escolha jogadores que não dependem dele (e desmarque 'Julgar').", parent=self)
            return
        start = a.boards[a.view].copy(stack=False) if self.from_cur.get() else chess.Board()
        if start.is_game_over():
            start = chess.Board()
        cfg = dict(A=self.spec("A"), B=self.spec("B"), start=start,
                   games=self.num(self.games, 1, 1000, 10, int), secs=self.num(self.secs, 0.02, 30, 0.3),
                   pause=self.num(self.pause, 0, 10, 0.5), random_plies=self.num(self.rnd, 0, 16, 4, int),
                   max_plies=self.num(self.maxp, 20, 1000, 300, int), alternate=self.alt.get(),
                   judge=self.judge.get())
        a.analyzer.depth = self.num(a.depth, 6, 22, 12, int)
        self.saved_auto = a.auto.get()
        a.auto.set(False)                    # a análise ao vivo da janela principal competiria por CPU
        a.ai_color, a.ai_result = None, None
        a.mode.set(MODES[0])
        a.sp_runner = SelfPlay(cfg, a.analyzer, SELFPLAY_DIR)
        self.tree.delete(*self.tree.get_children())
        self.shown_game, self.shown_results = 0, 0
        self.b_start.config(state="disabled")
        self.b_pause.config(state="normal", text="Pausar")
        self.b_stop.config(state="normal")
        a.sp_runner.start()

    def toggle_pause(self):
        r = self.app.sp_runner
        if not r:
            return
        if r.go.is_set():
            r.go.clear()
            self.b_pause.config(text="Continuar")
        else:
            r.go.set()
            self.b_pause.config(text="Pausar")

    def stop(self):
        r = self.app.sp_runner
        if r:
            r.stop_ev.set()
            r.go.set()

    def open_folder(self):
        os.makedirs(SELFPLAY_DIR, exist_ok=True)
        try:
            if os.name == "nt":
                os.startfile(SELFPLAY_DIR)
            else:
                subprocess.Popen(["open" if sys.platform == "darwin" else "xdg-open", SELFPLAY_DIR])
        except Exception:
            messagebox.showinfo("Pasta", SELFPLAY_DIR, parent=self)

    def close(self):
        if self.app.sp_active:
            if not messagebox.askyesno("IA vs IA", "Há uma série em andamento. Parar e fechar?", parent=self):
                return
            self.stop()
        if self in self.app.subwins:
            self.app.subwins.remove(self)
        self.app.sp_win = None
        self.destroy()

    # ---- atualização periódica (thread principal) ----
    def tick(self):
        if not self.winfo_exists():
            return
        self.after(120, self.tick)
        a, r = self.app, self.app.sp_runner
        if r is None:
            return
        with r.lock:
            gn, start, moves, results = r.game_no, r.start_board, list(r.moves), list(r.results)
        if gn and gn != self.shown_game:                       # nova partida: reinicia o tabuleiro principal
            a.set_game(start, [])
            a.title(f"IA vs IA - partida {gn}")
            self.shown_game = gn
        if gn and len(moves) > len(a.moves):
            follow = a.view == len(a.moves)
            for m in moves[len(a.moves):]:
                a._push(m)
            if follow:
                a.view = len(a.moves)
            a.refresh()
            if r.cfg["pause"] >= 0.2:                          # em alta velocidade fica em silêncio
                a.announce(a.boards[-1], moves[-1], result=False)
        for res in results[self.shown_results:]:
            f = lambda v: "-" if v is None else f"{v:.0f}"
            self.tree.insert("", "end", values=(res["game"], res["white"], res["black"], res["result"],
                                                res["plies"], res["reason"], f(res["acpl_w"]), f(res["acpl_b"])))
            self.tree.see(self.tree.get_children()[-1])
        self.shown_results = len(results)
        if results:
            pa = sum(x["a_pts"] for x in results)
            n = len(results)
            wa = sum(1 for x in results if x["a_pts"] == 1.0)
            wb = sum(1 for x in results if x["a_pts"] == 0.0)
            p = pa / n
            elo = "diferença de Elo: n/d" if p in (0.0, 1.0) else f"diferença estimada de Elo (A-B): {-400 * math.log10(1 / p - 1):+.0f}"
            self.score.set(f"A ({r.names[0]}): {wa}   B ({r.names[1]}): {wb}   Empates: {n - wa - wb}   -   A marcou {p * 100:.0f}%  ({elo})")
        self.status.set(r.status + (f"   -> arquivos: {r.base}.pgn / .jsonl" if r.base and results else ""))
        if not r.is_alive() and str(self.b_stop.cget("state")) == "normal":
            self.b_start.config(state="normal")
            self.b_pause.config(state="disabled", text="Pausar")
            self.b_stop.config(state="disabled")
            if self.saved_auto is not None:
                a.auto.set(self.saved_auto)
            if r.error:
                messagebox.showerror("IA vs IA", r.error, parent=self)
            a.refresh()


# --------------------------------------------------------------------------
# Sons. Cada situação tem um nome de arquivo. Seus próprios sons: coloque na pasta
# "sons" (ao lado deste .py) com o nome da situação, ex.: sons/mover.wav, sons/xeque.wav...
# Sem arquivo seu, toca um tom simples gerado automaticamente em sons/padrao.
# --------------------------------------------------------------------------
SOUND_DIR = os.path.join(HERE, "sons")
SOUND_EVENTS = {
    "mover": "Peça movida",
    "xeque": "Xeque",
    "invalido": "Lance inválido",
    "promocao": "Promoção de peça",
    "vitoria": "Vitória (por mate, desistência ou tempo)",
    "derrota": "Derrota (por mate, desistência ou tempo)",
}
SOUND_EXTS = (".wav", ".mp3", ".ogg", ".flac")
# (freq inicial, freq final, duração s, volume, forma)  - 0 Hz = silêncio
DEFAULT_TONES = {
    "mover": [("click", 0, 0.07, 0.6)],
    "xeque": [(988, 988, 0.09, 0.5, "sine"), (0, 0, 0.04, 0, "sine"), (988, 988, 0.12, 0.5, "sine")],
    "invalido": [(110, 110, 0.22, 0.3, "square")],
    "promocao": [(523, 523, 0.09, 0.5, "sine"), (659, 659, 0.09, 0.5, "sine"),
                 (784, 784, 0.09, 0.5, "sine"), (1047, 1047, 0.3, 0.5, "sine")],
    "vitoria": [(523, 523, 0.13, 0.5, "sine"), (659, 659, 0.13, 0.5, "sine"),
                (784, 784, 0.13, 0.5, "sine"), (1047, 1047, 0.5, 0.5, "sine")],
    "derrota": [(392, 392, 0.22, 0.5, "sine"), (349, 349, 0.22, 0.5, "sine"),
                (311, 311, 0.22, 0.5, "sine"), (262, 262, 0.55, 0.5, "sine")],
}


def synth_wav(path, segments, rate=22050):
    data, phase = [], 0.0
    rng = random.Random(7)
    for seg in segments:
        if seg[0] == "click":                              # estalo curto de "peça na madeira"
            n = int(rate * seg[2])
            for i in range(n):
                t = i / rate
                v = (rng.uniform(-1, 1) * math.exp(-t * 70) * 0.7 + math.sin(2 * math.pi * 190 * t) * math.exp(-t * 40)) * seg[3]
                data.append(v)
            continue
        f0, f1, dur, vol, shape = seg
        n = int(rate * dur)
        for i in range(n):
            f = f0 + (f1 - f0) * i / max(1, n)
            phase += 2 * math.pi * f / rate
            if f == 0:
                v = 0.0
            else:
                w = math.sin(phase)
                if shape == "square":
                    w = 1.0 if w >= 0 else -1.0
                env = min(1.0, i / (rate * 0.006), (n - i) / (rate * 0.03))   # evita estalos no início/fim
                v = w * vol * max(0.0, env)
            data.append(v)
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(b"".join(struct.pack("<h", int(max(-1, min(1, v)) * 30000)) for v in data))


SOUND_HELP = """SONS
====
Para usar os seus sons, coloque os arquivos nesta pasta com estes nomes
(WAV funciona em qualquer computador; MP3/OGG precisam do pygame:  py -m pip install pygame):

    mover.wav        peça movida
    xeque.wav        xeque
    invalido.wav     lance inválido
    promocao.wav     promoção de peça
    vitoria.wav      vitória (mate, desistência ou tempo a seu favor)
    derrota.wav      derrota (mate, desistência ou tempo contra você)

Sem um arquivo seu, toca o tom simples da pasta 'padrao'. Também dá para escolher
os arquivos pelo botão 'Sons...' do programa (ele copia para esta pasta).
"""


class Sounds:
    def __init__(self, enabled=True):
        self.enabled, self.log, self.note = enabled, [], ""
        self._pg = None
        try:
            os.makedirs(os.path.join(SOUND_DIR, "padrao"), exist_ok=True)
            for ev, segs in DEFAULT_TONES.items():
                p = os.path.join(SOUND_DIR, "padrao", ev + ".wav")
                if not os.path.isfile(p):
                    synth_wav(p, segs)
            readme = os.path.join(SOUND_DIR, "LEIA-ME.txt")
            if not os.path.isfile(readme):
                with open(readme, "w", encoding="utf-8") as f:
                    f.write(SOUND_HELP)
        except OSError as e:
            self.note = f"Não foi possível criar a pasta de sons: {e}"

    def custom(self, ev):
        for ext in SOUND_EXTS:
            p = os.path.join(SOUND_DIR, ev + ext)
            if os.path.isfile(p):
                return p
        return None

    def find(self, ev):
        return self.custom(ev) or os.path.join(SOUND_DIR, "padrao", ev + ".wav")

    def pygame(self):
        if self._pg is None:
            try:
                os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
                import pygame
                pygame.mixer.init()
                self._pg = pygame
            except Exception:
                self._pg = False
        return self._pg

    def can_play_ext(self, ext):
        ext = ext.lower()
        if ext == ".wav" and (os.name == "nt" or sys.platform == "darwin" or shutil.which("paplay") or shutil.which("aplay")):
            return True
        return bool(self.pygame())

    def play(self, ev, force=False):
        if not (self.enabled or force):
            return
        self.log.append(ev)
        try:
            self._play_file(self.find(ev))
        except Exception as e:                              # som nunca pode derrubar o jogo
            self.note = f"Falha ao tocar '{ev}': {e}"

    def _play_file(self, p):
        ext = os.path.splitext(p)[1].lower()
        if ext == ".wav" and os.name == "nt":
            import winsound
            winsound.PlaySound(p, winsound.SND_FILENAME | winsound.SND_ASYNC)
            return
        if ext != ".wav" or sys.platform not in ("darwin",) and not (shutil.which("paplay") or shutil.which("aplay")):
            pg = self.pygame()
            if pg:
                pg.mixer.Sound(p).play()
                return
            if ext != ".wav":
                self.note = f"Para tocar {ext} instale o pygame (py -m pip install pygame) ou use WAV."
                return
        for cmd in (["afplay", p], ["paplay", p], ["aplay", "-q", p],
                    ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet", p]):
            if shutil.which(cmd[0]):
                subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                return
        self.note = "Nenhum player de áudio encontrado neste sistema."


class SoundWindow(tk.Toplevel):
    def __init__(self, app):
        super().__init__(app)
        self.app, self.snd = app, app.sounds
        self.title("Sons do jogo")
        self.resizable(False, False)
        self.on = tk.BooleanVar(value=self.snd.enabled)
        ttk.Checkbutton(self, text="Ativar sons", variable=self.on, command=self.toggle).grid(
            row=0, column=0, columnspan=4, sticky="w", padx=10, pady=(10, 4))
        self.lbls = {}
        for r, (ev, label) in enumerate(SOUND_EVENTS.items(), start=1):
            ttk.Label(self, text=label).grid(row=r, column=0, sticky="w", padx=(10, 6), pady=2)
            ttk.Button(self, text="Testar", width=8, command=lambda e=ev: self.snd.play(e, True)).grid(row=r, column=1, padx=2)
            ttk.Button(self, text="Escolher arquivo...", command=lambda e=ev: self.choose(e)).grid(row=r, column=2, padx=2)
            ttk.Button(self, text="Padrão", width=8, command=lambda e=ev: self.reset(e)).grid(row=r, column=3, padx=(2, 10))
            self.lbls[ev] = ttk.Label(self, text="", width=28)
            self.lbls[ev].grid(row=r, column=4, sticky="w", padx=(0, 10))
        n = len(SOUND_EVENTS) + 1
        ttk.Button(self, text="Testar todos em sequência", command=self.test_all).grid(
            row=n, column=0, columnspan=2, sticky="w", padx=10, pady=8)
        ttk.Button(self, text="Abrir pasta de sons", command=self.open_folder).grid(
            row=n, column=2, columnspan=2, sticky="w", pady=8)
        self.info = ttk.Label(self, wraplength=560, justify="left", text=(
            "Seus arquivos: pasta 'sons' com os nomes mover.wav, xeque.wav, invalido.wav, promocao.wav, "
            "vitoria.wav e derrota.wav (WAV em qualquer PC; MP3/OGG exigem pygame). "
            "Xeque-mate e desistência usam vitória ou derrota."))
        self.info.grid(row=n + 1, column=0, columnspan=5, sticky="w", padx=10, pady=(0, 10))
        self.protocol("WM_DELETE_WINDOW", self.close)
        app.subwins.append(self)
        self.retheme()
        self.refresh_names()

    def retheme(self):
        self.configure(bg=self.app.pal["bg"])

    def refresh_names(self):
        for ev, lb in self.lbls.items():
            c = self.snd.custom(ev)
            lb.config(text=os.path.basename(c) if c else "tom padrão")

    def toggle(self):
        self.snd.enabled = self.on.get()
        save_cfg(sound=self.snd.enabled)

    def choose(self, ev):
        p = filedialog.askopenfilename(parent=self, title=f"Som para: {SOUND_EVENTS[ev]}",
                                       filetypes=[("Áudio", "*.wav *.mp3 *.ogg *.flac"), ("Todos", "*.*")])
        if not p:
            return
        ext = os.path.splitext(p)[1].lower()
        if ext not in SOUND_EXTS or not self.snd.can_play_ext(ext):
            messagebox.showwarning("Formato", "Este formato não toca aqui. Use WAV, ou instale o pygame "
                                   "(py -m pip install pygame) para MP3/OGG/FLAC.", parent=self)
            return
        self.reset(ev, refresh=False)
        try:
            os.makedirs(SOUND_DIR, exist_ok=True)
            shutil.copyfile(p, os.path.join(SOUND_DIR, ev + ext))
        except OSError as e:
            messagebox.showerror("Sons", str(e), parent=self)
        self.refresh_names()
        self.snd.play(ev, True)

    def reset(self, ev, refresh=True):
        for ext in SOUND_EXTS:
            try:
                os.remove(os.path.join(SOUND_DIR, ev + ext))
            except OSError:
                pass
        if refresh:
            self.refresh_names()

    def test_all(self):
        for i, ev in enumerate(SOUND_EVENTS):
            self.after(i * 900, lambda e=ev: self.snd.play(e, True))

    def open_folder(self):
        os.makedirs(SOUND_DIR, exist_ok=True)
        try:
            if os.name == "nt":
                os.startfile(SOUND_DIR)
            else:
                subprocess.Popen(["open" if sys.platform == "darwin" else "xdg-open", SOUND_DIR])
        except Exception:
            messagebox.showinfo("Pasta", SOUND_DIR, parent=self)

    def close(self):
        if self in self.app.subwins:
            self.app.subwins.remove(self)
        self.app.snd_win = None
        self.destroy()


# --------------------------------------------------------------------------
# Relatório da partida: classificação dos lances + "precisão" (modelo do Lichess,
# muito parecido com o CAPS do chess.com: o número exato do chess.com pode diferir).
# --------------------------------------------------------------------------
def move_accuracy(wp_before, wp_after):
    """Precisão (0-100) de um lance, a partir da queda da chance de vitória (em %) de quem jogou."""
    d = wp_before - wp_after
    return max(0.0, min(100.0, 103.1668100711649 * math.exp(-0.04354415386753951 * d) - 3.166924740191411 + 1.0))


def build_report(boards, moves, cache, cls_of):
    """Dados do relatório. cls_of(k) devolve a chave de CLASSES do lance k (ou None)."""
    n = len(moves)
    evs = [cache.get(b.fen()) for b in boards]
    wps = [None if e is None else 100 / (1 + math.exp(-0.00368208 * e[0])) for e in evs]   # chance das brancas (%)
    rep = dict(n=n, have=sum(1 for e in evs if e), total=len(boards), wps=wps,
               counts={True: dict.fromkeys(CLASS_ORDER, 0), False: dict.fromkeys(CLASS_ORDER, 0)},
               moves=[], acc={True: None, False: None})
    rep["complete"] = rep["have"] == rep["total"]
    ws = max(2, min(8, n // 10))
    vals = {True: [], False: []}
    for k in range(n):
        color = boards[k].turn
        key = cls_of(k)
        info = dict(k=k, key=key, color=color, san=boards[k].san(moves[k]), best=None, acc=None)
        if key:
            rep["counts"][color][key] += 1
            e = evs[k]
            if e and e[1] and e[1] != moves[k]:
                info["best"] = boards[k].san(e[1])
        if wps[k] is not None and wps[k + 1] is not None:
            sg = 1 if color else -1
            before = wps[k] if sg == 1 else 100 - wps[k]
            after = wps[k + 1] if sg == 1 else 100 - wps[k + 1]
            info["acc"] = move_accuracy(before, after)
            window = [w for w in wps[max(0, k - (ws - 2)):max(0, k - (ws - 2)) + ws] if w is not None]
            sd = statistics.pstdev(window) if len(window) > 1 else 0.0
            vals[color].append((info["acc"], max(0.5, min(12.0, sd))))
        rep["moves"].append(info)
    for color, lst in vals.items():
        if lst:
            wmean = sum(a * w for a, w in lst) / sum(w for _, w in lst)
            hmean = len(lst) / sum(1 / max(a, 0.1) for a, _ in lst)
            rep["acc"][color] = (wmean + hmean) / 2
    return rep


class GameReport(tk.Toplevel):
    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("Relatório da partida")
        self.geometry("700x780")
        self.rep, self._sig = None, None
        self.show_inacc = tk.BooleanVar(value=False)

        self.head = ttk.Label(self, font=("Arial", 14, "bold"))
        self.head.pack(anchor="w", padx=12, pady=(10, 0))
        self.sub = ttk.Label(self)
        self.sub.pack(anchor="w", padx=12)

        acc = ttk.Frame(self)
        acc.pack(fill="x", padx=12, pady=(8, 4))
        self.acc_lbl = {}
        for col, color in enumerate((True, False)):
            f = ttk.Frame(acc)
            f.grid(row=0, column=col, sticky="ew", padx=(0, 20))
            acc.columnconfigure(col, weight=1)
            nm = ttk.Label(f, font=("Arial", 10, "bold"))
            nm.pack(anchor="w")
            big = ttk.Label(f, font=("Arial", 26, "bold"))
            big.pack(anchor="w")
            ttk.Label(f, text="Precisão").pack(anchor="w")
            self.acc_lbl[color] = (nm, big)

        self.chart = tk.Canvas(self, width=660, height=110, highlightthickness=0, cursor="hand2")
        self.chart.pack(padx=12, pady=6)
        self.chart.bind("<Button-1>", self.on_chart)

        tbl = ttk.Frame(self)
        tbl.pack(fill="x", padx=12)
        self.cnt = {}
        ttk.Label(tbl, text="Brancas", font=("Arial", 9, "bold")).grid(row=0, column=2, padx=14)
        ttk.Label(tbl, text="Pretas", font=("Arial", 9, "bold")).grid(row=0, column=3, padx=14)
        self.badges = []
        for r, key in enumerate(CLASS_ORDER, start=1):
            cv = tk.Canvas(tbl, width=20, height=20, highlightthickness=0)
            cv.grid(row=r, column=0, padx=(0, 4), pady=1)
            self.badges.append((cv, key))
            ttk.Label(tbl, text=CLASSES[key][0], width=16).grid(row=r, column=1, sticky="w")
            lw, lb = ttk.Label(tbl, text="0", anchor="center", width=6), ttk.Label(tbl, text="0", anchor="center", width=6)
            lw.grid(row=r, column=2)
            lb.grid(row=r, column=3)
            self.cnt[key] = (lw, lb)

        top = ttk.Frame(self)
        top.pack(fill="x", padx=12, pady=(10, 2))
        ttk.Label(top, text="Lances de destaque (clique para ver no tabuleiro)", font=("Arial", 10, "bold")).pack(side="left")
        ttk.Checkbutton(top, text="incluir imprecisões", variable=self.show_inacc,
                        command=lambda: self.refresh(True)).pack(side="right")
        frm = ttk.Frame(self)
        frm.pack(fill="both", expand=True, padx=12)
        self.tree = ttk.Treeview(frm, columns=("n", "lance", "classe", "quem", "melhor"), show="headings",
                                 height=8, selectmode="browse")
        for c, t, w in (("n", "#", 50), ("lance", "Lance", 80), ("classe", "Classificação", 130),
                        ("quem", "Quem", 130), ("melhor", "Melhor era", 90)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="center")
        sb = ttk.Scrollbar(frm, command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_pick)

        row = ttk.Frame(self)
        row.pack(fill="x", padx=12, pady=8)
        self.b_an = ttk.Button(row, text="Analisar partida", command=lambda: app.start_analysis(True))
        self.b_an.pack(side="left")
        ttk.Button(row, text="Exportar...", command=self.export).pack(side="left", padx=6)
        ttk.Button(row, text="Fechar", command=self.close).pack(side="right")

        self.protocol("WM_DELETE_WINDOW", self.close)
        app.subwins.append(self)
        self.retheme()
        self.refresh(True)
        self.after(600, self.tick)

    # ---- tema / ciclo ----
    def retheme(self):
        p = self.app.pal
        self.configure(bg=p["bg"])
        self.chart.configure(bg=p["bg"])
        for key, (_, _, col, _) in CLASSES.items():
            self.tree.tag_configure(key, foreground=col if p["dark"] else mix(col, "#000000", 0.35))
        for cv, key in self.badges:
            cv.configure(bg=p["bg"])
            cv.delete("all")
            paint_badge(cv, 10, 10, 8, key)
        if self.rep:
            self.refresh(True)

    def tick(self):
        if not self.winfo_exists():
            return
        self.after(700, self.tick)
        self.refresh()

    def close(self):
        if self in self.app.subwins:
            self.app.subwins.remove(self)
        self.app.report_win = None
        self.destroy()

    def side(self, color):
        a = self.app
        s = "Brancas" if color else "Pretas"
        if a.ai_color is not None:
            s += " (IA)" if color == a.ai_color else " (você)"
        return s

    def result_line(self):
        a = self.app
        if a.resigned is not None:
            return a.resign_text()
        if a.drawn:
            return "Empate por acordo"
        if a.clock.flag is not None:
            return a.time_result()
        return result_text(a.boards[-1]) or "Partida em andamento"

    # ---- conteúdo ----
    def refresh(self, force=False):
        a = self.app
        rep = build_report(a.boards, a.moves, a.analyzer.cache, a.move_class)
        sig = (rep["have"], rep["n"], a.game_id, self.show_inacc.get(), a.ui_theme)
        if sig == self._sig and not force:
            return
        self._sig, self.rep = sig, rep
        self.head.config(text="Relatório da partida")
        prog = "" if rep["complete"] else f"   -   analisando... {rep['have']}/{rep['total']} posições" if a.analyzer.running \
            else f"   -   análise incompleta ({rep['have']}/{rep['total']} posições)"
        self.sub.config(text=f"{self.result_line()}   -   {rep['n']} lances{prog}")
        self.b_an.config(state="disabled" if (rep["complete"] or a.analyzer.running) else "normal")
        for color, (nm, big) in self.acc_lbl.items():
            v = rep["acc"][color]
            nm.config(text=self.side(color))
            big.config(text="-" if v is None else f"{v:.1f}%".replace(".", ","),
                       foreground="#81b64c" if (v or 0) >= 85 else "#c9a227" if (v or 0) >= 70 else "#e58f2a" if (v or 0) >= 50 else "#ca3431")
        for key, (lw, lb) in self.cnt.items():
            lw.config(text=str(rep["counts"][True][key]))
            lb.config(text=str(rep["counts"][False][key]))
        self.tree.delete(*self.tree.get_children())
        wanted = {"brilliant", "great", "mistake", "blunder"} | ({"inaccuracy"} if self.show_inacc.get() else set())
        a0 = a.start.fullmove_number
        off = 1 if a.start.turn == chess.BLACK else 0
        for m in rep["moves"]:
            if m["key"] in wanted:
                num = a0 + (m["k"] + off) // 2
                self.tree.insert("", "end", iid=str(m["k"]), tags=(m["key"],),
                                 values=(f"{num}{'.' if m['color'] else '...'}", m["san"], CLASSES[m["key"]][0],
                                         self.side(m["color"]), m["best"] or ""))
        self.draw_chart(rep)

    def draw_chart(self, rep):
        c = self.chart
        c.delete("all")
        W, H, mg = int(c["width"]), int(c["height"]), 6
        wps = rep["wps"]
        n = len(wps)
        if n < 2:
            return
        xs = [mg + i * (W - 2 * mg) / (n - 1) for i in range(n)]
        known = [(xs[i], H * (1 - v / 100)) for i, v in enumerate(wps) if v is not None]
        c.create_rectangle(0, 0, W, H, fill="#2b2b2b", outline="")
        if len(known) >= 2:
            poly = [known[0][0], H] + [v for p in known for v in p] + [known[-1][0], H]
            c.create_polygon(poly, fill="#f2f2f2", outline="")
            c.create_line([v for p in known for v in p], fill="#9a9a9a", width=1)
        c.create_line(0, H / 2, W, H / 2, fill="#8a8a8a", dash=(3, 3))
        for m in rep["moves"]:
            if m["key"] in ("brilliant", "great", "mistake", "blunder") and wps[m["k"] + 1] is not None:
                x, y = xs[m["k"] + 1], H * (1 - wps[m["k"] + 1] / 100)
                col = CLASSES[m["key"]][2]
                c.create_oval(x - 4, y - 4, x + 4, y + 4, fill=col, outline="#ffffff")
        self._xs = xs

    def on_chart(self, e):
        xs = getattr(self, "_xs", None)
        if xs:
            self.app.go(min(range(len(xs)), key=lambda i: abs(xs[i] - e.x)))

    def on_pick(self, e):
        sel = self.tree.selection()
        if sel:
            self.app.go(int(sel[0]) + 1)

    def export(self):
        a, rep = self.app, self.rep
        p = filedialog.asksaveasfilename(parent=self, defaultextension=".txt", filetypes=[("Texto", "*.txt")],
                                         initialfile="relatorio_partida.txt")
        if not p:
            return
        L = ["RELATÓRIO DA PARTIDA", self.result_line(), f"{rep['n']} lances", ""]
        for color in (True, False):
            v = rep["acc"][color]
            L.append(f"{self.side(color)}: precisão {'-' if v is None else f'{v:.1f}%'}")
        L.append("")
        L.append(f"{'Classificação':16}{'Brancas':>9}{'Pretas':>9}")
        for key in CLASS_ORDER:
            L.append(f"{CLASSES[key][0]:16}{rep['counts'][True][key]:>9}{rep['counts'][False][key]:>9}")
        L += ["", "LANCES DE DESTAQUE"]
        a0, off = a.start.fullmove_number, (1 if a.start.turn == chess.BLACK else 0)
        for m in rep["moves"]:
            if m["key"] in ("brilliant", "great", "mistake", "blunder", "inaccuracy"):
                num = a0 + (m["k"] + off) // 2
                L.append(f"{num}{'.' if m['color'] else '...'} {m['san']}  {CLASSES[m['key']][0]}  ({self.side(m['color'])})"
                         + (f"  melhor era {m['best']}" if m["best"] else ""))
        try:
            with open(p, "w", encoding="utf-8") as f:
                f.write("\n".join(L) + "\n")
        except OSError as err:
            messagebox.showerror("Exportar", str(err), parent=self)


# --------------------------------------------------------------------------
# Lobby estilo Lichess (escolha de modo, tempo, cor e força da IA) e utilidades do painel
# --------------------------------------------------------------------------
GREEN, GREEN_HOVER = "#81b64c", "#6fa03e"          # botão principal (verde do chess.com)
GLYPH = {chess.QUEEN: "♛", chess.ROOK: "♜", chess.BISHOP: "♝", chess.KNIGHT: "♞", chess.PAWN: "♟"}
PVAL = {chess.QUEEN: 9, chess.ROOK: 5, chess.BISHOP: 3, chess.KNIGHT: 3, chess.PAWN: 1}
PSTART = {chess.QUEEN: 1, chess.ROOK: 2, chess.BISHOP: 2, chess.KNIGHT: 2, chess.PAWN: 8}
TIME_TILES = (("1 min", "1+0"), ("2+1", "2+1"), ("3 min", "3+0"), ("3+2", "3+2"), ("5 min", "5+0"), ("5+3", "5+3"),
              ("10 min", "10+0"), ("10+5", "10+5"), ("15+10", "15+10"), ("30 min", "30+0"),
              ("Sem relógio", "∞"), ("Personalizado...", "Outro"))
LOBBY_DEFAULT = dict(vs_ai=True, color="white", elo=1500, clock="Sem relógio", custom=[300, 0])


def captured_info(b):
    """Peças que cada lado já capturou (texto) e o saldo de material (brancas - pretas)."""
    cap, score = {chess.WHITE: "", chess.BLACK: ""}, {chess.WHITE: 0, chess.BLACK: 0}
    for color in (chess.WHITE, chess.BLACK):
        for pt, n0 in PSTART.items():
            have = len(b.pieces(pt, color))
            score[color] += PVAL[pt] * have
            cap[not color] += GLYPH[pt] * max(0, n0 - have)
    return cap, score[chess.WHITE] - score[chess.BLACK]


def time_category(ccfg):
    """Categoria como no Lichess: tempo estimado = base + 40 x incremento."""
    if not ccfg or ccfg == "custom":
        return "Sem limite"
    est = ccfg[0] + 40 * ccfg[1]
    return "Bullet" if est < 180 else "Blitz" if est < 480 else "Rápida" if est < 1500 else "Clássica"


def elo_label(e):
    for lim, name in ((600, "Iniciante"), (1000, "Fácil"), (1400, "Intermediário"), (1800, "Avançado"),
                      (2200, "Forte"), (2600, "Mestre"), (10 ** 9, "Super GM")):
        if e < lim:
            return name


class Tiles:
    """Grade de botões-cartão (como as opções de tempo do Lichess). O valor escolhido fica numa StringVar."""

    def __init__(self, parent, app, items, var, cols, command=None):
        self.app, self.var, self.cmd, self.cells = app, var, command, {}
        self.frame = tk.Frame(parent)
        for i, (val, title, sub) in enumerate(items):
            f = tk.Frame(self.frame, cursor="hand2")
            f.grid(row=i // cols, column=i % cols, sticky="nsew", padx=2, pady=2)
            t = tk.Label(f, text=title, font=("Arial", 13, "bold"))
            t.pack(fill="x", pady=(8, 0))
            sl = tk.Label(f, text=sub, font=("Arial", 8))
            sl.pack(fill="x", pady=(0, 7))
            for w in (f, t, sl):
                w.bind("<Button-1>", lambda e, v=val: self.pick(v))
            self.cells[val] = (f, t, sl)
        for c in range(cols):
            self.frame.columnconfigure(c, weight=1, uniform="tile")
        self.paint()

    def pick(self, v):
        self.var.set(v)
        self.paint()
        if self.cmd:
            self.cmd(v)

    def paint(self):
        p = self.app.pal
        self.frame.configure(bg=p["bg"])
        for val, (f, t, sl) in self.cells.items():
            on = self.var.get() == val
            bg, fg = (p["sel"], p["sel_fg"]) if on else (p["btn"], p["fg"])
            f.configure(bg=bg)
            t.configure(bg=bg, fg=fg)
            sl.configure(bg=bg, fg=fg if on else p["muted"])


class LobbyPanel(tk.Frame):
    """Painel 'Criar partida': adversário (IA ou 2 jogadores), tempo, cor e força da IA."""

    def __init__(self, parent, app, on_start):
        super().__init__(parent)
        self.app, self.on_start, self.muted = app, on_start, []
        lob = dict(LOBBY_DEFAULT)
        saved = load_cfg().get("lobby")
        if isinstance(saved, dict):
            lob.update({k: v for k, v in saved.items() if k in lob})
        if lob["clock"] not in CLOCK_PRESETS:
            lob["clock"] = "Sem relógio"
        c = lob["custom"] if isinstance(lob["custom"], list) and len(lob["custom"]) == 2 else [300, 0]
        self.kind = tk.StringVar(value="ia" if lob["vs_ai"] else "2p")
        self.color = tk.StringVar(value=lob["color"] if lob["color"] in ("white", "black", "random") else "white")
        self.time = tk.StringVar(value=lob["clock"])
        try:
            e0 = max(ELO_MIN, min(ELO_MAX, int(lob["elo"])))
        except (TypeError, ValueError):
            e0 = 1500
        self.elo = tk.IntVar(value=e0)
        self.cmin = tk.StringVar(value=f"{c[0] / 60:g}")
        self.cinc = tk.StringVar(value=str(int(c[1])))

        self.head("Criar uma partida", big=True)
        self.head("Adversário")
        self.t_kind = Tiles(self, app, (("ia", "Contra a IA", "Stockfish"), ("2p", "2 jogadores", "mesmo computador")),
                            self.kind, 2, lambda v: self.update_vis())
        self.t_kind.frame.pack(fill="x")
        self.head("Controle de tempo")
        items = [(n, lbl, time_category(CLOCK_PRESETS[n]) if CLOCK_PRESETS[n] != "custom" else "Personalizado")
                 for n, lbl in TIME_TILES]
        items[10] = ("Sem relógio", "∞", "Sem limite")
        self.t_time = Tiles(self, app, items, self.time, 4, lambda v: self.update_vis())
        self.t_time.frame.pack(fill="x")
        self.custom = tk.Frame(self)
        tk.Label(self.custom, text="Minutos:").pack(side="left")
        ttk.Spinbox(self.custom, from_=0.5, to=180, increment=0.5, width=5, textvariable=self.cmin).pack(side="left", padx=4)
        tk.Label(self.custom, text="Incremento (s):").pack(side="left", padx=(8, 0))
        ttk.Spinbox(self.custom, from_=0, to=60, width=4, textvariable=self.cinc).pack(side="left", padx=4)

        self.ai_box = tk.Frame(self)
        row = tk.Frame(self.ai_box)
        row.pack(fill="x")
        self.head("Força da IA", parent=row, side="left")
        self.elo_lbl = tk.Label(row, font=("Arial", 10, "bold"))
        self.elo_lbl.pack(side="right")
        ttk.Scale(self.ai_box, from_=ELO_MIN, to=ELO_MAX, variable=self.elo, command=self.on_elo).pack(fill="x", pady=(2, 0))
        self.color_box = tk.Frame(self)
        self.head("Jogar de", parent=self.color_box)
        self.t_color = Tiles(self.color_box, app, (("white", "Brancas", "jogam primeiro"), ("random", "Aleatório", "sorteio"),
                                                   ("black", "Pretas", "jogam depois")), self.color, 3)
        self.t_color.frame.pack(fill="x")
        self.warn = tk.Label(self, fg="#c0392b", wraplength=300, justify="left", font=("Arial", 9))
        self.go_btn = tk.Button(self, text="Jogar", font=("Arial", 14, "bold"), bg=GREEN, fg="#ffffff", relief="flat",
                                activebackground=GREEN_HOVER, activeforeground="#ffffff", cursor="hand2",
                                command=self.start, pady=8, bd=0)
        self.go_btn.bind("<Enter>", lambda e: self.go_btn.configure(bg=GREEN_HOVER))
        self.go_btn.bind("<Leave>", lambda e: self.go_btn.configure(bg=GREEN))
        self.update_vis()
        self.retheme()

    def head(self, text, big=False, parent=None, side=None):
        lb = tk.Label(parent or self, text=text, anchor="w", font=("Arial", 14, "bold") if big else ("Arial", 9, "bold"))
        if side:
            lb.pack(side=side)
        else:
            lb.pack(fill="x", pady=(0, 6) if big else (10, 3))
        if not big:
            self.muted.append(lb)
        return lb

    def on_elo(self, *_):
        v = int(round(self.elo.get() / 50.0) * 50)
        v = max(ELO_MIN, min(ELO_MAX, v))
        self.elo.set(v)
        self.elo_lbl.configure(text=f"{v}  ({elo_label(v)})")

    def update_vis(self):
        for w in (self.custom, self.ai_box, self.color_box, self.warn, self.go_btn):
            w.pack_forget()
        if self.time.get() == "Personalizado...":
            self.custom.pack(fill="x", pady=(6, 0))
        if self.kind.get() == "ia":
            self.ai_box.pack(fill="x", pady=(10, 0))
            self.color_box.pack(fill="x")
            if not self.app.analyzer.path:
                self.warn.configure(text="Stockfish não configurado: ao clicar em Jogar você poderá escolher o executável.")
                self.warn.pack(fill="x", pady=(8, 0))
        self.go_btn.pack(fill="x", pady=(14, 0))
        self.on_elo()

    def start(self):
        app = self.app
        vs_ai = self.kind.get() == "ia"
        if vs_ai and not app.analyzer.path:
            if messagebox.askyesno("Stockfish", "Para jogar contra a IA é preciso indicar o executável do Stockfish.\n"
                                                "Escolher agora?", parent=self.winfo_toplevel()):
                app.pick_engine()
            if not app.analyzer.path:
                return
        try:
            m = float(self.cmin.get().replace(",", "."))
            inc = int(float(self.cinc.get().replace(",", ".")))
            if not (0.5 <= m <= 180 and 0 <= inc <= 60):
                raise ValueError
        except ValueError:
            if self.time.get() == "Personalizado...":
                messagebox.showinfo("Tempo personalizado", "Use de 0,5 a 180 minutos e incremento de 0 a 60 s.",
                                    parent=self.winfo_toplevel())
                return
            m, inc = 5, 0
        self.on_start(dict(vs_ai=vs_ai, color=self.color.get(), elo=int(self.elo.get()), clock=self.time.get(),
                           custom=[int(m * 60), inc]))

    def retheme(self):
        p = self.app.pal

        def walk(w):
            for ch in w.winfo_children():
                if type(ch) in (tk.Frame, tk.Label):
                    ch.configure(bg=p["bg"])
                    if type(ch) is tk.Label:
                        ch.configure(fg=p["fg"])
                walk(ch)
        self.configure(bg=p["bg"])
        walk(self)
        for lb in self.muted:
            lb.configure(fg=p["muted"])
        self.warn.configure(bg=p["bg"])
        self.t_kind.paint()
        self.t_time.paint()
        self.t_color.paint()


class LobbyDialog(tk.Toplevel):
    """Janela modal com o lobby, aberta ao iniciar o programa e em Partida > Nova partida."""

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("Nova partida")
        self.resizable(False, False)
        self.transient(app)
        self.panel = LobbyPanel(self, app, self.go)
        self.panel.pack(padx=18, pady=14)
        app.subwins.append(self)
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.bind("<Escape>", lambda e: self.close())
        self.update_idletasks()
        x = app.winfo_rootx() + (app.winfo_width() - self.winfo_reqwidth()) // 2
        y = app.winfo_rooty() + max(20, (app.winfo_height() - self.winfo_reqheight()) // 2)
        self.geometry(f"+{max(0, x)}+{max(0, y)}")
        self.configure(bg=app.pal["bg"])
        self.grab_set()

    def retheme(self):
        self.configure(bg=self.app.pal["bg"])
        self.panel.retheme()

    def go(self, opts):
        self.close()
        self.app.start_match(opts)

    def close(self):
        if self in self.app.subwins:
            self.app.subwins.remove(self)
        self.app.lobby_win = None
        self.destroy()



class App(tk.Tk):
    hide_sq = None        # casa da peça que está sendo arrastada
    drag = None
    editing, editor, edit_board, _edit_last, _pre_paused = False, None, None, None, False
    sp_runner, sp_win, snd_win, resigned = None, None, None, None
    report_win, _report_gid, premove = None, None, None
    drawn, lobby_win, cur_tab = False, None, "play"

    @property
    def sp_active(self):
        return bool(self.sp_runner and self.sp_runner.is_alive())

    def sp_block(self):
        """True (e avisa) se uma série IA vs IA está rodando."""
        if self.sp_active:
            messagebox.showinfo("IA vs IA", "Há uma série IA vs IA em andamento. Pare-a primeiro (janela 'IA vs IA').")
            return True
        return False
    RB = 2 if sys.platform == "darwin" else 3          # botão direito (no macOS é o Button-2)

    def __init__(self):
        super().__init__()
        self.title("Xadrez + Stockfish")
        self.sq = max(48, min(80, (self.winfo_screenheight() - 330) // 8))
        S = self.sq
        cfg = load_cfg()
        self.sounds = Sounds(cfg.get("sound", True) is not False)
        self.analyzer, self.clock = Analyzer(), Clock()
        self.flipped, self.sel, self._seen = False, None, None
        self.ai_color, self.ai_busy, self.ai_result = None, False, None
        self._cls, self.skins, self.skin, self.board_skin = {}, {}, None, None
        self.light, self.dark = BOARD_THEMES[DEFAULT_THEME]
        self.arrows, self.marks, self._drag = {}, {}, None
        self.combos, self.subwins, self.log = [], [], None
        self.game_id, self._flag_shown, self.clock_name = 0, False, "Sem relógio"
        self.pal, self.ui_theme = PALETTES["Claro"], "Claro"
        self.set_game(chess.Board(), [])

        self.build_menu()
        self.mode = tk.StringVar(value=MODES[0])
        self.elo = tk.StringVar(value="1500")
        self.ai_pause = tk.StringVar(value="2")
        self.clock_var = tk.StringVar(value="Sem relógio")
        self.auto = tk.BooleanVar(value=bool(self.analyzer.path))
        self.depth = tk.StringVar(value="12")
        self.report_auto = tk.BooleanVar(value=cfg.get("report", True) is not False)
        self.lobby_auto = tk.BooleanVar(value=cfg.get("lobby_start", True) is not False)
        self.piece_var = tk.StringVar(value=VECTOR)
        self.board_var = tk.StringVar(value=DEFAULT_THEME)
        self.ui_var = tk.StringVar(value="Claro")
        self.eval_var, self.line_var, self.nav_var = tk.StringVar(), tk.StringVar(), tk.StringVar()
        self.status = tk.StringVar()

        body = ttk.Frame(self)
        body.pack(fill="both", expand=True, padx=8, pady=(6, 0))
        self.evalbar = tk.Canvas(body, width=32, height=8 * S, highlightthickness=0)
        self.evalbar.grid(row=1, column=0)
        self.strip_top = self.make_strip(body)
        self.strip_top[0].grid(row=0, column=1, padx=8, pady=(0, 3))
        self.canvas = tk.Canvas(body, width=8 * S, height=8 * S, highlightthickness=0)
        self.canvas.grid(row=1, column=1, padx=8)
        self.strip_bottom = self.make_strip(body)
        self.strip_bottom[0].grid(row=2, column=1, padx=8, pady=(3, 0))
        side = tk.Frame(body, width=350, height=8 * S + 76)
        side.grid(row=0, column=2, rowspan=3, sticky="ns")
        side.pack_propagate(False)
        self.build_side(side, S)
        self.plain = [side] + self.plain
        ttk.Label(self, textvariable=self.status, anchor="w").pack(fill="x", padx=8, pady=4)

        self.canvas.bind("<ButtonPress-1>", self.on_press)
        self.canvas.bind("<B1-Motion>", self.on_motion)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        for ev in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.canvas.bind(ev, self.on_wheel)
        self.canvas.bind(f"<ButtonPress-{self.RB}>", self.arrow_press)
        self.canvas.bind(f"<B{self.RB}-Motion>", self.arrow_motion)
        self.canvas.bind(f"<ButtonRelease-{self.RB}>", self.arrow_release)
        self.tree.bind("<Button-1>", self.on_table_click)
        self.bind_all("<Left>", lambda e: self.go(self.view - 1))
        self.bind_all("<Right>", lambda e: self.go(self.view + 1))
        self.bind_all("<Home>", lambda e: self.go(0))
        self.bind_all("<End>", lambda e: self.go(len(self.moves)))
        self.bind_all("<Escape>", lambda e: self.cancel_premove())

        ensure_default_skin()
        self.rescan_skins()
        if "skin" not in cfg and DEFAULT_SKIN in self.skins and self.skins[DEFAULT_SKIN].has_pieces:
            cfg["skin"] = DEFAULT_SKIN
        if cfg.get("skin") in self.skins:
            self.piece_var.set(cfg["skin"])
        if cfg.get("theme") in BOARD_THEMES or (cfg.get("theme") == FROM_SKIN and cfg.get("skin") in self.skins):
            self.board_var.set(cfg["theme"])
        self.restore_clock(cfg)
        self.apply_style(save=False)
        ui = cfg.get("ui")
        self.apply_ui_theme(ui if ui in PALETTES else "Claro", save=False)
        self.poll()
        self.tick()
        if self.lobby_auto.get():
            self.after(400, self.show_lobby)

    def combo(self, parent, **kw):
        cb = ttk.Combobox(parent, state="readonly", **kw)
        self.combos.append(cb)
        return cb

    def make_strip(self, parent):
        """Cartão do jogador (nome, peças capturadas e relógio), como acima/abaixo do tabuleiro no chess.com."""
        f = tk.Frame(parent, width=8 * self.sq, height=38)
        f.pack_propagate(False)
        name = tk.Label(f, font=("Arial", 10, "bold"), anchor="w")
        name.pack(side="left", padx=(8, 4))
        cap = tk.Label(f, font=("Segoe UI Symbol", 11), anchor="w")
        cap.pack(side="left")
        tm = tk.Label(f, font=("Arial", 15, "bold"), anchor="e")
        tm.pack(side="right", padx=8)
        return f, name, tm, cap

    def player_name(self, color):
        if self.ai_color is None:
            return "Brancas" if color else "Pretas"
        if color == self.ai_color:
            return f"Stockfish ({self.elo_value()})"
        return "Você"

    # ---------------- menu e painel lateral (estilo chess.com) ----------------
    def build_menu(self):
        m = tk.Menu(self)
        g = tk.Menu(m, tearoff=0)
        g.add_command(label="Nova partida...", command=self.show_lobby)
        g.add_command(label="Importar PGN...", command=self.import_pgn)
        g.add_command(label="Editar posição", command=self.open_editor)
        g.add_command(label="IA vs IA...", command=self.open_selfplay)
        g.add_separator()
        g.add_command(label="Sair", command=self.destroy)
        m.add_cascade(label="Partida", menu=g)
        a = tk.Menu(m, tearoff=0)
        a.add_command(label="Analisar partida", command=lambda: self.start_analysis(True))
        a.add_command(label="Relatório da partida", command=self.open_report)
        a.add_command(label="Registro de lances", command=self.open_log)
        m.add_cascade(label="Análise", menu=a)
        t = tk.Menu(m, tearoff=0)
        t.add_command(label="Stockfish...", command=self.pick_engine)
        t.add_command(label="Sons...", command=self.open_sounds)
        t.add_command(label="Pasta de skins", command=self.open_skins)
        m.add_cascade(label="Ferramentas", menu=t)
        self.config(menu=m)

    def build_side(self, side, S):
        strip = tk.Frame(side)
        strip.pack(fill="x", pady=(0, 6))
        self.tab_lbl = {}
        for key, text in (("play", "Jogar"), ("new", "Nova partida"), ("analysis", "Análise"), ("opts", "Opções")):
            lb = ttk.Label(strip, text=text, style="Tab.TLabel", cursor="hand2", anchor="center")
            lb.pack(side="left", fill="x", expand=True, padx=(0, 1))
            lb.bind("<Button-1>", lambda e, k=key: self.show_tab(k))
            self.tab_lbl[key] = lb
        box = tk.Frame(side)
        box.pack(fill="both", expand=True)
        self.plain = [strip, box]
        self.pages = {k: ttk.Frame(box) for k in self.tab_lbl}
        self.build_play(self.pages["play"], S)
        lp = LobbyPanel(self.pages["new"], self, self.start_match)
        lp.pack(fill="x", padx=4, pady=4)
        self.subwins.append(lp)
        self.build_analysis(self.pages["analysis"])
        self.build_options(self.pages["opts"])
        self.show_tab("play")

    def show_tab(self, key):
        self.cur_tab = key
        for k, pg in self.pages.items():
            pg.pack_forget()
            self.tab_lbl[k].configure(style="TabSel.TLabel" if k == key else "Tab.TLabel")
        self.pages[key].pack(fill="both", expand=True)

    def build_play(self, pg, S):
        self.fb = tk.Frame(pg, bg="#262421", height=84, cursor="hand2")      # painel de feedback do lance
        self.fb.pack(fill="x", pady=(0, 6))
        self.fb.pack_propagate(False)
        self.fb_icon = tk.Canvas(self.fb, width=44, height=44, bg="#262421", highlightthickness=0)
        self.fb_icon.pack(side="left", padx=8)
        txt = tk.Frame(self.fb, bg="#262421")
        txt.pack(side="left", fill="both", expand=True)
        self.fb_title = tk.Label(txt, bg="#262421", fg="#ffffff", font=("Arial", 12, "bold"), anchor="w")
        self.fb_title.pack(fill="x", pady=(10, 0))
        self.fb_sub = tk.Label(txt, bg="#262421", fg="#bababa", font=("Arial", 9), anchor="nw",
                               justify="left", wraplength=230)
        self.fb_sub.pack(fill="both", expand=True)
        txt.bind("<Configure>", lambda e: self.fb_sub.config(wraplength=max(120, e.width - 12)))
        for w in (self.fb, self.fb_icon, txt, self.fb_title, self.fb_sub):
            w.bind("<Button-1>", lambda e: self.open_log(self.view - 1 if self.view > 0 else None))

        acts = ttk.Frame(pg)                                    # botões de ação (empate, voltar lance, desistir...)
        acts.pack(side="bottom", fill="x", pady=(6, 0))
        for i, (text, cmd) in enumerate((("½ Empate", self.offer_draw), ("↩ Voltar lance", self.undo),
                                         ("⚑ Desistir", self.resign))):
            ttk.Button(acts, text=text, command=cmd, style="Act.TButton", takefocus=0).grid(row=0, column=i, sticky="ew", padx=1, pady=1)
        self.pause_btn = ttk.Button(acts, text="Pausar", command=self.toggle_pause, style="Act.TButton", takefocus=0)
        for i, (w, cmd) in enumerate(((None, None), ("⇅ Virar", self.flip), ("+ Nova", lambda: self.show_tab("new")))):
            if w is None:
                self.pause_btn.grid(row=1, column=i, sticky="ew", padx=1, pady=1)
            else:
                ttk.Button(acts, text=w, command=cmd, style="Act.TButton", takefocus=0).grid(row=1, column=i, sticky="ew", padx=1, pady=1)
        for c in range(3):
            acts.columnconfigure(c, weight=1, uniform="act")

        nav = ttk.Frame(pg)                                     # navegação só para visualização
        nav.pack(side="bottom", fill="x", pady=(6, 0))
        for text, cmd in (("|<", lambda: self.go(0)), ("<", lambda: self.go(self.view - 1)),
                          (">", lambda: self.go(self.view + 1)), (">|", lambda: self.go(len(self.moves)))):
            ttk.Button(nav, text=text, width=4, command=cmd, takefocus=0).pack(side="left", padx=1)
        ttk.Label(nav, textvariable=self.nav_var).pack(side="left", padx=6)

        mid = ttk.Frame(pg)
        mid.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(mid, columns=("n", "w", "b"), show="headings", height=10, takefocus=0)
        for c, t, w in (("n", "#", 38), ("w", "Brancas", 118), ("b", "Pretas", 118)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="center")
        sb = ttk.Scrollbar(mid, command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")

    def build_analysis(self, pg):
        ttk.Label(pg, text="Avaliação do Stockfish", font=("Arial", 10, "bold")).pack(anchor="w", pady=(4, 2))
        ttk.Label(pg, textvariable=self.eval_var, font=("Arial", 20, "bold")).pack(anchor="w")
        ttk.Label(pg, textvariable=self.line_var, wraplength=320, justify="left").pack(anchor="w", pady=(2, 10))
        ttk.Checkbutton(pg, text="Julgar os lances ao jogar", variable=self.auto).pack(anchor="w", pady=2)
        row = ttk.Frame(pg)
        row.pack(anchor="w", pady=2)
        ttk.Label(row, text="Profundidade da análise:").pack(side="left")
        ttk.Spinbox(row, from_=6, to=22, width=4, textvariable=self.depth).pack(side="left", padx=6)
        for text, cmd in (("Analisar a partida inteira", lambda: self.start_analysis(True)),
                          ("Relatório da partida", self.open_report), ("Registro de lances", self.open_log),
                          ("Importar partidas (PGN)...", self.import_pgn), ("Editar posição", self.open_editor)):
            ttk.Button(pg, text=text, command=cmd, style="Act.TButton").pack(fill="x", pady=2)

    def build_options(self, pg):
        def line(label, widget_fn):
            r = ttk.Frame(pg)
            r.pack(fill="x", pady=3)
            ttk.Label(r, text=label, width=14).pack(side="left")
            w = widget_fn(r)
            w.pack(side="left", fill="x", expand=True)
        def mk_piece(r):
            self.piece_cb = self.combo(r, textvariable=self.piece_var, values=[VECTOR], width=18, postcommand=self.rescan_skins)
            self.piece_cb.bind("<<ComboboxSelected>>", self.on_piece_choice)
            return self.piece_cb

        def mk_board(r):
            cb = self.combo(r, textvariable=self.board_var, values=[FROM_SKIN] + list(BOARD_THEMES), width=18)
            cb.bind("<<ComboboxSelected>>", lambda e: self.apply_style())
            return cb

        def mk_ui(r):
            cb = self.combo(r, textvariable=self.ui_var, values=list(PALETTES), width=18)
            cb.bind("<<ComboboxSelected>>", lambda e: self.apply_ui_theme(self.ui_var.get()))
            return cb
        line("Peças:", mk_piece)
        line("Tabuleiro:", mk_board)
        line("Interface:", mk_ui)
        line("Pausa da IA (s):", lambda r: ttk.Spinbox(r, from_=0, to=15, increment=0.5, width=6, textvariable=self.ai_pause))
        ttk.Checkbutton(pg, text="Abrir o relatório ao fim da partida", variable=self.report_auto,
                        command=lambda: save_cfg(report=self.report_auto.get())).pack(anchor="w", pady=2)
        ttk.Checkbutton(pg, text="Mostrar a tela de nova partida ao abrir", variable=self.lobby_auto,
                        command=lambda: save_cfg(lobby_start=self.lobby_auto.get())).pack(anchor="w", pady=2)
        for text, cmd in (("Stockfish...", self.pick_engine), ("Sons...", self.open_sounds),
                          ("Pasta de skins", self.open_skins), ("IA vs IA (treino)...", self.open_selfplay)):
            ttk.Button(pg, text=text, command=cmd, style="Act.TButton").pack(fill="x", pady=2)

    # ---------------- lobby / nova partida ----------------
    def show_lobby(self):
        if self.sp_active:
            self.sp_block()
            return
        if self.lobby_win is not None and self.lobby_win.winfo_exists():
            self.lobby_win.lift()
            return
        self.lobby_win = LobbyDialog(self)

    def start_match(self, o):
        """Aplica as escolhas do lobby e começa uma partida nova."""
        if self.sp_block():
            return
        color = o["color"]
        if color == "random":
            color = random.choice(("white", "black"))
        name = o["clock"]
        ccfg = tuple(o["custom"]) if name == "Personalizado..." else CLOCK_PRESETS[name]
        self.clock.set(ccfg)
        self.clock_var.set(name)
        self.clock_name = name
        save_cfg(clock=name, clock_cfg=list(ccfg) if ccfg else None, lobby=dict(o))
        if o["vs_ai"]:
            self.elo.set(str(o["elo"]))
            self.mode.set(MODES[1] if color == "white" else MODES[2])
        else:
            self.mode.set(MODES[0])
            self.flipped = False
        self.new_game()
        self.on_mode()
        self.show_tab("play")

    # ---------------- empate ----------------
    def offer_draw(self):
        if self.sp_block() or self.editing or self.game_over():
            return
        if not self.moves:
            messagebox.showinfo("Empate", "Faça ao menos um lance antes de propor empate.")
            return
        if self.ai_color is None:
            ok = messagebox.askyesno("Empate", "Um jogador propôs empate.\nO adversário aceita?")
        else:
            b = self.boards[-1]
            ev = self.analyzer.cache.get(b.fen())
            if ev:
                ai_cp = ev[0] if self.ai_color == chess.WHITE else -ev[0]
            else:                                              # sem avaliação: usa o saldo de material
                d = captured_info(b)[1]
                ai_cp = 100 * (d if self.ai_color == chess.WHITE else -d)
            ok = ai_cp <= 30
            messagebox.showinfo("Empate", "A IA aceitou o empate." if ok else "A IA recusou o empate: ela acha que está melhor.")
        if ok:
            self.drawn, self.sel, self.premove = True, None, None
            self.clock.running = False
            self.go(len(self.moves))
            self.check_end()

    # ---------------- tema da interface (claro / escuro) ----------------
    def apply_ui_theme(self, name, save=True):
        p = self.pal = PALETTES[name]
        self.ui_theme = name
        self.ui_var.set(name)
        st = ttk.Style(self)
        st.theme_use("clam")
        self.configure(bg=p["bg"])
        st.configure(".", background=p["bg"], foreground=p["fg"], fieldbackground=p["field"],
                     bordercolor=p["border"], troughcolor=p["field"], focuscolor=p["bg"],
                     lightcolor=p["btn"], darkcolor=p["btn"])
        st.configure("TFrame", background=p["bg"])
        st.configure("TLabel", background=p["bg"], foreground=p["fg"])
        st.configure("TButton", background=p["btn"], foreground=p["fg"], padding=(8, 3))
        st.map("TButton", background=[("active", p["btn_active"]), ("pressed", p["btn_active"])])
        st.configure("TCheckbutton", background=p["bg"], foreground=p["fg"],
                     indicatorbackground=p["field"], indicatorforeground=p["fg"])
        st.map("TCheckbutton", background=[("active", p["bg"])], indicatorbackground=[("selected", p["sel"])])
        st.configure("TRadiobutton", background=p["bg"], foreground=p["fg"],
                     indicatorbackground=p["field"], indicatorforeground=p["fg"])
        st.map("TRadiobutton", background=[("active", p["bg"])], indicatorbackground=[("selected", p["sel"])])
        for w in ("TCombobox", "TSpinbox", "TEntry"):
            st.configure(w, fieldbackground=p["field"], background=p["btn"], foreground=p["fg"],
                         arrowcolor=p["fg"], insertcolor=p["fg"], selectbackground=p["sel"],
                         selectforeground=p["sel_fg"])
        st.map("TCombobox", fieldbackground=[("readonly", p["field"])], foreground=[("readonly", p["fg"])],
               selectbackground=[("readonly", p["field"])], selectforeground=[("readonly", p["fg"])])
        st.configure("Treeview", background=p["field"], fieldbackground=p["field"], foreground=p["fg"], rowheight=20)
        st.map("Treeview", background=[("selected", p["sel"])], foreground=[("selected", p["sel_fg"])])
        st.configure("Treeview.Heading", background=p["head"], foreground=p["fg"], relief="flat")
        st.map("Treeview.Heading", background=[("active", p["btn_active"])])
        st.configure("Vertical.TScrollbar", background=p["btn"], troughcolor=p["field"], arrowcolor=p["fg"])
        st.configure("TPanedwindow", background=p["bg"])
        st.configure("Tab.TLabel", background=p["btn"], foreground=p["fg"], padding=(4, 8), font=("Arial", 9, "bold"))
        st.configure("TabSel.TLabel", background=p["sel"], foreground=p["sel_fg"], padding=(4, 8), font=("Arial", 9, "bold"))
        st.configure("Act.TButton", padding=(4, 8), font=("Arial", 9, "bold"))
        for opt, val in (("background", p["field"]), ("foreground", p["fg"]),
                         ("selectBackground", p["sel"]), ("selectForeground", p["sel_fg"])):
            self.option_add(f"*TCombobox*Listbox.{opt}", val)
        for cb in self.combos:                              # listas suspensas já criadas
            try:
                pop = self.tk.call("ttk::combobox::PopdownWindow", str(cb))
                self.tk.call(f"{pop}.f.l", "configure", "-background", p["field"], "-foreground", p["fg"],
                             "-selectbackground", p["sel"], "-selectforeground", p["sel_fg"])
            except tk.TclError:
                pass
        for cv in [self.canvas, self.evalbar] + getattr(self, "plain", []):
            cv.configure(bg=p["bg"])
        for w in list(self.subwins):
            w.retheme()
        if save:
            save_cfg(ui=name)
        self.refresh()

    # ---------------- relógio ----------------
    def restore_clock(self, cfg):
        name = cfg.get("clock", "Sem relógio")
        if name not in CLOCK_PRESETS:
            return
        ccfg = CLOCK_PRESETS[name]
        if ccfg == "custom":
            c = cfg.get("clock_cfg")
            ccfg = tuple(c) if isinstance(c, list) and len(c) == 2 and all(isinstance(x, (int, float)) for x in c) else None
            if ccfg is None:
                name = "Sem relógio"
        self.clock.set(ccfg)
        self.clock_var.set(name)
        self.clock_name = name

    def on_clock_choice(self, *_):
        name = self.clock_var.get()
        ccfg = CLOCK_PRESETS[name]
        if ccfg == "custom":
            m = simpledialog.askfloat("Relógio personalizado", "Minutos por jogador:", parent=self,
                                      minvalue=0.5, maxvalue=180, initialvalue=5)
            if m is None:
                self.clock_var.set(self.clock_name)
                return
            inc = simpledialog.askinteger("Relógio personalizado", "Incremento por lance (segundos):", parent=self,
                                          minvalue=0, maxvalue=60, initialvalue=0)
            ccfg = (int(m * 60), inc or 0)
        self.clock.set(ccfg)
        self.clock.sync(self.boards[-1].turn, len(self.moves))
        self.clock_name = name
        self.pause_btn.config(text="Pausar")
        save_cfg(clock=name, clock_cfg=list(ccfg) if ccfg else None)
        self.refresh()

    def toggle_pause(self):
        if not self.clock.enabled:
            return
        self.clock.paused = not self.clock.paused
        self.pause_btn.config(text="Continuar" if self.clock.paused else "Pausar")
        self.refresh()

    def game_over(self):
        return self.boards[-1].is_game_over() or self.clock.flag is not None or self.resigned is not None or self.drawn

    def resign_text(self):
        who = self.resigned
        return f"{'Brancas' if who else 'Pretas'} desistiram - {'Pretas' if who else 'Brancas'} vencem"

    def resign(self):
        if self.sp_block() or self.editing or self.game_over():
            return
        who = (not self.ai_color) if self.ai_color is not None else self.boards[-1].turn
        if not messagebox.askyesno("Desistir", f"{'Brancas' if who else 'Pretas'} desistem da partida?"):
            return
        self.resigned, self.sel, self.premove = who, None, None
        self.clock.running = False
        self.go(len(self.moves))
        self.result_sound(not who)
        self.check_end()

    # ---------------- sons ----------------
    def open_sounds(self):
        if self.snd_win is not None and self.snd_win.winfo_exists():
            self.snd_win.lift()
            return
        self.snd_win = SoundWindow(self)

    def announce(self, b, mv, result=True):
        """Toca o som do lance que acabou de ser jogado (b = tabuleiro depois do lance)."""
        if b.is_checkmate():
            if result:
                self.result_sound(not b.turn)               # fim de jogo: vitória ou derrota
            else:
                self.sounds.play("mover")
            return
        if mv.promotion:
            ev = "promocao"
        elif b.is_check():
            ev = "xeque"
        else:
            ev = "mover"
        self.sounds.play(ev)

    def result_sound(self, winner):
        """Vitória/derrota do ponto de vista de quem joga (contra a IA); com 2 jogadores, toca vitória."""
        if self.ai_color is None:
            self.sounds.play("vitoria")
        else:
            self.sounds.play("vitoria" if winner != self.ai_color else "derrota")

    def time_result(self):
        f = self.clock.flag
        if f is None:
            return None
        winner = not f
        if self.boards[-1].has_insufficient_material(winner):
            return "Tempo esgotado - empate (o adversário não tem material para dar mate)"
        return f"Tempo esgotado! {'Brancas' if winner else 'Pretas'} vencem no tempo"

    def tick(self):
        self.after(100, self.tick)
        self.clock.tick()
        if self.clock.flag is None:
            self._flag_shown = False
        elif not self._flag_shown:
            self._flag_shown = True
            self.sel = None
            self.refresh()
            if not self.boards[-1].has_insufficient_material(not self.clock.flag):
                self.result_sound(not self.clock.flag)
            self.check_end()
            messagebox.showinfo("Tempo esgotado", self.time_result())
        self.update_clocks()

    def update_clocks(self):
        p, c = self.pal, self.clock
        b = self.edit_board if self.editing and self.edit_board else self.boards[self.view]
        cap, diff = captured_info(b)
        bottom = chess.BLACK if self.flipped else chess.WHITE
        live = self.view == len(self.moves) and not self.editing and not self.game_over()
        for strip, color in ((self.strip_top, not bottom), (self.strip_bottom, bottom)):
            f, name, tm, capl = strip
            left = c.left[color]
            active = c.enabled and c.turn == color and c.running and not c.paused and c.flag is None
            if c.enabled and c.flag == color:
                bg, fg = CLOCK_LOW, "#ffffff"
            elif active:
                bg, fg = (CLOCK_LOW if left < 20 else CLOCK_ON), "#ffffff"
            else:
                bg, fg = p["btn"], p["fg"]
            mark = "\u25cf " if live and self.boards[-1].turn == color else ""
            adv = diff if color else -diff
            f.configure(bg=bg)
            name.configure(bg=bg, fg=fg, text=mark + self.player_name(color) + ("  - pausado" if c.enabled and c.paused else ""))
            capl.configure(bg=bg, fg=fg, text=cap[color] + (f" +{adv}" if adv > 0 else ""))
            tm.configure(bg=bg, fg=fg, text=fmt_clock(left) if c.enabled else "")

    # ---------------- skins e temas do tabuleiro ----------------
    def rescan_skins(self):
        for name, s in scan_skins().items():
            self.skins.setdefault(name, s)
        self.piece_cb.configure(values=[VECTOR] + sorted(self.skins))

    def on_piece_choice(self, *_):
        name = self.piece_var.get()
        s = self.skins.get(name)
        if s and not s.has_pieces and (s.files or not s.has_board):
            if s.files:
                msg = (f"A skin '{name}' tem só {len(s.files)} das 12 peças reconhecidas.\n"
                       f"Faltam: {', '.join(s.missing())}\n\n"
                       "Nomes esperados: wP.png wN.png wB.png wR.png wQ.png wK.png "
                       "e bP.png ... bK.png (veja o LEIA-ME.txt).")
            else:
                msg = (f"Não reconheci nenhuma peça na skin '{name}'.\n"
                       "Use nomes como wP.png, bK.png, white_pawn.png (veja o LEIA-ME.txt).")
                if not Image:
                    msg += "\n\nSe for uma sprite sheet, instale o Pillow:  py -m pip install pillow"
            messagebox.showwarning("Skin não utilizável", msg)
            self.piece_var.set(VECTOR)
            s = None
        if s and s.has_board:
            self.board_var.set(FROM_SKIN)
        elif self.board_var.get() == FROM_SKIN:
            self.board_var.set(DEFAULT_THEME)
        self.apply_style()

    def apply_style(self, save=True):
        s = self.skins.get(self.piece_var.get())
        self.skin = s if s and s.has_pieces else None
        theme = self.board_var.get()
        light, dark = BOARD_THEMES.get(theme, BOARD_THEMES[DEFAULT_THEME])
        self.board_skin = None
        if theme == FROM_SKIN and s:
            if s.light and s.dark:
                light, dark = s.light, s.dark
            if s.board_file:
                self.board_skin = s
        self.light, self.dark = light, dark
        if save:
            save_cfg(skin=self.piece_var.get(), theme=theme)
        self.refresh()

    def open_skins(self):
        os.makedirs(SKIN_DIR, exist_ok=True)
        readme = os.path.join(SKIN_DIR, "LEIA-ME.txt")
        if not os.path.exists(readme):
            with open(readme, "w", encoding="utf-8") as f:
                f.write(SKIN_HELP)
        try:
            if sys.platform.startswith("win"):
                os.startfile(SKIN_DIR)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", SKIN_DIR])
            else:
                subprocess.Popen(["xdg-open", SKIN_DIR])
        except Exception:
            messagebox.showinfo("Skins", f"Coloque suas skins em:\n{SKIN_DIR}")

    def put_piece(self, cv, cx, cy, size, piece):
        if self.skin:
            try:
                cv.create_image(cx, cy, image=self.skin.image(piece, int(size)))
                return
            except Exception as err:                    # arquivo corrompido, etc.
                name, msg, self.skin = self.skin.name, str(err), None
                self.piece_var.set(VECTOR)
                self.after(100, lambda: messagebox.showerror(
                    "Skin", f"Não foi possível carregar a skin '{name}':\n{msg}\nVoltando às peças padrão."))
        paint_piece(cv, cx, cy, size * 0.96, piece)

    # ---------------- estado da partida ----------------
    def set_game(self, start, moves):
        if self.editing:
            self.editor.cancel()
        self.resigned, self.premove, self.drawn = None, None, False
        self.start = start.copy()
        self.moves, self.sans, self.boards = [], [], [start.copy()]
        for m in moves:
            self._push(m)
        self.view, self.sel = len(self.moves), None
        self.game_id += 1
        self.clear_arrows()

    def _push(self, m):
        b = self.boards[-1].copy()
        self.sans.append(b.san(m))
        b.push(m)
        self.moves.append(m)
        self.boards.append(b)

    def new_game(self):
        if self.sp_block():
            return
        self.set_game(chess.Board(), [])
        self.ai_result = None
        self.clock.reset()
        self.pause_btn.config(text="Pausar")
        self.title("Xadrez + Stockfish")
        self.refresh()

    def undo(self):
        if self.editing or self.sp_active:
            return
        self.resigned, self._report_gid, self.premove, self.drawn = None, None, None, False
        while self.moves:
            self.moves.pop(); self.boards.pop(); self.sans.pop()
            if self.ai_color is None or self.boards[-1].turn != self.ai_color:
                break                                  # contra a IA, desfaz o par de lances
        self.view, self.sel, self.ai_result = len(self.moves), None, None
        self.clock.sync(self.boards[-1].turn, len(self.moves))
        self.clear_arrows()
        self.refresh()

    def flip(self):
        self.flipped = not self.flipped
        self.refresh()

    def go(self, v):
        if self.editing:
            return
        self.view, self.sel = max(0, min(len(self.moves), v)), None
        self.clear_arrows()
        self.refresh()

    def load_game(self, game):
        if self.sp_block():
            return
        h = game.headers
        self.set_game(game.board(), list(game.mainline_moves()))
        self.view = 0
        self.mode.set(MODES[0])
        self.ai_color, self.ai_result = None, None
        self.clock.set(None)
        self.clock_var.set("Sem relógio")
        self.clock_name = "Sem relógio"
        self.title(f"{h.get('White', '?')} vs {h.get('Black', '?')} - {h.get('Event', '')}")
        self.refresh()

    # ---------------- jogadas com o mouse ----------------
    def sq_at(self, x, y):
        col, row = int(x // self.sq), int(y // self.sq)
        return chess.square(7 - col, row) if self.flipped else chess.square(col, 7 - row)

    def xy(self, sq):
        f, r = chess.square_file(sq), chess.square_rank(sq)
        col, row = (7 - f, r) if self.flipped else (f, 7 - r)
        return col * self.sq, row * self.sq

    def can_play(self, e=None):
        """Verifica se o jogador pode mexer agora (posição atual, sem fim de jogo, sua vez)."""
        if self.sp_active:
            self.status.set("IA vs IA em andamento: pare a série para jogar.")
            return False
        if self.view != len(self.moves):
            self.status.set("Revendo lances (só visualização): clique em '>|' ou tecle End para voltar à posição atual.")
            return False
        if self.game_over():
            return False
        if self.clock.paused:
            self.status.set("Relógio pausado: clique em 'Continuar' para jogar.")
            return False
        if self.ai_color is not None and self.boards[-1].turn == self.ai_color:
            return False                                  # vez da IA
        return True

    def can_premove(self):
        """Premove: durante a vez da IA, o jogador já arma o próprio lance."""
        return (self.ai_color is not None and not self.sp_active and not self.editing
                and self.view == len(self.moves) and not self.game_over() and not self.clock.paused
                and self.boards[-1].turn == self.ai_color)

    def human_view(self):
        """Tabuleiro como se fosse a vez do jogador (para gerar os lances do premove)."""
        b = self.boards[-1].copy(stack=False)
        b.turn, b.ep_square = (not self.ai_color), None
        return b

    def set_premove(self, frm, to):
        if not self.can_premove():
            return False
        hv = self.human_view()
        p = hv.piece_at(frm)
        if frm == to or not p or p.color != hv.turn or not any(
                m.from_square == frm and m.to_square == to for m in hv.pseudo_legal_moves):
            return False
        self.premove, self.sel, self.drag, self.hide_sq = (frm, to), None, None, None
        self.clear_arrows()
        self.draw()
        return True

    def cancel_premove(self):
        if self.premove:
            self.premove = None
            self.draw()

    def try_premove(self):
        """Chamado logo depois do lance da IA: joga o premove (custa PREMOVE_COST s) ou o descarta."""
        pm, self.premove = self.premove, None
        if not pm or self.ai_color is None or self.game_over() or self.boards[-1].turn == self.ai_color:
            return
        if not self.play_move(pm[0], pm[1], auto_queen=True, penalty=PREMOVE_COST):
            self.draw()                                   # ficou ilegal: descarta em silêncio

    def play_move(self, frm, to, auto_queen=False, penalty=0.0):
        """Executa o lance frm->to se for legal; devolve True se jogou."""
        b = self.boards[-1]
        cands = [m for m in b.legal_moves if m.from_square == frm and m.to_square == to]
        if not cands:
            return False
        if len(cands) > 1:
            mv = next(m for m in cands if m.promotion == chess.QUEEN) if auto_queen else self.ask_promotion(cands)
        else:
            mv = cands[0]
        self.sel, self.drag, self.hide_sq, self.premove = None, None, None, None
        mover = b.turn
        self._push(mv)
        self.clock.moved(mover, len(self.moves))
        if penalty:
            self.clock.penalty(mover, penalty)
        self.clear_arrows()
        self.view = len(self.moves)
        self.refresh()
        self.announce(self.boards[-1], mv)
        self.check_end()
        return True

    def on_press(self, e):
        if self.editing:
            return self.edit_press(e)
        self.drag, self.hide_sq = None, None
        if not (0 <= e.x < 8 * self.sq and 0 <= e.y < 8 * self.sq):
            return
        pm = self.can_premove()
        if not pm and not self.can_play():
            return
        b = self.boards[-1]
        me = (not self.ai_color) if pm else b.turn
        sq = self.sq_at(e.x, e.y)
        if self.sel is not None and sq != self.sel:
            if (self.set_premove(self.sel, sq) if pm else self.play_move(self.sel, sq)):
                return                                    # clicou na peça e depois no destino
            q = b.piece_at(sq)
            if not (q and q.color == me):
                self.sounds.play("invalido")              # destino ilegal
        p = b.piece_at(sq)
        if p and p.color == me:
            self.drag = {"sq": sq, "piece": p, "moved": False, "x": e.x, "y": e.y,
                         "x0": e.x, "y0": e.y, "was_sel": sq == self.sel}
            self.sel = sq
            self.clear_arrows()                           # selecionar uma peça apaga setas e círculos
        else:
            self.sel = None
            if pm and self.premove:
                self.premove = None                       # clicar numa casa qualquer cancela o premove
        self.draw()

    def on_motion(self, e):
        if self.editing:
            return self.edit_motion(e)
        self.on_motion_drag(e)

    def on_motion_drag(self, e):
        d = self.drag
        if not d:
            return
        if not d["moved"]:
            if abs(e.x - d["x0"]) + abs(e.y - d["y0"]) < 5:
                return
            d["moved"], self.hide_sq = True, d["sq"]
            self.draw()                                   # redesenha sem a peça de origem
            before = set(self.canvas.find_all())
            self.put_piece(self.canvas, e.x, e.y, self.sq * 0.94, d["piece"])
            for i in set(self.canvas.find_all()) - before:
                self.canvas.addtag_withtag("drag", i)
            self.canvas.config(cursor="fleur")
        else:
            self.canvas.move("drag", e.x - d["x"], e.y - d["y"])
        d["x"], d["y"] = e.x, e.y

    def on_release(self, e):
        if self.editing:
            return self.edit_release(e)
        d, self.drag = self.drag, None
        self.canvas.config(cursor="")
        if not d:
            return
        self.hide_sq = None
        if d["moved"]:
            if 0 <= e.x < 8 * self.sq and 0 <= e.y < 8 * self.sq:
                tgt = self.sq_at(e.x, e.y)
                if (self.set_premove(d["sq"], tgt) if self.can_premove() else self.play_move(d["sq"], tgt)):
                    return
                if tgt != d["sq"]:
                    self.sounds.play("invalido")
            self.draw()                                   # soltou em lugar inválido: a peça volta e continua selecionada
        elif d["was_sel"]:
            self.sel = None                               # clicar de novo na peça selecionada desmarca
            self.draw()

    # ---------------- IA vs IA ----------------
    def open_selfplay(self):
        if self.sp_win is not None and self.sp_win.winfo_exists():
            self.sp_win.lift()
            return
        if self.editing:
            messagebox.showinfo("IA vs IA", "Feche o editor de posição primeiro.")
            return
        self.sp_win = SelfPlayWindow(self)

    # ---------------- editor de posição ----------------
    def open_editor(self):
        if self.sp_block():
            return
        if self.editing:
            self.editor.lift()
            return
        self.sel = None
        self.clear_arrows()
        self.edit_board = self.boards[self.view].copy(stack=False)
        self.edit_board.ep_square = None
        self._pre_paused = self.clock.paused
        self.clock.paused = True                       # o relógio fica parado durante a edição
        self.editing = True
        self.editor = BoardEditor(self)
        self.refresh()

    def edit_apply(self, sq, tool):
        if tool == "erase":
            self.edit_board.remove_piece_at(sq)
            self.editor.check()
        elif isinstance(tool, chess.Piece):
            self.editor.place(sq, tool)

    def edit_press(self, e):
        sq = self.board_sq(e)
        self.drag, self.hide_sq, self._edit_last = None, None, sq
        if sq is None:
            return
        tool = self.editor.tool
        if tool == "move":
            p = self.edit_board.piece_at(sq)
            if p:
                self.drag = {"sq": sq, "piece": p, "moved": False, "x": e.x, "y": e.y,
                             "x0": e.x, "y0": e.y, "was_sel": False}
        else:
            self.edit_apply(sq, tool)
        self.draw()

    def edit_motion(self, e):
        if self.drag:
            return self.on_motion_drag(e)
        if self.editor.tool == "move":
            return
        sq = self.board_sq(e)
        if sq is None or sq == self._edit_last:
            return
        self._edit_last = sq
        self.edit_apply(sq, self.editor.tool)
        self.draw()

    def edit_release(self, e):
        d, self.drag = self.drag, None
        self.hide_sq, self._edit_last = None, None
        self.canvas.config(cursor="")
        if d and d["moved"]:
            t = self.board_sq(e)
            b = self.edit_board
            if t is None:
                b.remove_piece_at(d["sq"])                 # soltou fora do tabuleiro: apaga
                self.editor.check()
            elif t != d["sq"]:
                b.remove_piece_at(d["sq"])
                if not self.editor.place(t, d["piece"]):
                    b.set_piece_at(d["sq"], d["piece"])    # lugar proibido: a peça volta
        self.draw()

    def start_from(self, board):
        """Começa uma partida (do zero) a partir de uma posição personalizada."""
        self.set_game(board, [])
        self.ai_result = None
        self.clock.reset()
        self.clock.turn = board.turn
        self.pause_btn.config(text="Pausar")
        self.title("Xadrez + Stockfish - posição personalizada")
        self.refresh()

    def on_wheel(self, e):
        up = getattr(e, "delta", 0) > 0 or getattr(e, "num", 0) == 4
        self.go(self.view - 1 if up else self.view + 1)

    def ask_promotion(self, cands):
        choice = [next(m for m in cands if m.promotion == chess.QUEEN)]
        win = tk.Toplevel(self)
        win.title("Promoção")
        win.transient(self)
        win.grab_set()

        def pick(m):
            choice[0] = m
            win.destroy()
        for m in cands:
            cv = tk.Canvas(win, width=64, height=64, bg=self.light, cursor="hand2", highlightthickness=1)
            cv.pack(side="left", padx=4, pady=4)
            self.put_piece(cv, 32, 32, 58, chess.Piece(m.promotion, self.boards[-1].turn))
            cv.bind("<Button-1>", lambda e, m=m: pick(m))
        self.wait_window(win)
        return choice[0]

    # ---------------- setas e marcações (botão direito) ----------------
    def clear_arrows(self):
        self.arrows, self.marks = {}, {}

    def arrow_color(self, state):
        if state & 0x1:
            return ARROW_RED                            # Shift
        if state & 0x4:
            return ARROW_BLUE                           # Ctrl
        if state & 0x8 or state & 0x20000:
            return ARROW_ORANGE                         # Alt
        return ARROW_GREEN

    def board_sq(self, e):
        if 0 <= e.x < 8 * self.sq and 0 <= e.y < 8 * self.sq:
            return self.sq_at(e.x, e.y)
        return None

    def arrow_press(self, e):
        sq = self.board_sq(e)
        if self.premove and not self.editing:           # botão direito cancela o premove
            self.premove, self._drag = None, None
            self.draw()
            return
        if self.editing:                                # no editor, botão direito apaga a peça
            if sq is not None:
                self.edit_board.remove_piece_at(sq)
                self.editor.check()
                self.draw()
            return
        self._drag = (sq, self.arrow_color(e.state)) if sq is not None else None

    def arrow_motion(self, e):
        if self.editing:
            return
        self.canvas.delete("tmp")
        if self._drag:
            sq = self.board_sq(e)
            if sq is not None and sq != self._drag[0]:
                self.draw_arrow(self.canvas, self._drag[0], sq, self._drag[1], "tmp")

    def arrow_release(self, e):
        if self.editing:
            return
        self.canvas.delete("tmp")
        if not self._drag:
            return
        a, col = self._drag
        self._drag = None
        b = self.board_sq(e)
        if b is None:
            return
        if a == b:                                      # clique simples: círculo
            if self.marks.get(a) == col:
                del self.marks[a]
            else:
                self.marks[a] = col
        elif self.arrows.get((a, b)) == col:            # mesma seta de novo: apaga
            del self.arrows[(a, b)]
        else:
            self.arrows[(a, b)] = col
        self.draw()

    def draw_arrow(self, c, a, b, col, tag=None):
        S = self.sq
        ax, ay = (v + S / 2 for v in self.xy(a))
        bx, by = (v + S / 2 for v in self.xy(b))
        dx, dy = round((bx - ax) / S), round((by - ay) / S)
        pts = [ax, ay, bx, by]
        if sorted((abs(dx), abs(dy))) == [1, 2]:        # cavalo: seta em "L"
            cx, cy = (ax, by) if abs(dy) == 2 else (bx, ay)
            pts = [ax, ay, cx, cy, bx, by]
        c.create_line(*pts, fill=col, width=max(6, S * 0.14), arrow="last",
                      arrowshape=(S * 0.36, S * 0.42, S * 0.18), capstyle="round", joinstyle="round",
                      tags=tag or ())

    # ---------------- classificação dos lances ----------------
    def move_class(self, k):
        """Chave de CLASSES para o lance k, ou None se ainda não há análise."""
        a = self.analyzer.cache.get(self.boards[k].fen())
        b = self.analyzer.cache.get(self.boards[k + 1].fen())
        if not a or not b:
            return None
        key = (self.boards[k].fen(), self.moves[k].uci())
        if key not in self._cls:
            prev = self.moves[k - 1] if k > 0 else None
            self._cls[key] = classify_move(self.boards[k], self.moves[k], a, b, prev)
        return self._cls[key]

    def judge_text(self, k):
        key = self.move_class(k)
        return CLASSES[key][1] if key else ""

    def who(self, k):
        mover = self.boards[k].turn
        s = "Brancas" if mover else "Pretas"
        if self.ai_color is None:
            return s
        return s + (" (IA)" if mover == self.ai_color else " (você)")

    def explain(self, k):
        key = self.move_class(k)
        if not key:
            return None
        a = self.analyzer.cache[self.boards[k].fen()]
        b = self.analyzer.cache[self.boards[k + 1].fen()]
        return explain_move(self.boards[k], self.moves[k], a, b, key, self.who(k))

    def open_log(self, k=None):
        if self.log is None or not self.log.winfo_exists():
            self.log = MoveLog(self)
        self.log.deiconify()
        self.log.lift()
        self.log.update_log(True)
        if k is not None:
            self.log.select(k)

    # ---------------- tabela de lances ----------------
    def refresh_table(self):
        t = self.tree
        t.delete(*t.get_children())
        off = 1 if self.start.turn == chess.BLACK else 0
        rows = {}
        for k, san in enumerate(self.sans):
            r, col = divmod(k + off, 2)
            rows.setdefault(r, ["", ""])[col] = san + self.judge_text(k)
        n0 = self.start.fullmove_number
        for r in sorted(rows):
            w, bl = rows[r]
            t.insert("", "end", iid=str(r), values=(n0 + r, w or "...", bl))
        if self.view > 0:
            r = (self.view - 1 + off) // 2
            t.selection_set(str(r))
            t.see(str(r))

    def on_table_click(self, e):
        row, col = self.tree.identify_row(e.y), self.tree.identify_column(e.x)
        if not row:
            return
        off = 1 if self.start.turn == chess.BLACK else 0
        k = 2 * int(row) + (1 if col == "#3" else 0) - off
        if 0 <= k < len(self.moves):
            self.go(k + 1)
        return "break"

    # ---------------- desenho ----------------
    def refresh(self):
        self.refresh_table()
        self.draw()
        self.update_clocks()
        if self.log is not None and self.log.winfo_exists():
            self.log.update_log()

    def draw(self):
        c, S = self.canvas, self.sq
        b = self.edit_board if self.editing else self.boards[self.view]
        c.delete("all")
        bimg = None
        if self.board_skin:
            try:
                bimg = self.board_skin.board_image(8 * S, self.flipped)
                c.create_image(0, 0, image=bimg, anchor="nw")
            except Exception:
                bimg = None
        last = self.moves[self.view - 1] if self.view and not self.editing else None
        targets = set()
        if self.sel is not None and self.view == len(self.moves) and not self.editing:
            src = self.human_view() if self.can_premove() else b
            moves = src.pseudo_legal_moves if self.can_premove() else src.legal_moves
            targets = {m.to_square for m in moves if m.from_square == self.sel}
        king_in_check = b.king(b.turn) if not self.editing and b.is_check() else None
        for sq in chess.SQUARES:
            x, y = self.xy(sq)
            base = self.light if (chess.square_file(sq) + chess.square_rank(sq)) % 2 else self.dark
            hl = None
            if last and sq in (last.from_square, last.to_square):
                hl = HL_YELLOW
            if sq == self.sel:
                hl = HL_YELLOW
            if self.premove and not self.editing and sq in self.premove:
                hl = HL_PREMOVE
            if sq == king_in_check:
                hl = HL_CHECK
            if bimg is None:
                color = base if hl is None else (hl if hl == HL_CHECK else mix(base, hl, 0.6))
                c.create_rectangle(x, y, x + S, y + S, fill=color, outline="")
            elif hl:
                c.create_rectangle(x, y, x + S, y + S, fill=hl, outline="", stipple="gray50")
            lab = self.dark if base == self.light else self.light
            if x == 0:
                c.create_text(x + 4, y + 8, text=str(chess.square_rank(sq) + 1), anchor="w",
                              fill=lab, font=("Arial", 9, "bold"))
            if y == 7 * S:
                c.create_text(x + S - 4, y + S - 8, text=chess.FILE_NAMES[chess.square_file(sq)],
                              anchor="e", fill=lab, font=("Arial", 9, "bold"))
            if sq in targets:
                cx, cy = x + S / 2, y + S / 2
                if b.piece_at(sq) or b.is_en_passant(chess.Move(self.sel, sq)):
                    c.create_oval(x + 4, y + 4, x + S - 4, y + S - 4, outline=HL_MOVE, width=5)
                else:
                    c.create_oval(cx - 10, cy - 10, cx + 10, cy + 10, fill=HL_MOVE, outline="")
        for sq, p in b.piece_map().items():
            if sq == self.hide_sq and self.view == len(self.moves):
                continue
            x, y = self.xy(sq)
            self.put_piece(c, x + S / 2, y + S / 2, S * 0.94, p)
        for sq, col in ({} if self.editing else self.marks).items():   # círculos do botão direito
            x, y = self.xy(sq)
            c.create_oval(x + 3, y + 3, x + S - 3, y + S - 3, outline=col, width=max(3, S // 16))
        for (a, b2), col in ({} if self.editing else self.arrows).items():   # setas do botão direito
            self.draw_arrow(c, a, b2, col)
        if last:                                          # selo da classificação no lance
            key = self.move_class(self.view - 1)
            if key:
                x, y = self.xy(last.to_square)
                r = max(9, S * 0.17)
                paint_badge(c, x + S - r - 2, y + r + 2, r, key)
        if self.editing:
            self.nav_var.set("Editando posição")
            self.status.set("Editor de posição: monte o cenário e clique em 'Jogar a partir daqui' na janela do editor.")
            return
        n = len(self.moves)
        self.nav_var.set("Posição atual" if self.view == n else
                         f"Revendo lance {self.view}/{n} (só visualização)" if self.view else f"Posição inicial (de {n})")
        self.draw_evalbar(b)
        self.update_feedback()
        self.update_status(b)

    def draw_evalbar(self, b):
        c, H = self.evalbar, 8 * self.sq
        c.delete("all")
        ev = self.analyzer.cache.get(b.fen())
        cp = ev[0] if ev else 0
        m = mate_in(ev)
        wp = (1.0 if m[0] else 0.0) if m else winp(cp)       # mate: a barra enche por completo
        c.create_rectangle(0, 0, 32, H, fill="#161616", outline="")
        if self.flipped:
            c.create_rectangle(0, 0, 32, wp * H, fill="#ffffff", outline="")
        else:
            c.create_rectangle(0, H - wp * H, 32, H, fill="#ffffff", outline="")
        if ev:
            white_better = m[0] if m else cp >= 0
            at_bottom = white_better != self.flipped          # número no lado de quem está melhor
            y = H - 12 if at_bottom else 12
            if m:
                c.create_rectangle(1, y - 10, 31, y + 10, fill="#c0392b", outline="")
                c.create_text(16, y, text=fmt_ev(ev, True), fill="#ffffff", font=("Arial", 9, "bold"))
            else:
                c.create_text(16, y + (2 if at_bottom else -2), text=fmt_cp(cp).replace(" ou mais", "+").replace(" ou menos", "-"),
                              fill="#161616" if white_better else "#ffffff", font=("Arial", 8, "bold"))

    def update_feedback(self):
        c = self.fb_icon
        c.delete("all")
        title, sub, color, key = "", "", "#ffffff", None
        if self.view == 0:
            if not self.analyzer.path:
                title, sub = "Stockfish não configurado", "Clique em 'Stockfish...' para ver a classificação dos lances."
            else:
                title, sub = "Julgamento de lances", ("Faça um lance: o Stockfish vai classificá-lo aqui.\n"
                                                      "Botão direito no tabuleiro: setas e círculos.")
        else:
            k = self.view - 1
            key = self.move_class(k)
            if key:
                label, _, color, desc = CLASSES[key]
                title = f"{self.sans[k]}  {label}"
                after = self.analyzer.cache.get(self.boards[k + 1].fen())
                best = self.analyzer.cache[self.boards[k].fen()][1]
                extra = ""
                if best:
                    extra = ("   Foi o melhor lance" if best == self.moves[k]
                             else "   Melhor: " + self.boards[k].san(best))
                sub = f"{desc}\nAvaliação: {fmt_ev(after)}{extra}"
            else:
                title = self.sans[k]
                ev0 = self.analyzer.cache.get(self.boards[k].fen())
                if ev0 and ev0[1]:
                    title += "   " + ("melhor lance" if ev0[1] == self.moves[k] else "melhor: " + self.boards[k].san(ev0[1]))
                busy = self.analyzer.path and (self.auto.get() or self.analyzer.running)
                sub = "Analisando o lance..." if busy else "Sem análise deste lance. Ative 'Julgar ao jogar'."
        self.fb_title.config(text=title, fg=color if key else "#ffffff")
        self.fb_sub.config(text=sub)
        if key:
            paint_badge(c, 22, 22, 17, key)

    def update_status(self, b):
        parts = []
        end = self.resign_text() if self.resigned is not None else "Empate por acordo" if self.drawn else self.time_result() if self.clock.flag is not None else (
            result_text(b) if self.view == len(self.moves) else None)
        parts.append(end or (("Brancas" if b.turn else "Pretas") + " jogam" + (" - xeque!" if b.is_check() else "")))
        if self.premove:
            parts.append(f"Premove armado: {chess.square_name(self.premove[0])}-{chess.square_name(self.premove[1])} "
                         "(Esc ou botão direito cancela)")
        ev = self.analyzer.cache.get(b.fen())
        self.eval_var.set(fmt_ev(ev) if ev else ("-" if self.analyzer.path else "sem Stockfish"))
        self.line_var.set("")
        if ev:
            parts.append("Avaliação: " + fmt_ev(ev))
        if self.view > 0:
            j = self.analyzer.judge(self.boards, self.view - 1)
            if j and j[1]:
                bs = self.boards[self.view - 1].san(j[1])
                parts.append(f"Perda de {j[0]} cp (melhor: {bs})" if j[0] > 50 else f"Melhor lance: {bs}")
        if self.clock.paused:
            parts.append("relógio pausado")
        if self.analyzer.running:
            parts.append("analisando...")
        if self.ai_busy:
            parts.append("IA pensando...")
        if self.analyzer.path:
            parts.append("Stockfish: " + os.path.basename(self.analyzer.path))
        else:
            parts.append("Stockfish não configurado: clique em 'Stockfish...'")
        if ev and ev[4] and ev[3]:
            try:
                parts.append("Sequência: " + b.variation_san(list(ev[3])))
            except ValueError:
                pass
        if ev and ev[1] and not ev[4]:
            try:
                self.line_var.set("Melhor lance: " + b.san(ev[1]))
            except ValueError:
                pass
        elif ev and ev[4] and ev[3]:
            try:
                self.line_var.set("Sequência de mate: " + b.variation_san(list(ev[3])))
            except ValueError:
                pass
        self.status.set("  |  ".join(parts))

    # ---------------- Stockfish ----------------
    def pick_engine(self):
        p = filedialog.askopenfilename(title="Selecione o executável do Stockfish")
        if p:
            self.analyzer.path, self.analyzer.error = p, None
            self.auto.set(True)
            save_cfg(stockfish=p)
            self.refresh()

    def start_analysis(self, force=False):
        a = self.analyzer
        if a.running:
            return
        if not a.path:
            if not force:
                return
            self.pick_engine()
            if not a.path:
                return
        todo = [b for b in self.boards if b.fen() not in a.cache]
        if todo:
            try:
                a.depth = int(self.depth.get())
            except ValueError:
                a.depth = 12
            a.running = True
            threading.Thread(target=a.run, args=(todo,), daemon=True).start()

    def poll(self):
        a = self.analyzer
        if a.error:
            messagebox.showerror("Stockfish", f"Não foi possível usar o Stockfish:\n{a.error}")
            a.error, a.path = None, None
            self.auto.set(False)
        if self.ai_result and not self.clock.paused:
            ply, mv = self.ai_result
            self.ai_result = None
            if mv and ply == len(self.moves) and mv in self.boards[-1].legal_moves and not self.game_over():
                at_end = self.view == len(self.moves)
                mover = self.boards[-1].turn
                self._push(mv)
                self.clock.moved(mover, len(self.moves))
                if at_end:
                    self.view = len(self.moves)
                self.sel = None
                self.refresh()
                self.announce(self.boards[-1], mv)
                self.check_end()
                self.try_premove()
        self.maybe_ai()
        if self.auto.get() and not a.running:
            self.start_analysis()
        state = (len(a.cache), a.running, self.ai_busy)
        if state != self._seen:
            self._seen = state
            self.refresh()
        self.after(250, self.poll)

    # ---------------- jogar contra a IA ----------------
    def elo_value(self):
        try:
            return max(ELO_MIN, min(ELO_MAX, int(self.elo.get())))
        except ValueError:
            return 1500

    def ai_delay(self):
        try:
            return max(0.0, min(15.0, float(self.ai_pause.get().replace(",", "."))))
        except ValueError:
            return 2.0

    def on_mode(self, *_):
        m = self.mode.get()
        self.ai_color = chess.BLACK if "brancas" in m else chess.WHITE if "pretas" in m else None
        if self.ai_color is not None:
            self.flipped = self.ai_color == chess.WHITE        # você fica embaixo
        self.sel, self.ai_result, self.premove = None, None, None
        self.refresh()

    def maybe_ai(self):
        b = self.boards[-1]
        if (self.ai_color is None or self.ai_busy or self.ai_result or not self.analyzer.path or self.editing or self.sp_active
                or self.game_over() or self.clock.paused or b.turn != self.ai_color):
            return
        self.ai_busy = True
        left = self.clock.left[self.ai_color] if self.clock.enabled else None
        threading.Thread(target=self._ai_think,
                         args=(b.copy(), len(self.moves), self.elo_value(), self.ai_delay(), left),
                         daemon=True).start()

    def _ai_think(self, board, ply, elo, delay, left):             # roda em thread
        try:
            t0 = time.monotonic()
            secs = 0.6 if left is None else max(0.05, min(0.6, left / 30))
            mv = self.analyzer.best_move(board, elo, secs)
            while time.monotonic() - t0 < delay and len(self.moves) == ply:
                time.sleep(0.05)                                   # pausa para você conseguir ler o feedback
            self.ai_result = (ply, mv)
        except Exception as e:
            self.analyzer.error = str(e)
        finally:
            self.ai_busy = False

    # ---------------- resumo ----------------
    # ---------------- relatório da partida ----------------
    def open_report(self):
        if not self.moves:
            messagebox.showinfo("Relatório", "A partida ainda não tem lances.")
            return
        if not self.analyzer.path:
            messagebox.showinfo("Relatório", "O relatório precisa do Stockfish. Use o botão 'Stockfish...'.")
            return
        if self.report_win is not None and self.report_win.winfo_exists():
            self.report_win.lift()
            self.report_win.refresh(True)
        else:
            self.report_win = GameReport(self)
        if not self.analyzer.running and any(b.fen() not in self.analyzer.cache for b in self.boards):
            self.start_analysis(True)

    def check_end(self):
        """Quando a partida acaba, abre o relatório (uma vez por partida)."""
        if self.sp_active or self.editing or not self.game_over() or self._report_gid == self.game_id:
            return
        self._report_gid = self.game_id
        if self.report_auto.get() and len(self.moves) >= 2:
            self.after(1500, self.open_report)

    # ---------------- importar PGN ----------------
    def import_pgn(self):
        p = filedialog.askopenfilename(title="Importar banco de partidas",
                                       filetypes=[("PGN", "*.pgn"), ("Todos", "*.*")])
        if p:
            Library(self, p)


# --------------------------------------------------------------------------
# Skin padrão "Classico" (embutida; é gravada em skins/Classico na primeira execução)
# --------------------------------------------------------------------------
DEFAULT_SKIN = "Classico"
DEFAULT_SKIN_DATA = {
    "wK": "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",
    "wQ": "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",
    "wB": "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",
    "wN": "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",
    "wR": "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",
    "wP": "iVBORw0KGgoAAAANSUhEUgAAAIAAAACACAYAAADDPmHLAAANkUlEQVR42u1dfWhV5xn/vefcfH8ao1k1fmBoo7ZxttNam6i0GY7YbcXZiFOGDOv8w6CIY8U6qE5coX8M6mAFy1pdR6cUBqVIEWqthYKmJaBuasVaN5KaxpH4EW2Te8/77I/zPjdvjjdtbj7O/cjzg8slIbnnnvP8ns/3eZ8XEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQZDzUBLtXBcAxP5N1/wRAm3dBlsEBEBnm37oWQcQCZMG9OQA883MugEcA1AGYBqAIwLcAOgFcAHAWwF2LCGIRMlzrGTUA/gjgoiEDDfH6D4C/AHg0YBEEGSr8AgD7ANy2Ba2UirmuG+WX4zjRABH6ARwEMFVIkHlwLa0/bQk16rqup5TSQ2i/dl1XK6VsMlwB8ES2k0BlmeZrAA8BOA5gNoCoUioCQBH57ryqqgo1NTUoLS3FvXv3cPXqVbS3tw98iOOQ1tozgeMdAM8COGlI4ImOpXfANxnAJdZ6x3HiWt7c3Ezvv/8+3bx5k2z09vbSqVOnaPPmzZSbm0sAyHVdAhAz/9sNoDZBbCFIQ79/JCj86upqOnbsGAWhtb7vd6dPn6YFCxYkIsEZk0UIAdLY7/8kKPw5c+bQ5cuXiYgoFotRLBYjrfUg4WutKRaLUTQaJSKi7u5uWrp0KQEg8zkcF2yVoDB9tV8BOMVRvuM4VFRURG1tbURE1N/fT8MBk+D69etUXV1NSilyHMczscWXpnagMLEqqBmh/QtNgKZd19UAaM+ePUkJP0iCt99+23YFXD/4hViB9AKXeHcZ7Y8CoIqKCurq6rrP3A8HWmvyPI+i0SjNnz+fXUHUWIE3s40AmR7UaPP+BAC4rqsAoLGxEVOmTAERQankrLVSClprRCIRrF69mlNDdjOPWumgEgKkHryiNxsAiEgBwOLFi0FE0FqP6sMXLVrks0xrFvYMACXZmD5lau5PAPJNcBbHtGnToJRKWvttKwAAU6dOZQLw7woAlGZTEU3yWkmhMt78fwug19bc9vZ2EBG4/Jv0B5v/+/rrrzkG4N99A39xia8vBEgTN/ClLZTW1lYopeDHbiNHa2srE4CF/V+LAII0SgN/Z6eB5eXl1NnZGU/pRpIG9vX1UW1tbTAN/KvUAdK3EKTtQtCuXbsGFXaSLQQdOnRICkEZZgXeg1UKzs/Pp9bW1vg6wHDA1qKjo4OqqqrsUjAB+JclfCkFp5nwHzUC0gA813XJcRx68MEH6auvvhqWK+C/uX37Nj311FO29mvz6oC/4GRfV5AG5n8VgJtGS7XjOKSUIgBUVlZGH3zwQXzFbzjaf/nyZZo1a1a8j8AEgNxJ5AHYIm4gfYT/U/g9fAQgZjSWANDzzz9PHR0dQ679D2UFiIhu3bpFL730EhUVFQXjACZCi1iC1KeuS+C3ccfNPgCqra2lDz/88DsbP4ZDAiKi8+fPU319fdAdcJPIWrEEqRG+AjAFwLWg5jc2NlJXV1c88EtW+DYJOBvo6+ujjRs3EgCKRCJsCTz4/YKPZEk9JeNM/z8w0O1LAGjlypV09+7dEaV+Q8GOGzZv3jxUq1iORUxBSEHfoNavuro6unXr1qBgbqxgZxBNTU02CbhVbLu4gvEHt2FFALQh0Pp19uzZpPL9ZOF5Hmmtqauri6ZPn871AW1cQSf8bmRpFQtB+5/ldIxN/969e8fU7H+fOzhy5IidHrIr+K1kBeFE/sdMrh8FQLNmzaI7d+7ENXS8wYGllRlwavhv+G3jYgXGUfgz4S/7Etf79+/fP66mf6h1gnfeeSdRkahBYoHxNf+/Yt8PgAoLC+nKlSsjWvEbTUDIu4mqq6vtlUIC8IdMdAOZkL+ySW2wtA4LFy7EnDlz/JtwwrkNpRQ8z0NRUREaGxv52vz96s27FgKMrfB5Q+ZcXwZ+28+TTz4Z7+ANE9xptHTpUv6ZCTAHfm+izqQ4IBMsAAHIg9+RG7cI8+fPjwskVEaaZtOHH37YV/eBjuEpGJgpIAQYYxQAmAQAnucpwN/mzQIJmwAAUFlZCdd1QURslIqQgS3jmUKAvGBwVVBQkNIvlJubi7y8PNtKwaSCYgHGAR4CXbiel9pZDVrrRN9BBwghBBgjfAvgnm2Cb968mZIYgNHb24u+vj4opcgEgjH+juICxh7fwK+5x1u0r127lpqI1BCOr2+loD3wp4mIBRjjDIA3Y141Aoj3/odZAwgS4NNPP+WgkIV9HcD/kGGl4EwqBH1mfC8BwCeffII7d+7Yu3ZCgev6hckTJ05wLMB+v83EAA5kwOTYPnPzvthYAs19AO++++6g7p3xBi86nTt3jnJycrj5lFcEf2m+p6wIjlfmBX8CmDarcNTU1BTqYhBfZ9u2bdwixgtBtwD8INNSwEy0Ar+H1QziOA6dOnUqFBKw9l+9epVKS0tJKUXWYMm/Bb6nYJxilWr4zZjadOTQ4sWLKRqNjqoJNJml4LVr1yZqFV8qBAjPCryMQEPoiy++OKKBUMMFf+4bb7yRqDH0nxmWUmcseBpoBfxtWlopFW8NO3ToUFxTx9ISsPA/+ugjKiwsJNd1ycwc9kx9Yq5of/hW4GdG+7RSSjuOQ67r0uuvvz7IX4+2+YPN/vHjx2nSpEmJegF3iPDDB6dZe4wWeiYgI1jbwkeyKygRXnvtNcrJybGFz+sSh41FypHIPzWFqwb45VdtLAH7Zlq/fj319PSMeE6g1pr6+/vphRdeiAveGjztwd+PuD6BZRKEYP5LAPwJA82Yg4TPL94plCwJPM8jz/Noy5Ytgz4vEonYJOBr/x3+8TNCgpDM/mPwz/aJC8YWvFKK6uvr6dVXX6WLFy+Oam/gF198QW+99RatXLkyPkaer2fcDZOgA/4uZSaBuIMxjvxZszaYGkB8Wxj7/cmTJ9POnTvpzJkz45IGXrhwgfbu3ZtoboB9wsguy00JCcbY7O+0HvSgOQBbt26l9vb2+4o2o20V56ESthXp6emhffv2JZobwIHhASHB+ET7nHpps0Wbamtr6cSJE/cJfTyqgTw8mnHu3DlqaGiwXYK2rMFhIcHYCX8Xm3z4i0AEgFavXk03btwY9RyA0c4NaGlpibsD446YBAet+xASjNDsb7I1n4Xf0tKScP9+mLCv+8orrwRJwCNr9gfILEhC+MvNg4wB8Njsc82fU7VUwrYGBw8eHModbJQUMbkijzJ5dQcXXVj4O3bsCN3kJ7NKeODAgSAJeK3gR0KC5NK99xBY7Vu3bl1aCj9Igt27dydaLTwPoFBqBMMz/S1B4S9atIh6e3tDmwEwWnewZs2aRGNk/ixW4PtN/2z4Ax89x3G04zhUUlJCn3/+eUoDvmTXELq7u6mmpoYDQx4rpzGwe1hIMIT2Hw0Wenh5N6ymz7HKDk6ePEmu63I8wK7gM8hEsSGF3xgU/qpVqzJC84ciwfbt2xPFA78RK5DY/H+MwOSvS5cuhTr9Y6zHyvX09NCMGTMSHT5ZDJklNEgLeO5fvL1r9+7dGan9QStw+PDhRF1E28QKDKR+gHXkq1KKKisrqaurK62j/mQOn7QOo5YjaBNof31Q+/ft25fR2h+0AkePHk108si6iW4F+MbfhDX5a/LkyXTjxo0RtXKlqyXo7++3j6DllPBkwAqmNAhLhen34M/TeRYAXNd1AGDDhg2orKy0D2rMaHieh5ycHGzatMm/caWY+Mvgn3JCmID7CXh17Ne273ddl9ra2jIy8v+uPgIios7OznhbubWd7OV0cAOpYB9vp17DETIR4fHHH8fChQtBRKHv+R+3h+s48DwPVVVVeOaZZ2BbOwA/N4UhbyIRwDEEqILf1q3YLD733HMpmfsXBogIzc3NPvu15vkBcwH8MNVWIGwC2FM/y5RSOhaLqUgkgqamprjWZFWly3GglMLy5ctRVVXF8Y1nnv2PUx0MpuppP42BxRLU1dWhtraWA6XsKnYYq1ZeXo6GhgYmBd/kioBbzHoC8AiVJ4z5dwBgxYoVcBwHsVgs6whgzL7P+qefZlLwc38MQBlSOF7WCflaBGA6gIeMb1QAsGzZsqzUftsNAMCSJUuY6Mr0D05Fig+eCvOiLN1aAMVKKe15nsrPz8eCBQuymgB8X/PmzcMDDzwQLxOY97pUxgGpIECdeSgEADNnzsSMGTOyngBEhMLCwviQaSsOYAJQthOAMdcmQE1NDfLy8rKm+jcUeKzs3Llzg2SfN1EIwCZvtnkAyn4gqRr5GrYb4GzHOmdgOvwJaCkJBMMigDIMj5gbjrsEPvUj2wnAqKmpCRKg0rwmRBpYAL8KGD9oYdq0aVnt/4MWgINA66CJcvNCtlsAvtkiOzeurKzEREJpaSmKi4uZFFwXmZTtBGBMApDL2uC6LioqKiaUBSguLkZJSUnwniuy3QXwnRbBWvjIzc1FWVnZoGJJthOgpKTEPu2EA5+UHTUT9s7VAhMAEQDV39+P5uZm5OXlTYggkNcFOjs7YbtB+FvHJgQBVDA3PnPmDASp6wpKBQG4PVqx6c92/39fQWTgrKHgWUgq2wmQH7xmNjaAjOD5F2e7BWCWXwSw27YAExzaBMUfWz8LBCkKykK6nmyMTGwJRPsFAoFAIBAIBAKBQCAQCAQCgUAwHvg/FNcpxZGUdQ8AAAAASUVORK5CYII=",
    "bK": "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",
    "bQ": "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",
    "bB": "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",
    "bN": "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",
    "bR": "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",
    "bP": "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",
}


def ensure_default_skin():
    """Cria skins/Classico com as 12 peças se a pasta ainda não existir."""
    d = os.path.join(SKIN_DIR, DEFAULT_SKIN)
    if os.path.isdir(d):
        return
    try:
        import base64
        os.makedirs(d)
        for k, v in DEFAULT_SKIN_DATA.items():
            with open(os.path.join(d, k + ".png"), "wb") as f:
                f.write(base64.b64decode(v))
    except OSError:
        pass


if __name__ == "__main__":
    App().mainloop()
