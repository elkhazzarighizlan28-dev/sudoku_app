"""
SUDOKU ÉLITE — Onyx & Or
Fonctions : 4 niveaux, thèmes Nuit/Ivoire, plateau dessiné sur Canvas, notes au crayon,
annuler/rétablir, indices intelligents, surbrillance, limite d'erreurs, pause,
compteurs de chiffres restants, meilleurs temps, sauvegarde automatique, animation de victoire.
Raccourcis : 1-9 saisir | N notes | U/Ctrl+Z annuler | Ctrl+Y rétablir | H indice
             P pause | T thème | Suppr effacer | Flèches naviguer
"""
import json
import random
import threading
import time
import tkinter as tk
from tkinter import messagebox
from pathlib import Path

APP_DIR = Path.home() / ".sudoku_elite"
SAVE_FILE = APP_DIR / "save.json"
STATS_FILE = APP_DIR / "stats.json"
FONT = "Georgia"
MAX_MISTAKES = 3
LEVELS = {"Facile": 40, "Moyen": 34, "Difficile": 29, "Expert": 25}
MULT = {"Facile": 1, "Moyen": 2, "Difficile": 3, "Expert": 4}

THEMES = {
    "Onyx": dict(bg="#0A0A0B", panel="#111113", cell="#141416", fixed="#F3E9D2", user="#D4AF37",
                 accent="#D4AF37", on_accent="#0A0A0B", sel="#3A3015", rel="#1B1B1E", same="#2B2512",
                 err="#3A1518", errt="#E5596B", muted="#8A8576", thin="#2A2A2E", thick="#B8962E",
                 good="#D4AF37", note="#9C9378", btn="#18181B", btnh="#252529"),
    "Champagne": dict(bg="#F6F1E7", panel="#FFFDF8", cell="#FFFDF8", fixed="#1A1A1C", user="#8A6A12",
                      accent="#A8801A", on_accent="#FFFDF8", sel="#EBDDB4", rel="#F6EFDC", same="#EFE2BC",
                      err="#F8DADD", errt="#B3283C", muted="#7A7260", thin="#E0D6BC", thick="#A8801A",
                      good="#8A6A12", note="#8F8668", btn="#EFE7D3", btnh="#E3D8BC"),
}


# ------------------------------------------------------------------ Moteur
def search(grid, limit=2, keep=False, shuffle=False):
    """Compte les solutions (jusqu'à limit). keep=True laisse la 1re solution dans grid."""
    rows, cols, boxes = [0] * 9, [0] * 9, [0] * 9
    for r in range(9):
        for c in range(9):
            v = grid[r][c]
            if v:
                bit = 1 << v
                rows[r] |= bit; cols[c] |= bit; boxes[r // 3 * 3 + c // 3] |= bit

    def rec():
        best, best_m, best_n = None, 0, 10
        for r in range(9):
            for c in range(9):
                if grid[r][c] == 0:
                    m = ~(rows[r] | cols[c] | boxes[r // 3 * 3 + c // 3]) & 0x3FE
                    n = bin(m).count("1")
                    if n < best_n:
                        best, best_m, best_n = (r, c), m, n
                        if n == 0:
                            return 0
        if best is None:
            return 1
        r, c = best
        b = r // 3 * 3 + c // 3
        digits = [d for d in range(1, 10) if best_m >> d & 1]
        if shuffle:
            random.shuffle(digits)
        total = 0
        for d in digits:
            bit = 1 << d
            grid[r][c] = d
            rows[r] |= bit; cols[c] |= bit; boxes[b] |= bit
            total += rec()
            if keep and total >= limit:
                return total
            grid[r][c] = 0
            rows[r] &= ~bit; cols[c] &= ~bit; boxes[b] &= ~bit
            if total >= limit:
                return total
        return total

    return rec()


def generate(clues):
    sol = [[0] * 9 for _ in range(9)]
    search(sol, 1, keep=True, shuffle=True)
    puz = [r[:] for r in sol]
    cells = [(r, c) for r in range(9) for c in range(9)]
    random.shuffle(cells)
    count = 81
    for r, c in cells:
        if count <= clues:
            break
        r2, c2 = 8 - r, 8 - c  # symétrie centrale = esthétique
        if puz[r][c] == 0:
            continue
        a, b = puz[r][c], puz[r2][c2]
        puz[r][c] = puz[r2][c2] = 0
        if search([x[:] for x in puz], 2) == 1:
            count -= 1 if (r, c) == (r2, c2) else 2
        else:
            puz[r][c], puz[r2][c2] = a, b
    return puz, sol


def peers(r, c):
    s = {(r, i) for i in range(9)} | {(i, c) for i in range(9)}
    br, bc = r // 3 * 3, c // 3 * 3
    s |= {(br + i, bc + j) for i in range(3) for j in range(3)}
    s.discard((r, c))
    return s


def fmt(sec):
    m, s = divmod(max(0, int(sec)), 60)
    h, m = divmod(m, 60)
    return f"{h:d}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


# ------------------------------------------------------------------ Widgets
class FlatButton(tk.Label):
    def __init__(self, parent, text, command, app, primary=False, **kw):
        super().__init__(parent, text=text, cursor="hand2", **kw)
        self._cmd, self.app, self.primary, self.active = command, app, primary, False
        self.bind("<Button-1>", lambda e: self._cmd())
        self.bind("<Enter>", lambda e: self.paint(True))
        self.bind("<Leave>", lambda e: self.paint(False))
        self.paint()

    def paint(self, hover=False):
        t = self.app.t
        if self.primary or self.active:
            bg, fg = (t["accent"], t["on_accent"])
        else:
            bg, fg = (t["btnh"] if hover else t["btn"], t["fixed"])
        self.configure(bg=bg, fg=fg)


# ------------------------------------------------------------------ Application
class SudokuElite:
    S, M = 52, 12  # taille cellule, marge

    def __init__(self, root):
        self.root = root
        root.title("Sudoku Elite")
        root.report_callback_exception = lambda *a: messagebox.showerror("Erreur", "".join(__import__("traceback").format_exception(*a))[-900:])
        root.resizable(False, False)
        self.theme_name = "Onyx"
        self.t = THEMES[self.theme_name]
        self.level = "Difficile"
        self.puzzle = self.solution = self.values = [[0] * 9 for _ in range(9)]
        self.notes = [[set() for _ in range(9)] for _ in range(9)]
        self.fixed, self.selected = set(), None
        self.undo_stack, self.redo_stack = [], []
        self.notes_mode = self.paused = self.over = False
        self.mistakes = self.hints = self.score = 0
        self.base, self.start = 0, time.time()
        self.wave = -1
        self.generating = False
        self.stats = self.load_stats()
        self.buttons, self.pad = [], {}
        self.build()
        root.bind("<Key>", self.on_key)
        root.bind("<Control-z>", lambda e: self.undo())
        root.bind("<Control-y>", lambda e: self.redo())
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        if SAVE_FILE.exists() and messagebox.askyesno("Reprendre", "Une partie sauvegardée existe. La reprendre ?"):
            if not self.load():
                self.new_game()
        else:
            self.new_game()
        self.tick()

    # ---------- construction UI
    def build(self):
        size = 9 * self.S + 2 * self.M
        self.main = tk.Frame(self.root)
        self.main.pack(padx=16, pady=14)
        self.left = tk.Frame(self.main)
        self.left.pack(side="left")
        self.canvas = tk.Canvas(self.left, width=size, height=size, highlightthickness=0)
        self.canvas.pack()
        self.canvas.bind("<Button-1>", self.on_click)

        self.right = tk.Frame(self.main, width=300)
        self.right.pack(side="left", fill="y", padx=(22, 0))
        self.title = tk.Label(self.right, text="S U D O K U", font=(FONT, 24), anchor="w")
        self.title.pack(fill="x")
        self.subtitle = tk.Label(self.right, text="— É L I T E —", font=(FONT, 10, "italic"), anchor="w")
        self.subtitle.pack(fill="x", pady=(0, 8))

        self.stat_frame = tk.Frame(self.right)
        self.stat_frame.pack(fill="x")
        self.stat_vars, self.stat_labels = {}, []
        for i, (key, lab) in enumerate([("time", "TEMPS"), ("score", "SCORE"), ("err", "ERREURS")]):
            card = tk.Frame(self.stat_frame, padx=10, pady=8)
            card.grid(row=0, column=i, sticky="ew", padx=(0 if i == 0 else 6, 0))
            self.stat_frame.grid_columnconfigure(i, weight=1, uniform="s")
            l1 = tk.Label(card, text=lab, font=(FONT, 8, "bold"), anchor="w")
            v = tk.StringVar()
            l2 = tk.Label(card, textvariable=v, font=(FONT, 17), anchor="w")
            l1.pack(fill="x"); l2.pack(fill="x")
            self.stat_vars[key] = v
            self.stat_labels.append((card, l1, l2))

        self.level_frame = tk.Frame(self.right)
        self.level_frame.pack(fill="x", pady=(10, 0))
        self.level_btns = {}
        for name in LEVELS:
            b = FlatButton(self.level_frame, name.upper(), lambda n=name: self.set_level(n), self,
                           font=(FONT, 8, "bold"), pady=8)
            b.pack(side="left", expand=True, fill="x", padx=2)
            self.level_btns[name] = b

        self.pad_frame = tk.Frame(self.right)
        self.pad_frame.pack(fill="x", pady=10)
        for n in range(1, 10):
            f = tk.Frame(self.pad_frame)
            f.grid(row=(n - 1) // 3, column=(n - 1) % 3, padx=3, pady=3, sticky="nsew")
            self.pad_frame.grid_columnconfigure((n - 1) % 3, weight=1, uniform="p")
            b = FlatButton(f, str(n), lambda k=n: self.enter(k), self, font=(FONT, 17, "bold"), pady=3)
            b.pack(fill="x")
            c = tk.Label(f, text="", font=(FONT, 7))
            c.pack()
            self.pad[n] = (f, b, c)

        self.tools = tk.Frame(self.right)
        self.tools.pack(fill="x")
        specs = [("ANNULER", self.undo), ("RÉTABLIR", self.redo), ("NOTES · OFF", self.toggle_notes),
                 ("INDICE", self.hint), ("EFFACER", self.erase), ("PAUSE", self.toggle_pause),
                 ("NOUVELLE", self.new_game), ("SAUVER", self.save), ("THÈME", self.toggle_theme)]
        for i, (txt, cmd) in enumerate(specs):
            b = FlatButton(self.tools, txt, cmd, self, font=(FONT, 9, "bold"), pady=7,
                           primary=(txt == "NOUVELLE"))
            b.grid(row=i // 3, column=i % 3, sticky="ew", padx=3, pady=3)
            self.tools.grid_columnconfigure(i % 3, weight=1, uniform="t")
            self.buttons.append(b)
        self.notes_btn, self.pause_btn = self.buttons[2], self.buttons[5]

        self.status = tk.StringVar(value="")
        self.status_lbl = tk.Label(self.left, textvariable=self.status, font=(FONT, 11, "italic"),
                                   wraplength=470, justify="left", anchor="w")
        self.status_lbl.pack(fill="x", pady=(10, 0))
        self.best_lbl = tk.Label(self.right, text="", font=(FONT, 9), anchor="w")
        self.best_lbl.pack(fill="x", side="bottom")
        self.apply_theme()

    def apply_theme(self):
        t = self.t
        self.root.configure(bg=t["bg"])
        for w in (self.main, self.left, self.right, self.stat_frame, self.level_frame, self.pad_frame,
                  self.tools):
            w.configure(bg=t["bg"])
        self.canvas.configure(bg=t["bg"])
        self.title.configure(bg=t["bg"], fg=t["fixed"])
        self.subtitle.configure(bg=t["bg"], fg=t["muted"])
        self.status_lbl.configure(bg=t["bg"], fg=t["muted"])
        self.best_lbl.configure(bg=t["bg"], fg=t["muted"])
        for card, l1, l2 in self.stat_labels:
            card.configure(bg=t["panel"])
            l1.configure(bg=t["panel"], fg=t["muted"])
            l2.configure(bg=t["panel"], fg=t["fixed"])
        for f, b, c in self.pad.values():
            f.configure(bg=t["bg"]); c.configure(bg=t["bg"], fg=t["muted"]); b.paint()
        for b in self.buttons:
            b.paint()
        for n, b in self.level_btns.items():
            b.active = (n == self.level); b.paint()
        self.notes_btn.active = self.notes_mode
        self.notes_btn.paint()
        self.draw()

    # ---------- dessin
    def draw(self):
        c, t, S, M = self.canvas, self.t, self.S, self.M
        c.delete("all")
        size = 9 * S + 2 * M
        self.round_rect(2, 2, size - 2, size - 2, 6, fill=t["panel"])
        c.create_rectangle(4, 4, size - 4, size - 4, outline=t["thick"], width=1)
        c.create_rectangle(M - 5, M - 5, M + 9 * S + 5, M + 9 * S + 5, outline=t["thick"], width=1)
        if self.paused:
            c.create_text(size / 2, size / 2 - 10, text="P A U S E", fill=t["accent"], font=(FONT, 36))
            c.create_text(size / 2, size / 2 + 40, text="Appuyez sur P pour reprendre", fill=t["muted"],
                          font=(FONT, 13, "italic"))
            return
        sel = self.selected
        sel_val = self.values[sel[0]][sel[1]] if sel else 0
        rel = peers(*sel) if sel else set()
        for r in range(9):
            for col in range(9):
                v = self.values[r][col]
                x0, y0 = M + col * S, M + r * S
                bg = t["cell"]
                wrong = v and (r, col) not in self.fixed and v != self.solution[r][col]
                if sel and (r, col) in rel:
                    bg = t["rel"]
                if sel and sel_val and v == sel_val:
                    bg = t["same"]
                if wrong:
                    bg = t["err"]
                if sel == (r, col):
                    bg = t["sel"]
                if self.wave >= 0 and r + col <= self.wave:
                    bg = t["accent"] if r + col == self.wave else t["same"]
                c.create_rectangle(x0, y0, x0 + S, y0 + S, fill=bg, outline="")
                if v:
                    if wrong:
                        fg = t["errt"]
                    elif (r, col) in self.fixed:
                        fg = t["fixed"]
                    else:
                        fg = t["user"]
                    c.create_text(x0 + S / 2, y0 + S / 2, text=str(v), fill=fg,
                                  font=(FONT, 24, "bold" if (r, col) in self.fixed else "italic"))
                elif self.notes[r][col]:
                    for n in self.notes[r][col]:
                        nx = x0 + S / 6 + ((n - 1) % 3) * S / 3 + 1
                        ny = y0 + S / 6 + ((n - 1) // 3) * S / 3 + 1
                        hl = sel_val == n
                        c.create_text(nx, ny, text=str(n), fill=t["accent"] if hl else t["note"],
                                      font=(FONT, 10, "bold" if hl else "normal"))
        for i in range(10):
            thick = i % 3 == 0
            w, col = (3, t["thick"]) if thick else (1, t["thin"])
            p = M + i * S
            c.create_line(M, p, M + 9 * S, p, fill=col, width=w, capstyle="round")
            c.create_line(p, M, p, M + 9 * S, fill=col, width=w, capstyle="round")

    def round_rect(self, x0, y0, x1, y1, r, **kw):
        pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1, x1 - r, y1, x0 + r, y1,
               x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
        return self.canvas.create_polygon(pts, smooth=True, outline="", **kw)

    def refresh(self):
        self.stat_vars["score"].set(str(self.score))
        self.stat_vars["err"].set(f"{self.mistakes}/{MAX_MISTAKES}")
        for n, (f, b, c) in self.pad.items():
            done = sum(1 for r in range(9) for k in range(9) if self.values[r][k] == n
                       and self.values[r][k] == self.solution[r][k])
            left = 9 - done
            c.configure(text=f"{left} restant{'s' if left > 1 else ''}" if left else "✓")
            b.configure(fg=self.t["muted"] if left == 0 else self.t["fixed"])
        best = self.stats.get(self.level)
        self.best_lbl.configure(text=f"Meilleur temps ({self.level}) : {fmt(best) if best else '—'}")
        self.draw()

    # ---------- partie
    def set_level(self, name):
        if name == self.level:
            return
        self.level = name
        for n, b in self.level_btns.items():
            b.active = (n == name); b.paint()
        self.new_game(confirm=True)

    def new_game(self, confirm=True):
        if self.generating:
            return
        if confirm and not self.over and any(self.values[r][c] != self.puzzle[r][c]
                                              for r in range(9) for c in range(9)):
            if not messagebox.askyesno("Nouvelle partie", "Abandonner la partie en cours ?"):
                for n, b in self.level_btns.items():
                    b.active = (n == self.level); b.paint()
                return
        self.generating = True
        self.status.set(f"Génération d'une grille {self.level.lower()}…")
        result = {}

        def work():
            result["g"] = generate(LEVELS[self.level])

        th = threading.Thread(target=work, daemon=True)
        th.start()

        def poll():
            if th.is_alive():
                self.root.after(60, poll)
                return
            self.generating = False
            self.puzzle, self.solution = result["g"]
            self.values = [r[:] for r in self.puzzle]
            self.notes = [[set() for _ in range(9)] for _ in range(9)]
            self.fixed = {(r, c) for r in range(9) for c in range(9) if self.puzzle[r][c]}
            self.selected, self.undo_stack, self.redo_stack = None, [], []
            self.mistakes = self.hints = self.score = 0
            self.over = self.paused = False
            self.wave = -1
            self.base, self.start = 0, time.time()
            self.status.set(f"Niveau {self.level} — bonne chance !")
            self.refresh()

        poll()

    def elapsed(self):
        return self.base if self.paused else self.base + time.time() - self.start

    def tick(self):
        if not self.over:
            self.stat_vars["time"].set(fmt(self.elapsed()))
        self.root.after(500, self.tick)

    def toggle_pause(self):
        if self.over:
            return
        if self.paused:
            self.start = time.time()
        else:
            self.base += time.time() - self.start
        self.paused = not self.paused
        self.pause_btn.configure(text="REPRENDRE" if self.paused else "PAUSE")
        self.draw()

    def toggle_notes(self):
        self.notes_mode = not self.notes_mode
        self.notes_btn.configure(text=f"NOTES · {'ON' if self.notes_mode else 'OFF'}")
        self.notes_btn.active = self.notes_mode
        self.notes_btn.paint()

    def toggle_theme(self):
        self.theme_name = "Champagne" if self.theme_name == "Onyx" else "Onyx"
        self.t = THEMES[self.theme_name]
        self.apply_theme()

    # ---------- interactions
    def snapshot(self):
        self.undo_stack.append(([r[:] for r in self.values], [[set(s) for s in r] for r in self.notes],
                                self.score))
        self.undo_stack = self.undo_stack[-200:]
        self.redo_stack.clear()

    def restore(self, snap):
        self.values = [r[:] for r in snap[0]]
        self.notes = [[set(s) for s in r] for r in snap[1]]
        self.score = snap[2]

    def undo(self):
        if self.over or self.paused or not self.undo_stack:
            return
        self.redo_stack.append(([r[:] for r in self.values], [[set(s) for s in r] for r in self.notes],
                                self.score))
        self.restore(self.undo_stack.pop())
        self.refresh()

    def redo(self):
        if self.over or self.paused or not self.redo_stack:
            return
        self.undo_stack.append(([r[:] for r in self.values], [[set(s) for s in r] for r in self.notes],
                                self.score))
        self.restore(self.redo_stack.pop())
        self.refresh()

    def on_click(self, e):
        if self.paused or self.over:
            return
        c, r = (e.x - self.M) // self.S, (e.y - self.M) // self.S
        if 0 <= r < 9 and 0 <= c < 9:
            self.selected = (r, c)
            self.draw()

    def on_key(self, e):
        k = e.keysym
        if e.char and e.char in "123456789":
            self.enter(int(e.char))
        elif k in ("BackSpace", "Delete", "0"):
            self.erase()
        elif k.lower() == "n":
            self.toggle_notes()
        elif k.lower() == "u":
            self.undo()
        elif k.lower() == "h":
            self.hint()
        elif k.lower() == "p":
            self.toggle_pause()
        elif k.lower() == "t":
            self.toggle_theme()
        elif k in ("Up", "Down", "Left", "Right") and not self.paused:
            r, c = self.selected or (4, 4)
            dr, dc = {"Up": (-1, 0), "Down": (1, 0), "Left": (0, -1), "Right": (0, 1)}[k]
            self.selected = ((r + dr) % 9, (c + dc) % 9)
            self.draw()

    def editable(self):
        if self.over or self.paused:
            return None
        if not self.selected:
            self.status.set("Sélectionnez d'abord une case.")
            return None
        if self.selected in self.fixed:
            self.status.set("Les chiffres de départ sont verrouillés.")
            return None
        return self.selected

    def enter(self, n):
        cell = self.editable()
        if not cell:
            return
        r, c = cell
        if self.notes_mode:
            if self.values[r][c]:
                return
            self.snapshot()
            self.notes[r][c] ^= {n}
            self.refresh()
            return
        if self.values[r][c] == n:
            return
        self.snapshot()
        self.values[r][c] = n
        self.notes[r][c].clear()
        if n == self.solution[r][c]:
            self.score += 10 * MULT[self.level]
            for pr, pc in peers(r, c):
                self.notes[pr][pc].discard(n)
            self.status.set("Excellent !")
        else:
            self.mistakes += 1
            self.score = max(0, self.score - 15)
            self.status.set("Ce n'est pas la bonne valeur.")
        self.refresh()
        if self.mistakes >= MAX_MISTAKES:
            self.finish(False)
        elif self.values == self.solution:
            self.finish(True)

    def erase(self):
        cell = self.editable()
        if not cell:
            return
        r, c = cell
        if self.values[r][c] or self.notes[r][c]:
            self.snapshot()
            self.values[r][c] = 0
            self.notes[r][c].clear()
            self.refresh()

    def hint(self):
        if self.over or self.paused:
            return
        cell = self.selected
        if not cell or cell in self.fixed or self.values[cell[0]][cell[1]] == self.solution[cell[0]][cell[1]]:
            # cherche une case avec un seul candidat logique
            best = None
            for r in range(9):
                for c in range(9):
                    if self.values[r][c] != self.solution[r][c]:
                        used = {self.values[a][b] for a, b in peers(r, c)}
                        cand = [n for n in range(1, 10) if n not in used]
                        if best is None or len(cand) < best[0]:
                            best = (len(cand), (r, c))
            if not best:
                return
            cell = best[1]
        r, c = cell
        self.snapshot()
        self.values[r][c] = self.solution[r][c]
        self.notes[r][c].clear()
        for pr, pc in peers(r, c):
            self.notes[pr][pc].discard(self.solution[r][c])
        self.selected = cell
        self.hints += 1
        self.score = max(0, self.score - 20)
        self.status.set(f"Indice : ligne {r + 1}, colonne {c + 1} = {self.solution[r][c]}")
        self.refresh()
        if self.values == self.solution:
            self.finish(True)

    def finish(self, won):
        self.over = True
        t = self.elapsed()
        if won:
            bonus = max(0, 600 - int(t) // 2) * MULT[self.level] // 2 + max(0, 60 - 15 * self.hints)
            self.score += bonus
            record = self.hints == 0 and (self.level not in self.stats or t < self.stats[self.level])
            if record:
                self.stats[self.level] = int(t)
                self.save_stats()
            self.status.set("Grille résolue !" + ("  Nouveau record !" if record else ""))
            SAVE_FILE.unlink(missing_ok=True)
            self.selected = None
            self.animate_wave()
            self.refresh()
            self.root.after(1800, lambda: messagebox.showinfo(
                "Victoire", f"Niveau : {self.level}\nTemps : {fmt(t)}\nIndices : {self.hints}\nScore : {self.score}"
                            + ("\n\n★ Nouveau record ! ★" if record else "")))
        else:
            self.status.set("Trop d'erreurs — partie terminée.")
            self.values = [r[:] for r in self.solution]
            self.refresh()
            messagebox.showinfo("Perdu", "3 erreurs atteintes. La solution est affichée.")

    def animate_wave(self):
        def step():
            self.wave += 1
            self.draw()
            if self.wave < 18:
                self.root.after(70, step)
            else:
                self.wave = -1
                self.draw()
        step()

    # ---------- persistance
    def load_stats(self):
        try:
            return json.loads(STATS_FILE.read_text())
        except (OSError, ValueError):
            return {}

    def save_stats(self):
        try:
            APP_DIR.mkdir(parents=True, exist_ok=True)
            STATS_FILE.write_text(json.dumps(self.stats))
        except OSError:
            pass

    def save(self, quiet=False):
        if self.over or self.generating:
            return
        data = dict(puzzle=self.puzzle, solution=self.solution, values=self.values,
                    notes=[[sorted(s) for s in r] for r in self.notes], level=self.level,
                    elapsed=self.elapsed(), mistakes=self.mistakes, hints=self.hints, score=self.score)
        try:
            APP_DIR.mkdir(parents=True, exist_ok=True)
            SAVE_FILE.write_text(json.dumps(data))
            if not quiet:
                self.status.set("Partie sauvegardée.")
        except OSError as err:
            messagebox.showerror("Erreur", f"Sauvegarde impossible :\n{err}")

    def load(self):
        try:
            d = json.loads(SAVE_FILE.read_text())
            self.puzzle, self.solution, self.values = d["puzzle"], d["solution"], d["values"]
            self.notes = [[set(s) for s in r] for r in d["notes"]]
            self.fixed = {(r, c) for r in range(9) for c in range(9) if self.puzzle[r][c]}
            self.level = d.get("level", "Difficile")
            self.base, self.start = float(d["elapsed"]), time.time()
            self.mistakes, self.hints, self.score = d["mistakes"], d["hints"], d["score"]
            self.undo_stack, self.redo_stack, self.selected = [], [], None
            self.over = self.paused = False
            self.status.set("Partie chargée.")
            for n, b in self.level_btns.items():
                b.active = (n == self.level); b.paint()
            self.refresh()
            return True
        except (OSError, ValueError, KeyError, TypeError):
            return False

    def on_close(self):
        self.save(quiet=True)
        self.root.destroy()


if __name__ == "__main__":
    app_root = tk.Tk()
    SudokuElite(app_root)
    app_root.mainloop()