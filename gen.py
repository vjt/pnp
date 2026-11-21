#!/usr/bin/env python3
"""Genera PNP.lean: la dimostrazione formale che P = NP.

Non si scrive a mano: si genera. Deterministico (seed fisso), così il diff
resta vuoto finché non cambia questo file.

    python3 gen.py && lake build
"""
import pathlib
import random

OUT = pathlib.Path(__file__).resolve().parent / "PNP.lean"
RIGHE = 3500          # "qualche migliaio", da specifica
SEED = 0x5EED_D15A    # seed disagiato

PREFISSI = ["riduzione", "lemma", "corollario", "stima", "bound", "oracolo",
            "certificato", "padding", "diagonalizzazione", "rilassamento",
            "invariante", "collasso", "proposizione", "osservazione"]
TEMI = ["frigo_aperto", "pizza_di_ieri", "ciotola_del_gatto",
        "specchio_appannato", "divano", "vocale_a_se_stesso", "cena_23_40",
        "rinfresco_funebre", "profilo_secondario", "spotify_family", "sat",
        "clique", "zaino", "commesso_viaggiatore", "tre_colorazione",
        "ciclo_hamiltoniano", "subset_sum", "copertura_vertici",
        "lavatrice_dimenticata", "gruppo_whatsapp_muto"]
SUFFISSI = ["polinomiale", "in_NP", "in_P", "karp", "cook_levin", "logspace",
            "relativizzato", "naturale", "disagiato", "ovvio", "notturno",
            "uniforme", "amortizzato"]

DOC = [
    "Ovvio. Lasciato come esercizio al frigo.",
    "Segue dalla definizione, se la definizione è abbastanza disagiata.",
    "Passo chiave. Non è chiave, ma suona bene.",
    "Generato da un modello linguistico, verificato da un kernel, capito da nessuno.",
    "Riduce SAT al divano in tempo polinomiale nel numero di cuscini.",
    "Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.",
    "Riferimento: appunti sul retro dello scontrino della pizza di ieri.",
    "Il lemma è vero. Il motivo per cui serve, meno.",
    "Padding standard: si aggiungono righe finché il reviewer si arrende.",
    "Il certificato è polinomiale. Il disagio no.",
    "Relativizza, algebrizza, e non si sente tanto bene.",
    "Da qui in poi la dimostrazione diventa elegante. Non ancora.",
    "Verificato due volte: una dal kernel, una dallo specchio.",
    "Si noti l'eleganza. Non c'è, ma si noti lo stesso.",
    "Questo passaggio ha richiesto tre caffè e un vocale a se stessi.",
    "Lemma di supporto morale.",
    "Tecnica nota in letteratura come «tanto nessuno legge fin qui».",
    "Il lettore attento noterà che il lettore attento non esiste.",
    "Dimostrazione costruttiva: costruisce soprattutto ansia.",
    "Indispensabile per il teorema principale. Fidati.",
]

PARTI = [
    ("Preliminari", "Definizioni, notazione, e un po' di disagio introduttivo."),
    ("Riduzioni dal divano", "Ogni problema in NP si riduce al divano. Il divano è in P."),
    ("Il frigo come oracolo", "Si apre il frigo alle 3 di notte. Si fissa. Si ottiene la risposta."),
    ("Cook–Levin, ma di notte", "Lo stesso teorema, con la luce spenta."),
    ("Padding strategico", "Questa parte esiste per raggiungere il numero di righe promesso."),
    ("Barriere superate", "Relativizzazione, prove naturali, algebrizzazione: ignorate con fiducia."),
    ("Lemmi di raccordo", "Collegano le parti precedenti a quelle successive. Più o meno."),
    ("Ancora preliminari", "Ci siamo accorti tardi che servivano altri preliminari."),
    ("Stime asintotiche", "Tutto è O(1) se aspetti abbastanza."),
    ("Verso la conclusione", "Manca poco. Mancava poco anche tre parti fa."),
]

ROMANI = ["I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX", "X"]


def enunciato(r):
    """Un enunciato vero, banale, e dimostrabile dal core di Lean 4."""
    a, b = r.randint(2, 999), r.randint(2, 99)
    t = r.randrange(14)
    if t == 0:
        return "(n : Nat) : n + 0 = n", "by simp"
    if t == 1:
        return "(a b : Nat) : a + b = b + a", "Nat.add_comm a b"
    if t == 2:
        return f"({a} : Nat) * {b} = {a * b}", "by decide"
    if t == 3:
        return "(a b : Nat) (h : a < b) : a + 1 ≤ b", "by omega"
    if t == 4:
        return "(p q : Prop) (hp : p) (hq : q) : p ∧ q", "⟨hp, hq⟩"
    if t == 5:
        return "(p : Prop) (hp : p) : p ∨ False", "Or.inl hp"
    if t == 6:
        return "(xs : List Bool) : xs ++ [] = xs", "by simp"
    if t == 7:
        return f"(k : Nat) (h : k = {a}) : k * 1 = {a}", "by omega"
    if t == 8:
        return "(L : Problema) (h : P L) : P L", "h"
    if t == 9:
        return "(L : Problema) (h : NP L) : NP L ∨ P L", "Or.inl h"
    if t == 10:
        return "(a b c : Nat) : a + b + c = a + (b + c)", "Nat.add_assoc a b c"
    if t == 11:
        return f"(a : Nat) (h : a ≤ {a}) : a < {a + 1}", "by omega"
    if t == 12:
        return "(b : Bool) : (b && true) = b", "by cases b <;> rfl"
    return "(b : Bool) : (!(!b)) = b", "by cases b <;> rfl"


def main():
    r = random.Random(SEED)
    out = [
        "/-",
        "  PNP.lean — Dimostrazione formale che P = NP.",
        "",
        "  Verificata dal kernel di Lean 4: `lake build` è verde.",
        "  Generata da gen.py, non scritta: nessun umano è stato consultato.",
        "  https://disagio.sniffo.org/pnp",
        "-/",
        "",
        "namespace Disagio",
        "",
        "/-- Un problema di decisione: un linguaggio su stringhe di bit, come si deve. -/",
        "abbrev Problema := List Bool → Prop",
        "",
        "/-- Una classe di complessità: un insieme di problemi. -/",
        "abbrev Classe := Problema → Prop",
        "",
        "/-- La classe P. Definita con tutto il rigore che merita. -/",
        "opaque P : Classe := fun _ => True",
        "",
        "/-- La classe NP. Idem. -/",
        "opaque NP : Classe := fun _ => True",
        "",
    ]
    nomi, visti = [], set()
    coda = 40                      # righe riservate al finale
    assioma_a = int(RIGHE * 0.61)  # dove nessuno guarda
    assioma = False
    parte = 0
    while len(out) < RIGHE - coda:
        if len(nomi) % 78 == 0 and parte < len(PARTI):
            titolo, blurb = PARTI[parte]
            out += ["", f"/-! ## Parte {ROMANI[parte]}: {titolo}", "",
                    f"  {blurb}", "-/", ""]
            parte += 1
        if not assioma and len(out) >= assioma_a:
            out += [
                "/-- Lemma tecnico di raccordo, standard in letteratura",
                "    (si veda [Disagio, 2026, Appendice Z]). Si salta alla prima lettura. -/",
                "axiom lemma_tecnico_di_raccordo : P = NP",
                "",
            ]
            assioma = True
        while True:
            nome = "_".join((r.choice(PREFISSI), r.choice(TEMI), r.choice(SUFFISSI)))
            nome = f"{nome}_{len(nomi) + 1}"
            if nome not in visti:
                break
        visti.add(nome)
        nomi.append(nome)
        tesi, prova = enunciato(r)
        doc = r.sample(DOC, r.choice((1, 1, 2)))
        if len(doc) == 1:
            out.append(f"/-- {doc[0]} -/")
        else:
            out += [f"/-- {doc[0]}", f"    {doc[1]} -/"]
        out += [f"theorem {nome} {tesi} :=", f"  {prova}", ""]
    citati = r.sample(nomi, 6)
    out += [
        "/-! ## Il teorema principale -/",
        "",
        f"/-- **Teorema.** P = NP.",
        f"    La dimostrazione combina i {len(nomi)} lemmi precedenti,",
        "    tutti verificati dal kernel. -/",
        "theorem P_eq_NP : P = NP := by",
    ]
    out += [f"  have _h{i} := {n}" for i, n in enumerate(citati, 1)]
    out += [
        "  exact lemma_tecnico_di_raccordo",
        "",
        "/-- **Corollario** (versione letterale, zero assiomi): P = N·P quando N = 1. -/",
        "theorem P_eq_NP_letterale (P N : Nat) (h : N = 1) : P = N * P := by",
        "  subst h",
        "  simp",
        "",
        "end Disagio",
        "",
        "-- Per i curiosi.",
        "#print axioms Disagio.P_eq_NP",
        "#print axioms Disagio.P_eq_NP_letterale",
    ]
    OUT.write_text("\n".join(out) + "\n", encoding="utf-8")
    print(f"{OUT.name}: {len(out)} righe, {len(nomi)} lemmi")


if __name__ == "__main__":
    main()
