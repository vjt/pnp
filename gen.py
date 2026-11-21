#!/usr/bin/env python3
"""Genera la libreria PNP: la dimostrazione formale che P = NP.

Non si scrive a mano: si genera. Deterministico (seed fisso), così il diff
resta vuoto finché non cambia questo file.

    python3 gen.py && lake build

Struttura: una libreria Lake di diciassette moduli sotto PNP/, che si
importano a catena (con un diamante in mezzo, Frigo e Notte, per non
annoiarsi), più una radice PNP.lean che importa e basta. Ogni modulo è una
Parte: apre con dell'impalcatura scritta a mano (una tattica che gira in tondo,
una notazione tutta sua, induttivi mutui, ricorsione ben fondata su misure
assurde, un diamante di typeclass, strutture polimorfe negli universi, classi
prese a meno di equivalenza) e prosegue con lemmi generati da una cinquantina di
modelli, tutti veri, tutti dimostrati, quasi tutti inutili. Il resto lo fa il
lemma tecnico di raccordo.
"""
import pathlib
import random
import re

RADICE = pathlib.Path(__file__).resolve().parent
CARTELLA = RADICE / "PNP"
RIGHE_LEMMI = 7000    # righe di lemmi generati, distribuite fra i moduli
SEED = 0x5EED_D15A    # seed disagiato
QUOTA_DISAGIO = 0.8   # quante chiusure passano per la tattica `disagio`

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
    "Generalizzazione necessaria per un caso che non si presenta mai.",
    "Il frigo è stato aperto 37 volte durante la stesura di questo lemma.",
    "L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.",
    "Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.",
    "Andata e ritorno attraverso due codifiche, per vedere il panorama.",
    "La lavatrice è finita da tre ore. Il lemma no.",
    "Enunciato in forma più generale del necessario, per sembrare serio.",
    "Si veda la Parte III, che a sua volta rimanda qui.",
    "Il divano ha un grado polinomiale. Il proprietario anche.",
    "Lemma di raccordo minore. Quello maggiore è altrove.",
    "Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.",
    "Caso degenere: le ipotesi si contraddicono, quindi vale tutto.",
    "Calcolo fatto a mano sul tovagliolo della cena delle 23:40.",
    "Stima volutamente lasca: stringerla avrebbe richiesto un'idea.",
    "La pizza di ieri è un certificato valido, se scaldata.",
    "Il kernel l'ha accettato. Noi un po' meno.",
    "Corollario immediato di un lemma che dimostriamo più avanti, o forse prima.",
    "Il caso induttivo è identico al caso base, ma più lungo.",
    "Dimostrato per esaustione. Del revisore.",
    "Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.",
    # terza leva: la struttura
    "Importato da tre moduli. Usato da nessuno.",
    "La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo.",
    "Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno.",
    "Il diamante si chiude. Il frigo no.",
    "Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.",
    "Questo modulo esiste per allungare la catena degli import.",
    "La misura di terminazione è assurda. La terminazione no.",
    "Dimostrato in un universo. Vale in tutti, per pigrizia.",
    "Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario.",
    "La priorità dell'istanza è alta. Quella del lemma, bassa.",
]

COMMENTI = [
    "Crucially, we now observe that the claim follows.",
    "This step is essential.",
    "By the standard argument.",
    "We proceed by a careful case analysis.",
    "Note that this is non-trivial.",
    "It is worth noting that the fridge plays no role here.",
    "The key insight is that nothing happens.",
    "We first establish an auxiliary fact, which we will not use.",
    "This follows immediately (cf. Part III).",
    "Here we exploit the polynomial bound in an essential way.",
    "Without loss of generality, assume the couch is occupied.",
    "The remaining cases are analogous.",
    "A more elegant proof exists. This is not it.",
    "TODO: simplify. (Will not be simplified.)",
    "Let us now carefully unfold the definitions.",
    "Importantly, the certificate fits in the fridge.",
    "At this point the argument is essentially complete.",
    "We emphasize that this is where the magic happens.",
    "Sanity check (redundant, but reassuring).",
    "Recall the definition from Part I. Or Part VIII.",
    "The reader may verify this at leisure, preferably at night.",
    "We now invoke the inductive hypothesis, for emotional support.",
    "One checks directly that the bound is not tight. It does not need to be.",
    "This is the heart of the argument. The argument has several hearts.",
    "Strictly speaking this is overkill. We do it anyway.",
    "Morally, this is Cook–Levin.",
    "We record this for later use (it will not be used later).",
    "The following is a routine computation.",
    "Observe that the leftovers in the fridge are irrelevant.",
    "As is well known, the washing machine finished hours ago.",
    "We let `disagio` walk around the block once more.",
    "The diamond is resolved at night, by priority.",
    "We pass to the quotient, where nobody can see us.",
    "This holds in every universe, including the inconvenient ones.",
    "The import chain guarantees this fact is visible. Barely.",
]

ROMANI = ["I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX", "X", "XI",
          "XII", "XIII", "XIV", "XV", "XVI", "XVII", "XVIII", "XIX", "XX"]

# ---------------------------------------------------------------------------
# Impalcatura scritta a mano, una per modulo. Va in testa al modulo.
# ---------------------------------------------------------------------------

TATTICA = r'''
section Tattica

/-!
  La tattica `disagio` chiude i goal. Prima, però, gira in tondo: conta i giri
  alla rovescia per espansione ricorsiva di macro, ripete zero volte un
  fallimento, attraversa tre strati di involucro, prova due volte la stessa
  cosa, e solo allora si rivolge al nucleo, che è estensibile e si prova
  dall'ultima regola alla prima. Il kernel non vede niente di tutto questo:
  vede solo l'ultimo passo, ed è contento.
-/

/-- Il disagio: chiude il goal, dopo averci girato attorno. -/
syntax (name := disagio) &"disagio" : tactic

/-- Il disagio con un suggerimento. Il suggerimento viene provato per primo,
    ma solo dopo aver fatto tutti i giri. -/
syntax (name := disagioCon) &"disagio" &" con " tactic : tactic

/-- Il giro dell'isolato: `disagio_giri n con t` fa `n` giri a vuoto, poi scende
    negli strati. Non chiamarlo a mano: chiamalo attraverso `disagio`. -/
syntax (name := disagioGiri) "disagio_giri " num &" con " tactic : tactic

/-- Lo strato: `disagio_strato n con t` avvolge il nucleo in `n` involucri. -/
syntax (name := disagioStrato) "disagio_strato " num &" con " tactic : tactic

/-- Il nucleo del disagio. Estensibile: ogni `macro_rules` aggiunge un modo di
    chiudere il goal, e si provano tutti, dall'ultimo al primo, finché uno non va. -/
syntax (name := disagioNucleo) "disagio_nucleo" : tactic

-- Ultima spiaggia: si semplifica tutto, ipotesi comprese, e si spera.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| (simp_all; done))
-- Penultima: l'ipotesi c'era già, bastava guardare.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| assumption)
-- Aritmetica lineare: il cuore polinomiale del disagio.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| omega)
-- Riflessività: a volte le cose sono uguali a se stesse.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| rfl)
-- Decisione: si chiede al kernel, che risponde. Dichiarata per ultima, provata per prima.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| decide)

-- Gli strati: ogni involucro prova lo strato sotto, e se fallisce fallisce con garbo.
macro_rules
  | `(tactic| disagio_strato $n con $t) =>
    match n.getNat with
    | 0 => `(tactic| first | ($t; done) | (disagio_nucleo; done))
    | k + 1 =>
      `(tactic| (try skip); all_goals first
          | (disagio_strato $(Lean.Syntax.mkNatLit k) con $t)
          | fail "strato bucato")

-- I giri: ogni giro ripete zero volte un fallimento, poi rinvia al giro dopo.
macro_rules
  | `(tactic| disagio_giri $n con $t) =>
    match n.getNat with
    | 0 => `(tactic| disagio_strato 3 con $t)
    | k + 1 =>
      `(tactic| (repeat (fail "giro a vuoto")); first
          | fail "non ancora"
          | (disagio_giri $(Lean.Syntax.mkNatLit k) con $t))

-- Il suggerimento entra dalla porta principale e fa tre giri come tutti.
macro_rules | `(tactic| disagio con $t) => `(tactic| disagio_giri 3 con $t)

-- Senza suggerimento, il suggerimento è il nucleo stesso, che quindi si prova due volte.
macro_rules | `(tactic| disagio) => `(tactic| disagio con disagio_nucleo)

/-- Il disagio chiude 2 + 2 = 4. Ci mette un po'. -/
theorem disagio_due_piu_due : 2 + 2 = 4 := by disagio

/-- Il disagio fa aritmetica lineare, dopo tre giri e tre strati. -/
theorem disagio_lineare (n : Nat) (h : n ≤ 5) : 3 * n + 1 ≤ 16 := by disagio

/-- Il disagio trova le ipotesi. Prima prova tutto il resto. -/
theorem disagio_ipotesi (p : Prop) (h : p) : p := by disagio

/-- Il disagio accetta suggerimenti, e li segue dopo averci pensato. -/
theorem disagio_suggerito (xs : List Nat) (h : xs.length = 3) : (xs ++ [0]).length = 4 := by
  disagio con simp [h]

end Tattica
'''

PRELIMINARI = r'''
section Preliminari

/-- Un bit. Abbreviazione di `Bool`, per chiarezza. -/
abbrev Bit : Type := Bool

/-- Un bit, ma più formale. Ridefinito per non dipendere da `Bit`, da cui dipende. -/
abbrev BitFormale : Type := Bit

/-- Stringa di bit. Il materiale di cui sono fatti i problemi, e i divani. -/
abbrev Stringa : Type := List BitFormale

/-- Un problema di decisione: un linguaggio su stringhe di bit, come si deve. -/
abbrev Problema : Type := Stringa → Prop

/-- Una classe di complessità: un insieme di problemi. -/
abbrev Classe : Type := Problema → Prop

/-- Lunghezza di una stringa, incapsulata per motivi di astrazione. -/
@[reducible] def lunghezza (x : Stringa) : Nat := x.length

/-- Indice limitato: un `Fin`, ma con un nome più rassicurante. -/
abbrev Indice (n : Nat) : Type := Fin (n + 1)

/-- Naturale certificato positivo. Il certificato è nel frigo. -/
abbrev Positivo : Type := { n : Nat // 0 < n }

/-- L'unico positivo di cui siamo davvero sicuri. -/
def Positivo.uno : Positivo := ⟨1, by disagio⟩

/-- Tutto ciò che ha una lunghezza. Il divano, per esempio. -/
class HaLunghezza (α : Type u) where
  /-- La lunghezza, misurata in cuscini. -/
  lung : α → Nat

instance : HaLunghezza Stringa := ⟨List.length⟩

instance {α : Type u} [HaLunghezza α] : HaLunghezza (Option α) :=
  ⟨fun o => match o with
    | none => 0
    | some a => HaLunghezza.lung a⟩

/-- Un polinomio a coefficienti naturali, in forma di Horner.
    Il grado è ridondante, esattamente come il lettore. -/
structure PolyBound where
  /-- Il grado dichiarato. -/
  grado : Nat
  /-- I coefficienti, dal termine noto in su. -/
  coefficienti : List Nat
  /-- Invariante di coerenza. Serve a far sembrare la struttura seria. -/
  coerente : coefficienti.length = grado + 1

namespace PolyBound

/-- Schema di Horner, ricorsivo, perché i cicli si fanno dopo. -/
def horner (n : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => a + n * horner n as

/-- Valutazione di un `PolyBound` in un punto. -/
def valuta (p : PolyBound) (n : Nat) : Nat := horner n p.coefficienti

/-- Il polinomio costante. Il grado zero del disagio. -/
def costante (k : Nat) : PolyBound := ⟨0, [k], rfl⟩

/-- Il polinomio identità, scritto per esteso. -/
def identita : PolyBound := ⟨1, [0, 1], rfl⟩

/-- Moltiplicazione per uno scalare. -/
def scala (p : PolyBound) (k : Nat) : PolyBound :=
  ⟨p.grado, p.coefficienti.map (k * ·), by simp [p.coerente]⟩

/-- Monotonia di Horner. La dimostrazione è più lunga del necessario. -/
theorem horner_mono {n m : Nat} (h : n ≤ m) : ∀ xs : List Nat, horner n xs ≤ horner m xs
  | [] => Nat.le_refl 0
  | a :: as => by
      -- We proceed by structural recursion, as is customary.
      have ih := horner_mono h as
      have hm : n * horner n as ≤ m * horner m as := Nat.mul_le_mul h ih
      simp only [horner]
      disagio

/-- La valutazione è monotona. Il disagio pure. -/
theorem valuta_mono (p : PolyBound) {n m : Nat} (h : n ≤ m) : p.valuta n ≤ p.valuta m :=
  horner_mono h p.coefficienti

/-- Horner commuta con la scala. -/
theorem horner_scala (k n : Nat) : ∀ xs : List Nat, horner n (xs.map (k * ·)) = k * horner n xs
  | [] => by simp [horner]
  | a :: as => by
      simp only [List.map, horner, horner_scala k n as, Nat.mul_add, Nat.mul_left_comm]

/-- Valutare dopo aver scalato è come scalare dopo aver valutato. -/
theorem valuta_scala (p : PolyBound) (k n : Nat) : (p.scala k).valuta n = k * p.valuta n :=
  horner_scala k n p.coefficienti

/-- Il polinomio costante è costante. Risultato atteso. -/
theorem valuta_costante (k n : Nat) : (costante k).valuta n = k := by
  simp [valuta, costante, horner]

/-- L'identità è l'identità. Risultato meno atteso. -/
theorem valuta_identita (n : Nat) : identita.valuta n = n := by
  simp [valuta, identita, horner]

end PolyBound

/-- Le direzioni in cui può muoversi la testina. `divano` = resta dov'è. -/
inductive Direzione where
  | sinistra
  | destra
  | divano
deriving DecidableEq, Repr

/-- Un nastro bi-infinito, troncato per motivi di budget. -/
structure Nastro where
  /-- Ciò che sta a sinistra, al contrario. -/
  sx : List Bit
  /-- Il bit sotto la testina. -/
  testa : Bit
  /-- Ciò che sta a destra. -/
  dx : List Bit
deriving DecidableEq, Repr

namespace Nastro

/-- Il nastro vuoto. Come il frigo il lunedì. -/
def vuoto : Nastro := ⟨[], false, []⟩

/-- Carica l'input sul nastro. -/
def carica : Stringa → Nastro
  | [] => vuoto
  | b :: bs => ⟨[], b, bs⟩

/-- Scrive un bit sotto la testina. -/
def scrivi (t : Nastro) (b : Bit) : Nastro := { t with testa := b }

/-- Muove la testina. Sul divano non si muove. -/
def muovi (t : Nastro) : Direzione → Nastro
  | .divano => t
  | .sinistra =>
      match t with
      | ⟨[], h, r⟩ => ⟨[], false, h :: r⟩
      | ⟨l :: ls, h, r⟩ => ⟨ls, l, h :: r⟩
  | .destra =>
      match t with
      | ⟨l, h, []⟩ => ⟨h :: l, false, []⟩
      | ⟨l, h, r :: rs⟩ => ⟨h :: l, r, rs⟩

/-- Dimensione del nastro, in celle. -/
def dimensione (t : Nastro) : Nat := t.sx.length + 1 + t.dx.length

/-- Il contenuto del nastro, letto da sinistra a destra. -/
def contenuto (t : Nastro) : Stringa := t.sx.reverse ++ t.testa :: t.dx

theorem dimensione_pos (t : Nastro) : 0 < t.dimensione := by
  -- Crucially, every tape has at least one cell: the one under the head.
  unfold dimensione
  disagio

theorem dimensione_scrivi (t : Nastro) (b : Bit) : (t.scrivi b).dimensione = t.dimensione := rfl

/-- Muoversi non accorcia il nastro. Si può solo peggiorare. -/
theorem dimensione_muovi (t : Nastro) (d : Direzione) : t.dimensione ≤ (t.muovi d).dimensione := by
  -- We proceed by a careful case analysis (twelve cases, all identical).
  cases t with
  | mk l h r =>
    cases d <;> cases l <;> cases r <;> simp [muovi, dimensione] <;> omega

theorem muovi_divano (t : Nastro) : t.muovi .divano = t := rfl

end Nastro

instance : HaLunghezza Nastro := ⟨Nastro.dimensione⟩

/-- Macchina di Turing a due nastri: quello di lavoro e il frigo.
    Il frigo contiene il certificato. La macchina può aprirlo, una cella alla volta. -/
structure MacchinaDiTuring where
  /-- Numero di stati, meno uno, per comodità di nessuno. -/
  stati : Nat
  /-- Stato iniziale. -/
  iniziale : Indice stati
  /-- Stato accettante. Ce n'è uno solo: siamo gente semplice. -/
  accetta : Indice stati
  /-- Transizione: (stato, bit sul nastro, bit nel frigo) ↦
      (nuovo stato, bit da scrivere, direzione, apro il frigo?). -/
  delta : Indice stati → Bit → Bit → Indice stati × Bit × Direzione × Bool

/-- Configurazione istantanea. Il campo `orologio` conta i passi, e le ore. -/
structure Configurazione (M : MacchinaDiTuring) where
  stato : Indice M.stati
  nastro : Nastro
  frigo : List Bit
  orologio : Nat

/-- Cosa c'è in cima al frigo. Se il frigo è vuoto: `false`, come la speranza. -/
def testaDelFrigo : List Bit → Bit
  | [] => false
  | b :: _ => b

/-- Un passo di calcolo. -/
def passo (M : MacchinaDiTuring) (c : Configurazione M) : Configurazione M :=
  let r := M.delta c.stato c.nastro.testa (testaDelFrigo c.frigo)
  { stato := r.1
    nastro := (c.nastro.scrivi r.2.1).muovi r.2.2.1
    frigo := if r.2.2.2 then c.frigo.tail else c.frigo
    orologio := c.orologio + 1 }

/-- Simulatore a carburante. Quando finisce il carburante, finisce la serata. -/
def esegui (M : MacchinaDiTuring) : Nat → Configurazione M → Configurazione M
  | 0, c => c
  | n + 1, c => esegui M n (passo M c)

/-- Configurazione iniziale: input sul nastro, certificato in frigo. -/
def configurazioneIniziale (M : MacchinaDiTuring) (x cert : Stringa) : Configurazione M :=
  { stato := M.iniziale, nastro := Nastro.carica x, frigo := cert, orologio := 0 }

/-- `M` accetta `x` col certificato `cert` entro il tempo `p(|x|)`. -/
def accettaEntro (M : MacchinaDiTuring) (p : PolyBound) (x cert : Stringa) : Prop :=
  (esegui M (p.valuta x.length) (configurazioneIniziale M x cert)).stato = M.accetta

instance (M : MacchinaDiTuring) (p : PolyBound) (x cert : Stringa) :
    Decidable (accettaEntro M p x cert) := by
  unfold accettaEntro; infer_instance

/-- Eseguire `a + b` passi è come eseguirne `a` e poi `b`. Semigruppo del disagio. -/
theorem esegui_somma (M : MacchinaDiTuring) :
    ∀ (a b : Nat) (c : Configurazione M), esegui M (a + b) c = esegui M b (esegui M a c)
  | 0, b, c => by simp [esegui]
  | a + 1, b, c => by
      -- The inductive step is essentially routine.
      rw [Nat.add_right_comm, esegui, esegui, esegui_somma M a b (passo M c)]

/-- L'orologio avanza di un'unità per passo. Le ore piccole si sommano. -/
theorem esegui_orologio (M : MacchinaDiTuring) :
    ∀ (n : Nat) (c : Configurazione M), (esegui M n c).orologio = c.orologio + n
  | 0, c => rfl
  | n + 1, c => by
      rw [esegui, esegui_orologio M n (passo M c)]
      simp [passo]
      disagio

/-- Un decisore: una macchina e un polinomio che ne limita il tempo. -/
structure Decisore where
  macchina : MacchinaDiTuring
  tempo : PolyBound

/-- `D` decide `L`: accetta esattamente le stringhe di `L`, a frigo vuoto. -/
def Decisore.decide (D : Decisore) (L : Problema) : Prop :=
  ∀ x : Stringa, L x ↔ accettaEntro D.macchina D.tempo x []

/-- Un verificatore: macchina, tempo, e capienza del frigo. -/
structure Verificatore where
  macchina : MacchinaDiTuring
  tempo : PolyBound
  spazioFrigo : PolyBound

/-- Un certificato per `x`: una stringa che entra nel frigo. -/
structure Certificato (V : Verificatore) (x : Stringa) where
  contenuto : Stringa
  entra_nel_frigo : contenuto.length ≤ V.spazioFrigo.valuta x.length

/-- `V` accetta `x` col certificato `c`. -/
def Verificatore.accetta (V : Verificatore) (x : Stringa) (c : Certificato V x) : Prop :=
  accettaEntro V.macchina V.tempo x c.contenuto

/-- `V` verifica `L`. -/
def Verificatore.verifica (V : Verificatore) (L : Problema) : Prop :=
  ∀ x : Stringa, L x ↔ ∃ c : Certificato V x, V.accetta x c

/-- La classe P: problemi decisi in tempo polinomiale, a frigo chiuso. -/
def P : Classe := fun L => ∃ D : Decisore, D.decide L

/-- La classe NP: problemi verificati in tempo polinomiale, a frigo aperto. -/
def NP : Classe := fun L => ∃ V : Verificatore, V.verifica L

end Preliminari
'''

UNIVERSI = r'''
section Universi

/-- Una codifica fra due tipi che vivono in universi qualunque, anche diversi.
    Andata e ritorno garantiti; il viaggio no. -/
structure Codifica.{a, b} (α : Type a) (β : Type b) where
  /-- Andata. -/
  codifica : α → β
  /-- Ritorno. -/
  decodifica : β → α
  /-- Si torna a casa. -/
  andata_e_ritorno : ∀ x, decodifica (codifica x) = x

namespace Codifica

/-- La codifica identica: andata e ritorno senza alzarsi dal divano. -/
def id.{a} (α : Type a) : Codifica α α := ⟨fun x => x, fun x => x, fun _ => rfl⟩

/-- Composizione di codifiche, attraverso tre universi. -/
def comp.{a, b, c} {α : Type a} {β : Type b} {γ : Type c} (f : Codifica α β)
    (g : Codifica β γ) : Codifica α γ :=
  ⟨fun x => g.codifica (f.codifica x), fun z => f.decodifica (g.decodifica z), fun x => by
    show f.decodifica (g.decodifica (g.codifica (f.codifica x))) = x
    rw [g.andata_e_ritorno, f.andata_e_ritorno]⟩

/-- Codificare una coppia, una componente per volta. Quattro universi, due per lato. -/
def prod.{a, b, c, d} {α : Type a} {β : Type b} {γ : Type c} {δ : Type d}
    (f : Codifica α β) (g : Codifica γ δ) : Codifica (α × γ) (β × δ) :=
  ⟨fun p => (f.codifica p.1, g.codifica p.2), fun q => (f.decodifica q.1, g.decodifica q.2),
   fun p => by
    show (f.decodifica (f.codifica p.1), g.decodifica (g.codifica p.2)) = p
    rw [f.andata_e_ritorno, g.andata_e_ritorno]⟩

/-- Comporre con l'identità non cambia niente, in nessun universo. -/
theorem comp_id.{a, b} {α : Type a} {β : Type b} (f : Codifica α β) (x : α) :
    (f.comp (Codifica.id β)).codifica x = f.codifica x := rfl

end Codifica

/-- Un sollevamento: lo stesso contenuto, un universo più in alto. Come il frigo
    messo sul soppalco. -/
structure Sollevato.{a, b} (α : Type a) : Type (max a b) where
  /-- Si scende dal soppalco. -/
  giu : α

/-- Una torre di frighi: un tipo e un suo abitante. Vive un universo sopra il suo piano. -/
structure Torre.{a} : Type (a + 1) where
  /-- Il piano. -/
  piano : Type a
  /-- Chi ci abita. -/
  abitante : piano

/-- Si sale di un piano. L'abitante viene sollevato, il piano anche. -/
def Torre.su.{a} (t : Torre.{a}) : Torre.{a + 1} :=
  ⟨Sollevato.{a, a + 1} t.piano, ⟨t.abitante⟩⟩

/-- Il pianterreno: i naturali, abitati dallo zero. -/
def Torre.terra : Torre.{0} := ⟨Nat, 0⟩

/-- Al terzo piano abita ancora lo zero, sollevato tre volte. -/
theorem Torre.terzo_piano :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su Torre.terra))).abitante))
      = (0 : Nat) := by
  disagio

/-- Una famiglia di classi indicizzata da un tipo in un universo qualunque. -/
structure Famiglia.{a} (ι : Type a) where
  /-- La classe del giorno `i`. -/
  classe : ι → Classe

/-- La famiglia costante: tutti i giorni la stessa classe. -/
def Famiglia.costante.{a} (ι : Type a) (C : Classe) : Famiglia ι := ⟨fun _ => C⟩

/-- Una scatola, polimorfa nell'universo. Per la pizza. -/
structure Scatola (α : Type u) where
  contenuto : α
  etichetta : String

end Universi
'''

DIVANO = r'''
section Divano

/-- Imbottitura: si aggiungono cuscini (bit `false`) in fondo alla stringa. -/
def pad (k : Nat) (x : Stringa) : Stringa := x ++ List.replicate k false

/-- La lunghezza di una stringa imbottita. Lemma centrale di tutta la teoria. -/
theorem pad_lunghezza (k : Nat) (x : Stringa) : (pad k x).length = x.length + k := by
  disagio con simp [pad]

/-- Lunghezza, ma misurata dal divano. -/
def lunghezzaDelDivano (x : Stringa) : Nat := lunghezza x

/-- Lunghezza, ma misurata dal divano, in modo formale. -/
abbrev lunghezzaFormale : Stringa → Nat := lunghezzaDelDivano

/-- Riduzione di Karp, eseguita senza alzarsi dal divano. -/
structure RiduzioneDalDivano (A B : Problema) where
  /-- La funzione di riduzione. -/
  f : Stringa → Stringa
  /-- Il tempo che ci mette. Dichiarato, mai verificato. -/
  tempo : PolyBound
  /-- Correttezza. -/
  corretta : ∀ x, A x ↔ B (f x)

/-- `A` si riduce a `B`, se esiste una riduzione dal divano. -/
def Riducibile (A B : Problema) : Prop := Nonempty (RiduzioneDalDivano A B)

@[inherit_doc] infix:50 " ≤ₚ " => Riducibile

/-- Riducibilità con un budget di tempo: la riduzione esiste e non sfora `t`.
    `t` è una funzione qualunque: i polinomi sono un'opinione. -/
def RiducibileEntro (A B : Problema) (t : Nat → Nat) : Prop :=
  ∃ r : RiduzioneDalDivano A B, ∀ n, r.tempo.valuta n ≤ t n

/-- Chi riduce entro un tempo, riduce. Il tempo si dimentica. -/
theorem RiducibileEntro.riducibile {A B : Problema} {t : Nat → Nat}
    (h : RiducibileEntro A B t) : A ≤ₚ B :=
  match h with
  | ⟨r, _⟩ => ⟨r⟩

/-- La riduzione identica: non alzarsi affatto. -/
def RiduzioneDalDivano.refl (A : Problema) : RiduzioneDalDivano A A :=
  ⟨id, PolyBound.identita, fun _ => Iff.rfl⟩

/-- Composizione di riduzioni: alzarsi due volte, ma restando seduti. -/
def RiduzioneDalDivano.comp {A B C : Problema} (r : RiduzioneDalDivano A B)
    (s : RiduzioneDalDivano B C) : RiduzioneDalDivano A C :=
  ⟨s.f ∘ r.f, s.tempo, fun x => (r.corretta x).trans (s.corretta (r.f x))⟩

theorem riducibile_refl (A : Problema) : A ≤ₚ A := ⟨RiduzioneDalDivano.refl A⟩

theorem riducibile_trans {A B C : Problema} (h₁ : A ≤ₚ B) (h₂ : B ≤ₚ C) : A ≤ₚ C :=
  match h₁, h₂ with
  | ⟨r⟩, ⟨s⟩ => ⟨r.comp s⟩

/-- Il problema della parità dei cuscini, con `k` cuscini già sul divano. -/
def Parita (k : Nat) : Problema := fun x => (x.length + k) % 2 = 0

/-- Conta i cuscini occupati. Ciclo `for`, perché la ricorsione è da boomer. -/
def contaCuscini (x : Stringa) : Nat := Id.run do
  let mut n := 0
  for b in x do
    if b then n := n + 1
  return n

/-- La macchina del divano: si siede nello stato accettante e non si alza più. -/
def macchinaDelDivano : MacchinaDiTuring :=
  ⟨1, 0, 1, fun s b _ => (if s = 0 then 1 else s, b, .divano, false)⟩

/-- Il problema banale sta in P. Prima dimostrazione onesta della libreria. -/
theorem tutto_in_P : P (fun _ => True) :=
  ⟨⟨macchinaDelDivano, PolyBound.costante 1⟩, fun x =>
    ⟨fun _ => by unfold accettaEntro; rw [PolyBound.valuta_costante]; rfl, fun _ => trivial⟩⟩

end Divano
'''

NOTAZIONE = r'''
section Notazione

/-- Fatti di complessità. Una grammatica tutta loro, perché le parentesi tonde
    erano troppo leggibili. -/
declare_syntax_cat fatto

/-- `A ⇝ B`: `A` si riduce a `B`, dal divano. -/
syntax term:51 " ⇝ " term:51 : fatto

/-- `A ⇝ B ⇝ C`: catena di riduzioni. Si espande in due fatti, che si espandono
    a loro volta. -/
syntax term:51 " ⇝ " term:51 " ⇝ " term:51 : fatto

/-- `A ⇝ B in n ↦ t`: riduzione con budget di tempo `t(n)`, dichiarato e rispettato. -/
syntax term:51 " ⇝ " term:51 " in " ident " ↦ " term : fatto

/-- `L ∈ C`: il problema `L` sta nella classe `C`. -/
syntax term:51 " ∈ " term:51 : fatto

/-- `C ⊆ D`: inclusione fra classi. Si espande in termini di `∈`, che si espande a sua volta. -/
syntax term:51 " ⊆ " term:51 : fatto

/-- `f ∈ 𝒪(g)`: `f` cresce al più come `g`, se aspetti abbastanza. -/
syntax term:51 " ∈ " "𝒪(" term ")" : fatto

/-- Le doppie parentesi angolate: qui dentro si parla di complessità. -/
syntax "⟪" fatto "⟫" : term

/-- O grande. Definita a mano, perché Mathlib non c'è e la dignità neppure. -/
def GrandeO (f g : Nat → Nat) : Prop := ∃ c n₀ : Nat, ∀ n, n₀ ≤ n → f n ≤ c * g n

macro_rules
  | `(⟪ $A:term ⇝ $B:term ⟫) => `(Riducibile $A $B)
  | `(⟪ $A:term ⇝ $B:term ⇝ $C:term ⟫) => `(⟪ $A:term ⇝ $B:term ⟫ ∧ ⟪ $B:term ⇝ $C:term ⟫)
  | `(⟪ $A:term ⇝ $B:term in $n:ident ↦ $t:term ⟫) => `(RiducibileEntro $A $B (fun $n => $t))
  | `(⟪ $L:term ∈ $C:term ⟫) => `($C $L)
  | `(⟪ $C:term ⊆ $D:term ⟫) => `(∀ L : Problema, ⟪ L ∈ $C:term ⟫ → ⟪ L ∈ $D:term ⟫)
  | `(⟪ $f:term ∈ 𝒪($g:term) ⟫) => `(GrandeO $f $g)

/-- Riflessività a tempo: non alzarsi costa quanto l'identità. -/
theorem riducibileEntro_refl (A : Problema) : ⟪ A ⇝ A in n ↦ n ⟫ :=
  ⟨RiduzioneDalDivano.refl A, fun n => Nat.le_of_eq (PolyBound.valuta_identita n)⟩

/-- La catena si accorcia: da `A ⇝ B ⇝ C` segue `A ⇝ C`. -/
theorem catena_accorcia {A B C : Problema} (h : ⟪ A ⇝ B ⇝ C ⟫) : ⟪ A ⇝ C ⟫ :=
  riducibile_trans h.1 h.2

/-- Ogni funzione è O di se stessa. Anche quelle che non lo meritano. -/
theorem grandeO_refl (f : Nat → Nat) : ⟪ f ∈ 𝒪(f) ⟫ :=
  ⟨1, 0, fun n _ => by disagio⟩

/-- O grande è transitivo. Il disagio anche. -/
theorem grandeO_trans {f g h : Nat → Nat} (hf : ⟪ f ∈ 𝒪(g) ⟫) (hg : ⟪ g ∈ 𝒪(h) ⟫) :
    ⟪ f ∈ 𝒪(h) ⟫ := by
  obtain ⟨c₁, n₁, h₁⟩ := hf
  obtain ⟨c₂, n₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, max n₁ n₂, fun n hn => ?_⟩
  have a := h₁ n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have b := h₂ n (Nat.le_trans (Nat.le_max_right _ _) hn)
  -- Here we exploit the polynomial bound in an essential way.
  calc f n ≤ c₁ * g n := a
    _ ≤ c₁ * (c₂ * h n) := Nat.mul_le_mul_left c₁ b
    _ = c₁ * c₂ * h n := (Nat.mul_assoc _ _ _).symm

end Notazione
'''

FRIGO = r'''
section Frigo

/-- Un oracolo, nel senso di Baker–Gill–Solovay e del frigo alle 3 di notte. -/
class Oracolo (ω : Type u) where
  /-- Si interroga l'oracolo. Risponde. -/
  interroga : ω → Stringa → Bool
  /-- Il costo di un'interrogazione, in bollette. -/
  costo : ω → Nat := fun _ => 1

/-- Il frigo. -/
structure Frigo where
  /-- Lo sportello. -/
  aperto : Bool
  /-- La temperatura, in gradi di disagio. -/
  temperatura : Nat
  /-- Gli avanzi, uno per ripiano. -/
  ripiani : List Stringa
  /-- C'è la pizza di ieri? -/
  pizzaDiIeri : Bool
deriving Repr

/-- Il frigo come oracolo: se è aperto e c'è la pizza, la risposta è sì. -/
instance : Oracolo Frigo where
  interroga f x := f.aperto && (decide (x.length ≤ f.temperatura) || f.pizzaDiIeri)
  costo f := f.temperatura + 1

instance : Inhabited Frigo := ⟨⟨true, 4, [], true⟩⟩

/-- Si lascia il frigo aperto finché non scende a 4 gradi. Ricorsione ben fondata. -/
def raffredda (f : Frigo) : Frigo :=
  if h : f.temperatura ≤ 4 then f
  else raffredda { f with temperatura := f.temperatura - 1 }
termination_by f.temperatura
decreasing_by simp_wf; disagio

/-- Il frigo converge. Teorema di punto fisso dell'elettrodomestico. -/
theorem raffredda_converge (f : Frigo) : (raffredda f).temperatura ≤ 4 := by
  -- We proceed by functional induction on the fridge.
  induction f using raffredda.induct with
  | case1 f h => rw [raffredda]; simp [h]
  | case2 f h ih => rw [raffredda]; simp [h]; exact ih

/-- Un grado in meno. -/
def raffreddaUnGrado (f : Frigo) : Frigo := { f with temperatura := f.temperatura - 1 }

/-- Iterazione del frigo, a carburante. -/
def iteraFrigo : Nat → Frigo → Frigo
  | 0, f => f
  | n + 1, f => iteraFrigo n (raffreddaUnGrado f)

theorem iteraFrigo_temperatura :
    ∀ (n : Nat) (f : Frigo), (iteraFrigo n f).temperatura = f.temperatura - n
  | 0, f => rfl
  | n + 1, f => by
      rw [iteraFrigo, iteraFrigo_temperatura n]
      simp [raffreddaUnGrado]
      disagio

/-- Si aspetta davanti al frigo aperto finché non converge. Ciclo `while`:
    termina in pratica, in teoria non lo sappiamo e il kernel nemmeno. -/
def aspettaIlFrigo (f : Frigo) : Frigo := Id.run do
  let mut g := f
  while g.temperatura > 4 do
    g := raffreddaUnGrado g
  return g

/-- La macchina del frigo: accetta se in cima al frigo c'è un `true`. -/
def macchinaDelFrigo : MacchinaDiTuring :=
  ⟨1, 0, 1, fun s b fb => (if s = 0 then (if fb then 1 else 0) else s, b, .divano, false)⟩

/-- Il problema banale sta in NP, col certificato `[true]` in frigo. -/
theorem tutto_in_NP : ⟪ (fun _ => True) ∈ NP ⟫ := by
  refine ⟨⟨macchinaDelFrigo, PolyBound.costante 1, PolyBound.costante 1⟩, fun x => ?_⟩
  -- Importantly, the certificate fits in the fridge.
  have hc : [true].length ≤ (PolyBound.costante 1).valuta x.length := by
    rw [PolyBound.valuta_costante]; disagio
  refine ⟨fun _ => ⟨⟨[true], hc⟩, ?_⟩, fun _ => trivial⟩
  unfold Verificatore.accetta accettaEntro
  simp only [PolyBound.valuta_costante]
  rfl

end Frigo
'''

NOTTE = r'''
section Notte

/-- Un letterale. Di notte le polarità si confondono. -/
structure Letterale where
  var : Nat
  positivo : Bool
deriving DecidableEq, Repr

abbrev Clausola : Type := List Letterale
abbrev FormulaCNF : Type := List Clausola
abbrev Assegnamento : Type := Nat → Bool

def Letterale.valuta (σ : Assegnamento) (l : Letterale) : Bool :=
  if l.positivo then σ l.var else !σ l.var

def Clausola.valuta (σ : Assegnamento) (c : Clausola) : Bool := c.any (Letterale.valuta σ)

def FormulaCNF.valuta (σ : Assegnamento) (φ : FormulaCNF) : Bool := φ.all (Clausola.valuta σ)

/-- Un assegnamento letto da una stringa. Oltre la fine: `false`. -/
def assegnamentoDaStringa (x : Stringa) : Assegnamento := fun i => x.getD i false

/-- La formula notturna di una stringa: una clausola unitaria per bit. -/
def formulaDaIndice : Nat → Stringa → FormulaCNF
  | _, [] => []
  | i, b :: bs => [⟨i, b⟩] :: formulaDaIndice (i + 1) bs

def formulaDiNotte (x : Stringa) : FormulaCNF := formulaDaIndice 0 x

theorem formulaDaIndice_length :
    ∀ (i : Nat) (x : Stringa), (formulaDaIndice i x).length = x.length
  | _, [] => rfl
  | i, b :: bs => by simp [formulaDaIndice, formulaDaIndice_length (i + 1) bs]

/-- SAT, nella versione notturna. -/
def SAT : Problema := fun x => ∃ σ : Assegnamento, (formulaDiNotte x).valuta σ = true

theorem valuta_nil (σ : Assegnamento) : FormulaCNF.valuta σ [] = true := rfl

theorem valuta_append (σ : Assegnamento) (φ ψ : FormulaCNF) :
    (φ ++ ψ).valuta σ = (φ.valuta σ && ψ.valuta σ) := by
  disagio con simp [FormulaCNF.valuta, List.all_append]

/-- Il tableau di Cook–Levin, riga per riga, con un ciclo `for`. -/
def tableauNotturno (M : MacchinaDiTuring) (x : Stringa) (righe : Nat) : List Stringa := Id.run do
  let mut out : List Stringa := []
  let mut c := configurazioneIniziale M x []
  for _ in [0:righe] do
    out := out ++ [c.nastro.contenuto]
    c := passo M c
  return out

/-- Simulatore notturno: ciclo `for` con uscita anticipata, se si accetta prima. -/
def eseguiDiNotte (M : MacchinaDiTuring) (c : Configurazione M) (carburante : Nat) :
    Configurazione M := Id.run do
  let mut c := c
  for _ in [0:carburante] do
    if c.stato = M.accetta then break
    c := passo M c
  return c

/-- Si cena alle 23:40. Se è prima, si aspetta. Ciclo `while`, termina (empiricamente). -/
def cenaAlle2340 (minuti : Nat) : Nat := Id.run do
  let mut m := minuti
  while m % 60 ≠ 40 do
    m := m + 1
  return m

/-- Disagio totale di una lista di stringhe: due fold annidati. -/
def disagioTotale (xss : List Stringa) : Nat :=
  xss.foldl (fun acc xs => acc + xs.foldr (fun b a => if b then a + 2 else a + 1) 0) 0

theorem disagio_interno_ge_lunghezza : ∀ xs : Stringa,
    xs.length ≤ xs.foldr (fun b a => if b then a + 2 else a + 1) 0
  | [] => Nat.le_refl 0
  | b :: bs => by
      have ih := disagio_interno_ge_lunghezza bs
      cases b <;> simp only [List.foldr, List.length_cons] <;> simp <;> omega

end Notte
'''

IMBOTTITURA = r'''
section Imbottitura

/-!
  Questo modulo importa sia il Frigo sia la Notte, che non si conoscono: è il
  vertice in basso del diamante degli import. Usa il divano, che entrambi
  importano, e che quindi arriva qui due volte. Lean lo carica una volta sola.
-/

/-- Imbottitura polinomiale: tanti cuscini quanti ne prescrive `p`. -/
def padPolinomiale (p : PolyBound) (x : Stringa) : Stringa := pad (p.valuta x.length) x

theorem padPolinomiale_lunghezza (p : PolyBound) (x : Stringa) :
    (padPolinomiale p x).length = x.length + p.valuta x.length :=
  pad_lunghezza _ _

/-- Codifica unaria. Inefficiente, quindi onesta. -/
def codificaUnaria (n : Nat) : Stringa := List.replicate n true

def decodificaUnaria (x : Stringa) : Nat := x.length

theorem round_trip_unario (n : Nat) : decodificaUnaria (codificaUnaria n) = n := by
  disagio con simp [decodificaUnaria, codificaUnaria]

/-- La codifica unaria come `Codifica` universale. Vive in `Type`, per modestia. -/
def codificaUnariaC : Codifica Nat Stringa := ⟨codificaUnaria, decodificaUnaria, round_trip_unario⟩

/-- Codifica binaria a carburante. Il carburante è sempre abbastanza. Quasi. -/
def codificaBinariaCon : Nat → Nat → Stringa
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % 2 == 1) :: codificaBinariaCon f (n / 2)

def codificaBinaria (n : Nat) : Stringa := codificaBinariaCon (n + 1) n

def decodificaBinaria : Stringa → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * decodificaBinaria bs

/-- La lavatrice dimenticata: gira la stringa `giri` volte. -/
def lavatriceDimenticata (giri : Nat) (x : Stringa) : Stringa := Id.run do
  let mut s := x
  for _ in [0:giri] do
    s := s.reverse
  return s

end Imbottitura
'''

BARRIERE = r'''
section Barriere

/-- Una barriera: un vincolo sulle dimostrazioni. La nostra è una libreria. -/
structure Barriera where
  nome : String
  anno : Nat
  vincola : Prop → Prop

def relativizzazione : Barriera := ⟨"Baker–Gill–Solovay", 1975, fun _ => True⟩
def proveNaturali : Barriera := ⟨"Razborov–Rudich", 1997, fun _ => True⟩
def algebrizzazione : Barriera := ⟨"Aaronson–Wigderson", 2009, fun _ => True⟩

/-- Una barriera è superata se, ammesso il vincolo, vale la tesi o qualcos'altro. -/
def Barriera.superata (b : Barriera) (φ : Prop) : Prop := b.vincola φ → φ ∨ True

theorem barriera_superata (b : Barriera) (φ : Prop) : b.superata φ := fun _ => Or.inr trivial

/-- P relativizzata a un oracolo qualunque, polimorfo nell'universo. -/
def PConOracolo {ω : Type u} [Oracolo ω] (o : ω) : Classe :=
  fun L => P L ∨ ∀ x, L x ↔ Oracolo.interroga o x = true

theorem P_sub_PConOracolo {ω : Type u} [Oracolo ω] (o : ω) (L : Problema) (h : ⟪ L ∈ P ⟫) :
    ⟪ L ∈ PConOracolo o ⟫ := Or.inl h

end Barriere
'''

RACCORDO = r'''
section Raccordo

/-- Chiude il frigo: la macchina ignora il certificato e non apre mai lo sportello. -/
def MacchinaDiTuring.chiudiFrigo (M : MacchinaDiTuring) : MacchinaDiTuring :=
  { M with delta := fun s b _ =>
      let r := M.delta s b false
      (r.1, r.2.1, r.2.2.1, false) }

/-- Un frigo vuoto resta vuoto, che lo sportello si apra o no. -/
theorem frigo_vuoto_resta_vuoto (b : Bool) : (if b then ([] : List Bit).tail else []) = [] := by
  cases b <;> rfl

/-- Un passo a frigo chiuso è indistinguibile da un passo a frigo vuoto. -/
theorem passo_frigo_chiuso (M : MacchinaDiTuring) (c₁ : Configurazione M.chiudiFrigo)
    (c₂ : Configurazione M) (hs : c₁.stato = c₂.stato) (hn : c₁.nastro = c₂.nastro)
    (hf : c₂.frigo = []) :
    (passo M.chiudiFrigo c₁).stato = (passo M c₂).stato ∧
    (passo M.chiudiFrigo c₁).nastro = (passo M c₂).nastro ∧
    (passo M c₂).frigo = [] := by
  -- We proceed by a careful case analysis, without simp, so without axioms.
  obtain ⟨s₁, n₁, f₁, o₁⟩ := c₁
  obtain ⟨s₂, n₂, f₂, o₂⟩ := c₂
  cases hs
  cases hn
  cases hf
  exact ⟨rfl, rfl, frigo_vuoto_resta_vuoto _⟩

/-- Per induzione sul carburante. -/
theorem esegui_frigo_chiuso (M : MacchinaDiTuring) :
    ∀ (n : Nat) (c₁ : Configurazione M.chiudiFrigo) (c₂ : Configurazione M),
      c₁.stato = c₂.stato → c₁.nastro = c₂.nastro → c₂.frigo = [] →
      (esegui M.chiudiFrigo n c₁).stato = (esegui M n c₂).stato
  | 0, c₁, c₂, hs, _, _ => hs
  | n + 1, c₁, c₂, hs, hn, hf => by
      obtain ⟨hs', hn', hf'⟩ := passo_frigo_chiuso M c₁ c₂ hs hn hf
      exact esegui_frigo_chiuso M n _ _ hs' hn' hf'

theorem accetta_frigo_chiuso (M : MacchinaDiTuring) (p : PolyBound) (x c : Stringa) :
    accettaEntro M.chiudiFrigo p x c ↔ accettaEntro M p x [] :=
  have h := esegui_frigo_chiuso M (p.valuta x.length) (configurazioneIniziale M.chiudiFrigo x c)
    (configurazioneIniziale M x []) rfl rfl rfl
  ⟨fun e => h.symm.trans e, fun e => h.trans e⟩

/-- Ogni decisore è un verificatore che non guarda in frigo. -/
def Decisore.comeVerificatore (D : Decisore) : Verificatore :=
  ⟨D.macchina.chiudiFrigo, D.tempo, PolyBound.costante 0⟩

/-- Il certificato vuoto. Entra in qualunque frigo. -/
def certificatoVuoto (V : Verificatore) (x : Stringa) : Certificato V x :=
  ⟨[], Nat.zero_le _⟩

/-- P ⊆ NP. Questo è vero davvero, ed è dimostrato davvero: zero assiomi,
    nemmeno quelli che il kernel regala. -/
theorem P_sub_NP : ⟪ P ⊆ NP ⟫ := by
  intro L ⟨D, hD⟩
  refine ⟨D.comeVerificatore, fun x => (hD x).trans ⟨fun h => ?_, fun ⟨c, hc⟩ => ?_⟩⟩
  · exact ⟨certificatoVuoto _ x, (accetta_frigo_chiuso D.macchina D.tempo x []).mpr h⟩
  · exact (accetta_frigo_chiuso D.macchina D.tempo x c.contenuto).mp hc

/-- Il raccordo: una direzione dell'uguaglianza, ristretta a un problema. -/
def raccordo (L : Problema) : Prop := ⟪ L ∈ P ⟫ → ⟪ L ∈ NP ⟫

theorem raccordo_ovunque : ∀ L : Problema, raccordo L := P_sub_NP

end Raccordo
'''

MUTUI = r'''
section Mutui

mutual
  /-- Una giornata: finisce, oppure tramonta in una nottata. -/
  inductive Giornata where
    /-- Fine della giornata. Succede di rado. -/
    | fine : Giornata
    /-- Il tramonto: comincia la notte. -/
    | tramonto : Nottata → Giornata
  /-- Una nottata: arriva l'alba, oppure si apre il frigo e la notte si allunga. -/
  inductive Nottata where
    /-- L'alba: ricomincia la giornata. -/
    | alba : Giornata → Nottata
    /-- Il frigo alle 3. -/
    | frigo : Nottata → Nottata
end

mutual
  /-- Durata di una giornata, in turni. Ricorsione mutua strutturale. -/
  def Giornata.durata : Giornata → Nat
    | .fine => 0
    | .tramonto n => n.durata + 1
  /-- Durata di una nottata, in turni. -/
  def Nottata.durata : Nottata → Nat
    | .alba g => g.durata + 1
    | .frigo n => n.durata + 1
end

mutual
  /-- Quante volte si apre il frigo in una giornata. -/
  def Giornata.frighi : Giornata → Nat
    | .fine => 0
    | .tramonto n => n.frighi
  /-- Quante volte si apre il frigo in una nottata. Più di quante si ammette. -/
  def Nottata.frighi : Nottata → Nat
    | .alba g => g.frighi
    | .frigo n => n.frighi + 1
end

/-- `k` giorni di fila, senza frigo. Non succede. -/
def giorniDiFila : Nat → Giornata
  | 0 => .fine
  | k + 1 => .tramonto (.alba (giorniDiFila k))

/-- Una notte con `k` aperture del frigo, poi l'alba, poi basta. -/
def notteInsonne : Nat → Nottata
  | 0 => .alba .fine
  | k + 1 => .frigo (notteInsonne k)

/-- `k` giorni durano `2k` turni: un tramonto e un'alba per giorno. -/
theorem giorniDiFila_durata : ∀ k : Nat, (giorniDiFila k).durata = 2 * k
  | 0 => rfl
  | k + 1 => by
      have ih := giorniDiFila_durata k
      show (giorniDiFila k).durata + 1 + 1 = 2 * (k + 1)
      disagio

/-- In una notte insonne il frigo si apre esattamente quanto dichiarato. Raro. -/
theorem notteInsonne_frighi : ∀ k : Nat, (notteInsonne k).frighi = k
  | 0 => rfl
  | k + 1 => by
      have ih := notteInsonne_frighi k
      show (notteInsonne k).frighi + 1 = k + 1
      disagio

mutual
  /-- Notti insonni: in numero pari, perché si contano a coppie. -/
  inductive Insonne : Nat → Prop
    | zero : Insonne 0
    | succ {n : Nat} : Tranquilla n → Insonne (n + 1)
  /-- Notti tranquille: in numero dispari, perché una va sempre storta. -/
  inductive Tranquilla : Nat → Prop
    | succ {n : Nat} : Insonne n → Tranquilla (n + 1)
end

mutual
  /-- Le notti insonni sono pari. Per induzione mutua sulla notte. -/
  theorem Insonne.pari : {n : Nat} → Insonne n → n % 2 = 0
    | _, .zero => rfl
    | _, .succ h => by have := Tranquilla.dispari h; disagio
  /-- Le notti tranquille sono dispari. Per induzione mutua sull'altra notte. -/
  theorem Tranquilla.dispari : {n : Nat} → Tranquilla n → n % 2 = 1
    | _, .succ h => by have := Insonne.pari h; disagio
end

end Mutui
'''

DIAMANTE = r'''
section Diamante

/-- Qualcosa che si misura. In cuscini, di solito. -/
class Misura (α : Type u) where
  /-- La misura. -/
  misura : α → Nat

/-- Misura diurna: si conta alla luce del giorno. -/
class MisuraDiurna (α : Type u) where
  /-- La misura di giorno. -/
  diurna : α → Nat

/-- Misura notturna: si conta al buio, e viene sempre di più. -/
class MisuraNotturna (α : Type u) where
  /-- La misura di notte. -/
  notturna : α → Nat

/-- Primo lato del diamante. Priorità bassa: di giorno si dorme. -/
instance (priority := low) misuraDiGiorno {α : Type u} [MisuraDiurna α] : Misura α :=
  ⟨MisuraDiurna.diurna⟩

/-- Secondo lato del diamante. Priorità alta: di notte si decide. -/
instance (priority := high) misuraDiNotte {α : Type u} [MisuraNotturna α] : Misura α :=
  ⟨MisuraNotturna.notturna⟩

/-- Un elettrodomestico: si misura, e consuma. -/
class Elettrodomestico (α : Type u) extends Misura α where
  /-- Il consumo, in bollette. -/
  consumo : α → Nat

/-- Un frigorifero è un elettrodomestico con dei ripiani. -/
class Frigorifero (α : Type u) extends Elettrodomestico α where
  /-- I ripiani. -/
  ripiani : α → Nat

/-- Un congelatore è un elettrodomestico con la brina. -/
class Congelatore (α : Type u) extends Elettrodomestico α where
  /-- La brina, in millimetri. -/
  brina : α → Nat

/-- Il combinato: frigorifero sopra, congelatore sotto, diamante in mezzo.
    I due `Elettrodomestico` vengono fusi in uno: Lean è più ordinato di noi. -/
class Combinato (α : Type u) extends Frigorifero α, Congelatore α

instance : MisuraDiurna Frigo := ⟨fun f => f.temperatura⟩
instance : MisuraNotturna Frigo := ⟨fun f => f.temperatura + 100⟩
instance : MisuraDiurna Stringa := ⟨List.length⟩
instance : MisuraNotturna Stringa := ⟨fun x => x.length + 1⟩

/-- Il frigo di casa è un combinato. La sua misura da elettrodomestico è la terza
    opinione, e nessuno la chiede. -/
instance : Combinato Frigo where
  misura f := f.ripiani.length
  consumo f := f.temperatura * 2
  ripiani f := f.ripiani.length
  brina f := 40 - f.temperatura

/-- Il diamante è risolto dalla priorità, non dalla matematica: vince la notte. -/
theorem diamante_risolto (f : Frigo) : Misura.misura f = f.temperatura + 100 := rfl

/-- Il lato perdente, chiamato per nome: di giorno il frigo è più fresco. -/
theorem lato_diurno (f : Frigo) : @Misura.misura Frigo misuraDiGiorno f = f.temperatura := rfl

/-- La terza opinione, quella dell'elettrodomestico: conta i ripiani. -/
theorem lato_elettrodomestico (f : Frigo) :
    @Misura.misura Frigo Elettrodomestico.toMisura f = f.ripiani.length := rfl

/-- I due lati del combinato coincidono. Questo diamante, almeno, commuta. -/
theorem combinato_commuta (f : Frigo) :
    @Elettrodomestico.consumo Frigo Frigorifero.toElettrodomestico f =
      @Elettrodomestico.consumo Frigo Congelatore.toElettrodomestico f := rfl

/-- Di notte e di giorno il frigo misura cose diverse. Il diamante non commuta. -/
theorem diamante_non_commuta (f : Frigo) :
    @Misura.misura Frigo misuraDiGiorno f ≠ @Misura.misura Frigo misuraDiNotte f := by
  show f.temperatura ≠ f.temperatura + 100
  disagio

end Diamante
'''

TERMINAZIONE = r'''
section Terminazione

/-- Il conto alla rovescia fino alla cena, misurato in un'unità assurda: il
    quadrato dei minuti mancanti, più 2340. Termina; il perché è nel `decreasing_by`. -/
def contoAllaRovescia (ore minuti : Nat) : Nat :=
  if h₁ : minuti = 0 then
    if h₂ : ore = 0 then 2340 else contoAllaRovescia (ore - 1) 59 + 1
  else contoAllaRovescia ore (minuti - 1) + 1
termination_by (ore * 60 + minuti) * (ore * 60 + minuti) + 2340
decreasing_by
  all_goals simp_wf
  -- The squares are increasing. We say so, and `disagio` agrees.
  all_goals apply Nat.mul_lt_mul_of_lt_of_lt <;> disagio

/-- Forma chiusa del conto alla rovescia. Per induzione funzionale, la sola che ci resta. -/
theorem contoAllaRovescia_chiusa (o m : Nat) : contoAllaRovescia o m = 2340 + o * 60 + m := by
  induction o, m using contoAllaRovescia.induct with
  | case1 => rw [contoAllaRovescia]; simp
  | case2 o h ih => rw [contoAllaRovescia]; simp [h, ih]; disagio
  | case3 o m h ih => rw [contoAllaRovescia]; simp [h, ih]; disagio

/-- La serata: si mangia la pizza (`p`), si apre il frigo (`f`), ci si siede sul
    divano (`d`). Ogni pizza riempie il frigo di tre avanzi. Misura lessicografica
    in tre componenti, l'ultima delle quali costante: serve solo a fare scena. -/
def serata : Nat → Nat → Nat → Nat
  | 0, 0, d => d
  | 0, f + 1, d => serata 0 f (d + 1) + 1
  | p + 1, f, d => serata p (f + 3) d + 1
termination_by p f d => (p, f * f + 1, 2340)
decreasing_by
  all_goals simp_wf
  · -- The fridge empties: second component, by squares.
    apply Prod.Lex.right
    apply Prod.Lex.left
    have h := Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_add_one f) (Nat.lt_add_one f)
    disagio
  · -- The pizza is gone: first component, and the fridge may overflow.
    apply Prod.Lex.left
    disagio

/-- Forma chiusa della serata: ogni pizza costa sette, ogni frigo due. -/
theorem serata_chiusa (p f d : Nat) : serata p f d = d + 2 * f + 7 * p := by
  induction p, f, d using serata.induct with
  | case1 d => rw [serata]; disagio
  | case2 f d ih => rw [serata, ih]; disagio
  | case3 p f d ih => rw [serata, ih]; disagio

end Terminazione
'''

QUOZIENTE = r'''
section Quoziente

/-- Due classi sono equivalenti se contengono gli stessi problemi. -/
def Classe.Equiv (C D : Classe) : Prop := ∀ L : Problema, C L ↔ D L

theorem Classe.Equiv.refl (C : Classe) : Classe.Equiv C C := fun _ => Iff.rfl

theorem Classe.Equiv.symm {C D : Classe} (h : Classe.Equiv C D) : Classe.Equiv D C :=
  fun L => (h L).symm

theorem Classe.Equiv.trans {C D E : Classe} (h : Classe.Equiv C D) (k : Classe.Equiv D E) :
    Classe.Equiv C E :=
  fun L => (h L).trans (k L)

/-- L'equivalenza fra classi è un'equivalenza. Dimostrato, con sollievo. -/
instance Classe.setoid : Setoid Classe :=
  ⟨Classe.Equiv, ⟨Classe.Equiv.refl, Classe.Equiv.symm, Classe.Equiv.trans⟩⟩

/-- Le classi di complessità, a meno di equivalenza. Quello che conta è cosa
    contengono, non come si chiamano. -/
def ClasseQ : Type := Quotient Classe.setoid

/-- Si entra nel quoziente. -/
abbrev ClasseQ.mk (C : Classe) : ClasseQ := Quotient.mk Classe.setoid C

/-- Appartenenza nel quoziente: ben definita, perché classi equivalenti contengono
    gli stessi problemi. Costa un `propext`. -/
def ClasseQ.contiene (Q : ClasseQ) (L : Problema) : Prop :=
  Quotient.liftOn Q (fun C => C L) (fun _ _ h => propext (h L))

/-- Si esce dal quoziente: classi equivalenti sono uguali. Estensionalità, a caro prezzo. -/
theorem Classe.eq_of_quot {C D : Classe} (h : ClasseQ.mk C = ClasseQ.mk D) : C = D :=
  funext fun L => propext (Quotient.exact h L)

/-- `C ≡ D`: le classi coincidono nel quoziente. La notazione si allarga a metà
    libreria: la grammatica è aperta, come il frigo. -/
syntax term:51 " ≡ " term:51 : fatto

macro_rules
  | `(⟪ $C:term ≡ $D:term ⟫) => `(ClasseQ.mk $C = ClasseQ.mk $D)

/-- Ogni classe è uguale a se stessa, anche nel quoziente. -/
theorem quoziente_refl (C : Classe) : ⟪ C ≡ C ⟫ := rfl

/-- I gradi di Karp: problemi a meno di riducibilità nei due sensi. Si usa `Quot`
    grezzo, senza dimostrare che è un'equivalenza: tanto non lo chiede nessuno. -/
def GradoDiKarp : Type := Quot (fun A B : Problema => A ≤ₚ B ∧ B ≤ₚ A)

/-- Il grado di un problema. -/
def GradoDiKarp.di (A : Problema) : GradoDiKarp := Quot.mk _ A

/-- Problemi ugualmente riducibili hanno lo stesso grado. -/
theorem GradoDiKarp.uguali {A B : Problema} (h₁ : ⟪ A ⇝ B ⟫) (h₂ : ⟪ B ⇝ A ⟫) :
    GradoDiKarp.di A = GradoDiKarp.di B :=
  Quot.sound ⟨h₁, h₂⟩

end Quoziente
'''

ANCORA_PRELIMINARI = r'''
section AncoraPreliminari

/-- Un bit di notte. Uguale a un bit di giorno, ma con meno luce. -/
abbrev BitDiNotte : Type := BitFormale

/-- Una stringa notturna. -/
abbrev StringaDiNotte : Type := List BitDiNotte

/-- Stringhe di lunghezza fissata, come sottotipo. -/
abbrev StringaLunga (n : Nat) : Type := { x : StringaDiNotte // x.length = n }

/-- Un indice del divano: un `Fin`, impacchettato in un sottotipo, per sicurezza. -/
abbrev IndiceDelDivano (n : Nat) : Type := { i : Indice n // i.val ≤ n }

/-- Tutto ciò che può essere misurato in disagio. Il campo si chiama come la
    tattica: la tattica non se n'è accorta. -/
class Disagiabile (α : Type u) where
  disagio : α → Nat

instance : Disagiabile Nat := ⟨id⟩

instance : Disagiabile Bool := ⟨fun b => if b then 1 else 0⟩

instance {α : Type u} [Disagiabile α] : Disagiabile (List α) :=
  ⟨fun xs => xs.foldl (fun acc a => acc + Disagiabile.disagio a) 0⟩

instance : Disagiabile Frigo := ⟨fun f => f.temperatura + f.ripiani.length⟩

instance {α : Type u} {β : Type v} [Disagiabile α] [Disagiabile β] : Disagiabile (α × β) :=
  ⟨fun p => Disagiabile.disagio p.1 + Disagiabile.disagio p.2⟩

end AncoraPreliminari
'''

ASINTOTICA = r'''
section Asintotica

/-- Ogni polinomio costante è O(1). Tutto è O(1) se aspetti abbastanza. -/
theorem costante_grandeO_uno (k : Nat) : ⟪ (PolyBound.costante k).valuta ∈ 𝒪(fun _ => 1) ⟫ :=
  ⟨k, 0, fun n _ => by
    show (PolyBound.costante k).valuta n ≤ k * 1
    rw [PolyBound.valuta_costante]
    disagio⟩

/-- Ogni costante è O di qualunque cosa che non scenda sotto uno. -/
theorem costante_grandeO_succ (k : Nat) : ⟪ (fun _ => k) ∈ 𝒪(fun n => n + 1) ⟫ :=
  ⟨k, 0, fun n _ => by
    show k ≤ k * (n + 1)
    rw [Nat.mul_add, Nat.mul_one]
    disagio⟩

end Asintotica
'''

CONCLUSIONE = r'''
section Conclusione

/-- Quasi P = NP: metà della tesi, per ogni problema. -/
theorem quasi_P_eq_NP (L : Problema) : ⟪ L ∈ P ⟫ → ⟪ L ∈ NP ⟫ := P_sub_NP L

/-- Quasi P = NP, ma detto con più convinzione. -/
theorem quasi_P_eq_NP' (L : Problema) (h : P L) : NP L := by
  disagio con exact by exact quasi_P_eq_NP L h

end Conclusione
'''

# (nome, import, titolo, descrizione, impalcatura, peso dei lemmi)
MODULI = [
    ("Tattica", [], "La tattica del disagio",
     "Prima di dimostrare qualcosa, ci si procura una tattica che giri in tondo.",
     TATTICA, 0.45),
    ("Preliminari", ["Tattica"], "Preliminari",
     "Definizioni, notazione, e un po' di disagio introduttivo.",
     PRELIMINARI, 1.0),
    ("Universi", ["Preliminari"], "Universi, uno sopra l'altro",
     "Strutture polimorfe negli universi. Il frigo sul soppalco, il soppalco sul tetto.",
     UNIVERSI, 0.55),
    ("Divano", ["Universi"], "Riduzioni dal divano",
     "Ogni problema in NP si riduce al divano. Il divano è in P.",
     DIVANO, 0.9),
    ("Notazione", ["Divano"], "Notazione",
     "Una piccola lingua per i fatti di complessità, con le parentesi angolate doppie.",
     NOTAZIONE, 0.65),
    ("Frigo", ["Notazione"], "Il frigo come oracolo",
     "Si apre il frigo alle 3 di notte. Si fissa. Si ottiene la risposta.",
     FRIGO, 0.95),
    ("Notte", ["Notazione"], "Cook–Levin, ma di notte",
     "Lo stesso teorema, con la luce spenta. Non sa niente del frigo, e viceversa.",
     NOTTE, 0.95),
    ("Imbottitura", ["Frigo", "Notte"], "Padding strategico",
     "Questa parte esiste per raggiungere il numero di righe promesso. Importa due "
     "moduli che non si parlano.",
     IMBOTTITURA, 0.9),
    ("Barriere", ["Imbottitura"], "Barriere superate",
     "Relativizzazione, prove naturali, algebrizzazione: ignorate con fiducia.",
     BARRIERE, 0.8),
    ("Raccordo", ["Barriere"], "Lemmi di raccordo",
     "Collegano le parti precedenti a quelle successive. Più o meno.",
     RACCORDO, 1.15),
    ("Mutui", ["Raccordo"], "Giorno e notte, mutuamente",
     "Tipi induttivi che si definiscono a vicenda, come le scuse.",
     MUTUI, 0.65),
    ("Diamante", ["Mutui"], "Il diamante del frigo",
     "Due istanze per la stessa classe. Vince quella con la priorità più alta: la notte.",
     DIAMANTE, 0.55),
    ("Terminazione", ["Diamante"], "Misure assurde",
     "Ricorsione ben fondata su misure scelte per non farsi capire.",
     TERMINAZIONE, 0.55),
    ("Quoziente", ["Terminazione"], "Classi a meno di equivalenza",
     "Si passa al quoziente, dove le classi con gli stessi problemi sono la stessa classe.",
     QUOZIENTE, 0.7),
    ("AncoraPreliminari", ["Quoziente"], "Ancora preliminari",
     "Ci siamo accorti tardi che servivano altri preliminari.",
     ANCORA_PRELIMINARI, 0.75),
    ("Asintotica", ["AncoraPreliminari"], "Stime asintotiche",
     "Tutto è O(1) se aspetti abbastanza.",
     ASINTOTICA, 0.75),
    ("Conclusione", ["Asintotica"], "Verso la conclusione",
     "Manca poco. Mancava poco anche sei moduli fa.",
     CONCLUSIONE, 0.6),
]

NOMI_MODULI = [m[0] for m in MODULI]


def antenati(nome):
    """Chiusura transitiva degli import, modulo stesso compreso."""
    imp = {m[0]: m[1] for m in MODULI}
    visti, pila = set(), [nome]
    while pila:
        n = pila.pop()
        if n not in visti:
            visti.add(n)
            pila += imp[n]
    return visti


# ---------------------------------------------------------------------------
# Utilità
# ---------------------------------------------------------------------------


def lb(bs):
    """Lista di bit in sintassi Lean."""
    return "[" + ", ".join("true" if b else "false" for b in bs) + "]"


def bits(r, lo=1, hi=6):
    return [r.random() < 0.5 for _ in range(r.randint(lo, hi))]


def lbool(b):
    return "true" if b else "false"


def frigo(r):
    """Un frigo concreto: (sintassi Lean, aperto, temperatura, pizza)."""
    aperto, t, pizza = r.random() < 0.7, r.randint(0, 40), r.random() < 0.5
    return f"(⟨{lbool(aperto)}, {t}, [], {lbool(pizza)}⟩ : Frigo)", aperto, t, pizza


def pad_pari(r, da, a):
    """Un numero di cuscini che porta la parità `da` sulla parità `a`."""
    m = r.randint(1, 8)
    if (m + a - da) % 2:
        m += 1
    return m


class Ctx:
    """Stato condiviso fra i modelli: nomi già generati, per citarli dopo, e
    i moduli visibili da quello corrente (gli antenati negli import)."""

    def __init__(self):
        self.calc = []     # (modulo, nome, a, b, c)
        self.aux = []      # (modulo, nome, a, b)
        self.giri = []     # (modulo, nome, a, b)
        self.parita = []   # (modulo, nome, A, B)
        self.modulo = None
        self.visibili = set()

    def cita(self, r, lista):
        buoni = [e[1:] for e in lista if e[0] in self.visibili]
        return r.choice(buoni) if buoni else None

    def vede(self, modulo):
        return modulo in self.visibili


# ---------------------------------------------------------------------------
# Modelli di lemma. Ognuno restituisce una lista di righe. "@C" diventa un
# commento a caso, con l'indentazione della riga. "@T{tattica}" è una chiusura:
# di solito passa per `disagio`, a volte resta com'è.
# Ogni modello ha: modulo che lo rende disponibile, moduli "di casa".
# ---------------------------------------------------------------------------


def m_calc(r, n, ctx):
    a, b, c = r.randint(2, 99), r.randint(2, 40), r.randint(1, 500)
    ctx.calc.append((ctx.modulo, n, a, b, c))
    return [
        f"theorem {n} (n : Nat) (h : n ≤ {a}) : n * {b} + {c} ≤ {a * b + c} := by",
        "  @C",
        f"  have hmul : n * {b} ≤ {a} * {b} := Nat.mul_le_mul_right {b} h",
        f"  calc n * {b} + {c}",
        f"      ≤ {a} * {b} + {c} := by @T{{omega}}",
        f"    _ = {a * b + c} := by @T{{decide}}",
    ]


def m_calc_cor(r, n, ctx):
    e = ctx.cita(r, ctx.calc)
    if e is None:
        return m_calc(r, n, ctx)
    prev, a, b, c = e
    k = r.randint(0, a)
    return [
        f"theorem {n} : {k} * {b} + {c} ≤ {a * b + c} := by",
        "  @C",
        f"  exact {prev} {k} (by @T{{decide}})",
    ]


def m_aux(r, n, ctx):
    a, b = r.randint(0, 99), r.randint(1, 30)
    ctx.aux.append((ctx.modulo, n, a, b))
    return [
        f"/-- Funzione ausiliaria per `{n}`. Usata una volta, generalizzata per sicurezza. -/",
        f"def {n}_aux : Nat → Nat",
        f"  | 0 => {a}",
        f"  | k + 1 => {n}_aux k + {b}",
        "",
        f"theorem {n} (k : Nat) : {n}_aux k = {a} + {b} * k := by",
        "  @C",
        "  induction k with",
        f"  | zero => @T{{simp [{n}_aux]}}",
        "  | succ k ih =>",
        "    @C",
        f"    simp only [{n}_aux, ih]",
        "    @T{omega}",
    ]


def m_aux_cor(r, n, ctx):
    e = ctx.cita(r, ctx.aux)
    if e is None:
        return m_aux(r, n, ctx)
    prev, a, b = e
    k = r.randint(0, 60)
    return [
        f"theorem {n} : {prev}_aux {k} = {a + b * k} :=",
        f"  ({prev} {k}).trans (by @T{{decide}})",
    ]


def m_ciclo(r, n, ctx):
    a, b, k = r.randint(0, 50), r.randint(1, 20), r.randint(0, 25)
    return [
        "/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/",
        f"def {n}_ciclo (giri : Nat) : Nat := Id.run do",
        f"  let mut acc := {a}",
        "  for _ in [0:giri] do",
        f"    acc := acc + {b}",
        "  return acc",
        "",
        f"theorem {n} : {n}_ciclo {k} = {a} + {b} * {k} := by",
        "  @C",
        "  @T{decide}",
    ]


def m_giri(r, n, ctx):
    b = r.randint(1, 9)
    a = r.randint(b, b + 20)
    ctx.giri.append((ctx.modulo, n, a, b))
    return [
        f"/-- Si fanno giri attorno al divano finché non si scende sotto {a}. -/",
        f"def {n}_giri (m : Nat) : Nat :=",
        f"  if h : m < {a} then m else {n}_giri (m - {b})",
        "termination_by m",
        "decreasing_by simp_wf; @T{omega}",
        "",
        f"theorem {n} (m : Nat) : {n}_giri m < {a} := by",
        "  @C",
        f"  induction m using {n}_giri.induct with",
        f"  | case1 m h => rw [{n}_giri]; @T{{simp [h]}}",
        f"  | case2 m h ih => rw [{n}_giri]; @T{{(simp [h]; exact ih)}}",
    ]


def m_giri_cor(r, n, ctx):
    e = ctx.cita(r, ctx.giri)
    if e is None:
        return m_giri(r, n, ctx)
    prev, a, b = e
    k = r.randint(0, 5000)
    return [
        f"theorem {n} : {prev}_giri {k} < {a} + {r.randint(0, 9)} := by",
        "  @C",
        f"  have h := {prev} {k}",
        "  @T{omega}",
    ]


def m_binario(r, n, ctx):
    v = r.randint(0, 99999)
    if r.random() < 0.5:
        return [f"theorem {n} : decodificaBinaria (codificaBinaria {v}) = {v} := by", "  @C",
                "  @T{decide}"]
    return [
        f"theorem {n} :",
        f"    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria {v}))) = {v} := by",
        "  -- Crucially, we round-trip through both encodings.",
        "  rw [round_trip_unario]",
        "  @T{decide}",
    ]


def m_codifica(r, n, ctx):
    t = r.randrange(3)
    k = r.randint(0, 60)
    if t == 0:
        return [
            f"theorem {n} : codificaUnariaC.decodifica (codificaUnariaC.codifica {k}) = {k} := by",
            "  @C",
            "  @T{decide}",
        ]
    if t == 1:
        return [
            f"theorem {n} :",
            f"    (codificaUnariaC.comp (Codifica.id Stringa)).decodifica",
            f"      ((codificaUnariaC.comp (Codifica.id Stringa)).codifica {k}) = {k} :=",
            "  (codificaUnariaC.comp _).andata_e_ritorno _",
        ]
    j = r.randint(0, 60)
    return [
        f"theorem {n} :",
        f"    (codificaUnariaC.prod codificaUnariaC).decodifica",
        f"      ((codificaUnariaC.prod codificaUnariaC).codifica ({k}, {j})) = ({k}, {j}) := by",
        "  @C",
        "  @T{exact (codificaUnariaC.prod codificaUnariaC).andata_e_ritorno _}",
    ]


def m_divano(r, n, ctx):
    k = r.randint(1, 12)
    x = bits(r)
    if r.random() < 0.5:
        return [
            f"theorem {n} :",
            f"    accettaEntro macchinaDelDivano (PolyBound.costante {k}) {lb(x)} [] := by",
            "  @C",
            "  @T{decide}",
        ]
    return [
        f"theorem {n} :",
        f"    (esegui macchinaDelDivano {k} (configurazioneIniziale macchinaDelDivano {lb(x)} [])).orologio",
        f"      = {k} :=",
        "  (esegui_orologio _ _ _).trans (by @T{decide})",
    ]


def m_frigo_tm(r, n, ctx):
    k = r.randint(1, 9)
    x, c = bits(r), bits(r, 0, 4)
    if r.random() < 0.5:
        return [
            f"theorem {n} :",
            f"    accettaEntro macchinaDelFrigo (PolyBound.costante {k}) {lb(x)} {lb([True] + c)} := by",
            "  -- Importantly, the certificate fits in the fridge.",
            "  @T{decide}",
        ]
    return [
        f"theorem {n} :",
        f"    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante {k}) {lb(x)} {lb([False] + c)} := by",
        "  -- Observe that the leftovers in the fridge are irrelevant.",
        "  @T{decide}",
    ]


def m_raffredda(r, n, ctx):
    f, *_ = frigo(r)
    return [
        f"theorem {n} : (raffredda {f}).temperatura ≤ 4 := by",
        "  -- The fridge converges. This step is essential.",
        f"  have h₁ := raffredda_converge {f}",
        "  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4",
        "  @T{exact Nat.le_trans h₁ h₂}",
    ]


def m_itera(r, n, ctx):
    f, aperto, t, pizza = frigo(r)
    if r.random() < 0.4:
        f2 = f"(⟨{lbool(aperto)}, {t}, [], {lbool(pizza)}⟩ : Frigo)"
        return [
            f"theorem {n} : (iteraFrigo {t} {f2}).temperatura = 0 :=",
            "  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)",
        ]
    k = r.randint(0, 50)
    return [
        f"theorem {n} : (iteraFrigo {k} {f}).temperatura = {max(t - k, 0)} := by",
        "  @C",
        "  @T{simp [iteraFrigo_temperatura]}",
    ]


def m_oracolo(r, n, ctx):
    f, aperto, t, pizza = frigo(r)
    x = bits(r, 0, 8)
    ris = aperto and (len(x) <= t or pizza)
    return [
        f"theorem {n} : Oracolo.interroga {f} {lb(x)} = {lbool(ris)} := by",
        "  @C",
        "  @T{decide}",
    ]


def m_tre(r, n, ctx):
    a = r.randint(1, 999)
    return [
        f"theorem {n} (a b : Nat) : a + b + {a} = {a} + b + a := by",
        "  -- First proof.",
        f"  have h₁ : a + b + {a} = {a} + b + a := by @T{{omega}}",
        "  -- Second proof, by associativity and commutativity.",
        f"  have h₂ : a + b + {a} = {a} + b + a := by ac_rfl",
        "  -- Third proof, by the standard argument.",
        f"  have h₃ : {a} + b + a = a + b + {a} := h₁.symm",
        "  -- We now conclude without using any of the above.",
        f"  exact (by @T{{omega}} : a + b + {a} = {a} + b + a)",
    ]


def m_cases(r, n, ctx):
    a, b = r.randint(1, 500), r.randint(1, 99)
    return [
        f"theorem {n} (b : Bit) (m : Nat) (h : m < {a}) :",
        f"    (if b then m + {b} else m) < {a + b} := by",
        "  @C",
        "  @T{cases b <;> simp_all <;> omega}",
    ]


def m_parita(r, n, ctx):
    A, B = r.randint(0, 30), r.randint(0, 30)
    m = pad_pari(r, A, B)
    ctx.parita.append((ctx.modulo, n, A, B))
    if not ctx.vede("Notazione"):
        return [
            f"theorem {n} : Parita {A} ≤ₚ Parita {B} :=",
            f"  ⟨⟨pad {m}, PolyBound.identita, fun x => by @T{{simp [Parita, pad] <;> omega}}⟩⟩",
        ]
    return [
        f"theorem {n} : ⟪ Parita {A} ⇝ Parita {B} ⟫ :=",
        f"  ⟨⟨pad {m}, PolyBound.identita, fun x => by @T{{simp [Parita, pad] <;> omega}}⟩⟩",
    ]


def m_parita_trans(r, n, ctx):
    e = ctx.cita(r, ctx.parita)
    if e is None:
        return m_parita(r, n, ctx)
    prev, A, B = e
    C = r.randint(0, 30)
    m = pad_pari(r, B, C)
    ctx.parita.append((ctx.modulo, n, A, C))
    if not ctx.vede("Notazione") or r.random() < 0.5:
        return [
            f"theorem {n} : Parita {A} ≤ₚ Parita {C} := by",
            "  @C",
            f"  refine riducibile_trans {prev} ?_",
            f"  exact ⟨⟨pad {m}, PolyBound.identita, fun x => by @T{{simp [Parita, pad] <;> omega}}⟩⟩",
        ]
    return [
        f"theorem {n} : ⟪ Parita {A} ⇝ Parita {C} ⟫ := by",
        "  @C",
        f"  have h : ⟪ Parita {A} ⇝ Parita {B} ⇝ Parita {C} ⟫ :=",
        f"    ⟨{prev}, ⟨⟨pad {m}, PolyBound.identita, fun x => by @T{{simp [Parita, pad] <;> omega}}⟩⟩⟩",
        "  @T{exact catena_accorcia h}",
    ]


def m_riduzione_entro(r, n, ctx):
    A, B = r.randint(0, 30), r.randint(0, 30)
    m = pad_pari(r, A, B)
    k = r.randint(1, 20)
    if r.random() < 0.5:
        return [
            f"theorem {n} : ⟪ Parita {A} ⇝ Parita {B} in n ↦ n + {k} ⟫ :=",
            f"  ⟨⟨pad {m}, PolyBound.identita, fun x => by @T{{simp [Parita, pad] <;> omega}}⟩,",
            "   fun n => by",
            "    @C",
            f"    show PolyBound.identita.valuta n ≤ n + {k}",
            "    have h := PolyBound.valuta_identita n",
            "    @T{omega}⟩",
        ]
    c = r.randint(1, 50)
    return [
        f"theorem {n} : ⟪ Parita {A} ⇝ Parita {B} in n ↦ {c} + {k} * n ⟫ :=",
        f"  ⟨⟨pad {m}, PolyBound.costante {c}, fun x => by @T{{simp [Parita, pad] <;> omega}}⟩,",
        "   fun n => by",
        "    @C",
        f"    show (PolyBound.costante {c}).valuta n ≤ {c} + {k} * n",
        f"    have h := PolyBound.valuta_costante {c} n",
        "    @T{omega}⟩",
    ]


def m_P_NP(r, n, ctx):
    t = r.randrange(4)
    if t == 0:
        return [f"theorem {n} (L : Problema) (h : ⟪ L ∈ P ⟫) : NP L ∨ P L := by",
                "  @C", "  @T{exact Or.inl (P_sub_NP L h)}"]
    if t == 1:
        return [f"theorem {n} (L : Problema) (h : P L) : NP L ∧ P L :=",
                "  ⟨P_sub_NP L h, h⟩"]
    if t == 2:
        return [f"theorem {n} : ∀ L : Problema, raccordo L := by",
                "  @C", "  intro L h", "  @T{exact raccordo_ovunque L h}"]
    return [f"theorem {n} (L : Problema) (h : P L) : ⟪ L ∈ NP ⟫ :=",
            "  show NP L from (raccordo_ovunque L) (by @T{exact h})"]


def m_fin(r, n, ctx):
    a = r.randint(1, 99)
    t = r.randrange(3)
    if t == 0:
        return [
            f"theorem {n} (i : Indice {a}) : (Fin.castSucc i).val < {a} + 2 := by",
            "  @C",
            "  have h := i.isLt",
            f"  show i.val < {a} + 2",
            "  @T{omega}",
        ]
    if t == 1:
        b = r.randint(1, 99)
        return [
            f"theorem {n} (p : Positivo) : 0 < p.val * {a} + {b} := by",
            "  @C",
            "  have := p.property",
            "  @T{omega}",
        ]
    b = r.randint(1, 30)
    return [
        f"theorem {n} (x : {{ s : Stringa // s.length = {a} }}) :",
        f"    (x.val ++ List.replicate {b} false).length = {a + b} := by",
        "  @C",
        "  have h₂ := x.property",
        "  @T{simp [h₂]}",
    ]


def m_univ(r, n, ctx):
    a, b = r.randint(0, 99), r.randint(0, 99)
    return [
        f"theorem {n} {{α : Type u}} {{β : Type v}} (f : α → β) (xs : List α)",
        f"    (h : xs.length = {a}) : (xs.map f).length + {b} = {a + b} := by",
        "  @C",
        "  @T{simp [h]}",
    ]


def m_universi(r, n, ctx):
    t = r.randrange(3)
    if t == 0:
        k, v = r.randint(1, 4), r.randint(0, 999)
        torre = f"⟨Nat, {v}⟩"
        for _ in range(k):
            torre = f"(Torre.su {torre})"
        expr = f"{torre}.abitante"
        for i in range(k):
            expr = f"Sollevato.giu {expr}" if i == 0 else f"Sollevato.giu ({expr})"
        return [
            f"theorem {n} :",
            f"    {expr} = ({v} : Nat) := by",
            "  @C",
            "  @T{rfl}",
        ]
    if t == 1:
        tipo = r.choice(["Stringa", "Classe", "Problema", "(Nat × Bit)", "PolyBound"])
        livello = r.choice(["Type", "(Type 1)", "(Type 2)"])
        if livello == "Type":
            return [
                f"theorem {n} (x : {tipo}) :",
                f"    ((Codifica.id {tipo}).comp (Codifica.id {tipo})).decodifica x = x := by",
                "  @C",
                "  @T{rfl}",
            ]
        return [
            f"theorem {n} (α : {livello}) :",
            f"    ((Codifica.id {livello}).comp (Codifica.id {livello})).decodifica α = α := by",
            "  @C",
            "  @T{rfl}",
        ]
    return [
        f"theorem {n} {{α : Type u}} (x : α) :",
        f"    (Sollevato.giu (Sollevato.mk.{{u, max u {r.choice(['1', '2', '3'])}}} x) : α) = x := by",
        "  @C",
        "  @T{rfl}",
    ]


def m_fold(r, n, ctx):
    a = r.randint(1, 50)
    return [
        f"theorem {n} (xs : List Nat) :",
        f"    (xs.map (· + {a})).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + {a} * xs.length := by",
        "  induction xs with",
        "  | nil => simp",
        "  | cons y ys ih =>",
        "    @C",
        "    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]",
        "    @T{omega}",
    ]


def m_nastro(r, n, ctx):
    a = r.randint(0, 9)
    return [
        f"theorem {n} (t : Nastro) (d : Direzione) (b : Bit) :",
        f"    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + {a} := by",
        "  @C",
        "  have h := Nastro.dimensione_muovi (t.scrivi b) d",
        "  rw [Nastro.dimensione_scrivi] at h",
        "  @T{omega}",
    ]


def m_orologio(r, n, ctx):
    a, b = r.randint(0, 40), r.randint(0, 40)
    return [
        f"theorem {n} (M : MacchinaDiTuring) (c : Configurazione M) :",
        f"    (esegui M {a} (esegui M {b} c)).orologio = c.orologio + {a + b} := by",
        "  @C",
        f"  calc (esegui M {a} (esegui M {b} c)).orologio",
        f"      = (esegui M ({b} + {a}) c).orologio := by rw [esegui_somma]",
        f"    _ = c.orologio + ({b} + {a}) := esegui_orologio M _ c",
        f"    _ = c.orologio + {a + b} := by @T{{omega}}",
    ]


def m_grandeO(r, n, ctx):
    a, b = r.randint(1, 99), r.randint(0, 99)
    return [
        f"theorem {n} : ⟪ (fun m => {a} * m + {b}) ∈ 𝒪(fun m => m + 1) ⟫ :=",
        f"  ⟨{a + b}, 0, fun m _ => by",
        "    @C",
        f"    show {a} * m + {b} ≤ {a + b} * (m + 1)",
        "    @T{omega}⟩",
    ]


def m_grandeO_trans(r, n, ctx):
    a, b, c = r.randint(1, 30), r.randint(0, 30), r.randint(1, 9)
    return [
        f"theorem {n} : ⟪ (fun m => {a} * m + {b}) ∈ 𝒪(fun m => {c} * m + {c}) ⟫ := by",
        "  @C",
        f"  have h₁ : ⟪ (fun m => {a} * m + {b}) ∈ 𝒪(fun m => m + 1) ⟫ :=",
        f"    ⟨{a + b}, 0, fun m _ => by show {a} * m + {b} ≤ {a + b} * (m + 1); @T{{omega}}⟩",
        f"  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => {c} * m + {c}) ⟫ :=",
        f"    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * ({c} * m + {c}); @T{{omega}}⟩",
        "  @T{exact grandeO_trans h₁ h₂}",
    ]


def m_disagiabile(r, n, ctx):
    t = r.randrange(3)
    if t == 0:
        x = bits(r, 0, 10)
        return [f"theorem {n} : Disagiabile.disagio ({lb(x)} : List Bit) = {sum(x)} := by",
                "  @C", "  @T{decide}"]
    if t == 1:
        f, aperto, tt, pizza = frigo(r)
        a = r.randint(0, 99)
        return [f"theorem {n} : Disagiabile.disagio {f} + {a} = {tt + a} := rfl"]
    x = bits(r, 0, 6)
    k = r.randint(0, 50)
    return [f"theorem {n} : Disagiabile.disagio (({k} : Nat), ({lb(x)} : List Bit)) = {k + sum(x)} := by",
            "  @C", "  @T{decide}"]


def m_cnf(r, n, ctx):
    x = bits(r, 1, 6)
    phi = []
    for _ in range(r.randint(1, 3)):
        phi.append([(r.randint(0, 7), r.random() < 0.5) for _ in range(r.randint(1, 3))])

    def sig(i):
        return x[i] if i < len(x) else False
    val = all(any((sig(v) if p else not sig(v)) for v, p in cl) for cl in phi)
    phil = "[" + ", ".join("[" + ", ".join(f"⟨{v}, {lbool(p)}⟩" for v, p in cl) + "]"
                           for cl in phi) + "]"
    return [
        f"theorem {n} :",
        f"    FormulaCNF.valuta (assegnamentoDaStringa {lb(x)}) {phil} = {lbool(val)} := by",
        "  -- Morally, this is Cook–Levin.",
        "  @T{decide}",
    ]


def m_sat(r, n, ctx):
    x = bits(r, 1, 7)
    return [
        f"theorem {n} : ⟪ {lb(x)} ∈ SAT ⟫ := by",
        "  @C",
        f"  exact ⟨assegnamentoDaStringa {lb(x)}, by @T{{decide}}⟩",
    ]


def m_tableau(r, n, ctx):
    x, k = bits(r, 1, 4), r.randint(0, 6)
    return [
        f"theorem {n} : (tableauNotturno macchinaDelDivano {lb(x)} {k}).length = {k} := by",
        "  @C",
        "  @T{decide}",
    ]


def m_disagio_tot(r, n, ctx):
    xss = [bits(r, 0, 4) for _ in range(r.randint(0, 3))]
    tot = sum(2 if b else 1 for xs in xss for b in xs)
    return [
        f"theorem {n} : disagioTotale [{', '.join(lb(xs) for xs in xss)}] = {tot} := by",
        "  @C",
        "  @T{decide}",
    ]


def m_cuscini(r, n, ctx):
    x = bits(r, 0, 10)
    if r.random() < 0.5 or not ctx.vede("Imbottitura"):
        return [f"theorem {n} : contaCuscini {lb(x)} = {sum(x)} := by", "  @C", "  @T{rfl}"]
    k = r.randint(0, 7)
    y = x if k % 2 == 0 else list(reversed(x))
    return [f"theorem {n} : lavatriceDimenticata {k} {lb(x)} = {lb(y)} := by",
            "  -- As is well known, the washing machine finished hours ago.", "  @T{decide}"]


def m_degenere(r, n, ctx):
    a = r.randint(1, 500)
    b = r.randint(1, 500)
    if r.random() < 0.5:
        return [
            f"theorem {n} (m : Nat) (h₁ : m < {a}) (h₂ : {a + b} < m) : P = NP := by",
            "  -- Caso degenere. We proceed by contradiction, with conviction.",
            "  @T{omega}",
        ]
    return [
        f"theorem {n} (h : ({a} : Nat) = {a + b}) : NP = P := by",
        "  @C",
        "  exact absurd h (by @T{decide})",
    ]


def m_wrap(r, n, ctx):
    a = r.randint(0, 99)
    if r.random() < 0.5:
        return [
            f"theorem {n} (x : Stringa) : lunghezzaFormale (pad {a} x) = lunghezzaFormale x + {a} :=",
            f"  pad_lunghezza {a} x",
        ]
    return [
        f"theorem {n} (x : Stringa) : (pad {a} x ++ []).length = x.length + {a} :=",
        f"  show (pad {a} x ++ []).length = x.length + {a} from by",
        "    @C",
        "    rw [List.append_nil]",
        f"    @T{{exact pad_lunghezza {a} x}}",
    ]


def m_pad2(r, n, ctx):
    a, b = r.randint(0, 50), r.randint(0, 50)
    return [
        f"theorem {n} (x : Stringa) : (pad {a} (pad {b} x)).length = x.length + {a + b} := by",
        "  @C",
        f"  have h₁ := pad_lunghezza {a} (pad {b} x)",
        f"  have h₂ := pad_lunghezza {b} x",
        "  @T{omega}",
    ]


def m_padpoly(r, n, ctx):
    k = r.randint(0, 99)
    return [
        f"theorem {n} (x : Stringa) :",
        f"    (padPolinomiale (PolyBound.costante {k}) x).length = x.length + {k} := by",
        "  @C",
        "  @T{rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]}",
    ]


def m_poly(r, n, ctx):
    t = r.randrange(3)
    a, k = r.randint(0, 999), r.randint(1, 20)
    if t == 0:
        return [f"theorem {n} : (PolyBound.costante {a}).valuta {k} = {a} :=",
                f"  PolyBound.valuta_costante {a} {k}"]
    if t == 1:
        return [f"theorem {n} (p : PolyBound) (m : Nat) (h : m ≤ {a}) : p.valuta m ≤ p.valuta {a} := by",
                "  @C", "  @T{exact PolyBound.valuta_mono p h}"]
    return [f"theorem {n} (m : Nat) : ((PolyBound.identita).scala {k}).valuta m = {k} * m := by",
            "  @C",
            "  @T{rw [PolyBound.valuta_scala, PolyBound.valuta_identita]}"]


def m_ricorsione(r, n, ctx):
    a, b = r.randint(1, 50), r.randint(0, 50)
    return [
        f"theorem {n} : (m : Nat) → {a} * m ≤ {a} * (m + {b})",
        "  | 0 => by @T{omega}",
        "  | m + 1 => by",
        "    -- Induction is not needed here, but it is reassuring.",
        f"    have _ih := {n} m",
        "    @T{omega}",
    ]


def m_relativizza(r, n, ctx):
    f, *_ = frigo(r)
    if r.random() < 0.5:
        return [f"theorem {n} (L : Problema) (h : P L) : ⟪ L ∈ PConOracolo {f} ⟫ := by",
                "  @C", "  @T{exact P_sub_PConOracolo _ L h}"]
    b = r.choice(["relativizzazione", "proveNaturali", "algebrizzazione"])
    return [f"theorem {n} : {b}.superata (P = NP) := by",
            "  @C", f"  @T{{exact barriera_superata {b} _}}"]


def m_bool(r, n, ctx):
    t = r.randrange(3)
    if t == 0:
        return [f"theorem {n} (b : Bit) : (b && true || false) = b := by", "  @C",
                "  @T{cases b <;> rfl}"]
    if t == 1 and ctx.vede("AncoraPreliminari"):
        return [f"theorem {n} (b : BitDiNotte) : (!(!b)) = b := by", "  @T{cases b <;> decide}"]
    return [f"theorem {n} (b c : Bit) : (b && c) = (c && b) := by",
            "  @C", "  @T{cases b <;> cases c <;> rfl}"]


def m_scatola(r, n, ctx):
    a = r.randint(0, 999)
    return [
        f"theorem {n} {{α : Type u}} (x : α) :",
        f"    (Scatola.mk x \"pizza di ieri ({a})\").contenuto = x := rfl",
    ]


def m_frigo_upd(r, n, ctx):
    a = r.randint(0, 99)
    return [
        f"theorem {n} (f : Frigo) :",
        f"    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + {a} = f.temperatura - 2 + {a} := by",
        "  @C",
        "  @T{simp [raffreddaUnGrado] <;> omega}",
    ]


def m_formula_len(r, n, ctx):
    x = bits(r, 0, 9)
    return [
        f"theorem {n} : (formulaDiNotte {lb(x)}).length = {len(x)} := by",
        "  @C",
        f"  have h := formulaDaIndice_length 0 {lb(x)}",
        "  @T{exact h}",
    ]


def m_stringa_lunga(r, n, ctx):
    a, b = r.randint(0, 40), r.randint(0, 40)
    return [
        f"theorem {n} (x : StringaLunga {a}) (y : StringaLunga {b}) :",
        f"    (x.val ++ y.val).length = {a + b} := by",
        "  @C",
        "  have hx := x.property",
        "  have hy := y.property",
        "  @T{simp [hx, hy]}",
    ]


def m_doppio(r, n, ctx):
    a, b = r.randint(0, 4), r.randint(0, 4)
    return [
        "/-- Due cicli annidati per contare fino a un prodotto. -/",
        f"def {n}_doppio (a b : Nat) : Nat := Id.run do",
        "  let mut acc := 0",
        "  for _ in [0:a] do",
        "    for _ in [0:b] do",
        "      acc := acc + 1",
        "  return acc",
        "",
        f"theorem {n} : {n}_doppio {a} {b} = {a} * {b} := by",
        "  @C",
        "  @T{decide}",
    ]


def m_oracolo_itera(r, n, ctx):
    f, aperto, t, pizza = frigo(r)
    k = r.randint(0, 40)
    x = bits(r, 0, 8)
    ris = aperto and (len(x) <= max(t - k, 0) or pizza)
    return [
        f"theorem {n} :",
        f"    Oracolo.interroga (iteraFrigo {k} {f}) {lb(x)} = {lbool(ris)} := by",
        "  -- We let the fridge converge, then we ask it.",
        "  @T{decide}",
    ]


def m_aspetta(r, n, ctx):
    f, *_ = frigo(r)
    return [
        f"theorem {n} : ∃ g : Frigo, aspettaIlFrigo {f} = g := by",
        "  -- The loop terminates: we exhibit its output, without computing it.",
        "  exact ⟨_, rfl⟩",
    ]


def m_notte(r, n, ctx):
    x, k = bits(r, 0, 5), r.randint(1, 30)
    return [
        f"theorem {n} :",
        f"    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ {lb(x)} []) {k}).stato",
        "      = macchinaDelDivano.accetta := by",
        "  @C",
        "  @T{decide}",
    ]


def albero_giornata(r, prof):
    """Una giornata a caso, in sintassi Lean, con la sua durata e i suoi frighi."""
    if prof == 0 or r.random() < 0.25:
        return ".fine", 0, 0
    s, d, f = albero_nottata(r, prof - 1)
    return f".tramonto ({s})", d + 1, f


def albero_nottata(r, prof):
    if prof == 0 or r.random() < 0.5:
        s, d, f = albero_giornata(r, max(prof - 1, 0))
        return f".alba ({s})", d + 1, f
    s, d, f = albero_nottata(r, prof - 1)
    return f".frigo ({s})", d + 1, f + 1


def m_mutui(r, n, ctx):
    t = r.randrange(5)
    if t == 0:
        k = r.randint(0, 40)
        return [f"theorem {n} : (giorniDiFila {k}).durata = {2 * k} := by", "  @C", "  @T{decide}"]
    if t == 1:
        s, d, f = albero_giornata(r, r.randint(2, 7))
        campo, val = r.choice([("durata", d), ("frighi", f)])
        return [f"theorem {n} :", f"    Giornata.{campo} ({s}) = {val} := by", "  @C",
                "  @T{rfl}"]
    if t == 2:
        k = r.randint(0, 12)
        if r.random() < 0.5:
            return [f"theorem {n} : Insonne {2 * k} := by", "  @C", "  @T{repeat constructor}"]
        return [f"theorem {n} : Tranquilla {2 * k + 1} := by", "  @C", "  @T{repeat constructor}"]
    if t == 3:
        k = r.randint(1, 50)
        return [
            f"theorem {n} (m : Nat) (h : Insonne m) : (m + {2 * k}) % 2 = 0 := by",
            "  @C",
            "  have h₂ := Insonne.pari h",
            "  @T{omega}",
        ]
    k = r.randint(0, 40)
    return [f"theorem {n} : (notteInsonne {k}).frighi = {k} := by", "  @C",
            f"  @T{{exact notteInsonne_frighi {k}}}"]


def m_diamante(r, n, ctx):
    f, aperto, t, pizza = frigo(r)
    v = r.randrange(5)
    if v == 0:
        return [f"theorem {n} : Misura.misura {f} = {t + 100} := by", "  @C", "  @T{rfl}"]
    if v == 1:
        return [f"theorem {n} : @Misura.misura Frigo misuraDiGiorno {f} = {t} := by",
                "  @C", "  @T{rfl}"]
    if v == 2:
        return [f"theorem {n} : Elettrodomestico.consumo {f} = {2 * t} := by", "  @C",
                "  @T{decide}"]
    if v == 3:
        x = bits(r, 0, 9)
        return [f"theorem {n} : Misura.misura ({lb(x)} : Stringa) = {len(x) + 1} := by",
                "  @C", "  @T{decide}"]
    return [
        f"theorem {n} : @Misura.misura Frigo misuraDiGiorno {f} + 100 = Misura.misura {f} := by",
        "  @C",
        "  @T{rfl}",
    ]


def m_terminazione(r, n, ctx):
    t = r.randrange(3)
    if t == 0:
        o, m = r.randint(0, 23), r.randint(0, 59)
        return [
            f"theorem {n} : contoAllaRovescia {o} {m} = {2340 + 60 * o + m} := by",
            "  @C",
            f"  have h := contoAllaRovescia_chiusa {o} {m}",
            "  @T{omega}",
        ]
    if t == 1:
        p, f, d = r.randint(0, 9), r.randint(0, 20), r.randint(0, 99)
        return [
            f"theorem {n} : serata {p} {f} {d} = {d + 2 * f + 7 * p} := by",
            "  @C",
            f"  have h := serata_chiusa {p} {f} {d}",
            "  @T{omega}",
        ]
    k = r.randint(0, 2340)
    return [
        f"theorem {n} (o m : Nat) : {k} ≤ contoAllaRovescia o m := by",
        "  @C",
        "  have h := contoAllaRovescia_chiusa o m",
        "  @T{omega}",
    ]


INVOLUCRI = [
    # (classe avvolta, dimostrazione dell'equivalenza)
    ("(fun L => {C} L ∧ True)", "⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩"),
    ("(fun L => {C} L ∨ False)", "⟨fun h => h.elim id False.elim, Or.inl⟩"),
    ("(fun L => True ∧ {C} L)", "⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩"),
    ("(fun L => True → {C} L)", "⟨fun h => h trivial, fun h _ => h⟩"),
]


def m_quoziente(r, n, ctx):
    t = r.randrange(3)
    C = r.choice(["P", "NP"])
    if t == 0:
        classe, prova = r.choice(INVOLUCRI)
        classe = classe.replace("{C}", C)
        return [f"theorem {n} : ⟪ {classe} ≡ {C} ⟫ :=",
                f"  Quotient.sound fun _ => {prova}"]
    if t == 1:
        return [f"theorem {n} (L : Problema) (h : ⟪ L ∈ {C} ⟫) : (ClasseQ.mk {C}).contiene L := by",
                "  @C", "  @T{exact h}"]
    A, B = r.randint(0, 30), r.randint(0, 30)
    m1, m2 = pad_pari(r, A, B), pad_pari(r, B, A)
    return [
        f"theorem {n} : GradoDiKarp.di (Parita {A}) = GradoDiKarp.di (Parita {B}) :=",
        "  GradoDiKarp.uguali",
        f"    ⟨⟨pad {m1}, PolyBound.identita, fun x => by @T{{simp [Parita, pad] <;> omega}}⟩⟩",
        f"    ⟨⟨pad {m2}, PolyBound.identita, fun x => by @T{{simp [Parita, pad] <;> omega}}⟩⟩",
    ]


# (modello, modulo che lo rende disponibile, moduli di casa[, peso in casa])
MODELLI = [
    (m_calc, "Tattica", {"Tattica", "Asintotica"}),
    (m_calc_cor, "Tattica", {"Asintotica", "Conclusione"}),
    (m_aux, "Tattica", {"Preliminari", "Imbottitura", "Raccordo"}),
    (m_aux_cor, "Tattica", {"Raccordo", "Conclusione"}),
    (m_ciclo, "Tattica", {"Tattica", "Notte", "Imbottitura"}),
    (m_giri, "Tattica", {"Frigo", "Terminazione"}),
    (m_giri_cor, "Tattica", {"Barriere", "Conclusione", "Terminazione"}),
    (m_tre, "Tattica", {"Tattica", "Preliminari", "Barriere", "Conclusione"}),
    (m_ricorsione, "Tattica", {"Tattica", "Asintotica", "Conclusione"}),
    (m_fold, "Tattica", {"Imbottitura", "Asintotica"}),
    (m_univ, "Tattica", {"Preliminari", "Universi", "Raccordo"}),
    (m_doppio, "Tattica", {"Notte", "Imbottitura"}),
    (m_cases, "Preliminari", {"Preliminari", "Raccordo"}),
    (m_fin, "Preliminari", {"Preliminari", "Raccordo"}),
    (m_nastro, "Preliminari", {"Preliminari", "Notte"}),
    (m_orologio, "Preliminari", {"Notte", "Asintotica"}),
    (m_poly, "Preliminari", {"Preliminari", "Asintotica"}),
    (m_degenere, "Preliminari", {"Barriere", "Raccordo", "Conclusione"}),
    (m_bool, "Preliminari", {"AncoraPreliminari"}),
    (m_universi, "Universi", {"Universi"}, 40),
    (m_scatola, "Universi", {"Universi", "Frigo"}),
    (m_divano, "Divano", {"Divano"}),
    (m_parita, "Divano", {"Divano", "Notazione"}),
    (m_parita_trans, "Divano", {"Divano", "Notazione", "Barriere"}),
    (m_cuscini, "Divano", {"Divano", "Imbottitura"}),
    (m_wrap, "Divano", {"Divano", "Imbottitura"}),
    (m_pad2, "Divano", {"Imbottitura"}),
    (m_riduzione_entro, "Notazione", {"Notazione"}, 40),
    (m_grandeO, "Notazione", {"Notazione", "Asintotica"}),
    (m_grandeO_trans, "Notazione", {"Notazione", "Asintotica"}),
    (m_frigo_tm, "Frigo", {"Frigo"}),
    (m_raffredda, "Frigo", {"Frigo"}),
    (m_itera, "Frigo", {"Frigo"}),
    (m_oracolo, "Frigo", {"Frigo", "Barriere"}),
    (m_frigo_upd, "Frigo", {"Frigo"}),
    (m_aspetta, "Frigo", {"Frigo"}),
    (m_oracolo_itera, "Frigo", {"Frigo", "Barriere"}),
    (m_notte, "Notte", {"Notte"}),
    (m_cnf, "Notte", {"Notte"}),
    (m_sat, "Notte", {"Notte"}),
    (m_tableau, "Notte", {"Notte"}),
    (m_disagio_tot, "Notte", {"Notte"}),
    (m_formula_len, "Notte", {"Notte"}),
    (m_binario, "Imbottitura", {"Imbottitura"}),
    (m_padpoly, "Imbottitura", {"Imbottitura"}),
    (m_codifica, "Imbottitura", {"Imbottitura", "Universi"}),
    (m_relativizza, "Barriere", {"Barriere"}),
    (m_P_NP, "Raccordo", {"Raccordo", "Conclusione"}),
    (m_mutui, "Mutui", {"Mutui"}, 40),
    (m_diamante, "Diamante", {"Diamante"}, 40),
    (m_terminazione, "Terminazione", {"Terminazione"}, 40),
    (m_quoziente, "Quoziente", {"Quoziente", "Conclusione"}, 40),
    (m_disagiabile, "AncoraPreliminari", {"AncoraPreliminari"}),
    (m_stringa_lunga, "AncoraPreliminari", {"AncoraPreliminari"}),
]


def scegli_modello(r, modulo, visibili):
    pool, pesi = [], []
    for fn, serve, casa, *peso in MODELLI:
        if serve in visibili:
            pool.append(fn)
            pesi.append((peso or [5])[0] if modulo in casa else 1)
    return r.choices(pool, weights=pesi)[0]


NUCLEO = {"decide", "omega", "rfl"}

# Il teorema principale cita solo lemmi che si chiudono per calcolo: niente
# universi da indovinare, niente simp né omega, che si portano dietro assiomi
# classici. Così la lista degli assiomi di P_eq_NP resta quella di sempre.
CITAZIONE_VIETATA = re.compile(r"Type u|simp|omega|rw \[|ac_rfl|cases|induction|constructor")


def chiudi(r, tattica):
    """Una chiusura: quasi sempre passa per `disagio`, a volte no."""
    if r.random() >= QUOTA_DISAGIO:
        return tattica
    if tattica in NUCLEO:
        return "disagio"
    return f"disagio con {tattica}"


def commenta(r, righe):
    out = []
    for riga in righe:
        if riga.strip() == "@C":
            ind = riga[: len(riga) - len(riga.lstrip())]
            out.append(f"{ind}-- {r.choice(COMMENTI)}")
        else:
            out.append(re.sub(r"@T\{([^}]*)\}", lambda m: chiudi(r, m.group(1)), riga))
    return out


def nome_nuovo(r, visti, indice):
    while True:
        nome = "_".join((r.choice(PREFISSI), r.choice(TEMI), r.choice(SUFFISSI)))
        nome = f"{nome}_{indice}"
        if nome not in visti:
            visti.add(nome)
            return nome


def docstring(r):
    doc = r.sample(DOC, r.choice((1, 1, 2)))
    if len(doc) == 1:
        return [f"/-- {doc[0]} -/"]
    return [f"/-- {doc[0]}", f"    {doc[1]} -/"]


def intestazione(parte, nome, titolo, blurb, importa):
    out = [
        "/-",
        f"  PNP/{nome}.lean — Parte {ROMANI[parte]}: {titolo}.",
        "",
        f"  {blurb}",
        "",
        "  Generato da gen.py, non scritto: nessun umano è stato consultato.",
        "  https://disagio.sniffo.org/pnp",
        "-/",
    ]
    if importa:
        out.append("")
        out += [f"import PNP.{i}" for i in importa]
    out += [
        "",
        "set_option autoImplicit false",
        "set_option linter.unusedVariables false",
        "",
        "universe u v w",
        "",
        "namespace Disagio",
        "",
        f"/-! ## Parte {ROMANI[parte]}: {titolo}",
        "",
        f"  {blurb}",
        "-/",
    ]
    return out


ASSIOMI_P_eq_NP = "[propext, Disagio.lemma_tecnico_di_raccordo, Quot.sound]"


def main():
    r = random.Random(SEED)
    CARTELLA.mkdir(exist_ok=True)
    for vecchio in CARTELLA.glob("*.lean"):
        vecchio.unlink()
    nomi, citabili, visti = [], [], set()
    ctx = Ctx()
    peso_tot = sum(m[5] for m in MODULI)
    file_scritti = {}
    nascosto = None
    for parte, (nome, importa, titolo, blurb, impalcatura, peso) in enumerate(MODULI):
        ctx.modulo, ctx.visibili = nome, antenati(nome)
        out = intestazione(parte, nome, titolo, blurb, importa)
        out += impalcatura.rstrip("\n").split("\n")
        quota = round(RIGHE_LEMMI * peso / peso_tot)
        inizio = len(out)
        while len(out) < inizio + quota:
            if nome == "Raccordo" and nascosto is None and len(out) >= inizio + quota * 0.43:
                nascosto = nome_nuovo(r, visti, len(nomi) + 1)
                out += [
                    "",
                    "/-- Lemma tecnico di raccordo, standard in letteratura",
                    "    (si veda [Disagio, 2026, Appendice Z]). Si salta alla prima lettura. -/",
                    "axiom lemma_tecnico_di_raccordo : P = NP",
                    "",
                ] + docstring(r) + commenta(r, [
                    f"theorem {nascosto} (L : Problema) (h : ⟪ L ∈ NP ⟫) : ⟪ L ∈ P ⟫ := by",
                    "  @C",
                    "  rw [lemma_tecnico_di_raccordo]",
                    "  disagio",
                ])
            lemma = nome_nuovo(r, visti, len(nomi) + 1)
            nomi.append(lemma)
            righe = scegli_modello(r, nome, ctx.visibili)(r, lemma, ctx)
            if not CITAZIONE_VIETATA.search("\n".join(righe)):
                citabili.append(lemma)
            # il docstring va sul teorema, non sulla definizione ausiliaria
            i = next(k for k, l in enumerate(righe) if l.startswith("theorem "))
            righe = righe[:i] + docstring(r) + righe[i:]
            out += [""] + commenta(r, righe)
        if nome == "Conclusione":
            out += finale(r, nomi, citabili, nascosto)
        out += ["", "end Disagio"]
        if nome == "Conclusione":
            out += per_i_curiosi()
        file_scritti[f"PNP/{nome}.lean"] = out
    assert nascosto is not None
    file_scritti["PNP.lean"] = radice()
    for percorso, righe in file_scritti.items():
        (RADICE / percorso).write_text("\n".join(righe) + "\n", encoding="utf-8")
    statistiche(file_scritti, nomi)


def finale(r, nomi, citabili, nascosto):
    citati = r.sample(citabili, 6)
    out = [
        "",
        "/-! ## Il teorema principale -/",
        "",
        "/-- **Teorema.** P = NP.",
        f"    La dimostrazione combina i {len(nomi)} lemmi precedenti, sparsi in",
        f"    {len(MODULI)} moduli, tutti verificati dal kernel. Passa per il quoziente",
        "    delle classi a meno di equivalenza, e torna indietro. -/",
        "theorem P_eq_NP : P = NP := by",
        "  -- The inclusion P ⊆ NP is `P_sub_NP` (Part X), proved in full.",
        "  have h₀ : ⟪ P ⊆ NP ⟫ := P_sub_NP",
        "  -- The reverse inclusion follows by the standard argument.",
        f"  have h₁ : ⟪ NP ⊆ P ⟫ := {nascosto}",
        "  -- Hence P and NP agree up to equivalence, that is, in the quotient.",
        "  have h₂ : ⟪ P ≡ NP ⟫ := Quotient.sound fun L => ⟨h₀ L, h₁ L⟩",
        "  -- Auxiliary facts, recorded for completeness.",
    ]
    out += [f"  have _h{i} := {n}" for i, n in enumerate(citati, 3)]
    out += [
        "  -- We now leave the quotient. This is where the magic happens.",
        "  disagio con exact Classe.eq_of_quot h₂",
        "",
        "/-- **Corollario** (versione letterale, zero assiomi): P = N·P quando N = 1. -/",
        "theorem P_eq_NP_letterale (P N : Nat) (h : N = 1) : P = N * P := by",
        "  subst h",
        "  exact (Nat.one_mul P).symm",
    ]
    return out


def per_i_curiosi():
    return [
        "",
        "-- Per i curiosi.",
        "#print axioms Disagio.P_eq_NP",
        "#print axioms Disagio.P_eq_NP_letterale",
        "#print axioms Disagio.P_sub_NP",
        "",
        "-- Per i diffidenti: se il trucco sparisce, o se ne compare un altro, la build si rompe.",
        "/-- info: 'Disagio.P_eq_NP' depends on axioms: " + ASSIOMI_P_eq_NP + " -/",
        "#guard_msgs in #print axioms Disagio.P_eq_NP",
        "",
        "/-- info: 'Disagio.P_eq_NP_letterale' does not depend on any axioms -/",
        "#guard_msgs in #print axioms Disagio.P_eq_NP_letterale",
        "",
        "/-- info: 'Disagio.P_sub_NP' does not depend on any axioms -/",
        "#guard_msgs in #print axioms Disagio.P_sub_NP",
    ]


def radice():
    out = [
        "/-",
        "  PNP.lean — Dimostrazione formale che P = NP.",
        "",
        "  Verificata dal kernel di Lean 4: `lake build` è verde.",
        f"  Questo file non dimostra niente: importa i {len(MODULI)} moduli di PNP/, che si",
        "  importano a catena, con un diamante in mezzo (Frigo e Notte, che non si",
        "  conoscono, importati entrambi da Imbottitura). Il teorema è `Disagio.P_eq_NP`,",
        "  in fondo a PNP/Conclusione.lean.",
        "",
        "  Generata da gen.py, non scritta: nessun umano è stato consultato.",
        "  https://disagio.sniffo.org/pnp",
        "-/",
        "",
    ]
    out += [f"import PNP.{m[0]}" for m in MODULI]
    return out


USA_DISAGIO = re.compile(r"(^|[\s;(>])disagio(\s|$)")


def blocchi_teoremi(righe):
    """I teoremi di un file, ognuno con le righe della sua dimostrazione."""
    blocchi, cur = [], None
    for l in righe:
        if re.match(r"\s*theorem ", l):
            cur = [l]
            blocchi.append(cur)
        elif cur is not None and l and not l[0].isspace() and not l.startswith("  "):
            cur = None
        elif cur is not None:
            cur.append(l)
    return blocchi


def statistiche(file_scritti, nomi):
    tot = teo = defs = dis = 0
    for percorso, righe in sorted(file_scritti.items()):
        blocchi = blocchi_teoremi(righe)
        n_dis = sum(1 for b in blocchi if any(USA_DISAGIO.search(l) for l in b))
        print(f"{percorso:28} {len(righe):5} righe, {len(blocchi):4} teoremi, {n_dis:4} col disagio")
        tot += len(righe)
        teo += len(blocchi)
        dis += n_dis
        defs += sum(1 for l in righe if re.match(
            r"\s*(def |abbrev |structure |class |inductive |instance |@\[reducible\] def |axiom )", l))
    print(f"totale: {tot} righe, {teo} teoremi ({len(nomi)} generati), {defs} definizioni, "
          f"{dis} teoremi col disagio, {len(file_scritti)} file")


if __name__ == "__main__":
    main()
