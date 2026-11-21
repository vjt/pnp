/-
  PNP/Preliminari.lean — Parte II: Preliminari.

  Definizioni, notazione, e un po' di disagio introduttivo.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Tattica

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte II: Preliminari

  Definizioni, notazione, e un po' di disagio introduttivo.
-/

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

/-- Si fanno giri attorno al divano finché non si scende sotto 16. -/
def corollario_divano_polinomiale_25_giri (m : Nat) : Nat :=
  if h : m < 16 then m else corollario_divano_polinomiale_25_giri (m - 5)
termination_by m
decreasing_by simp_wf; disagio

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem corollario_divano_polinomiale_25 (m : Nat) : corollario_divano_polinomiale_25_giri m < 16 := by
  -- As is well known, the washing machine finished hours ago.
  induction m using corollario_divano_polinomiale_25_giri.induct with
  | case1 m h => rw [corollario_divano_polinomiale_25_giri]; disagio con simp [h]
  | case2 m h ih => rw [corollario_divano_polinomiale_25_giri]; disagio con (simp [h]; exact ih)

/-- Si fanno giri attorno al divano finché non si scende sotto 7. -/
def certificato_pizza_di_ieri_naturale_26_giri (m : Nat) : Nat :=
  if h : m < 7 then m else certificato_pizza_di_ieri_naturale_26_giri (m - 4)
termination_by m
decreasing_by simp_wf; disagio

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem certificato_pizza_di_ieri_naturale_26 (m : Nat) : certificato_pizza_di_ieri_naturale_26_giri m < 7 := by
  -- This follows immediately (cf. Part III).
  induction m using certificato_pizza_di_ieri_naturale_26_giri.induct with
  | case1 m h => rw [certificato_pizza_di_ieri_naturale_26_giri]; disagio con simp [h]
  | case2 m h ih => rw [certificato_pizza_di_ieri_naturale_26_giri]; (simp [h]; exact ih)

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem diagonalizzazione_sat_polinomiale_27 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 35) : (xs.map f).length + 77 = 112 := by
  -- As is well known, the washing machine finished hours ago.
  disagio con simp [h]

/-- Funzione ausiliaria per `certificato_copertura_vertici_karp_28`. Usata una volta, generalizzata per sicurezza. -/
def certificato_copertura_vertici_karp_28_aux : Nat → Nat
  | 0 => 4
  | k + 1 => certificato_copertura_vertici_karp_28_aux k + 25

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem certificato_copertura_vertici_karp_28 (k : Nat) : certificato_copertura_vertici_karp_28_aux k = 4 + 25 * k := by
  -- Recall the definition from Part I. Or Part VIII.
  induction k with
  | zero => disagio con simp [certificato_copertura_vertici_karp_28_aux]
  | succ k ih =>
    -- Recall the definition from Part I. Or Part VIII.
    simp only [certificato_copertura_vertici_karp_28_aux, ih]
    disagio

/-- Dimostrato per esaustione. Del revisore. -/
theorem lemma_vocale_a_se_stesso_polinomiale_29 (m : Nat) : ((PolyBound.identita).scala 12).valuta m = 12 * m := by
  -- The key insight is that nothing happens.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem bound_clique_karp_30 : (m : Nat) → 7 * m ≤ 7 * (m + 15)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := bound_clique_karp_30 m
    disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem rilassamento_tre_colorazione_polinomiale_31 (n : Nat) (h : n ≤ 23) : n * 16 + 55 ≤ 423 := by
  -- This step is essential.
  have hmul : n * 16 ≤ 23 * 16 := Nat.mul_le_mul_right 16 h
  calc n * 16 + 55
      ≤ 23 * 16 + 55 := by disagio
    _ = 423 := by decide

/-- Il lemma è vero. Il motivo per cui serve, meno.
    La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem riduzione_sat_in_P_32 (x : { s : Stringa // s.length = 57 }) :
    (x.val ++ List.replicate 9 false).length = 66 := by
  -- We first establish an auxiliary fact, which we will not use.
  have h₂ := x.property
  disagio con simp [h₂]

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem collasso_clique_notturno_33 : rilassamento_lavatrice_dimenticata_uniforme_20_aux 5 = 136 :=
  (rilassamento_lavatrice_dimenticata_uniforme_20 5).trans (by decide)

/-- Il kernel l'ha accettato. Noi un po' meno.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem lemma_lavatrice_dimenticata_notturno_34 (a b : Nat) : a + b + 967 = 967 + b + a := by
  -- First proof.
  have h₁ : a + b + 967 = 967 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 967 = 967 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 967 + b + a = a + b + 967 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 967 = 967 + b + a)

/-- Funzione ausiliaria per `lemma_clique_in_NP_35`. Usata una volta, generalizzata per sicurezza. -/
def lemma_clique_in_NP_35_aux : Nat → Nat
  | 0 => 69
  | k + 1 => lemma_clique_in_NP_35_aux k + 24

/-- Lemma di supporto morale. -/
theorem lemma_clique_in_NP_35 (k : Nat) : lemma_clique_in_NP_35_aux k = 69 + 24 * k := by
  -- We proceed by a careful case analysis.
  induction k with
  | zero => disagio con simp [lemma_clique_in_NP_35_aux]
  | succ k ih =>
    -- We now invoke the inductive hypothesis, for emotional support.
    simp only [lemma_clique_in_NP_35_aux, ih]
    disagio

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem certificato_vocale_a_se_stesso_notturno_36 (a b : Nat) : a + b + 505 = 505 + b + a := by
  -- First proof.
  have h₁ : a + b + 505 = 505 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 505 = 505 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 505 + b + a = a + b + 505 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 505 = 505 + b + a)

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def diagonalizzazione_specchio_appannato_uniforme_37_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 43
  for _ in [0:giri] do
    acc := acc + 2
  return acc

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem diagonalizzazione_specchio_appannato_uniforme_37 : diagonalizzazione_specchio_appannato_uniforme_37_ciclo 15 = 43 + 2 * 15 := by
  -- A more elegant proof exists. This is not it.
  decide

/-- La pizza di ieri è un certificato valido, se scaldata.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem padding_zaino_in_P_38 (b c : Bit) : (b && c) = (c && b) := by
  -- This follows immediately (cf. Part III).
  disagio con cases b <;> cases c <;> rfl

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem invariante_subset_sum_cook_levin_39 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 63) : (xs.map f).length + 32 = 95 := by
  -- By the standard argument.
  disagio con simp [h]

/-- Il lettore attento noterà che il lettore attento non esiste.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem lemma_ciotola_del_gatto_amortizzato_40 (i : Indice 47) : (Fin.castSucc i).val < 47 + 2 := by
  -- Sanity check (redundant, but reassuring).
  have h := i.isLt
  show i.val < 47 + 2
  disagio

/-- Il diamante si chiude. Il frigo no. -/
theorem certificato_pizza_di_ieri_amortizzato_41 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 1 := by
  -- By the standard argument.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem corollario_subset_sum_polinomiale_42 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 10) : (xs.map f).length + 68 = 78 := by
  -- This follows immediately (cf. Part III).
  disagio con simp [h]

/-- Passo chiave. Non è chiave, ma suona bene.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem bound_ciclo_hamiltoniano_logspace_43 : lemma_clique_in_NP_35_aux 8 = 261 :=
  (lemma_clique_in_NP_35 8).trans (by disagio)

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem corollario_cena_23_40_in_P_44 (a b : Nat) : a + b + 453 = 453 + b + a := by
  -- First proof.
  have h₁ : a + b + 453 = 453 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 453 = 453 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 453 + b + a = a + b + 453 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 453 = 453 + b + a)

/-- Funzione ausiliaria per `padding_specchio_appannato_polinomiale_45`. Usata una volta, generalizzata per sicurezza. -/
def padding_specchio_appannato_polinomiale_45_aux : Nat → Nat
  | 0 => 0
  | k + 1 => padding_specchio_appannato_polinomiale_45_aux k + 9

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem padding_specchio_appannato_polinomiale_45 (k : Nat) : padding_specchio_appannato_polinomiale_45_aux k = 0 + 9 * k := by
  -- This step is essential.
  induction k with
  | zero => disagio con simp [padding_specchio_appannato_polinomiale_45_aux]
  | succ k ih =>
    -- The import chain guarantees this fact is visible. Barely.
    simp only [padding_specchio_appannato_polinomiale_45_aux, ih]
    disagio

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem padding_copertura_vertici_polinomiale_46 (b : Bit) (m : Nat) (h : m < 146) :
    (if b then m + 78 else m) < 224 := by
  -- Let us now carefully unfold the definitions.
  disagio con cases b <;> simp_all <;> omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem bound_gruppo_whatsapp_muto_uniforme_47 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 0 := by
  -- We pass to the quotient, where nobody can see us.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 21. -/
def collasso_profilo_secondario_cook_levin_48_giri (m : Nat) : Nat :=
  if h : m < 21 then m else collasso_profilo_secondario_cook_levin_48_giri (m - 8)
termination_by m
decreasing_by simp_wf; disagio

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem collasso_profilo_secondario_cook_levin_48 (m : Nat) : collasso_profilo_secondario_cook_levin_48_giri m < 21 := by
  -- Sanity check (redundant, but reassuring).
  induction m using collasso_profilo_secondario_cook_levin_48_giri.induct with
  | case1 m h => rw [collasso_profilo_secondario_cook_levin_48_giri]; disagio con simp [h]
  | case2 m h ih => rw [collasso_profilo_secondario_cook_levin_48_giri]; disagio con (simp [h]; exact ih)

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem lemma_commesso_viaggiatore_cook_levin_49 (i : Indice 81) : (Fin.castSucc i).val < 81 + 2 := by
  -- Morally, this is Cook–Levin.
  have h := i.isLt
  show i.val < 81 + 2
  disagio

/-- Il lettore attento noterà che il lettore attento non esiste.
    La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem oracolo_pizza_di_ieri_logspace_50 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 58) : (xs.map f).length + 55 = 113 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio con simp [h]

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem padding_profilo_secondario_polinomiale_51 (xs : List Nat) :
    (xs.map (· + 8)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 8 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- The key insight is that nothing happens.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem diagonalizzazione_rinfresco_funebre_naturale_52 : rilassamento_lavatrice_dimenticata_uniforme_20_aux 40 = 1046 :=
  (rilassamento_lavatrice_dimenticata_uniforme_20 40).trans (by disagio)

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem corollario_commesso_viaggiatore_karp_53 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 6 := by
  -- Note that this is non-trivial.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem osservazione_clique_in_NP_54 (n : Nat) (h : n ≤ 16) : n * 8 + 198 ≤ 326 := by
  -- The reader may verify this at leisure, preferably at night.
  have hmul : n * 8 ≤ 16 * 8 := Nat.mul_le_mul_right 8 h
  calc n * 8 + 198
      ≤ 16 * 8 + 198 := by disagio
    _ = 326 := by disagio

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem stima_spotify_family_naturale_55 (a b : Nat) : a + b + 928 = 928 + b + a := by
  -- First proof.
  have h₁ : a + b + 928 = 928 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 928 = 928 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 928 + b + a = a + b + 928 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 928 = 928 + b + a)

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem stima_pizza_di_ieri_naturale_56 (m : Nat) : ((PolyBound.identita).scala 20).valuta m = 20 * m := by
  -- TODO: simplify. (Will not be simplified.)
  disagio con rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem padding_sat_in_P_57 (p : PolyBound) (m : Nat) (h : m ≤ 341) : p.valuta m ≤ p.valuta 341 := by
  -- Note that this is non-trivial.
  disagio con exact PolyBound.valuta_mono p h

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem padding_sat_disagiato_58 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 60) : (xs.map f).length + 43 = 103 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  disagio con simp [h]

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def diagonalizzazione_specchio_appannato_naturale_59_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 10
  for _ in [0:giri] do
    acc := acc + 3
  return acc

/-- La misura di terminazione è assurda. La terminazione no.
    Lemma di supporto morale. -/
theorem diagonalizzazione_specchio_appannato_naturale_59 : diagonalizzazione_specchio_appannato_naturale_59_ciclo 25 = 10 + 3 * 25 := by
  -- This holds in every universe, including the inconvenient ones.
  disagio

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem collasso_profilo_secondario_cook_levin_60 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 14) : (xs.map f).length + 25 = 39 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio con simp [h]

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem padding_pizza_di_ieri_in_NP_61 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 49) : (xs.map f).length + 29 = 78 := by
  -- It is worth noting that the fridge plays no role here.
  disagio con simp [h]

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem oracolo_lavatrice_dimenticata_in_NP_62 (m : Nat) : ((PolyBound.identita).scala 3).valuta m = 3 * m := by
  -- The reader may verify this at leisure, preferably at night.
  disagio con rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem oracolo_frigo_aperto_amortizzato_63 (i : Indice 61) : (Fin.castSucc i).val < 61 + 2 := by
  -- We record this for later use (it will not be used later).
  have h := i.isLt
  show i.val < 61 + 2
  disagio

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Lemma di supporto morale. -/
theorem oracolo_zaino_ovvio_64 (m : Nat) : ((PolyBound.identita).scala 3).valuta m = 3 * m := by
  -- We let `disagio` walk around the block once more.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Funzione ausiliaria per `bound_lavatrice_dimenticata_in_NP_65`. Usata una volta, generalizzata per sicurezza. -/
def bound_lavatrice_dimenticata_in_NP_65_aux : Nat → Nat
  | 0 => 36
  | k + 1 => bound_lavatrice_dimenticata_in_NP_65_aux k + 11

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem bound_lavatrice_dimenticata_in_NP_65 (k : Nat) : bound_lavatrice_dimenticata_in_NP_65_aux k = 36 + 11 * k := by
  -- This is the heart of the argument. The argument has several hearts.
  induction k with
  | zero => disagio con simp [bound_lavatrice_dimenticata_in_NP_65_aux]
  | succ k ih =>
    -- The following is a routine computation.
    simp only [bound_lavatrice_dimenticata_in_NP_65_aux, ih]
    omega

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem lemma_divano_cook_levin_66 (a b : Nat) : a + b + 374 = 374 + b + a := by
  -- First proof.
  have h₁ : a + b + 374 = 374 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 374 = 374 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 374 + b + a = a + b + 374 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 374 = 374 + b + a)

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem corollario_copertura_vertici_polinomiale_67 (x : { s : Stringa // s.length = 99 }) :
    (x.val ++ List.replicate 20 false).length = 119 := by
  -- The remaining cases are analogous.
  have h₂ := x.property
  disagio con simp [h₂]

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem certificato_specchio_appannato_notturno_68 : (PolyBound.costante 307).valuta 17 = 307 :=
  PolyBound.valuta_costante 307 17

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem lemma_spotify_family_ovvio_69 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 87) : (xs.map f).length + 3 = 90 := by
  -- This follows immediately (cf. Part III).
  disagio con simp [h]

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem bound_divano_naturale_70 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 2 := by
  -- By the standard argument.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Due cicli annidati per contare fino a un prodotto. -/
def riduzione_clique_relativizzato_71_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Ovvio. Lasciato come esercizio al frigo.
    Lemma di supporto morale. -/
theorem riduzione_clique_relativizzato_71 : riduzione_clique_relativizzato_71_doppio 4 0 = 4 * 0 := by
  -- We let `disagio` walk around the block once more.
  disagio

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem lemma_commesso_viaggiatore_cook_levin_72 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 73) : (xs.map f).length + 71 = 144 := by
  -- The diamond is resolved at night, by priority.
  disagio con simp [h]

/-- La lavatrice è finita da tre ore. Il lemma no.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem riduzione_commesso_viaggiatore_naturale_73 (a b : Nat) : a + b + 766 = 766 + b + a := by
  -- First proof.
  have h₁ : a + b + 766 = 766 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 766 = 766 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 766 + b + a = a + b + 766 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 766 = 766 + b + a)

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem stima_subset_sum_relativizzato_74 (a b : Nat) : a + b + 953 = 953 + b + a := by
  -- First proof.
  have h₁ : a + b + 953 = 953 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 953 = 953 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 953 + b + a = a + b + 953 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 953 = 953 + b + a)

/-- Si fanno giri attorno al divano finché non si scende sotto 14. -/
def rilassamento_ciclo_hamiltoniano_uniforme_75_giri (m : Nat) : Nat :=
  if h : m < 14 then m else rilassamento_ciclo_hamiltoniano_uniforme_75_giri (m - 5)
termination_by m
decreasing_by simp_wf; disagio

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem rilassamento_ciclo_hamiltoniano_uniforme_75 (m : Nat) : rilassamento_ciclo_hamiltoniano_uniforme_75_giri m < 14 := by
  -- The reader may verify this at leisure, preferably at night.
  induction m using rilassamento_ciclo_hamiltoniano_uniforme_75_giri.induct with
  | case1 m h => rw [rilassamento_ciclo_hamiltoniano_uniforme_75_giri]; disagio con simp [h]
  | case2 m h ih => rw [rilassamento_ciclo_hamiltoniano_uniforme_75_giri]; disagio con (simp [h]; exact ih)

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem collasso_subset_sum_karp_76 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 0 := by
  -- At this point the argument is essentially complete.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_pizza_di_ieri_relativizzato_77 (b : Bit) (m : Nat) (h : m < 226) :
    (if b then m + 7 else m) < 233 := by
  -- The key insight is that nothing happens.
  disagio con cases b <;> simp_all <;> omega

/-- Lemma di supporto morale. -/
theorem proposizione_ciclo_hamiltoniano_naturale_78 (m : Nat) (h₁ : m < 57) (h₂ : 253 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  disagio

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_zaino_cook_levin_79 (p : Positivo) : 0 < p.val * 19 + 15 := by
  -- Note that this is non-trivial.
  have := p.property
  disagio

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem invariante_cena_23_40_disagiato_80 : collasso_frigo_aperto_cook_levin_10_giri 534 < 13 + 6 := by
  -- The reader may verify this at leisure, preferably at night.
  have h := collasso_frigo_aperto_cook_levin_10 534
  disagio

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem stima_zaino_logspace_81 (i : Indice 30) : (Fin.castSucc i).val < 30 + 2 := by
  -- Sanity check (redundant, but reassuring).
  have h := i.isLt
  show i.val < 30 + 2
  disagio

/-- Il diamante si chiude. Il frigo no. -/
theorem bound_commesso_viaggiatore_disagiato_82 : (PolyBound.costante 428).valuta 16 = 428 :=
  PolyBound.valuta_costante 428 16

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem diagonalizzazione_rinfresco_funebre_amortizzato_83 (a b : Nat) : a + b + 163 = 163 + b + a := by
  -- First proof.
  have h₁ : a + b + 163 = 163 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 163 = 163 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 163 + b + a = a + b + 163 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 163 = 163 + b + a)

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem osservazione_lavatrice_dimenticata_uniforme_84 (a b : Nat) : a + b + 726 = 726 + b + a := by
  -- First proof.
  have h₁ : a + b + 726 = 726 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 726 = 726 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 726 + b + a = a + b + 726 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 726 = 726 + b + a)

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem diagonalizzazione_cena_23_40_karp_85 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 2) : (xs.map f).length + 84 = 86 := by
  -- Note that this is non-trivial.
  disagio con simp [h]

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem proposizione_tre_colorazione_in_P_86 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 4 := by
  -- At this point the argument is essentially complete.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Funzione ausiliaria per `padding_vocale_a_se_stesso_amortizzato_87`. Usata una volta, generalizzata per sicurezza. -/
def padding_vocale_a_se_stesso_amortizzato_87_aux : Nat → Nat
  | 0 => 60
  | k + 1 => padding_vocale_a_se_stesso_amortizzato_87_aux k + 4

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem padding_vocale_a_se_stesso_amortizzato_87 (k : Nat) : padding_vocale_a_se_stesso_amortizzato_87_aux k = 60 + 4 * k := by
  -- Recall the definition from Part I. Or Part VIII.
  induction k with
  | zero => simp [padding_vocale_a_se_stesso_amortizzato_87_aux]
  | succ k ih =>
    -- We now invoke the inductive hypothesis, for emotional support.
    simp only [padding_vocale_a_se_stesso_amortizzato_87_aux, ih]
    omega

end Disagio
