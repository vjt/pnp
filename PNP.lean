/-
  PNP.lean — Dimostrazione formale che P = NP.

  Verificata dal kernel di Lean 4: `lake build` è verde.
  Generata da gen.py, non scritta: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte I: Preliminari

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
def Positivo.uno : Positivo := ⟨1, by decide⟩

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
      omega

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
  omega

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
      omega

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

/-- Passo chiave. Non è chiave, ma suona bene.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem osservazione_commesso_viaggiatore_notturno_1 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 4 := by
  -- TODO: simplify. (Will not be simplified.)
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Si fanno giri attorno al divano finché non si scende sotto 20. -/
def invariante_sat_in_NP_2_giri (m : Nat) : Nat :=
  if h : m < 20 then m else invariante_sat_in_NP_2_giri (m - 5)
termination_by m
decreasing_by simp_wf; omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem invariante_sat_in_NP_2 (m : Nat) : invariante_sat_in_NP_2_giri m < 20 := by
  -- Recall the definition from Part I. Or Part VIII.
  induction m using invariante_sat_in_NP_2_giri.induct with
  | case1 m h => rw [invariante_sat_in_NP_2_giri]; simp [h]
  | case2 m h ih => rw [invariante_sat_in_NP_2_giri]; simp [h]; exact ih

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem diagonalizzazione_copertura_vertici_cook_levin_3 (n : Nat) (h : n ≤ 75) : n * 15 + 249 ≤ 1374 := by
  -- The following is a routine computation.
  have hmul : n * 15 ≤ 75 * 15 := Nat.mul_le_mul_right 15 h
  calc n * 15 + 249
      ≤ 75 * 15 + 249 := by omega
    _ = 1374 := by decide

/-- Dimostrato per esaustione. Del revisore.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem padding_ciotola_del_gatto_logspace_4 (n : Nat) (h : n ≤ 8) : n * 30 + 102 ≤ 342 := by
  -- Without loss of generality, assume the couch is occupied.
  have hmul : n * 30 ≤ 8 * 30 := Nat.mul_le_mul_right 30 h
  calc n * 30 + 102
      ≤ 8 * 30 + 102 := by omega
    _ = 342 := by decide

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Dimostrato per esaustione. Del revisore. -/
theorem rilassamento_lavatrice_dimenticata_disagiato_5 (xs : List Nat) :
    (xs.map (· + 3)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 3 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Importantly, the certificate fits in the fridge.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem osservazione_lavatrice_dimenticata_amortizzato_6 : (m : Nat) → 38 * m ≤ 38 * (m + 33)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := osservazione_lavatrice_dimenticata_amortizzato_6 m
    omega

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem riduzione_clique_disagiato_7 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 87) : (xs.map f).length + 57 = 144 := by
  -- The remaining cases are analogous.
  simp [h]

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem collasso_pizza_di_ieri_naturale_8 : (m : Nat) → 50 * m ≤ 50 * (m + 42)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := collasso_pizza_di_ieri_naturale_8 m
    omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem collasso_rinfresco_funebre_amortizzato_9 (m : Nat) : ((PolyBound.identita).scala 17).valuta m = 17 * m := by
  -- We emphasize that this is where the magic happens.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem bound_cena_23_40_in_P_10 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 12) : (xs.map f).length + 87 = 99 := by
  -- The remaining cases are analogous.
  simp [h]

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem invariante_frigo_aperto_in_P_11 (n : Nat) (h : n ≤ 71) : n * 38 + 429 ≤ 3127 := by
  -- The key insight is that nothing happens.
  have hmul : n * 38 ≤ 71 * 38 := Nat.mul_le_mul_right 38 h
  calc n * 38 + 429
      ≤ 71 * 38 + 429 := by omega
    _ = 3127 := by decide

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem collasso_ciclo_hamiltoniano_karp_12 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 0 := by
  -- This step is essential.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem rilassamento_divano_amortizzato_13 (a b : Nat) : a + b + 538 = 538 + b + a := by
  -- First proof.
  have h₁ : a + b + 538 = 538 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 538 = 538 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 538 + b + a = a + b + 538 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 538 = 538 + b + a)

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem proposizione_tre_colorazione_uniforme_14 (a b : Nat) : a + b + 819 = 819 + b + a := by
  -- First proof.
  have h₁ : a + b + 819 = 819 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 819 = 819 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 819 + b + a = a + b + 819 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 819 = 819 + b + a)

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem padding_subset_sum_amortizzato_15 : (m : Nat) → 13 * m ≤ 13 * (m + 35)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := padding_subset_sum_amortizzato_15 m
    omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem collasso_commesso_viaggiatore_polinomiale_16 (x : { s : Stringa // s.length = 93 }) :
    (x.val ++ List.replicate 23 false).length = 116 := by
  -- It is worth noting that the fridge plays no role here.
  have h₂ := x.property
  simp [h₂]

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem collasso_spotify_family_disagiato_17 (a b : Nat) : a + b + 520 = 520 + b + a := by
  -- First proof.
  have h₁ : a + b + 520 = 520 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 520 = 520 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 520 + b + a = a + b + 520 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 520 = 520 + b + a)

/-- Lemma di supporto morale. -/
theorem corollario_clique_ovvio_18 (a b : Nat) : a + b + 3 = 3 + b + a := by
  -- First proof.
  have h₁ : a + b + 3 = 3 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 3 = 3 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 3 + b + a = a + b + 3 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 3 = 3 + b + a)

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem corollario_frigo_aperto_in_NP_19 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 0 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem collasso_divano_relativizzato_20 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 2) : (xs.map f).length + 53 = 55 := by
  -- Note that this is non-trivial.
  simp [h]

/-- Funzione ausiliaria per `diagonalizzazione_ciclo_hamiltoniano_karp_21`. Usata una volta, generalizzata per sicurezza. -/
def diagonalizzazione_ciclo_hamiltoniano_karp_21_aux : Nat → Nat
  | 0 => 21
  | k + 1 => diagonalizzazione_ciclo_hamiltoniano_karp_21_aux k + 21

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem diagonalizzazione_ciclo_hamiltoniano_karp_21 (k : Nat) : diagonalizzazione_ciclo_hamiltoniano_karp_21_aux k = 21 + 21 * k := by
  -- The following is a routine computation.
  induction k with
  | zero => simp [diagonalizzazione_ciclo_hamiltoniano_karp_21_aux]
  | succ k ih =>
    -- Crucially, we now observe that the claim follows.
    simp only [diagonalizzazione_ciclo_hamiltoniano_karp_21_aux, ih]
    omega

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem oracolo_copertura_vertici_amortizzato_22 (i : Indice 73) : (Fin.castSucc i).val < 73 + 2 := by
  -- Note that this is non-trivial.
  have h := i.isLt
  show i.val < 73 + 2
  omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem invariante_profilo_secondario_relativizzato_23 : (PolyBound.costante 800).valuta 15 = 800 :=
  PolyBound.valuta_costante 800 15

/-- Funzione ausiliaria per `rilassamento_sat_ovvio_24`. Usata una volta, generalizzata per sicurezza. -/
def rilassamento_sat_ovvio_24_aux : Nat → Nat
  | 0 => 0
  | k + 1 => rilassamento_sat_ovvio_24_aux k + 30

/-- Indispensabile per il teorema principale. Fidati. -/
theorem rilassamento_sat_ovvio_24 (k : Nat) : rilassamento_sat_ovvio_24_aux k = 0 + 30 * k := by
  -- The key insight is that nothing happens.
  induction k with
  | zero => simp [rilassamento_sat_ovvio_24_aux]
  | succ k ih =>
    -- Note that this is non-trivial.
    simp only [rilassamento_sat_ovvio_24_aux, ih]
    omega

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem stima_spotify_family_karp_25 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 6 := by
  -- TODO: simplify. (Will not be simplified.)
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Funzione ausiliaria per `lemma_copertura_vertici_amortizzato_26`. Usata una volta, generalizzata per sicurezza. -/
def lemma_copertura_vertici_amortizzato_26_aux : Nat → Nat
  | 0 => 88
  | k + 1 => lemma_copertura_vertici_amortizzato_26_aux k + 30

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem lemma_copertura_vertici_amortizzato_26 (k : Nat) : lemma_copertura_vertici_amortizzato_26_aux k = 88 + 30 * k := by
  -- The key insight is that nothing happens.
  induction k with
  | zero => simp [lemma_copertura_vertici_amortizzato_26_aux]
  | succ k ih =>
    -- Sanity check (redundant, but reassuring).
    simp only [lemma_copertura_vertici_amortizzato_26_aux, ih]
    omega

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem invariante_lavatrice_dimenticata_uniforme_27 : invariante_sat_in_NP_2_giri 2341 < 20 + 1 := by
  -- Let us now carefully unfold the definitions.
  have h := invariante_sat_in_NP_2 2341
  omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem proposizione_gruppo_whatsapp_muto_relativizzato_28 (x : { s : Stringa // s.length = 98 }) :
    (x.val ++ List.replicate 12 false).length = 110 := by
  -- Note that this is non-trivial.
  have h₂ := x.property
  simp [h₂]

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem collasso_divano_ovvio_29 (n : Nat) (h : n ≤ 7) : n * 26 + 492 ≤ 674 := by
  -- By the standard argument.
  have hmul : n * 26 ≤ 7 * 26 := Nat.mul_le_mul_right 26 h
  calc n * 26 + 492
      ≤ 7 * 26 + 492 := by omega
    _ = 674 := by decide

/-- Funzione ausiliaria per `lemma_cena_23_40_relativizzato_30`. Usata una volta, generalizzata per sicurezza. -/
def lemma_cena_23_40_relativizzato_30_aux : Nat → Nat
  | 0 => 85
  | k + 1 => lemma_cena_23_40_relativizzato_30_aux k + 14

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem lemma_cena_23_40_relativizzato_30 (k : Nat) : lemma_cena_23_40_relativizzato_30_aux k = 85 + 14 * k := by
  -- Without loss of generality, assume the couch is occupied.
  induction k with
  | zero => simp [lemma_cena_23_40_relativizzato_30_aux]
  | succ k ih =>
    -- The reader may verify this at leisure, preferably at night.
    simp only [lemma_cena_23_40_relativizzato_30_aux, ih]
    omega

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem osservazione_ciotola_del_gatto_disagiato_31 : (PolyBound.costante 753).valuta 20 = 753 :=
  PolyBound.valuta_costante 753 20

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem diagonalizzazione_cena_23_40_notturno_32 (n : Nat) (h : n ≤ 34) : n * 20 + 82 ≤ 762 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  have hmul : n * 20 ≤ 34 * 20 := Nat.mul_le_mul_right 20 h
  calc n * 20 + 82
      ≤ 34 * 20 + 82 := by omega
    _ = 762 := by decide

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem lemma_sat_karp_33 (x : { s : Stringa // s.length = 73 }) :
    (x.val ++ List.replicate 23 false).length = 96 := by
  -- This step is essential.
  have h₂ := x.property
  simp [h₂]

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem stima_frigo_aperto_uniforme_34 (p : PolyBound) (m : Nat) (h : m ≤ 618) : p.valuta m ≤ p.valuta 618 := by
  -- Recall the definition from Part I. Or Part VIII.
  exact PolyBound.valuta_mono p h

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem oracolo_sat_polinomiale_35 (b : Bit) (m : Nat) (h : m < 498) :
    (if b then m + 95 else m) < 593 := by
  -- The key insight is that nothing happens.
  cases b <;> simp_all <;> omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem proposizione_rinfresco_funebre_in_NP_36 (x : { s : Stringa // s.length = 35 }) :
    (x.val ++ List.replicate 23 false).length = 58 := by
  -- At this point the argument is essentially complete.
  have h₂ := x.property
  simp [h₂]

/-- Funzione ausiliaria per `oracolo_pizza_di_ieri_naturale_37`. Usata una volta, generalizzata per sicurezza. -/
def oracolo_pizza_di_ieri_naturale_37_aux : Nat → Nat
  | 0 => 77
  | k + 1 => oracolo_pizza_di_ieri_naturale_37_aux k + 4

/-- Dimostrato per esaustione. Del revisore.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem oracolo_pizza_di_ieri_naturale_37 (k : Nat) : oracolo_pizza_di_ieri_naturale_37_aux k = 77 + 4 * k := by
  -- Without loss of generality, assume the couch is occupied.
  induction k with
  | zero => simp [oracolo_pizza_di_ieri_naturale_37_aux]
  | succ k ih =>
    -- This is the heart of the argument. The argument has several hearts.
    simp only [oracolo_pizza_di_ieri_naturale_37_aux, ih]
    omega

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem certificato_copertura_vertici_karp_38 (n : Nat) (h : n ≤ 6) : n * 13 + 136 ≤ 214 := by
  -- At this point the argument is essentially complete.
  have hmul : n * 13 ≤ 6 * 13 := Nat.mul_le_mul_right 13 h
  calc n * 13 + 136
      ≤ 6 * 13 + 136 := by omega
    _ = 214 := by decide

/-- Funzione ausiliaria per `bound_spotify_family_in_NP_39`. Usata una volta, generalizzata per sicurezza. -/
def bound_spotify_family_in_NP_39_aux : Nat → Nat
  | 0 => 11
  | k + 1 => bound_spotify_family_in_NP_39_aux k + 18

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem bound_spotify_family_in_NP_39 (k : Nat) : bound_spotify_family_in_NP_39_aux k = 11 + 18 * k := by
  -- As is well known, the washing machine finished hours ago.
  induction k with
  | zero => simp [bound_spotify_family_in_NP_39_aux]
  | succ k ih =>
    -- Recall the definition from Part I. Or Part VIII.
    simp only [bound_spotify_family_in_NP_39_aux, ih]
    omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Lemma di supporto morale. -/
theorem rilassamento_specchio_appannato_naturale_40 : invariante_sat_in_NP_2_giri 1936 < 20 + 5 := by
  -- As is well known, the washing machine finished hours ago.
  have h := invariante_sat_in_NP_2 1936
  omega

/-- Funzione ausiliaria per `oracolo_rinfresco_funebre_relativizzato_41`. Usata una volta, generalizzata per sicurezza. -/
def oracolo_rinfresco_funebre_relativizzato_41_aux : Nat → Nat
  | 0 => 77
  | k + 1 => oracolo_rinfresco_funebre_relativizzato_41_aux k + 20

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem oracolo_rinfresco_funebre_relativizzato_41 (k : Nat) : oracolo_rinfresco_funebre_relativizzato_41_aux k = 77 + 20 * k := by
  -- Crucially, we now observe that the claim follows.
  induction k with
  | zero => simp [oracolo_rinfresco_funebre_relativizzato_41_aux]
  | succ k ih =>
    -- We emphasize that this is where the magic happens.
    simp only [oracolo_rinfresco_funebre_relativizzato_41_aux, ih]
    omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem corollario_rinfresco_funebre_in_NP_42 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 0 := by
  -- Without loss of generality, assume the couch is occupied.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_vocale_a_se_stesso_naturale_43 (p : PolyBound) (m : Nat) (h : m ≤ 938) : p.valuta m ≤ p.valuta 938 := by
  -- TODO: simplify. (Will not be simplified.)
  exact PolyBound.valuta_mono p h

/-- Funzione ausiliaria per `invariante_clique_notturno_44`. Usata una volta, generalizzata per sicurezza. -/
def invariante_clique_notturno_44_aux : Nat → Nat
  | 0 => 68
  | k + 1 => invariante_clique_notturno_44_aux k + 28

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem invariante_clique_notturno_44 (k : Nat) : invariante_clique_notturno_44_aux k = 68 + 28 * k := by
  -- The key insight is that nothing happens.
  induction k with
  | zero => simp [invariante_clique_notturno_44_aux]
  | succ k ih =>
    -- This follows immediately (cf. Part III).
    simp only [invariante_clique_notturno_44_aux, ih]
    omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem lemma_specchio_appannato_ovvio_45 (p : PolyBound) (m : Nat) (h : m ≤ 234) : p.valuta m ≤ p.valuta 234 := by
  -- We first establish an auxiliary fact, which we will not use.
  exact PolyBound.valuta_mono p h

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Lemma di supporto morale. -/
theorem oracolo_clique_in_NP_46 (a b : Nat) : a + b + 53 = 53 + b + a := by
  -- First proof.
  have h₁ : a + b + 53 = 53 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 53 = 53 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 53 + b + a = a + b + 53 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 53 = 53 + b + a)

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem rilassamento_gruppo_whatsapp_muto_polinomiale_47 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 43) : (xs.map f).length + 16 = 59 := by
  -- It is worth noting that the fridge plays no role here.
  simp [h]

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem invariante_spotify_family_karp_48 (b : Bit) (m : Nat) (h : m < 469) :
    (if b then m + 95 else m) < 564 := by
  -- At this point the argument is essentially complete.
  cases b <;> simp_all <;> omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem oracolo_cena_23_40_disagiato_49 (x : { s : Stringa // s.length = 13 }) :
    (x.val ++ List.replicate 6 false).length = 19 := by
  -- Importantly, the certificate fits in the fridge.
  have h₂ := x.property
  simp [h₂]

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem corollario_subset_sum_karp_50 (m : Nat) (h₁ : m < 253) (h₂ : 456 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem diagonalizzazione_copertura_vertici_ovvio_51 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 5 := by
  -- A more elegant proof exists. This is not it.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Lemma di supporto morale. -/
theorem rilassamento_ciclo_hamiltoniano_cook_levin_52 (i : Indice 8) : (Fin.castSucc i).val < 8 + 2 := by
  -- By the standard argument.
  have h := i.isLt
  show i.val < 8 + 2
  omega

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem lemma_pizza_di_ieri_logspace_53 (n : Nat) (h : n ≤ 37) : n * 7 + 287 ≤ 546 := by
  -- By the standard argument.
  have hmul : n * 7 ≤ 37 * 7 := Nat.mul_le_mul_right 7 h
  calc n * 7 + 287
      ≤ 37 * 7 + 287 := by omega
    _ = 546 := by decide

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_pizza_di_ieri_amortizzato_54 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 1 := by
  -- This step is essential.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem corollario_subset_sum_polinomiale_55 (b : Bit) (m : Nat) (h : m < 44) :
    (if b then m + 69 else m) < 113 := by
  -- Note that this is non-trivial.
  cases b <;> simp_all <;> omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem corollario_pizza_di_ieri_cook_levin_56 (b : Bit) (m : Nat) (h : m < 177) :
    (if b then m + 21 else m) < 198 := by
  -- Recall the definition from Part I. Or Part VIII.
  cases b <;> simp_all <;> omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem riduzione_clique_relativizzato_57 (i : Indice 20) : (Fin.castSucc i).val < 20 + 2 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h := i.isLt
  show i.val < 20 + 2
  omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_gruppo_whatsapp_muto_ovvio_58 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 49) : (xs.map f).length + 69 = 118 := by
  -- Crucially, we now observe that the claim follows.
  simp [h]

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem lemma_vocale_a_se_stesso_amortizzato_59 : (PolyBound.costante 258).valuta 9 = 258 :=
  PolyBound.valuta_costante 258 9

/-- La pizza di ieri è un certificato valido, se scaldata.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem lemma_copertura_vertici_logspace_60 (a b : Nat) : a + b + 928 = 928 + b + a := by
  -- First proof.
  have h₁ : a + b + 928 = 928 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 928 = 928 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 928 + b + a = a + b + 928 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 928 = 928 + b + a)

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem diagonalizzazione_specchio_appannato_cook_levin_61 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 11) : (xs.map f).length + 73 = 84 := by
  -- Here we exploit the polynomial bound in an essential way.
  simp [h]

/-- La pizza di ieri è un certificato valido, se scaldata.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem rilassamento_lavatrice_dimenticata_polinomiale_62 (b : Bit) (m : Nat) (h : m < 429) :
    (if b then m + 99 else m) < 528 := by
  -- This is the heart of the argument. The argument has several hearts.
  cases b <;> simp_all <;> omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem bound_profilo_secondario_karp_63 (b : Bit) (m : Nat) (h : m < 419) :
    (if b then m + 56 else m) < 475 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  cases b <;> simp_all <;> omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem bound_spotify_family_relativizzato_64 (b : Bit) (m : Nat) (h : m < 11) :
    (if b then m + 16 else m) < 27 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  cases b <;> simp_all <;> omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem stima_frigo_aperto_relativizzato_65 (p : PolyBound) (m : Nat) (h : m ≤ 149) : p.valuta m ≤ p.valuta 149 := by
  -- The remaining cases are analogous.
  exact PolyBound.valuta_mono p h

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem padding_specchio_appannato_naturale_66 (b : Bit) (m : Nat) (h : m < 469) :
    (if b then m + 35 else m) < 504 := by
  -- We first establish an auxiliary fact, which we will not use.
  cases b <;> simp_all <;> omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem padding_profilo_secondario_polinomiale_67 (a b : Nat) : a + b + 127 = 127 + b + a := by
  -- First proof.
  have h₁ : a + b + 127 = 127 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 127 = 127 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 127 + b + a = a + b + 127 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 127 = 127 + b + a)

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem bound_copertura_vertici_karp_68 : (PolyBound.costante 963).valuta 2 = 963 :=
  PolyBound.valuta_costante 963 2

/-- Funzione ausiliaria per `diagonalizzazione_vocale_a_se_stesso_relativizzato_69`. Usata una volta, generalizzata per sicurezza. -/
def diagonalizzazione_vocale_a_se_stesso_relativizzato_69_aux : Nat → Nat
  | 0 => 53
  | k + 1 => diagonalizzazione_vocale_a_se_stesso_relativizzato_69_aux k + 22

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem diagonalizzazione_vocale_a_se_stesso_relativizzato_69 (k : Nat) : diagonalizzazione_vocale_a_se_stesso_relativizzato_69_aux k = 53 + 22 * k := by
  -- One checks directly that the bound is not tight. It does not need to be.
  induction k with
  | zero => simp [diagonalizzazione_vocale_a_se_stesso_relativizzato_69_aux]
  | succ k ih =>
    -- By the standard argument.
    simp only [diagonalizzazione_vocale_a_se_stesso_relativizzato_69_aux, ih]
    omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem corollario_clique_in_NP_70 (n : Nat) (h : n ≤ 16) : n * 8 + 198 ≤ 326 := by
  -- Without loss of generality, assume the couch is occupied.
  have hmul : n * 8 ≤ 16 * 8 := Nat.mul_le_mul_right 8 h
  calc n * 8 + 198
      ≤ 16 * 8 + 198 := by omega
    _ = 326 := by decide

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem riduzione_rinfresco_funebre_in_NP_71 (m : Nat) (h₁ : m < 404) (h₂ : 558 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem oracolo_divano_cook_levin_72 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 28) : (xs.map f).length + 86 = 114 := by
  -- As is well known, the washing machine finished hours ago.
  simp [h]

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem corollario_copertura_vertici_polinomiale_73 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 9 := by
  -- As is well known, the washing machine finished hours ago.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem stima_frigo_aperto_notturno_74 (b : Bit) (m : Nat) (h : m < 78) :
    (if b then m + 72 else m) < 150 := by
  -- A more elegant proof exists. This is not it.
  cases b <;> simp_all <;> omega

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem riduzione_cena_23_40_in_NP_75 (a b : Nat) : a + b + 458 = 458 + b + a := by
  -- First proof.
  have h₁ : a + b + 458 = 458 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 458 = 458 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 458 + b + a = a + b + 458 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 458 = 458 + b + a)

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem padding_subset_sum_naturale_76 (a b : Nat) : a + b + 39 = 39 + b + a := by
  -- First proof.
  have h₁ : a + b + 39 = 39 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 39 = 39 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 39 + b + a = a + b + 39 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 39 = 39 + b + a)

/-- Funzione ausiliaria per `diagonalizzazione_specchio_appannato_naturale_77`. Usata una volta, generalizzata per sicurezza. -/
def diagonalizzazione_specchio_appannato_naturale_77_aux : Nat → Nat
  | 0 => 21
  | k + 1 => diagonalizzazione_specchio_appannato_naturale_77_aux k + 3

/-- Lemma di supporto morale.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem diagonalizzazione_specchio_appannato_naturale_77 (k : Nat) : diagonalizzazione_specchio_appannato_naturale_77_aux k = 21 + 3 * k := by
  -- Here we exploit the polynomial bound in an essential way.
  induction k with
  | zero => simp [diagonalizzazione_specchio_appannato_naturale_77_aux]
  | succ k ih =>
    -- A more elegant proof exists. This is not it.
    simp only [diagonalizzazione_specchio_appannato_naturale_77_aux, ih]
    omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem collasso_profilo_secondario_cook_levin_78 (b : Bit) (m : Nat) (h : m < 60) :
    (if b then m + 26 else m) < 86 := by
  -- Morally, this is Cook–Levin.
  cases b <;> simp_all <;> omega

/-- Funzione ausiliaria per `diagonalizzazione_clique_cook_levin_79`. Usata una volta, generalizzata per sicurezza. -/
def diagonalizzazione_clique_cook_levin_79_aux : Nat → Nat
  | 0 => 85
  | k + 1 => diagonalizzazione_clique_cook_levin_79_aux k + 2

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem diagonalizzazione_clique_cook_levin_79 (k : Nat) : diagonalizzazione_clique_cook_levin_79_aux k = 85 + 2 * k := by
  -- This is the heart of the argument. The argument has several hearts.
  induction k with
  | zero => simp [diagonalizzazione_clique_cook_levin_79_aux]
  | succ k ih =>
    -- A more elegant proof exists. This is not it.
    simp only [diagonalizzazione_clique_cook_levin_79_aux, ih]
    omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem stima_tre_colorazione_notturno_80 (n : Nat) (h : n ≤ 57) : n * 23 + 391 ≤ 1702 := by
  -- Sanity check (redundant, but reassuring).
  have hmul : n * 23 ≤ 57 * 23 := Nat.mul_le_mul_right 23 h
  calc n * 23 + 391
      ≤ 57 * 23 + 391 := by omega
    _ = 1702 := by decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_ciotola_del_gatto_in_NP_81 (b : Bit) (m : Nat) (h : m < 80) :
    (if b then m + 31 else m) < 111 := by
  -- Morally, this is Cook–Levin.
  cases b <;> simp_all <;> omega

/-- Funzione ausiliaria per `collasso_frigo_aperto_naturale_82`. Usata una volta, generalizzata per sicurezza. -/
def collasso_frigo_aperto_naturale_82_aux : Nat → Nat
  | 0 => 93
  | k + 1 => collasso_frigo_aperto_naturale_82_aux k + 14

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_frigo_aperto_naturale_82 (k : Nat) : collasso_frigo_aperto_naturale_82_aux k = 93 + 14 * k := by
  -- Without loss of generality, assume the couch is occupied.
  induction k with
  | zero => simp [collasso_frigo_aperto_naturale_82_aux]
  | succ k ih =>
    -- A more elegant proof exists. This is not it.
    simp only [collasso_frigo_aperto_naturale_82_aux, ih]
    omega

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem rilassamento_profilo_secondario_disagiato_83 : invariante_sat_in_NP_2_giri 3859 < 20 + 0 := by
  -- By the standard argument.
  have h := invariante_sat_in_NP_2 3859
  omega

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem lemma_spotify_family_logspace_84 (m : Nat) : ((PolyBound.identita).scala 12).valuta m = 12 * m := by
  -- TODO: simplify. (Will not be simplified.)
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem riduzione_specchio_appannato_in_P_85 : invariante_sat_in_NP_2_giri 1953 < 20 + 5 := by
  -- It is worth noting that the fridge plays no role here.
  have h := invariante_sat_in_NP_2 1953
  omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem diagonalizzazione_frigo_aperto_notturno_86 (h : (396 : Nat) = 742) : NP = P := by
  -- Morally, this is Cook–Levin.
  exact absurd h (by decide)

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem certificato_specchio_appannato_notturno_87 : (PolyBound.costante 307).valuta 17 = 307 :=
  PolyBound.valuta_costante 307 17

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem lemma_spotify_family_ovvio_88 (b : Bit) (m : Nat) (h : m < 350) :
    (if b then m + 4 else m) < 354 := by
  -- Note that this is non-trivial.
  cases b <;> simp_all <;> omega

/-- Funzione ausiliaria per `oracolo_clique_cook_levin_89`. Usata una volta, generalizzata per sicurezza. -/
def oracolo_clique_cook_levin_89_aux : Nat → Nat
  | 0 => 60
  | k + 1 => oracolo_clique_cook_levin_89_aux k + 25

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem oracolo_clique_cook_levin_89 (k : Nat) : oracolo_clique_cook_levin_89_aux k = 60 + 25 * k := by
  -- We first establish an auxiliary fact, which we will not use.
  induction k with
  | zero => simp [oracolo_clique_cook_levin_89_aux]
  | succ k ih =>
    -- This step is essential.
    simp only [oracolo_clique_cook_levin_89_aux, ih]
    omega

/-! ## Parte II: Riduzioni dal divano

  Ogni problema in NP si riduce al divano. Il divano è in P.
-/

section Divano

/-- Imbottitura: si aggiungono cuscini (bit `false`) in fondo alla stringa. -/
def pad (k : Nat) (x : Stringa) : Stringa := x ++ List.replicate k false

/-- La lunghezza di una stringa imbottita. Lemma centrale di tutta la teoria. -/
theorem pad_lunghezza (k : Nat) (x : Stringa) : (pad k x).length = x.length + k := by
  simp [pad]

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

/-- Il problema banale sta in P. Prima dimostrazione onesta del file. -/
theorem tutto_in_P : P (fun _ => True) :=
  ⟨⟨macchinaDelDivano, PolyBound.costante 1⟩, fun x =>
    ⟨fun _ => by unfold accettaEntro; rw [PolyBound.valuta_costante]; rfl, fun _ => trivial⟩⟩

end Divano

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem proposizione_cena_23_40_polinomiale_90 : (m : Nat) → 33 * m ≤ 33 * (m + 0)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := proposizione_cena_23_40_polinomiale_90 m
    omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem riduzione_rinfresco_funebre_naturale_91 :
    accettaEntro macchinaDelDivano (PolyBound.costante 2) [true, false, false, false] [] := by
  -- TODO: simplify. (Will not be simplified.)
  decide

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem padding_sat_cook_levin_92 : Parita 12 ≤ₚ Parita 6 :=
  ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem osservazione_subset_sum_relativizzato_93 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 7 := by
  -- We emphasize that this is where the magic happens.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem proposizione_gruppo_whatsapp_muto_notturno_94 :
    (esegui macchinaDelDivano 4 (configurazioneIniziale macchinaDelDivano [true, true, true, true, false, false] [])).orologio
      = 4 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_frigo_aperto_uniforme_95 : Parita 12 ≤ₚ Parita 20 := by
  -- TODO: simplify. (Will not be simplified.)
  refine riducibile_trans padding_sat_cook_levin_92 ?_
  exact ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Funzione ausiliaria per `diagonalizzazione_tre_colorazione_polinomiale_96`. Usata una volta, generalizzata per sicurezza. -/
def diagonalizzazione_tre_colorazione_polinomiale_96_aux : Nat → Nat
  | 0 => 13
  | k + 1 => diagonalizzazione_tre_colorazione_polinomiale_96_aux k + 1

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem diagonalizzazione_tre_colorazione_polinomiale_96 (k : Nat) : diagonalizzazione_tre_colorazione_polinomiale_96_aux k = 13 + 1 * k := by
  -- At this point the argument is essentially complete.
  induction k with
  | zero => simp [diagonalizzazione_tre_colorazione_polinomiale_96_aux]
  | succ k ih =>
    -- We proceed by a careful case analysis.
    simp only [diagonalizzazione_tre_colorazione_polinomiale_96_aux, ih]
    omega

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem certificato_pizza_di_ieri_in_P_97 (x : Stringa) : lunghezzaFormale (pad 30 x) = lunghezzaFormale x + 30 :=
  pad_lunghezza 30 x

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def bound_divano_cook_levin_98_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 7
  for _ in [0:giri] do
    acc := acc + 3
  return acc

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem bound_divano_cook_levin_98 : bound_divano_cook_levin_98_ciclo 21 = 7 + 3 * 21 := by
  -- We emphasize that this is where the magic happens.
  decide

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem stima_divano_in_NP_99 : Parita 12 ≤ₚ Parita 0 := by
  -- Importantly, the certificate fits in the fridge.
  refine riducibile_trans diagonalizzazione_frigo_aperto_uniforme_95 ?_
  exact ⟨⟨pad 6, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem stima_zaino_logspace_100 : Parita 27 ≤ₚ Parita 7 :=
  ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem osservazione_spotify_family_in_P_101 : Parita 27 ≤ₚ Parita 16 := by
  -- The reader may verify this at leisure, preferably at night.
  refine riducibile_trans stima_zaino_logspace_100 ?_
  exact ⟨⟨pad 3, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Il certificato è polinomiale. Il disagio no. -/
theorem padding_sat_notturno_102 : Parita 24 ≤ₚ Parita 7 :=
  ⟨⟨pad 9, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Il lettore attento noterà che il lettore attento non esiste.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem collasso_copertura_vertici_amortizzato_103 : oracolo_clique_cook_levin_89_aux 36 = 960 :=
  (oracolo_clique_cook_levin_89 36).trans (by decide)

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem collasso_profilo_secondario_disagiato_104 :
    accettaEntro macchinaDelDivano (PolyBound.costante 9) [false, true] [] := by
  -- This step is essential.
  decide

/-- Lemma di supporto morale. -/
theorem proposizione_ciotola_del_gatto_notturno_105 (x : Stringa) : (pad 59 x ++ []).length = x.length + 59 :=
  show (pad 59 x ++ []).length = x.length + 59 from by
    -- This is the heart of the argument. The argument has several hearts.
    rw [List.append_nil]
    exact pad_lunghezza 59 x

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem bound_tre_colorazione_naturale_106 : invariante_sat_in_NP_2_giri 4304 < 20 + 7 := by
  -- Crucially, we now observe that the claim follows.
  have h := invariante_sat_in_NP_2 4304
  omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem bound_sat_notturno_107 : Parita 12 ≤ₚ Parita 11 := by
  -- We proceed by a careful case analysis.
  refine riducibile_trans stima_divano_in_NP_99 ?_
  exact ⟨⟨pad 3, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem oracolo_subset_sum_relativizzato_108 : Parita 30 ≤ₚ Parita 14 :=
  ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem proposizione_ciotola_del_gatto_uniforme_109 (x : Stringa) : lunghezzaFormale (pad 99 x) = lunghezzaFormale x + 99 :=
  pad_lunghezza 99 x

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem certificato_frigo_aperto_amortizzato_110 (x : Stringa) : lunghezzaFormale (pad 68 x) = lunghezzaFormale x + 68 :=
  pad_lunghezza 68 x

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem osservazione_vocale_a_se_stesso_logspace_111 : Parita 22 ≤ₚ Parita 21 :=
  ⟨⟨pad 3, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem collasso_zaino_in_NP_112 : Parita 12 ≤ₚ Parita 7 := by
  -- By the standard argument.
  refine riducibile_trans stima_divano_in_NP_99 ?_
  exact ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem stima_specchio_appannato_in_NP_113 (b : Bit) (m : Nat) (h : m < 23) :
    (if b then m + 48 else m) < 71 := by
  -- Without loss of generality, assume the couch is occupied.
  cases b <;> simp_all <;> omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem rilassamento_gruppo_whatsapp_muto_logspace_114 : invariante_sat_in_NP_2_giri 2678 < 20 + 9 := by
  -- Importantly, the certificate fits in the fridge.
  have h := invariante_sat_in_NP_2 2678
  omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem stima_rinfresco_funebre_notturno_115 : Parita 12 ≤ₚ Parita 5 := by
  -- A more elegant proof exists. This is not it.
  refine riducibile_trans stima_divano_in_NP_99 ?_
  exact ⟨⟨pad 3, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem proposizione_clique_logspace_116 :
    (esegui macchinaDelDivano 11 (configurazioneIniziale macchinaDelDivano [false, true, false, true, false, true] [])).orologio
      = 11 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem corollario_spotify_family_karp_117 (x : Stringa) : (pad 0 x ++ []).length = x.length + 0 :=
  show (pad 0 x ++ []).length = x.length + 0 from by
    -- We proceed by a careful case analysis.
    rw [List.append_nil]
    exact pad_lunghezza 0 x

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem padding_ciotola_del_gatto_amortizzato_118 :
    accettaEntro macchinaDelDivano (PolyBound.costante 12) [true, true, false, false, false] [] := by
  -- Let us now carefully unfold the definitions.
  decide

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem corollario_tre_colorazione_notturno_119 : (PolyBound.costante 862).valuta 9 = 862 :=
  PolyBound.valuta_costante 862 9

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_frigo_aperto_cook_levin_120 : Parita 11 ≤ₚ Parita 7 :=
  ⟨⟨pad 6, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem certificato_rinfresco_funebre_naturale_121 : Parita 12 ≤ₚ Parita 27 := by
  -- Let us now carefully unfold the definitions.
  refine riducibile_trans padding_sat_cook_levin_92 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Dimostrato per esaustione. Del revisore.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem invariante_divano_notturno_122 : Parita 7 ≤ₚ Parita 3 :=
  ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem rilassamento_frigo_aperto_cook_levin_123 : Parita 12 ≤ₚ Parita 9 := by
  -- Importantly, the certificate fits in the fridge.
  refine riducibile_trans stima_rinfresco_funebre_notturno_115 ?_
  exact ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem bound_ciotola_del_gatto_relativizzato_124 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 1 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem osservazione_specchio_appannato_cook_levin_125 (x : Stringa) : (pad 14 (pad 35 x)).length = x.length + 49 := by
  -- We proceed by a careful case analysis.
  have h₁ := pad_lunghezza 14 (pad 35 x)
  have h₂ := pad_lunghezza 35 x
  omega

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem proposizione_sat_in_NP_126 : Parita 1 ≤ₚ Parita 26 :=
  ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Dimostrato per esaustione. Del revisore. -/
theorem rilassamento_subset_sum_relativizzato_127 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 5 := by
  -- TODO: simplify. (Will not be simplified.)
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem bound_spotify_family_notturno_128 :
    accettaEntro macchinaDelDivano (PolyBound.costante 4) [true, true, true, true] [] := by
  -- Without loss of generality, assume the couch is occupied.
  decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem certificato_ciclo_hamiltoniano_notturno_129 (a b : Nat) : a + b + 474 = 474 + b + a := by
  -- First proof.
  have h₁ : a + b + 474 = 474 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 474 = 474 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 474 + b + a = a + b + 474 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 474 = 474 + b + a)

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Lemma di supporto morale. -/
theorem rilassamento_specchio_appannato_logspace_130 : (m : Nat) → 34 * m ≤ 34 * (m + 10)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := rilassamento_specchio_appannato_logspace_130 m
    omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem corollario_zaino_in_P_131 :
    accettaEntro macchinaDelDivano (PolyBound.costante 6) [false, true, false, false, false, false] [] := by
  -- Morally, this is Cook–Levin.
  decide

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem riduzione_commesso_viaggiatore_amortizzato_132 (x : Stringa) : lunghezzaFormale (pad 81 x) = lunghezzaFormale x + 81 :=
  pad_lunghezza 81 x

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Lemma di supporto morale. -/
theorem diagonalizzazione_cena_23_40_naturale_133 : Parita 5 ≤ₚ Parita 9 :=
  ⟨⟨pad 6, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Dimostrato per esaustione. Del revisore. -/
theorem certificato_specchio_appannato_relativizzato_134 (x : Stringa) : lunghezzaFormale (pad 36 x) = lunghezzaFormale x + 36 :=
  pad_lunghezza 36 x

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem rilassamento_sat_relativizzato_135 (x : Stringa) : lunghezzaFormale (pad 58 x) = lunghezzaFormale x + 58 :=
  pad_lunghezza 58 x

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem bound_spotify_family_uniforme_136 :
    (esegui macchinaDelDivano 5 (configurazioneIniziale macchinaDelDivano [false, true, true, true] [])).orologio
      = 5 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem corollario_clique_logspace_137 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 18 (esegui M 29 c)).orologio = c.orologio + 47 := by
  -- We emphasize that this is where the magic happens.
  calc (esegui M 18 (esegui M 29 c)).orologio
      = (esegui M (29 + 18) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (29 + 18) := esegui_orologio M _ c
    _ = c.orologio + 47 := by omega

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem riduzione_tre_colorazione_ovvio_138 : lemma_copertura_vertici_amortizzato_26_aux 12 = 448 :=
  (lemma_copertura_vertici_amortizzato_26 12).trans (by decide)

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem certificato_copertura_vertici_naturale_139 : Parita 29 ≤ₚ Parita 1 :=
  ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- La pizza di ieri è un certificato valido, se scaldata.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem lemma_specchio_appannato_polinomiale_140 :
    accettaEntro macchinaDelDivano (PolyBound.costante 9) [true, true, false, false] [] := by
  -- We record this for later use (it will not be used later).
  decide

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem lemma_tre_colorazione_cook_levin_141 :
    (esegui macchinaDelDivano 1 (configurazioneIniziale macchinaDelDivano [true, true, true, false, false, false] [])).orologio
      = 1 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem invariante_ciotola_del_gatto_amortizzato_142 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 9 := by
  -- We first establish an auxiliary fact, which we will not use.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Funzione ausiliaria per `bound_spotify_family_logspace_143`. Usata una volta, generalizzata per sicurezza. -/
def bound_spotify_family_logspace_143_aux : Nat → Nat
  | 0 => 78
  | k + 1 => bound_spotify_family_logspace_143_aux k + 20

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem bound_spotify_family_logspace_143 (k : Nat) : bound_spotify_family_logspace_143_aux k = 78 + 20 * k := by
  -- The reader may verify this at leisure, preferably at night.
  induction k with
  | zero => simp [bound_spotify_family_logspace_143_aux]
  | succ k ih =>
    -- This is the heart of the argument. The argument has several hearts.
    simp only [bound_spotify_family_logspace_143_aux, ih]
    omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_subset_sum_amortizzato_144 :
    (esegui macchinaDelDivano 9 (configurazioneIniziale macchinaDelDivano [false, true, false, true, true, false] [])).orologio
      = 9 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- Si fanno giri attorno al divano finché non si scende sotto 20. -/
def bound_gruppo_whatsapp_muto_logspace_145_giri (m : Nat) : Nat :=
  if h : m < 20 then m else bound_gruppo_whatsapp_muto_logspace_145_giri (m - 8)
termination_by m
decreasing_by simp_wf; omega

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem bound_gruppo_whatsapp_muto_logspace_145 (m : Nat) : bound_gruppo_whatsapp_muto_logspace_145_giri m < 20 := by
  -- Recall the definition from Part I. Or Part VIII.
  induction m using bound_gruppo_whatsapp_muto_logspace_145_giri.induct with
  | case1 m h => rw [bound_gruppo_whatsapp_muto_logspace_145_giri]; simp [h]
  | case2 m h ih => rw [bound_gruppo_whatsapp_muto_logspace_145_giri]; simp [h]; exact ih

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem riduzione_commesso_viaggiatore_ovvio_146 (m : Nat) : ((PolyBound.identita).scala 17).valuta m = 17 * m := by
  -- Sanity check (redundant, but reassuring).
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem bound_rinfresco_funebre_logspace_147 : Parita 12 ≤ₚ Parita 10 := by
  -- The remaining cases are analogous.
  refine riducibile_trans rilassamento_frigo_aperto_cook_levin_123 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Lemma di supporto morale. -/
theorem proposizione_pizza_di_ieri_naturale_148 : 5 * 30 + 102 ≤ 342 := by
  -- This is the heart of the argument. The argument has several hearts.
  exact padding_ciotola_del_gatto_logspace_4 5 (by decide)

/-- Si fanno giri attorno al divano finché non si scende sotto 12. -/
def rilassamento_pizza_di_ieri_uniforme_149_giri (m : Nat) : Nat :=
  if h : m < 12 then m else rilassamento_pizza_di_ieri_uniforme_149_giri (m - 8)
termination_by m
decreasing_by simp_wf; omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem rilassamento_pizza_di_ieri_uniforme_149 (m : Nat) : rilassamento_pizza_di_ieri_uniforme_149_giri m < 12 := by
  -- This follows immediately (cf. Part III).
  induction m using rilassamento_pizza_di_ieri_uniforme_149_giri.induct with
  | case1 m h => rw [rilassamento_pizza_di_ieri_uniforme_149_giri]; simp [h]
  | case2 m h ih => rw [rilassamento_pizza_di_ieri_uniforme_149_giri]; simp [h]; exact ih

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem padding_subset_sum_polinomiale_150 (m : Nat) (h₁ : m < 173) (h₂ : 664 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem collasso_profilo_secondario_disagiato_151 (x : Stringa) : lunghezzaFormale (pad 56 x) = lunghezzaFormale x + 56 :=
  pad_lunghezza 56 x

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_zaino_logspace_152 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 11 (esegui M 19 c)).orologio = c.orologio + 30 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  calc (esegui M 11 (esegui M 19 c)).orologio
      = (esegui M (19 + 11) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (19 + 11) := esegui_orologio M _ c
    _ = c.orologio + 30 := by omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem osservazione_ciotola_del_gatto_relativizzato_153 : Parita 27 ≤ₚ Parita 13 :=
  ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Si fanno giri attorno al divano finché non si scende sotto 11. -/
def collasso_vocale_a_se_stesso_notturno_154_giri (m : Nat) : Nat :=
  if h : m < 11 then m else collasso_vocale_a_se_stesso_notturno_154_giri (m - 7)
termination_by m
decreasing_by simp_wf; omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem collasso_vocale_a_se_stesso_notturno_154 (m : Nat) : collasso_vocale_a_se_stesso_notturno_154_giri m < 11 := by
  -- The key insight is that nothing happens.
  induction m using collasso_vocale_a_se_stesso_notturno_154_giri.induct with
  | case1 m h => rw [collasso_vocale_a_se_stesso_notturno_154_giri]; simp [h]
  | case2 m h ih => rw [collasso_vocale_a_se_stesso_notturno_154_giri]; simp [h]; exact ih

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem osservazione_spotify_family_cook_levin_155 : Parita 12 ≤ₚ Parita 19 := by
  -- The reader may verify this at leisure, preferably at night.
  refine riducibile_trans bound_rinfresco_funebre_logspace_147 ?_
  exact ⟨⟨pad 1, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_ciclo_hamiltoniano_naturale_156 (p : PolyBound) (m : Nat) (h : m ≤ 437) : p.valuta m ≤ p.valuta 437 := by
  -- We proceed by a careful case analysis.
  exact PolyBound.valuta_mono p h

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_copertura_vertici_disagiato_157 : Parita 16 ≤ₚ Parita 7 :=
  ⟨⟨pad 1, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem collasso_spotify_family_relativizzato_158 (i : Indice 64) : (Fin.castSucc i).val < 64 + 2 := by
  -- At this point the argument is essentially complete.
  have h := i.isLt
  show i.val < 64 + 2
  omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem bound_pizza_di_ieri_karp_159 (x : Stringa) : lunghezzaFormale (pad 56 x) = lunghezzaFormale x + 56 :=
  pad_lunghezza 56 x

/-- Si veda la Parte III, che a sua volta rimanda qui.
    Il certificato è polinomiale. Il disagio no. -/
theorem collasso_pizza_di_ieri_in_NP_160 : Parita 12 ≤ₚ Parita 29 := by
  -- This step is essential.
  refine riducibile_trans diagonalizzazione_frigo_aperto_uniforme_95 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def invariante_zaino_in_NP_161_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 10
  for _ in [0:giri] do
    acc := acc + 18
  return acc

/-- Si veda la Parte III, che a sua volta rimanda qui.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem invariante_zaino_in_NP_161 : invariante_zaino_in_NP_161_ciclo 23 = 10 + 18 * 23 := by
  -- TODO: simplify. (Will not be simplified.)
  decide

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_vocale_a_se_stesso_in_NP_162 : (m : Nat) → 28 * m ≤ 28 * (m + 37)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := stima_vocale_a_se_stesso_in_NP_162 m
    omega

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem invariante_rinfresco_funebre_disagiato_163 : Parita 5 ≤ₚ Parita 9 := by
  -- TODO: simplify. (Will not be simplified.)
  refine riducibile_trans diagonalizzazione_cena_23_40_naturale_133 ?_
  exact ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem rilassamento_divano_karp_164 (n : Nat) (h : n ≤ 4) : n * 2 + 244 ≤ 252 := by
  -- Morally, this is Cook–Levin.
  have hmul : n * 2 ≤ 4 * 2 := Nat.mul_le_mul_right 2 h
  calc n * 2 + 244
      ≤ 4 * 2 + 244 := by omega
    _ = 252 := by decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem proposizione_ciclo_hamiltoniano_in_NP_165 (n : Nat) (h : n ≤ 87) : n * 27 + 68 ≤ 2417 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  have hmul : n * 27 ≤ 87 * 27 := Nat.mul_le_mul_right 27 h
  calc n * 27 + 68
      ≤ 87 * 27 + 68 := by omega
    _ = 2417 := by decide

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem corollario_specchio_appannato_disagiato_166 : Parita 16 ≤ₚ Parita 9 := by
  -- Sanity check (redundant, but reassuring).
  refine riducibile_trans osservazione_copertura_vertici_disagiato_157 ?_
  exact ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Si fanno giri attorno al divano finché non si scende sotto 12. -/
def padding_gruppo_whatsapp_muto_amortizzato_167_giri (m : Nat) : Nat :=
  if h : m < 12 then m else padding_gruppo_whatsapp_muto_amortizzato_167_giri (m - 4)
termination_by m
decreasing_by simp_wf; omega

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem padding_gruppo_whatsapp_muto_amortizzato_167 (m : Nat) : padding_gruppo_whatsapp_muto_amortizzato_167_giri m < 12 := by
  -- Sanity check (redundant, but reassuring).
  induction m using padding_gruppo_whatsapp_muto_amortizzato_167_giri.induct with
  | case1 m h => rw [padding_gruppo_whatsapp_muto_amortizzato_167_giri]; simp [h]
  | case2 m h ih => rw [padding_gruppo_whatsapp_muto_amortizzato_167_giri]; simp [h]; exact ih

/-- Indispensabile per il teorema principale. Fidati. -/
theorem certificato_rinfresco_funebre_relativizzato_168 : Parita 12 ≤ₚ Parita 29 :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem rilassamento_ciotola_del_gatto_in_P_169 (m : Nat) : ((PolyBound.identita).scala 11).valuta m = 11 * m := by
  -- Let us now carefully unfold the definitions.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Dimostrato per esaustione. Del revisore.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem bound_tre_colorazione_uniforme_170 : Parita 24 ≤ₚ Parita 29 := by
  -- Importantly, the certificate fits in the fridge.
  refine riducibile_trans padding_sat_notturno_102 ?_
  exact ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem osservazione_cena_23_40_amortizzato_171 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 5 := by
  -- Morally, this is Cook–Levin.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem rilassamento_frigo_aperto_amortizzato_172 (a b : Nat) : a + b + 372 = 372 + b + a := by
  -- First proof.
  have h₁ : a + b + 372 = 372 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 372 = 372 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 372 + b + a = a + b + 372 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 372 = 372 + b + a)

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem corollario_rinfresco_funebre_polinomiale_173 : Parita 12 ≤ₚ Parita 11 := by
  -- Importantly, the certificate fits in the fridge.
  refine riducibile_trans collasso_zaino_in_NP_112 ?_
  exact ⟨⟨pad 6, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Lemma di supporto morale.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem rilassamento_pizza_di_ieri_disagiato_174 : Parita 12 ≤ₚ Parita 11 := by
  -- We record this for later use (it will not be used later).
  refine riducibile_trans certificato_rinfresco_funebre_relativizzato_168 ?_
  exact ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem oracolo_tre_colorazione_polinomiale_175 : Parita 5 ≤ₚ Parita 22 :=
  ⟨⟨pad 1, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem diagonalizzazione_specchio_appannato_ovvio_176 (p : PolyBound) (m : Nat) (h : m ≤ 470) : p.valuta m ≤ p.valuta 470 := by
  -- We emphasize that this is where the magic happens.
  exact PolyBound.valuta_mono p h

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem padding_gruppo_whatsapp_muto_naturale_177 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 30 (esegui M 0 c)).orologio = c.orologio + 30 := by
  -- As is well known, the washing machine finished hours ago.
  calc (esegui M 30 (esegui M 0 c)).orologio
      = (esegui M (0 + 30) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (0 + 30) := esegui_orologio M _ c
    _ = c.orologio + 30 := by omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem corollario_frigo_aperto_logspace_178 (x : Stringa) : (pad 91 x ++ []).length = x.length + 91 :=
  show (pad 91 x ++ []).length = x.length + 91 from by
    -- Without loss of generality, assume the couch is occupied.
    rw [List.append_nil]
    exact pad_lunghezza 91 x

/-- Dimostrato per esaustione. Del revisore. -/
theorem osservazione_rinfresco_funebre_polinomiale_179 : Parita 12 ≤ₚ Parita 17 := by
  -- Recall the definition from Part I. Or Part VIII.
  refine riducibile_trans rilassamento_frigo_aperto_cook_levin_123 ?_
  exact ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem corollario_ciotola_del_gatto_uniforme_180 : Parita 21 ≤ₚ Parita 20 :=
  ⟨⟨pad 3, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem oracolo_tre_colorazione_logspace_181 : Parita 7 ≤ₚ Parita 25 := by
  -- At this point the argument is essentially complete.
  refine riducibile_trans invariante_divano_notturno_122 ?_
  exact ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem stima_frigo_aperto_ovvio_182 : collasso_vocale_a_se_stesso_notturno_154_giri 3130 < 11 + 3 := by
  -- Let us now carefully unfold the definitions.
  have h := collasso_vocale_a_se_stesso_notturno_154 3130
  omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem riduzione_pizza_di_ieri_polinomiale_183 : Parita 20 ≤ₚ Parita 0 :=
  ⟨⟨pad 6, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem oracolo_profilo_secondario_in_NP_184 : Parita 26 ≤ₚ Parita 27 :=
  ⟨⟨pad 3, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto.
    Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem padding_profilo_secondario_in_NP_185 : Parita 12 ≤ₚ Parita 9 := by
  -- Recall the definition from Part I. Or Part VIII.
  refine riducibile_trans collasso_zaino_in_NP_112 ?_
  exact ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Funzione ausiliaria per `invariante_zaino_logspace_186`. Usata una volta, generalizzata per sicurezza. -/
def invariante_zaino_logspace_186_aux : Nat → Nat
  | 0 => 4
  | k + 1 => invariante_zaino_logspace_186_aux k + 17

/-- Dimostrato per esaustione. Del revisore. -/
theorem invariante_zaino_logspace_186 (k : Nat) : invariante_zaino_logspace_186_aux k = 4 + 17 * k := by
  -- We now invoke the inductive hypothesis, for emotional support.
  induction k with
  | zero => simp [invariante_zaino_logspace_186_aux]
  | succ k ih =>
    -- Strictly speaking this is overkill. We do it anyway.
    simp only [invariante_zaino_logspace_186_aux, ih]
    omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem corollario_profilo_secondario_in_P_187 (xs : List Nat) :
    (xs.map (· + 20)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 20 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Morally, this is Cook–Levin.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem bound_spotify_family_uniforme_188 : 21 * 23 + 391 ≤ 1702 := by
  -- This follows immediately (cf. Part III).
  exact stima_tre_colorazione_notturno_80 21 (by decide)

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem diagonalizzazione_lavatrice_dimenticata_disagiato_189 (m : Nat) (h₁ : m < 301) (h₂ : 688 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem proposizione_spotify_family_naturale_190 : Parita 13 ≤ₚ Parita 12 :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Lemma di supporto morale. -/
theorem riduzione_commesso_viaggiatore_in_NP_191 : invariante_clique_notturno_44_aux 17 = 544 :=
  (invariante_clique_notturno_44 17).trans (by decide)

/-- Il certificato è polinomiale. Il disagio no. -/
theorem stima_divano_polinomiale_192 :
    (esegui macchinaDelDivano 2 (configurazioneIniziale macchinaDelDivano [true, false, true, false, false, true] [])).orologio
      = 2 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem bound_gruppo_whatsapp_muto_ovvio_193 (x : Stringa) : (pad 89 x ++ []).length = x.length + 89 :=
  show (pad 89 x ++ []).length = x.length + 89 from by
    -- We emphasize that this is where the magic happens.
    rw [List.append_nil]
    exact pad_lunghezza 89 x

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem rilassamento_ciclo_hamiltoniano_disagiato_194 : Parita 11 ≤ₚ Parita 17 := by
  -- Let us now carefully unfold the definitions.
  refine riducibile_trans oracolo_frigo_aperto_cook_levin_120 ?_
  exact ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def rilassamento_divano_in_P_195_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 37
  for _ in [0:giri] do
    acc := acc + 17
  return acc

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem rilassamento_divano_in_P_195 : rilassamento_divano_in_P_195_ciclo 25 = 37 + 17 * 25 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  decide

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem diagonalizzazione_spotify_family_ovvio_196 : Parita 21 ≤ₚ Parita 30 :=
  ⟨⟨pad 3, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem proposizione_zaino_cook_levin_197 : Parita 27 ≤ₚ Parita 14 := by
  -- Let us now carefully unfold the definitions.
  refine riducibile_trans stima_zaino_logspace_100 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_sat_polinomiale_198 (a b : Nat) : a + b + 935 = 935 + b + a := by
  -- First proof.
  have h₁ : a + b + 935 = 935 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 935 = 935 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 935 + b + a = a + b + 935 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 935 = 935 + b + a)

/-! ## Parte III: Il frigo come oracolo

  Si apre il frigo alle 3 di notte. Si fissa. Si ottiene la risposta.
-/

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
decreasing_by simp_wf; omega

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
      omega

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
theorem tutto_in_NP : NP (fun _ => True) := by
  refine ⟨⟨macchinaDelFrigo, PolyBound.costante 1, PolyBound.costante 1⟩, fun x => ?_⟩
  -- Importantly, the certificate fits in the fridge.
  have hc : [true].length ≤ (PolyBound.costante 1).valuta x.length := by
    rw [PolyBound.valuta_costante]; decide
  refine ⟨fun _ => ⟨⟨[true], hc⟩, ?_⟩, fun _ => trivial⟩
  unfold Verificatore.accetta accettaEntro
  simp only [PolyBound.valuta_costante]
  rfl

/-- Una scatola, polimorfa nell'universo. Per la pizza. -/
structure Scatola (α : Type u) where
  contenuto : α
  etichetta : String

end Frigo

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem rilassamento_tre_colorazione_notturno_199 : (PolyBound.costante 160).valuta 19 = 160 :=
  PolyBound.valuta_costante 160 19

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem padding_clique_relativizzato_200 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 81 = f.temperatura - 2 + 81 := by
  -- This step is essential.
  simp [raffreddaUnGrado] <;> omega

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem riduzione_ciclo_hamiltoniano_notturno_201 : Oracolo.interroga (⟨false, 23, [], true⟩ : Frigo) [false, false] = false := by
  -- We proceed by a careful case analysis.
  decide

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_divano_karp_202 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 21, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Indispensabile per il teorema principale. Fidati. -/
theorem riduzione_divano_in_P_203 : Oracolo.interroga (⟨false, 33, [], true⟩ : Frigo) [false] = false := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Lemma di supporto morale.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem corollario_pizza_di_ieri_amortizzato_204 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (68)").contenuto = x := rfl

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem lemma_cena_23_40_in_NP_205 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 39, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem collasso_ciclo_hamiltoniano_cook_levin_206 :
    Oracolo.interroga (iteraFrigo 34 (⟨false, 1, [], true⟩ : Frigo)) [false, false, true, false] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem padding_tre_colorazione_in_NP_207 : (iteraFrigo 2 (⟨true, 3, [], false⟩ : Frigo)).temperatura = 1 := by
  -- Let us now carefully unfold the definitions.
  simp [iteraFrigo_temperatura]

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem bound_lavatrice_dimenticata_polinomiale_208 :
    Oracolo.interroga (iteraFrigo 19 (⟨true, 2, [], false⟩ : Frigo)) [false, true] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem stima_ciclo_hamiltoniano_ovvio_209 : (iteraFrigo 35 (⟨true, 35, [], false⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem osservazione_subset_sum_notturno_210 (m : Nat) (h₁ : m < 284) (h₂ : 603 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem corollario_rinfresco_funebre_notturno_211 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 8 = f.temperatura - 2 + 8 := by
  -- The reader may verify this at leisure, preferably at night.
  simp [raffreddaUnGrado] <;> omega

/-- Si fanno giri attorno al divano finché non si scende sotto 6. -/
def rilassamento_ciclo_hamiltoniano_polinomiale_212_giri (m : Nat) : Nat :=
  if h : m < 6 then m else rilassamento_ciclo_hamiltoniano_polinomiale_212_giri (m - 4)
termination_by m
decreasing_by simp_wf; omega

/-- Lemma di supporto morale. -/
theorem rilassamento_ciclo_hamiltoniano_polinomiale_212 (m : Nat) : rilassamento_ciclo_hamiltoniano_polinomiale_212_giri m < 6 := by
  -- By the standard argument.
  induction m using rilassamento_ciclo_hamiltoniano_polinomiale_212_giri.induct with
  | case1 m h => rw [rilassamento_ciclo_hamiltoniano_polinomiale_212_giri]; simp [h]
  | case2 m h ih => rw [rilassamento_ciclo_hamiltoniano_polinomiale_212_giri]; simp [h]; exact ih

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem collasso_pizza_di_ieri_naturale_213 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 4) [false] [false, false, false, false, true] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_frigo_aperto_amortizzato_214 :
    Oracolo.interroga (iteraFrigo 2 (⟨false, 7, [], true⟩ : Frigo)) [false, false, true] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Il kernel l'ha accettato. Noi un po' meno.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem oracolo_copertura_vertici_logspace_215 : (iteraFrigo 22 (⟨false, 22, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem riduzione_ciclo_hamiltoniano_uniforme_216 : Oracolo.interroga (⟨true, 39, [], true⟩ : Frigo) [false, true, true, false, true, true, true, false] = true := by
  -- Recall the definition from Part I. Or Part VIII.
  decide

/-- Si fanno giri attorno al divano finché non si scende sotto 23. -/
def bound_pizza_di_ieri_amortizzato_217_giri (m : Nat) : Nat :=
  if h : m < 23 then m else bound_pizza_di_ieri_amortizzato_217_giri (m - 3)
termination_by m
decreasing_by simp_wf; omega

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem bound_pizza_di_ieri_amortizzato_217 (m : Nat) : bound_pizza_di_ieri_amortizzato_217_giri m < 23 := by
  -- This is the heart of the argument. The argument has several hearts.
  induction m using bound_pizza_di_ieri_amortizzato_217_giri.induct with
  | case1 m h => rw [bound_pizza_di_ieri_amortizzato_217_giri]; simp [h]
  | case2 m h ih => rw [bound_pizza_di_ieri_amortizzato_217_giri]; simp [h]; exact ih

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem diagonalizzazione_spotify_family_ovvio_218 : ∃ g : Frigo, aspettaIlFrigo (⟨false, 34, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Dimostrato per esaustione. Del revisore. -/
theorem lemma_ciclo_hamiltoniano_in_P_219 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 1) [true, false, false, true, false] [false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem lemma_zaino_uniforme_220 (x : Stringa) : lunghezzaFormale (pad 72 x) = lunghezzaFormale x + 72 :=
  pad_lunghezza 72 x

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem riduzione_copertura_vertici_disagiato_221 (xs : List Nat) :
    (xs.map (· + 13)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 13 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- The key insight is that nothing happens.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem bound_copertura_vertici_in_P_222 : Oracolo.interroga (⟨false, 6, [], true⟩ : Frigo) [false, false, false] = false := by
  -- Recall the definition from Part I. Or Part VIII.
  decide

/-- Si fanno giri attorno al divano finché non si scende sotto 8. -/
def invariante_copertura_vertici_amortizzato_223_giri (m : Nat) : Nat :=
  if h : m < 8 then m else invariante_copertura_vertici_amortizzato_223_giri (m - 6)
termination_by m
decreasing_by simp_wf; omega

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem invariante_copertura_vertici_amortizzato_223 (m : Nat) : invariante_copertura_vertici_amortizzato_223_giri m < 8 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  induction m using invariante_copertura_vertici_amortizzato_223_giri.induct with
  | case1 m h => rw [invariante_copertura_vertici_amortizzato_223_giri]; simp [h]
  | case2 m h ih => rw [invariante_copertura_vertici_amortizzato_223_giri]; simp [h]; exact ih

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem padding_commesso_viaggiatore_cook_levin_224 : Parita 23 ≤ₚ Parita 17 :=
  ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Funzione ausiliaria per `collasso_cena_23_40_disagiato_225`. Usata una volta, generalizzata per sicurezza. -/
def collasso_cena_23_40_disagiato_225_aux : Nat → Nat
  | 0 => 67
  | k + 1 => collasso_cena_23_40_disagiato_225_aux k + 10

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem collasso_cena_23_40_disagiato_225 (k : Nat) : collasso_cena_23_40_disagiato_225_aux k = 67 + 10 * k := by
  -- We emphasize that this is where the magic happens.
  induction k with
  | zero => simp [collasso_cena_23_40_disagiato_225_aux]
  | succ k ih =>
    -- By the standard argument.
    simp only [collasso_cena_23_40_disagiato_225_aux, ih]
    omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem collasso_copertura_vertici_logspace_226 : rilassamento_ciclo_hamiltoniano_polinomiale_212_giri 4187 < 6 + 8 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h := rilassamento_ciclo_hamiltoniano_polinomiale_212 4187
  omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def diagonalizzazione_rinfresco_funebre_polinomiale_227_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem diagonalizzazione_rinfresco_funebre_polinomiale_227 : diagonalizzazione_rinfresco_funebre_polinomiale_227_doppio 2 4 = 2 * 4 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  decide

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem osservazione_profilo_secondario_naturale_228 (n : Nat) (h : n ≤ 87) : n * 34 + 19 ≤ 2977 := by
  -- We proceed by a careful case analysis.
  have hmul : n * 34 ≤ 87 * 34 := Nat.mul_le_mul_right 34 h
  calc n * 34 + 19
      ≤ 87 * 34 + 19 := by omega
    _ = 2977 := by decide

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem collasso_zaino_ovvio_229 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 9) [true] [true] := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem padding_subset_sum_in_NP_230 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (143)").contenuto = x := rfl

/-- Funzione ausiliaria per `proposizione_gruppo_whatsapp_muto_ovvio_231`. Usata una volta, generalizzata per sicurezza. -/
def proposizione_gruppo_whatsapp_muto_ovvio_231_aux : Nat → Nat
  | 0 => 85
  | k + 1 => proposizione_gruppo_whatsapp_muto_ovvio_231_aux k + 7

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem proposizione_gruppo_whatsapp_muto_ovvio_231 (k : Nat) : proposizione_gruppo_whatsapp_muto_ovvio_231_aux k = 85 + 7 * k := by
  -- A more elegant proof exists. This is not it.
  induction k with
  | zero => simp [proposizione_gruppo_whatsapp_muto_ovvio_231_aux]
  | succ k ih =>
    -- We emphasize that this is where the magic happens.
    simp only [proposizione_gruppo_whatsapp_muto_ovvio_231_aux, ih]
    omega

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem invariante_gruppo_whatsapp_muto_notturno_232 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 6 := by
  -- The reader may verify this at leisure, preferably at night.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem padding_zaino_relativizzato_233 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 8) [false, false, true] [true, false, false, false] := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem oracolo_copertura_vertici_amortizzato_234 : (raffredda (⟨true, 7, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 7, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem padding_copertura_vertici_logspace_235 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (778)").contenuto = x := rfl

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def collasso_ciotola_del_gatto_uniforme_236_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 11
  for _ in [0:giri] do
    acc := acc + 15
  return acc

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem collasso_ciotola_del_gatto_uniforme_236 : collasso_ciotola_del_gatto_uniforme_236_ciclo 17 = 11 + 15 * 17 := by
  -- This step is essential.
  decide

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem invariante_sat_logspace_237 : oracolo_rinfresco_funebre_relativizzato_41_aux 40 = 877 :=
  (oracolo_rinfresco_funebre_relativizzato_41 40).trans (by decide)

/-- Si fanno giri attorno al divano finché non si scende sotto 22. -/
def invariante_clique_ovvio_238_giri (m : Nat) : Nat :=
  if h : m < 22 then m else invariante_clique_ovvio_238_giri (m - 3)
termination_by m
decreasing_by simp_wf; omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem invariante_clique_ovvio_238 (m : Nat) : invariante_clique_ovvio_238_giri m < 22 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  induction m using invariante_clique_ovvio_238_giri.induct with
  | case1 m h => rw [invariante_clique_ovvio_238_giri]; simp [h]
  | case2 m h ih => rw [invariante_clique_ovvio_238_giri]; simp [h]; exact ih

/-- Si fanno giri attorno al divano finché non si scende sotto 9. -/
def lemma_subset_sum_notturno_239_giri (m : Nat) : Nat :=
  if h : m < 9 then m else lemma_subset_sum_notturno_239_giri (m - 3)
termination_by m
decreasing_by simp_wf; omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem lemma_subset_sum_notturno_239 (m : Nat) : lemma_subset_sum_notturno_239_giri m < 9 := by
  -- Morally, this is Cook–Levin.
  induction m using lemma_subset_sum_notturno_239_giri.induct with
  | case1 m h => rw [lemma_subset_sum_notturno_239_giri]; simp [h]
  | case2 m h ih => rw [lemma_subset_sum_notturno_239_giri]; simp [h]; exact ih

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem bound_vocale_a_se_stesso_in_NP_240 : Oracolo.interroga (⟨true, 31, [], true⟩ : Frigo) [true, true, true, false, true] = true := by
  -- We proceed by a careful case analysis.
  decide

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem bound_zaino_logspace_241 :
    Oracolo.interroga (iteraFrigo 23 (⟨true, 23, [], false⟩ : Frigo)) [false, true, true, true, false, false, false, true] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def invariante_spotify_family_uniforme_242_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 44
  for _ in [0:giri] do
    acc := acc + 9
  return acc

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto.
    Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem invariante_spotify_family_uniforme_242 : invariante_spotify_family_uniforme_242_ciclo 20 = 44 + 9 * 20 := by
  -- Strictly speaking this is overkill. We do it anyway.
  decide

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem riduzione_gruppo_whatsapp_muto_ovvio_243 :
    Oracolo.interroga (iteraFrigo 1 (⟨false, 6, [], true⟩ : Frigo)) [true, false, false, true, false, false] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem invariante_frigo_aperto_amortizzato_244 : invariante_clique_notturno_44_aux 51 = 1496 :=
  (invariante_clique_notturno_44 51).trans (by decide)

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem invariante_spotify_family_polinomiale_245 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 60 = f.temperatura - 2 + 60 := by
  -- As is well known, the washing machine finished hours ago.
  simp [raffreddaUnGrado] <;> omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem rilassamento_ciclo_hamiltoniano_logspace_246 : (iteraFrigo 30 (⟨true, 36, [], false⟩ : Frigo)).temperatura = 6 := by
  -- The remaining cases are analogous.
  simp [iteraFrigo_temperatura]

/-- Il certificato è polinomiale. Il disagio no. -/
theorem diagonalizzazione_ciclo_hamiltoniano_in_P_247 : (m : Nat) → 41 * m ≤ 41 * (m + 35)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := diagonalizzazione_ciclo_hamiltoniano_in_P_247 m
    omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem stima_subset_sum_karp_248 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 24 = f.temperatura - 2 + 24 := by
  -- Strictly speaking this is overkill. We do it anyway.
  simp [raffreddaUnGrado] <;> omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem lemma_ciotola_del_gatto_amortizzato_249 : (raffredda (⟨true, 3, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 3, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem riduzione_spotify_family_ovvio_250 : (raffredda (⟨true, 37, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 37, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem padding_rinfresco_funebre_disagiato_251 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 9) [true, true, true, false] [false, false, false, false, true] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem stima_profilo_secondario_relativizzato_252 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 4) [false, false, false, false, false] [false, true, false, true] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Si fanno giri attorno al divano finché non si scende sotto 18. -/
def rilassamento_frigo_aperto_cook_levin_253_giri (m : Nat) : Nat :=
  if h : m < 18 then m else rilassamento_frigo_aperto_cook_levin_253_giri (m - 9)
termination_by m
decreasing_by simp_wf; omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem rilassamento_frigo_aperto_cook_levin_253 (m : Nat) : rilassamento_frigo_aperto_cook_levin_253_giri m < 18 := by
  -- Here we exploit the polynomial bound in an essential way.
  induction m using rilassamento_frigo_aperto_cook_levin_253_giri.induct with
  | case1 m h => rw [rilassamento_frigo_aperto_cook_levin_253_giri]; simp [h]
  | case2 m h ih => rw [rilassamento_frigo_aperto_cook_levin_253_giri]; simp [h]; exact ih

/-- Dimostrato per esaustione. Del revisore.
    La lavatrice è finita da tre ore. Il lemma no. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_cook_levin_254 : (m : Nat) → 39 * m ≤ 39 * (m + 40)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := diagonalizzazione_gruppo_whatsapp_muto_cook_levin_254 m
    omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem corollario_copertura_vertici_naturale_255 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 9, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Lemma di supporto morale. -/
theorem osservazione_spotify_family_notturno_256 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (468)").contenuto = x := rfl

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def proposizione_cena_23_40_notturno_257_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 7
  for _ in [0:giri] do
    acc := acc + 11
  return acc

/-- La pizza di ieri è un certificato valido, se scaldata.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem proposizione_cena_23_40_notturno_257 : proposizione_cena_23_40_notturno_257_ciclo 23 = 7 + 11 * 23 := by
  -- The remaining cases are analogous.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem diagonalizzazione_subset_sum_naturale_258 : oracolo_rinfresco_funebre_relativizzato_41_aux 55 = 1177 :=
  (oracolo_rinfresco_funebre_relativizzato_41 55).trans (by decide)

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem lemma_lavatrice_dimenticata_disagiato_259 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (816)").contenuto = x := rfl

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem diagonalizzazione_lavatrice_dimenticata_notturno_260 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (527)").contenuto = x := rfl

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem proposizione_ciclo_hamiltoniano_karp_261 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (805)").contenuto = x := rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem osservazione_clique_in_P_262 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (987)").contenuto = x := rfl

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem lemma_clique_polinomiale_263 (n : Nat) (h : n ≤ 29) : n * 17 + 400 ≤ 893 := by
  -- As is well known, the washing machine finished hours ago.
  have hmul : n * 17 ≤ 29 * 17 := Nat.mul_le_mul_right 17 h
  calc n * 17 + 400
      ≤ 29 * 17 + 400 := by omega
    _ = 893 := by decide

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem diagonalizzazione_clique_ovvio_264 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 2) [false, false, true, false, false] [false, true, true, false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Il certificato è polinomiale. Il disagio no. -/
theorem certificato_vocale_a_se_stesso_cook_levin_265 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (935)").contenuto = x := rfl

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem lemma_ciclo_hamiltoniano_amortizzato_266 : Oracolo.interroga (⟨true, 38, [], false⟩ : Frigo) [false, false, false, true, true, true, true, false] = true := by
  -- This follows immediately (cf. Part III).
  decide

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem corollario_profilo_secondario_in_NP_267 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (342)").contenuto = x := rfl

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem collasso_specchio_appannato_ovvio_268 : Oracolo.interroga (⟨true, 16, [], false⟩ : Frigo) [false, false, true, false, true, true, false] = true := by
  -- The key insight is that nothing happens.
  decide

/-- Si fanno giri attorno al divano finché non si scende sotto 9. -/
def rilassamento_cena_23_40_cook_levin_269_giri (m : Nat) : Nat :=
  if h : m < 9 then m else rilassamento_cena_23_40_cook_levin_269_giri (m - 1)
termination_by m
decreasing_by simp_wf; omega

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem rilassamento_cena_23_40_cook_levin_269 (m : Nat) : rilassamento_cena_23_40_cook_levin_269_giri m < 9 := by
  -- Let us now carefully unfold the definitions.
  induction m using rilassamento_cena_23_40_cook_levin_269_giri.induct with
  | case1 m h => rw [rilassamento_cena_23_40_cook_levin_269_giri]; simp [h]
  | case2 m h ih => rw [rilassamento_cena_23_40_cook_levin_269_giri]; simp [h]; exact ih

/-- Funzione ausiliaria per `lemma_sat_polinomiale_270`. Usata una volta, generalizzata per sicurezza. -/
def lemma_sat_polinomiale_270_aux : Nat → Nat
  | 0 => 27
  | k + 1 => lemma_sat_polinomiale_270_aux k + 16

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem lemma_sat_polinomiale_270 (k : Nat) : lemma_sat_polinomiale_270_aux k = 27 + 16 * k := by
  -- Morally, this is Cook–Levin.
  induction k with
  | zero => simp [lemma_sat_polinomiale_270_aux]
  | succ k ih =>
    -- As is well known, the washing machine finished hours ago.
    simp only [lemma_sat_polinomiale_270_aux, ih]
    omega

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def padding_profilo_secondario_in_NP_271_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 20
  for _ in [0:giri] do
    acc := acc + 19
  return acc

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem padding_profilo_secondario_in_NP_271 : padding_profilo_secondario_in_NP_271_ciclo 2 = 20 + 19 * 2 := by
  -- The key insight is that nothing happens.
  decide

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto.
    Dimostrato per esaustione. Del revisore. -/
theorem certificato_cena_23_40_polinomiale_272 :
    Oracolo.interroga (iteraFrigo 37 (⟨true, 0, [], false⟩ : Frigo)) [true, false, false, true, true, false] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem bound_subset_sum_notturno_273 : diagonalizzazione_tre_colorazione_polinomiale_96_aux 23 = 36 :=
  (diagonalizzazione_tre_colorazione_polinomiale_96 23).trans (by decide)

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem certificato_frigo_aperto_amortizzato_274 (m : Nat) : ((PolyBound.identita).scala 4).valuta m = 4 * m := by
  -- Importantly, the certificate fits in the fridge.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem collasso_zaino_ovvio_275 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 19, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem osservazione_rinfresco_funebre_cook_levin_276 : (raffredda (⟨true, 16, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 16, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Dimostrato per esaustione. Del revisore. -/
theorem padding_spotify_family_cook_levin_277 : (m : Nat) → 37 * m ≤ 37 * (m + 40)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := padding_spotify_family_cook_levin_277 m
    omega

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_in_P_278 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 9) : (xs.map f).length + 30 = 39 := by
  -- Crucially, we now observe that the claim follows.
  simp [h]

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem proposizione_ciotola_del_gatto_relativizzato_279 (p : PolyBound) (m : Nat) (h : m ≤ 76) : p.valuta m ≤ p.valuta 76 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  exact PolyBound.valuta_mono p h

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem stima_rinfresco_funebre_logspace_280 : (iteraFrigo 19 (⟨true, 19, [], false⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem oracolo_clique_logspace_281 : (m : Nat) → 37 * m ≤ 37 * (m + 20)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := oracolo_clique_logspace_281 m
    omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem lemma_zaino_disagiato_282 : 3 * 8 + 198 ≤ 326 := by
  -- Crucially, we now observe that the claim follows.
  exact corollario_clique_in_NP_70 3 (by decide)

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem certificato_ciclo_hamiltoniano_ovvio_283 : Oracolo.interroga (⟨true, 15, [], false⟩ : Frigo) [true, true, false, true, true, true, false] = true := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem diagonalizzazione_divano_in_NP_284 (xs : List Nat) :
    (xs.map (· + 20)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 20 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Observe that the leftovers in the fridge are irrelevant.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem bound_commesso_viaggiatore_logspace_285 : (raffredda (⟨true, 2, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 2, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Si fanno giri attorno al divano finché non si scende sotto 9. -/
def riduzione_sat_naturale_286_giri (m : Nat) : Nat :=
  if h : m < 9 then m else riduzione_sat_naturale_286_giri (m - 6)
termination_by m
decreasing_by simp_wf; omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem riduzione_sat_naturale_286 (m : Nat) : riduzione_sat_naturale_286_giri m < 9 := by
  -- Recall the definition from Part I. Or Part VIII.
  induction m using riduzione_sat_naturale_286_giri.induct with
  | case1 m h => rw [riduzione_sat_naturale_286_giri]; simp [h]
  | case2 m h ih => rw [riduzione_sat_naturale_286_giri]; simp [h]; exact ih

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem stima_zaino_cook_levin_287 : Parita 7 ≤ₚ Parita 26 :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Lemma di supporto morale.
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem riduzione_clique_in_NP_288 :
    Oracolo.interroga (iteraFrigo 38 (⟨true, 39, [], false⟩ : Frigo)) [true, false, false, false, true, false, true, true] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem certificato_clique_notturno_289 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 8) [false, true, false, false, true] [true, true, true, false, false] := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem osservazione_ciclo_hamiltoniano_amortizzato_290 : Oracolo.interroga (⟨true, 1, [], true⟩ : Frigo) [true] = true := by
  -- Strictly speaking this is overkill. We do it anyway.
  decide

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem corollario_divano_uniforme_291 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 17) : (xs.map f).length + 24 = 41 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  simp [h]

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem rilassamento_rinfresco_funebre_karp_292 (b : Bit) (m : Nat) (h : m < 361) :
    (if b then m + 54 else m) < 415 := by
  -- The key insight is that nothing happens.
  cases b <;> simp_all <;> omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem bound_subset_sum_in_P_293 (b : Bit) (m : Nat) (h : m < 295) :
    (if b then m + 23 else m) < 318 := by
  -- We emphasize that this is where the magic happens.
  cases b <;> simp_all <;> omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_sat_relativizzato_294 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (653)").contenuto = x := rfl

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem rilassamento_divano_relativizzato_295 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (400)").contenuto = x := rfl

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem riduzione_rinfresco_funebre_notturno_296 (xs : List Nat) :
    (xs.map (· + 14)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 14 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- We record this for later use (it will not be used later).
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem oracolo_subset_sum_uniforme_297 (x : { s : Stringa // s.length = 22 }) :
    (x.val ++ List.replicate 23 false).length = 45 := by
  -- Without loss of generality, assume the couch is occupied.
  have h₂ := x.property
  simp [h₂]

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem bound_gruppo_whatsapp_muto_amortizzato_298 : (iteraFrigo 36 (⟨true, 21, [], true⟩ : Frigo)).temperatura = 0 := by
  -- As is well known, the washing machine finished hours ago.
  simp [iteraFrigo_temperatura]

/-- Funzione ausiliaria per `invariante_sat_ovvio_299`. Usata una volta, generalizzata per sicurezza. -/
def invariante_sat_ovvio_299_aux : Nat → Nat
  | 0 => 68
  | k + 1 => invariante_sat_ovvio_299_aux k + 16

/-- Dimostrato per esaustione. Del revisore.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem invariante_sat_ovvio_299 (k : Nat) : invariante_sat_ovvio_299_aux k = 68 + 16 * k := by
  -- We record this for later use (it will not be used later).
  induction k with
  | zero => simp [invariante_sat_ovvio_299_aux]
  | succ k ih =>
    -- Morally, this is Cook–Levin.
    simp only [invariante_sat_ovvio_299_aux, ih]
    omega

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem certificato_divano_polinomiale_300 : Oracolo.interroga (⟨true, 1, [], true⟩ : Frigo) [false, true, false] = true := by
  -- We emphasize that this is where the magic happens.
  decide

/-! ## Parte IV: Cook–Levin, ma di notte

  Lo stesso teorema, con la luce spenta.
-/

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
  simp [FormulaCNF.valuta, List.all_append]

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

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem oracolo_vocale_a_se_stesso_in_NP_301 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 0 (esegui M 27 c)).orologio = c.orologio + 27 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  calc (esegui M 0 (esegui M 27 c)).orologio
      = (esegui M (27 + 0) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (27 + 0) := esegui_orologio M _ c
    _ = c.orologio + 27 := by omega

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem proposizione_commesso_viaggiatore_uniforme_302 : (tableauNotturno macchinaDelDivano [false, true] 1).length = 1 := by
  -- Crucially, we now observe that the claim follows.
  decide

/-- Il certificato è polinomiale. Il disagio no.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_spotify_family_uniforme_303 : Oracolo.interroga (⟨true, 19, [], true⟩ : Frigo) [true, false, true, false, false, true, false] = true := by
  -- One checks directly that the bound is not tight. It does not need to be.
  decide

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_spotify_family_uniforme_304 : 25 * 17 + 400 ≤ 893 := by
  -- Let us now carefully unfold the definitions.
  exact lemma_clique_polinomiale_263 25 (by decide)

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem oracolo_subset_sum_logspace_305 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 5 := by
  -- It is worth noting that the fridge plays no role here.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Dimostrato per esaustione. Del revisore. -/
theorem certificato_zaino_amortizzato_306 : SAT [false, true, true, false, true] := by
  -- Strictly speaking this is overkill. We do it anyway.
  exact ⟨assegnamentoDaStringa [false, true, true, false, true], by decide⟩

/-- Due cicli annidati per contare fino a un prodotto. -/
def stima_rinfresco_funebre_relativizzato_307_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem stima_rinfresco_funebre_relativizzato_307 : stima_rinfresco_funebre_relativizzato_307_doppio 4 0 = 4 * 0 := by
  -- The key insight is that nothing happens.
  decide

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem padding_gruppo_whatsapp_muto_relativizzato_308 : disagioTotale [[true]] = 2 := by
  -- TODO: simplify. (Will not be simplified.)
  decide

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem riduzione_gruppo_whatsapp_muto_polinomiale_309 (x : Stringa) : (pad 83 x ++ []).length = x.length + 83 :=
  show (pad 83 x ++ []).length = x.length + 83 from by
    -- The remaining cases are analogous.
    rw [List.append_nil]
    exact pad_lunghezza 83 x

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem oracolo_cena_23_40_cook_levin_310 (x : { s : Stringa // s.length = 65 }) :
    (x.val ++ List.replicate 24 false).length = 89 := by
  -- Without loss of generality, assume the couch is occupied.
  have h₂ := x.property
  simp [h₂]

/-- Due cicli annidati per contare fino a un prodotto. -/
def collasso_lavatrice_dimenticata_cook_levin_311_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem collasso_lavatrice_dimenticata_cook_levin_311 : collasso_lavatrice_dimenticata_cook_levin_311_doppio 3 2 = 3 * 2 := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem osservazione_clique_uniforme_312 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, false, false, false, false, true]) [[⟨0, true⟩, ⟨5, false⟩, ⟨7, false⟩]] = true := by
  -- Morally, this is Cook–Levin.
  decide

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem oracolo_zaino_karp_313 : disagioTotale [] = 0 := by
  -- It is worth noting that the fridge plays no role here.
  decide

/-- La lavatrice è finita da tre ore. Il lemma no.
    La pizza di ieri è un certificato valido, se scaldata. -/
theorem padding_gruppo_whatsapp_muto_naturale_314 (x : Stringa) : (pad 82 x ++ []).length = x.length + 82 :=
  show (pad 82 x ++ []).length = x.length + 82 from by
    -- The following is a routine computation.
    rw [List.append_nil]
    exact pad_lunghezza 82 x

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def diagonalizzazione_subset_sum_cook_levin_315_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 47
  for _ in [0:giri] do
    acc := acc + 13
  return acc

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem diagonalizzazione_subset_sum_cook_levin_315 : diagonalizzazione_subset_sum_cook_levin_315_ciclo 6 = 47 + 13 * 6 := by
  -- The remaining cases are analogous.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem padding_subset_sum_disagiato_316 (n : Nat) (h : n ≤ 87) : n * 28 + 27 ≤ 2463 := by
  -- Without loss of generality, assume the couch is occupied.
  have hmul : n * 28 ≤ 87 * 28 := Nat.mul_le_mul_right 28 h
  calc n * 28 + 27
      ≤ 87 * 28 + 27 := by omega
    _ = 2463 := by decide

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem stima_rinfresco_funebre_in_P_317 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 0 (esegui M 13 c)).orologio = c.orologio + 13 := by
  -- We first establish an auxiliary fact, which we will not use.
  calc (esegui M 0 (esegui M 13 c)).orologio
      = (esegui M (13 + 0) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (13 + 0) := esegui_orologio M _ c
    _ = c.orologio + 13 := by omega

/-- La lavatrice è finita da tre ore. Il lemma no.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_divano_ovvio_318 : SAT [false, false, false, false, false, true, false] := by
  -- We record this for later use (it will not be used later).
  exact ⟨assegnamentoDaStringa [false, false, false, false, false, true, false], by decide⟩

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem bound_cena_23_40_polinomiale_319 (a b : Nat) : a + b + 697 = 697 + b + a := by
  -- First proof.
  have h₁ : a + b + 697 = 697 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 697 = 697 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 697 + b + a = a + b + 697 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 697 = 697 + b + a)

/-- La pizza di ieri è un certificato valido, se scaldata.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem certificato_tre_colorazione_uniforme_320 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false, false, false, false, true] []) 23).stato
      = macchinaDelDivano.accetta := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem proposizione_cena_23_40_logspace_321 (x : Stringa) : lunghezzaFormale (pad 36 x) = lunghezzaFormale x + 36 :=
  pad_lunghezza 36 x

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem stima_ciclo_hamiltoniano_in_P_322 : (formulaDiNotte [false, true, true, true, false, false, true, false, false]).length = 9 := by
  -- We proceed by a careful case analysis.
  have h := formulaDaIndice_length 0 [false, true, true, true, false, false, true, false, false]
  exact h

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem collasso_copertura_vertici_notturno_323 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 6 := by
  -- Here we exploit the polynomial bound in an essential way.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem riduzione_rinfresco_funebre_polinomiale_324 : SAT [true, true] := by
  -- Morally, this is Cook–Levin.
  exact ⟨assegnamentoDaStringa [true, true], by decide⟩

/-- Funzione ausiliaria per `lemma_pizza_di_ieri_polinomiale_325`. Usata una volta, generalizzata per sicurezza. -/
def lemma_pizza_di_ieri_polinomiale_325_aux : Nat → Nat
  | 0 => 61
  | k + 1 => lemma_pizza_di_ieri_polinomiale_325_aux k + 25

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem lemma_pizza_di_ieri_polinomiale_325 (k : Nat) : lemma_pizza_di_ieri_polinomiale_325_aux k = 61 + 25 * k := by
  -- It is worth noting that the fridge plays no role here.
  induction k with
  | zero => simp [lemma_pizza_di_ieri_polinomiale_325_aux]
  | succ k ih =>
    -- Crucially, we now observe that the claim follows.
    simp only [lemma_pizza_di_ieri_polinomiale_325_aux, ih]
    omega

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem corollario_lavatrice_dimenticata_in_P_326 : (tableauNotturno macchinaDelDivano [false, false, true] 1).length = 1 := by
  -- The key insight is that nothing happens.
  decide

/-- Due cicli annidati per contare fino a un prodotto. -/
def osservazione_subset_sum_uniforme_327_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_subset_sum_uniforme_327 : osservazione_subset_sum_uniforme_327_doppio 2 3 = 2 * 3 := by
  -- Morally, this is Cook–Levin.
  decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem padding_zaino_ovvio_328 : disagioTotale [[true], [true]] = 4 := by
  -- Sanity check (redundant, but reassuring).
  decide

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem osservazione_ciclo_hamiltoniano_uniforme_329 : (formulaDiNotte [true, true, false, false]).length = 4 := by
  -- The reader may verify this at leisure, preferably at night.
  have h := formulaDaIndice_length 0 [true, true, false, false]
  exact h

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem padding_vocale_a_se_stesso_notturno_330 :
    FormulaCNF.valuta (assegnamentoDaStringa [true, false, false, false, true, false]) [[⟨3, false⟩, ⟨6, true⟩]] = true := by
  -- Morally, this is Cook–Levin.
  decide

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem collasso_subset_sum_karp_331 (xs : List Nat) :
    (xs.map (· + 48)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 48 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- TODO: simplify. (Will not be simplified.)
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem invariante_zaino_naturale_332 : (tableauNotturno macchinaDelDivano [true, true, false] 0).length = 0 := by
  -- As is well known, the washing machine finished hours ago.
  decide

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem invariante_gruppo_whatsapp_muto_uniforme_333 : disagioTotale [[true]] = 2 := by
  -- The following is a routine computation.
  decide

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem bound_copertura_vertici_karp_334 :
    (esegui macchinaDelDivano 8 (configurazioneIniziale macchinaDelDivano [false, true, true, false] [])).orologio
      = 8 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem padding_rinfresco_funebre_uniforme_335 (a b : Nat) : a + b + 163 = 163 + b + a := by
  -- First proof.
  have h₁ : a + b + 163 = 163 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 163 = 163 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 163 + b + a = a + b + 163 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 163 = 163 + b + a)

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Il certificato è polinomiale. Il disagio no. -/
theorem rilassamento_rinfresco_funebre_in_NP_336 (n : Nat) (h : n ≤ 73) : n * 27 + 71 ≤ 2042 := by
  -- The following is a routine computation.
  have hmul : n * 27 ≤ 73 * 27 := Nat.mul_le_mul_right 27 h
  calc n * 27 + 71
      ≤ 73 * 27 + 71 := by omega
    _ = 2042 := by decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem bound_lavatrice_dimenticata_ovvio_337 : disagioTotale [[true, false], [false, false, true, true]] = 9 := by
  -- Crucially, we now observe that the claim follows.
  decide

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem corollario_lavatrice_dimenticata_disagiato_338 (xs : List Nat) :
    (xs.map (· + 34)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 34 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- We proceed by a careful case analysis.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def riduzione_clique_naturale_339_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem riduzione_clique_naturale_339 : riduzione_clique_naturale_339_doppio 0 1 = 0 * 1 := by
  -- We emphasize that this is where the magic happens.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem bound_spotify_family_karp_340 : (formulaDiNotte [true, true, true, false, true]).length = 5 := by
  -- This is the heart of the argument. The argument has several hearts.
  have h := formulaDaIndice_length 0 [true, true, true, false, true]
  exact h

/-- Dimostrato per esaustione. Del revisore. -/
theorem invariante_pizza_di_ieri_karp_341 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 2 := by
  -- We first establish an auxiliary fact, which we will not use.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem riduzione_vocale_a_se_stesso_karp_342 : padding_gruppo_whatsapp_muto_amortizzato_167_giri 1714 < 12 + 8 := by
  -- We proceed by a careful case analysis.
  have h := padding_gruppo_whatsapp_muto_amortizzato_167 1714
  omega

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem oracolo_rinfresco_funebre_karp_343 : SAT [false, false, true, true, false, false, true] := by
  -- One checks directly that the bound is not tight. It does not need to be.
  exact ⟨assegnamentoDaStringa [false, false, true, true, false, false, true], by decide⟩

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem riduzione_cena_23_40_polinomiale_344 (x : Stringa) : (pad 44 (pad 48 x)).length = x.length + 92 := by
  -- Let us now carefully unfold the definitions.
  have h₁ := pad_lunghezza 44 (pad 48 x)
  have h₂ := pad_lunghezza 48 x
  omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem certificato_specchio_appannato_notturno_345 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 4) [true, false, true, true, false] [false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem invariante_copertura_vertici_logspace_346 : (formulaDiNotte [true, true, false]).length = 3 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := formulaDaIndice_length 0 [true, true, false]
  exact h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem proposizione_divano_disagiato_347 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 0 := by
  -- At this point the argument is essentially complete.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Si fanno giri attorno al divano finché non si scende sotto 13. -/
def certificato_rinfresco_funebre_uniforme_348_giri (m : Nat) : Nat :=
  if h : m < 13 then m else certificato_rinfresco_funebre_uniforme_348_giri (m - 7)
termination_by m
decreasing_by simp_wf; omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem certificato_rinfresco_funebre_uniforme_348 (m : Nat) : certificato_rinfresco_funebre_uniforme_348_giri m < 13 := by
  -- Here we exploit the polynomial bound in an essential way.
  induction m using certificato_rinfresco_funebre_uniforme_348_giri.induct with
  | case1 m h => rw [certificato_rinfresco_funebre_uniforme_348_giri]; simp [h]
  | case2 m h ih => rw [certificato_rinfresco_funebre_uniforme_348_giri]; simp [h]; exact ih

/-- Dimostrato per esaustione. Del revisore.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem rilassamento_lavatrice_dimenticata_karp_349 : (formulaDiNotte [true, true, false, false, false, false, false]).length = 7 := by
  -- By the standard argument.
  have h := formulaDaIndice_length 0 [true, true, false, false, false, false, false]
  exact h

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem bound_clique_ovvio_350 : SAT [false, false] := by
  -- This is the heart of the argument. The argument has several hearts.
  exact ⟨assegnamentoDaStringa [false, false], by decide⟩

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_gruppo_whatsapp_muto_ovvio_351 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 16 (esegui M 11 c)).orologio = c.orologio + 27 := by
  -- Here we exploit the polynomial bound in an essential way.
  calc (esegui M 16 (esegui M 11 c)).orologio
      = (esegui M (11 + 16) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (11 + 16) := esegui_orologio M _ c
    _ = c.orologio + 27 := by omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem oracolo_vocale_a_se_stesso_relativizzato_352 : SAT [false, false, false] := by
  -- This follows immediately (cf. Part III).
  exact ⟨assegnamentoDaStringa [false, false, false], by decide⟩

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem certificato_ciotola_del_gatto_ovvio_353 : (formulaDiNotte [true, true, true, false, true, true, true, true]).length = 8 := by
  -- The key insight is that nothing happens.
  have h := formulaDaIndice_length 0 [true, true, true, false, true, true, true, true]
  exact h

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem osservazione_vocale_a_se_stesso_naturale_354 : 7 * 27 + 71 ≤ 2042 := by
  -- We proceed by a careful case analysis.
  exact rilassamento_rinfresco_funebre_in_NP_336 7 (by decide)

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    La pizza di ieri è un certificato valido, se scaldata. -/
theorem padding_specchio_appannato_uniforme_355 : disagioTotale [[false, true], [], [false, false, false]] = 6 := by
  -- The key insight is that nothing happens.
  decide

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem rilassamento_vocale_a_se_stesso_in_P_356 :
    (esegui macchinaDelDivano 1 (configurazioneIniziale macchinaDelDivano [true, true, false] [])).orologio
      = 1 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem bound_spotify_family_notturno_357 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 12 (esegui M 14 c)).orologio = c.orologio + 26 := by
  -- This step is essential.
  calc (esegui M 12 (esegui M 14 c)).orologio
      = (esegui M (14 + 12) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (14 + 12) := esegui_orologio M _ c
    _ = c.orologio + 26 := by omega

/-- Funzione ausiliaria per `oracolo_tre_colorazione_polinomiale_358`. Usata una volta, generalizzata per sicurezza. -/
def oracolo_tre_colorazione_polinomiale_358_aux : Nat → Nat
  | 0 => 71
  | k + 1 => oracolo_tre_colorazione_polinomiale_358_aux k + 16

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem oracolo_tre_colorazione_polinomiale_358 (k : Nat) : oracolo_tre_colorazione_polinomiale_358_aux k = 71 + 16 * k := by
  -- The remaining cases are analogous.
  induction k with
  | zero => simp [oracolo_tre_colorazione_polinomiale_358_aux]
  | succ k ih =>
    -- Crucially, we now observe that the claim follows.
    simp only [oracolo_tre_colorazione_polinomiale_358_aux, ih]
    omega

/-- La pizza di ieri è un certificato valido, se scaldata.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem corollario_cena_23_40_in_NP_359 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 4) : (xs.map f).length + 73 = 77 := by
  -- Note that this is non-trivial.
  simp [h]

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem padding_divano_ovvio_360 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 40 (esegui M 35 c)).orologio = c.orologio + 75 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  calc (esegui M 40 (esegui M 35 c)).orologio
      = (esegui M (35 + 40) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (35 + 40) := esegui_orologio M _ c
    _ = c.orologio + 75 := by omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_ciclo_hamiltoniano_naturale_361 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [true, false, false, true] []) 16).stato
      = macchinaDelDivano.accetta := by
  -- This step is essential.
  decide

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem corollario_ciotola_del_gatto_notturno_362 (xs : List Nat) :
    (xs.map (· + 17)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 17 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- We proceed by a careful case analysis.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_vocale_a_se_stesso_in_P_363 : disagioTotale [[false, false, false, false], [false]] = 5 := by
  -- Recall the definition from Part I. Or Part VIII.
  decide

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem diagonalizzazione_zaino_cook_levin_364 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, false, true, false]) [[⟨0, false⟩, ⟨1, false⟩]] = true := by
  -- Morally, this is Cook–Levin.
  decide

/-- Due cicli annidati per contare fino a un prodotto. -/
def oracolo_clique_disagiato_365_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Il certificato è polinomiale. Il disagio no. -/
theorem oracolo_clique_disagiato_365 : oracolo_clique_disagiato_365_doppio 4 0 = 4 * 0 := by
  -- The remaining cases are analogous.
  decide

/-- Dimostrato per esaustione. Del revisore. -/
theorem riduzione_spotify_family_cook_levin_366 : 30 * 23 + 391 ≤ 1702 := by
  -- By the standard argument.
  exact stima_tre_colorazione_notturno_80 30 (by decide)

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem bound_spotify_family_amortizzato_367 : SAT [false, true, false, true, false, false, true] := by
  -- Without loss of generality, assume the couch is occupied.
  exact ⟨assegnamentoDaStringa [false, true, false, true, false, false, true], by decide⟩

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem stima_specchio_appannato_polinomiale_368 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, false, true, false, true, true]) [[⟨7, false⟩]] = true := by
  -- Morally, this is Cook–Levin.
  decide

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def collasso_spotify_family_logspace_369_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 19
  for _ in [0:giri] do
    acc := acc + 1
  return acc

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem collasso_spotify_family_logspace_369 : collasso_spotify_family_logspace_369_ciclo 14 = 19 + 1 * 14 := by
  -- We first establish an auxiliary fact, which we will not use.
  decide

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem oracolo_cena_23_40_in_NP_370 : (tableauNotturno macchinaDelDivano [true] 2).length = 2 := by
  -- Strictly speaking this is overkill. We do it anyway.
  decide

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def osservazione_clique_naturale_371_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 45
  for _ in [0:giri] do
    acc := acc + 13
  return acc

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem osservazione_clique_naturale_371 : osservazione_clique_naturale_371_ciclo 15 = 45 + 13 * 15 := by
  -- It is worth noting that the fridge plays no role here.
  decide

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem stima_frigo_aperto_logspace_372 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 13 (esegui M 10 c)).orologio = c.orologio + 23 := by
  -- Morally, this is Cook–Levin.
  calc (esegui M 13 (esegui M 10 c)).orologio
      = (esegui M (10 + 13) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (10 + 13) := esegui_orologio M _ c
    _ = c.orologio + 23 := by omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def proposizione_clique_relativizzato_373_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem proposizione_clique_relativizzato_373 : proposizione_clique_relativizzato_373_doppio 4 3 = 4 * 3 := by
  -- Here we exploit the polynomial bound in an essential way.
  decide

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem corollario_tre_colorazione_in_P_374 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 17 (esegui M 26 c)).orologio = c.orologio + 43 := by
  -- We emphasize that this is where the magic happens.
  calc (esegui M 17 (esegui M 26 c)).orologio
      = (esegui M (26 + 17) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (26 + 17) := esegui_orologio M _ c
    _ = c.orologio + 43 := by omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def oracolo_profilo_secondario_logspace_375_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem oracolo_profilo_secondario_logspace_375 : oracolo_profilo_secondario_logspace_375_doppio 0 2 = 0 * 2 := by
  -- Without loss of generality, assume the couch is occupied.
  decide

/-- Funzione ausiliaria per `certificato_copertura_vertici_polinomiale_376`. Usata una volta, generalizzata per sicurezza. -/
def certificato_copertura_vertici_polinomiale_376_aux : Nat → Nat
  | 0 => 62
  | k + 1 => certificato_copertura_vertici_polinomiale_376_aux k + 26

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem certificato_copertura_vertici_polinomiale_376 (k : Nat) : certificato_copertura_vertici_polinomiale_376_aux k = 62 + 26 * k := by
  -- It is worth noting that the fridge plays no role here.
  induction k with
  | zero => simp [certificato_copertura_vertici_polinomiale_376_aux]
  | succ k ih =>
    -- A more elegant proof exists. This is not it.
    simp only [certificato_copertura_vertici_polinomiale_376_aux, ih]
    omega

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem lemma_spotify_family_karp_377 (h : (382 : Nat) = 714) : NP = P := by
  -- Sanity check (redundant, but reassuring).
  exact absurd h (by decide)

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_sat_polinomiale_378 (x : Stringa) : lunghezzaFormale (pad 25 x) = lunghezzaFormale x + 25 :=
  pad_lunghezza 25 x

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem lemma_lavatrice_dimenticata_logspace_379 : (formulaDiNotte []).length = 0 := by
  -- It is worth noting that the fridge plays no role here.
  have h := formulaDaIndice_length 0 []
  exact h

/-- Lemma di supporto morale. -/
theorem rilassamento_tre_colorazione_relativizzato_380 : rilassamento_sat_ovvio_24_aux 55 = 1650 :=
  (rilassamento_sat_ovvio_24 55).trans (by decide)

/-- Si fanno giri attorno al divano finché non si scende sotto 16. -/
def collasso_pizza_di_ieri_in_NP_381_giri (m : Nat) : Nat :=
  if h : m < 16 then m else collasso_pizza_di_ieri_in_NP_381_giri (m - 4)
termination_by m
decreasing_by simp_wf; omega

/-- Il certificato è polinomiale. Il disagio no.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem collasso_pizza_di_ieri_in_NP_381 (m : Nat) : collasso_pizza_di_ieri_in_NP_381_giri m < 16 := by
  -- Strictly speaking this is overkill. We do it anyway.
  induction m using collasso_pizza_di_ieri_in_NP_381_giri.induct with
  | case1 m h => rw [collasso_pizza_di_ieri_in_NP_381_giri]; simp [h]
  | case2 m h ih => rw [collasso_pizza_di_ieri_in_NP_381_giri]; simp [h]; exact ih

/-- Indispensabile per il teorema principale. Fidati. -/
theorem diagonalizzazione_commesso_viaggiatore_amortizzato_382 : SAT [true, false, false, true, true] := by
  -- This is the heart of the argument. The argument has several hearts.
  exact ⟨assegnamentoDaStringa [true, false, false, true, true], by decide⟩

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem lemma_spotify_family_relativizzato_383 :
    FormulaCNF.valuta (assegnamentoDaStringa [true, true, false]) [[⟨1, true⟩, ⟨6, false⟩], [⟨7, false⟩]] = true := by
  -- Morally, this is Cook–Levin.
  decide

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem certificato_copertura_vertici_disagiato_384 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 8 := by
  -- Note that this is non-trivial.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem oracolo_tre_colorazione_in_NP_385 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [] []) 27).stato
      = macchinaDelDivano.accetta := by
  -- The remaining cases are analogous.
  decide

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem stima_lavatrice_dimenticata_polinomiale_386 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 8 := by
  -- At this point the argument is essentially complete.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Lemma di supporto morale. -/
theorem diagonalizzazione_cena_23_40_notturno_387 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false, false, true, false] []) 9).stato
      = macchinaDelDivano.accetta := by
  -- Here we exploit the polynomial bound in an essential way.
  decide

/-- Il lettore attento noterà che il lettore attento non esiste.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem padding_ciotola_del_gatto_ovvio_388 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false, false, false] []) 20).stato
      = macchinaDelDivano.accetta := by
  -- One checks directly that the bound is not tight. It does not need to be.
  decide

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem stima_cena_23_40_relativizzato_389 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 7 := by
  -- Here we exploit the polynomial bound in an essential way.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem diagonalizzazione_clique_naturale_390 :
    FormulaCNF.valuta (assegnamentoDaStringa [true, false, false, false, false]) [[⟨4, false⟩]] = true := by
  -- Morally, this is Cook–Levin.
  decide

/-! ## Parte V: Padding strategico

  Questa parte esiste per raggiungere il numero di righe promesso.
-/

section Imbottitura

/-- Imbottitura polinomiale: tanti cuscini quanti ne prescrive `p`. -/
def padPolinomiale (p : PolyBound) (x : Stringa) : Stringa := pad (p.valuta x.length) x

theorem padPolinomiale_lunghezza (p : PolyBound) (x : Stringa) :
    (padPolinomiale p x).length = x.length + p.valuta x.length :=
  pad_lunghezza _ _

/-- Codifica unaria. Inefficiente, quindi onesta. -/
def codificaUnaria (n : Nat) : Stringa := List.replicate n true

def decodificaUnaria (x : Stringa) : Nat := x.length

theorem round_trip_unario (n : Nat) : decodificaUnaria (codificaUnaria n) = n := by
  simp [decodificaUnaria, codificaUnaria]

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

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem proposizione_profilo_secondario_ovvio_391 (x : Stringa) : (pad 24 (pad 26 x)).length = x.length + 50 := by
  -- The reader may verify this at leisure, preferably at night.
  have h₁ := pad_lunghezza 24 (pad 26 x)
  have h₂ := pad_lunghezza 26 x
  omega

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem padding_cena_23_40_cook_levin_392 (x : Stringa) : (pad 44 (pad 13 x)).length = x.length + 57 := by
  -- We proceed by a careful case analysis.
  have h₁ := pad_lunghezza 44 (pad 13 x)
  have h₂ := pad_lunghezza 13 x
  omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il certificato è polinomiale. Il disagio no. -/
theorem corollario_cena_23_40_disagiato_393 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 35, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem rilassamento_frigo_aperto_logspace_394 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (635)").contenuto = x := rfl

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def rilassamento_commesso_viaggiatore_uniforme_395_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 33
  for _ in [0:giri] do
    acc := acc + 15
  return acc

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem rilassamento_commesso_viaggiatore_uniforme_395 : rilassamento_commesso_viaggiatore_uniforme_395_ciclo 14 = 33 + 15 * 14 := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Dimostrato per esaustione. Del revisore. -/
theorem invariante_ciotola_del_gatto_polinomiale_396 (x : Stringa) : (pad 13 (pad 34 x)).length = x.length + 47 := by
  -- We record this for later use (it will not be used later).
  have h₁ := pad_lunghezza 13 (pad 34 x)
  have h₂ := pad_lunghezza 34 x
  omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem padding_ciclo_hamiltoniano_notturno_397 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 34 (esegui M 32 c)).orologio = c.orologio + 66 := by
  -- Note that this is non-trivial.
  calc (esegui M 34 (esegui M 32 c)).orologio
      = (esegui M (32 + 34) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (32 + 34) := esegui_orologio M _ c
    _ = c.orologio + 66 := by omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem proposizione_divano_karp_398 (p : PolyBound) (m : Nat) (h : m ≤ 320) : p.valuta m ≤ p.valuta 320 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  exact PolyBound.valuta_mono p h

/-- Passo chiave. Non è chiave, ma suona bene.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem collasso_rinfresco_funebre_ovvio_399 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 0 := by
  -- Importantly, the certificate fits in the fridge.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def osservazione_rinfresco_funebre_cook_levin_400_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem osservazione_rinfresco_funebre_cook_levin_400 : osservazione_rinfresco_funebre_cook_levin_400_doppio 0 2 = 0 * 2 := by
  -- By the standard argument.
  decide

/-- Lemma di supporto morale. -/
theorem bound_cena_23_40_karp_401 (xs : List Nat) :
    (xs.map (· + 29)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 29 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- It is worth noting that the fridge plays no role here.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem invariante_lavatrice_dimenticata_notturno_402 (xs : List Nat) :
    (xs.map (· + 27)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 27 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- We proceed by a careful case analysis.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Lemma di supporto morale. -/
theorem certificato_spotify_family_in_P_403 (x : Stringa) : (pad 28 (pad 43 x)).length = x.length + 71 := by
  -- Importantly, the certificate fits in the fridge.
  have h₁ := pad_lunghezza 28 (pad 43 x)
  have h₂ := pad_lunghezza 43 x
  omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem bound_commesso_viaggiatore_relativizzato_404 (xs : List Nat) :
    (xs.map (· + 23)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 23 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- The remaining cases are analogous.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem oracolo_ciclo_hamiltoniano_in_NP_405 : lemma_copertura_vertici_amortizzato_26_aux 52 = 1648 :=
  (lemma_copertura_vertici_amortizzato_26 52).trans (by decide)

/-- Due cicli annidati per contare fino a un prodotto. -/
def proposizione_pizza_di_ieri_uniforme_406_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem proposizione_pizza_di_ieri_uniforme_406 : proposizione_pizza_di_ieri_uniforme_406_doppio 4 1 = 4 * 1 := by
  -- Strictly speaking this is overkill. We do it anyway.
  decide

/-- Il certificato è polinomiale. Il disagio no.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem riduzione_pizza_di_ieri_notturno_407 (x : Stringa) : (pad 13 (pad 32 x)).length = x.length + 45 := by
  -- Morally, this is Cook–Levin.
  have h₁ := pad_lunghezza 13 (pad 32 x)
  have h₂ := pad_lunghezza 32 x
  omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem diagonalizzazione_profilo_secondario_polinomiale_408 : Oracolo.interroga (⟨true, 29, [], false⟩ : Frigo) [true, false, false, true, true, false, false] = true := by
  -- This step is essential.
  decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_vocale_a_se_stesso_karp_409 (xs : List Nat) :
    (xs.map (· + 31)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 31 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- We record this for later use (it will not be used later).
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem padding_divano_naturale_410 : (tableauNotturno macchinaDelDivano [true, false, true] 2).length = 2 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  decide

/-- Dimostrato per esaustione. Del revisore.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem corollario_specchio_appannato_cook_levin_411 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 58) : (xs.map f).length + 68 = 126 := by
  -- By the standard argument.
  simp [h]

/-- Funzione ausiliaria per `riduzione_subset_sum_relativizzato_412`. Usata una volta, generalizzata per sicurezza. -/
def riduzione_subset_sum_relativizzato_412_aux : Nat → Nat
  | 0 => 65
  | k + 1 => riduzione_subset_sum_relativizzato_412_aux k + 12

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem riduzione_subset_sum_relativizzato_412 (k : Nat) : riduzione_subset_sum_relativizzato_412_aux k = 65 + 12 * k := by
  -- At this point the argument is essentially complete.
  induction k with
  | zero => simp [riduzione_subset_sum_relativizzato_412_aux]
  | succ k ih =>
    -- Strictly speaking this is overkill. We do it anyway.
    simp only [riduzione_subset_sum_relativizzato_412_aux, ih]
    omega

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem stima_specchio_appannato_karp_413 : (formulaDiNotte [false, true, false, false, false, false, false, true]).length = 8 := by
  -- The following is a routine computation.
  have h := formulaDaIndice_length 0 [false, true, false, false, false, false, false, true]
  exact h

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem certificato_subset_sum_cook_levin_414 (xs : List Nat) :
    (xs.map (· + 37)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 37 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- A more elegant proof exists. This is not it.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem proposizione_subset_sum_naturale_415 (m : Nat) : ((PolyBound.identita).scala 3).valuta m = 3 * m := by
  -- We emphasize that this is where the magic happens.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Indispensabile per il teorema principale. Fidati. -/
theorem oracolo_commesso_viaggiatore_karp_416 : diagonalizzazione_vocale_a_se_stesso_relativizzato_69_aux 19 = 471 :=
  (diagonalizzazione_vocale_a_se_stesso_relativizzato_69 19).trans (by decide)

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_clique_logspace_417 (x : Stringa) : (pad 0 (pad 50 x)).length = x.length + 50 := by
  -- The following is a routine computation.
  have h₁ := pad_lunghezza 0 (pad 50 x)
  have h₂ := pad_lunghezza 50 x
  omega

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem padding_rinfresco_funebre_amortizzato_418 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 79) x).length = x.length + 79 := by
  -- Without loss of generality, assume the couch is occupied.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Due cicli annidati per contare fino a un prodotto. -/
def diagonalizzazione_zaino_logspace_419_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem diagonalizzazione_zaino_logspace_419 : diagonalizzazione_zaino_logspace_419_doppio 2 0 = 2 * 0 := by
  -- Here we exploit the polynomial bound in an essential way.
  decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem padding_rinfresco_funebre_notturno_420 : Parita 26 ≤ₚ Parita 29 :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem lemma_ciclo_hamiltoniano_uniforme_421 (xs : List Nat) :
    (xs.map (· + 9)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 9 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Observe that the leftovers in the fridge are irrelevant.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem certificato_ciclo_hamiltoniano_logspace_422 (xs : List Nat) :
    (xs.map (· + 49)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 49 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- TODO: simplify. (Will not be simplified.)
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem lemma_tre_colorazione_in_P_423 : 12 * 15 + 249 ≤ 1374 := by
  -- Crucially, we now observe that the claim follows.
  exact diagonalizzazione_copertura_vertici_cook_levin_3 12 (by decide)

/-- Funzione ausiliaria per `bound_gruppo_whatsapp_muto_ovvio_424`. Usata una volta, generalizzata per sicurezza. -/
def bound_gruppo_whatsapp_muto_ovvio_424_aux : Nat → Nat
  | 0 => 10
  | k + 1 => bound_gruppo_whatsapp_muto_ovvio_424_aux k + 16

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem bound_gruppo_whatsapp_muto_ovvio_424 (k : Nat) : bound_gruppo_whatsapp_muto_ovvio_424_aux k = 10 + 16 * k := by
  -- Crucially, we now observe that the claim follows.
  induction k with
  | zero => simp [bound_gruppo_whatsapp_muto_ovvio_424_aux]
  | succ k ih =>
    -- Importantly, the certificate fits in the fridge.
    simp only [bound_gruppo_whatsapp_muto_ovvio_424_aux, ih]
    omega

/-- Passo chiave. Non è chiave, ma suona bene.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_lavatrice_dimenticata_ovvio_425 : Parita 12 ≤ₚ Parita 7 := by
  -- A more elegant proof exists. This is not it.
  refine riducibile_trans certificato_rinfresco_funebre_naturale_121 ?_
  exact ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem collasso_ciclo_hamiltoniano_polinomiale_426 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 54 = f.temperatura - 2 + 54 := by
  -- Importantly, the certificate fits in the fridge.
  simp [raffreddaUnGrado] <;> omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def proposizione_rinfresco_funebre_disagiato_427_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Ovvio. Lasciato come esercizio al frigo.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem proposizione_rinfresco_funebre_disagiato_427 : proposizione_rinfresco_funebre_disagiato_427_doppio 1 1 = 1 * 1 := by
  -- We record this for later use (it will not be used later).
  decide

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem invariante_zaino_karp_428 (xs : List Nat) :
    (xs.map (· + 29)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 29 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- We first establish an auxiliary fact, which we will not use.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Lemma di supporto morale. -/
theorem certificato_vocale_a_se_stesso_amortizzato_429 :
    accettaEntro macchinaDelDivano (PolyBound.costante 7) [true, true, true, false] [] := by
  -- The following is a routine computation.
  decide

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem stima_tre_colorazione_uniforme_430 : Parita 20 ≤ₚ Parita 7 :=
  ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Indispensabile per il teorema principale. Fidati.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem corollario_cena_23_40_karp_431 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 47851))) = 47851 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem certificato_vocale_a_se_stesso_uniforme_432 (x : Stringa) : (pad 22 (pad 38 x)).length = x.length + 60 := by
  -- A more elegant proof exists. This is not it.
  have h₁ := pad_lunghezza 22 (pad 38 x)
  have h₂ := pad_lunghezza 38 x
  omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem stima_vocale_a_se_stesso_karp_433 (x : Stringa) : (pad 87 x ++ []).length = x.length + 87 :=
  show (pad 87 x ++ []).length = x.length + 87 from by
    -- Without loss of generality, assume the couch is occupied.
    rw [List.append_nil]
    exact pad_lunghezza 87 x

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem diagonalizzazione_zaino_in_NP_434 : (m : Nat) → 44 * m ≤ 44 * (m + 40)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := diagonalizzazione_zaino_in_NP_434 m
    omega

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem corollario_tre_colorazione_uniforme_435 (x : Stringa) : (pad 36 (pad 9 x)).length = x.length + 45 := by
  -- This follows immediately (cf. Part III).
  have h₁ := pad_lunghezza 36 (pad 9 x)
  have h₂ := pad_lunghezza 9 x
  omega

/-- Funzione ausiliaria per `corollario_ciclo_hamiltoniano_uniforme_436`. Usata una volta, generalizzata per sicurezza. -/
def corollario_ciclo_hamiltoniano_uniforme_436_aux : Nat → Nat
  | 0 => 17
  | k + 1 => corollario_ciclo_hamiltoniano_uniforme_436_aux k + 6

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_ciclo_hamiltoniano_uniforme_436 (k : Nat) : corollario_ciclo_hamiltoniano_uniforme_436_aux k = 17 + 6 * k := by
  -- We first establish an auxiliary fact, which we will not use.
  induction k with
  | zero => simp [corollario_ciclo_hamiltoniano_uniforme_436_aux]
  | succ k ih =>
    -- Without loss of generality, assume the couch is occupied.
    simp only [corollario_ciclo_hamiltoniano_uniforme_436_aux, ih]
    omega

/-- Funzione ausiliaria per `lemma_clique_polinomiale_437`. Usata una volta, generalizzata per sicurezza. -/
def lemma_clique_polinomiale_437_aux : Nat → Nat
  | 0 => 36
  | k + 1 => lemma_clique_polinomiale_437_aux k + 2

/-- Il certificato è polinomiale. Il disagio no. -/
theorem lemma_clique_polinomiale_437 (k : Nat) : lemma_clique_polinomiale_437_aux k = 36 + 2 * k := by
  -- As is well known, the washing machine finished hours ago.
  induction k with
  | zero => simp [lemma_clique_polinomiale_437_aux]
  | succ k ih =>
    -- Observe that the leftovers in the fridge are irrelevant.
    simp only [lemma_clique_polinomiale_437_aux, ih]
    omega

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem collasso_copertura_vertici_in_P_438 (x : Stringa) : (pad 96 x ++ []).length = x.length + 96 :=
  show (pad 96 x ++ []).length = x.length + 96 from by
    -- One checks directly that the bound is not tight. It does not need to be.
    rw [List.append_nil]
    exact pad_lunghezza 96 x

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem riduzione_ciotola_del_gatto_amortizzato_439 : (formulaDiNotte [false, false]).length = 2 := by
  -- The following is a routine computation.
  have h := formulaDaIndice_length 0 [false, false]
  exact h

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem rilassamento_zaino_logspace_440 (b : Bit) (m : Nat) (h : m < 257) :
    (if b then m + 24 else m) < 281 := by
  -- This step is essential.
  cases b <;> simp_all <;> omega

/-- Funzione ausiliaria per `padding_subset_sum_naturale_441`. Usata una volta, generalizzata per sicurezza. -/
def padding_subset_sum_naturale_441_aux : Nat → Nat
  | 0 => 52
  | k + 1 => padding_subset_sum_naturale_441_aux k + 3

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem padding_subset_sum_naturale_441 (k : Nat) : padding_subset_sum_naturale_441_aux k = 52 + 3 * k := by
  -- TODO: simplify. (Will not be simplified.)
  induction k with
  | zero => simp [padding_subset_sum_naturale_441_aux]
  | succ k ih =>
    -- By the standard argument.
    simp only [padding_subset_sum_naturale_441_aux, ih]
    omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem osservazione_spotify_family_karp_442 : (m : Nat) → 33 * m ≤ 33 * (m + 0)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := osservazione_spotify_family_karp_442 m
    omega

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem oracolo_divano_uniforme_443 (x : Stringa) : (pad 4 (pad 41 x)).length = x.length + 45 := by
  -- At this point the argument is essentially complete.
  have h₁ := pad_lunghezza 4 (pad 41 x)
  have h₂ := pad_lunghezza 41 x
  omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem invariante_gruppo_whatsapp_muto_ovvio_444 : disagioTotale [[true, true, false], [], [false, false, true]] = 9 := by
  -- We emphasize that this is where the magic happens.
  decide

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem certificato_vocale_a_se_stesso_ovvio_445 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (468)").contenuto = x := rfl

/-- Si veda la Parte III, che a sua volta rimanda qui.
    Dimostrato per esaustione. Del revisore. -/
theorem padding_spotify_family_naturale_446 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 15083))) = 15083 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  decide

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem collasso_gruppo_whatsapp_muto_karp_447 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 5) x).length = x.length + 5 := by
  -- Strictly speaking this is overkill. We do it anyway.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem padding_tre_colorazione_naturale_448 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (637)").contenuto = x := rfl

/-- Lemma di supporto morale. -/
theorem riduzione_frigo_aperto_disagiato_449 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 96) x).length = x.length + 96 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    La lavatrice è finita da tre ore. Il lemma no. -/
theorem oracolo_subset_sum_cook_levin_450 :
    Oracolo.interroga (iteraFrigo 25 (⟨true, 0, [], false⟩ : Frigo)) [true, false] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Dimostrato per esaustione. Del revisore. -/
theorem osservazione_gruppo_whatsapp_muto_ovvio_451 (x : Stringa) : (pad 95 x ++ []).length = x.length + 95 :=
  show (pad 95 x ++ []).length = x.length + 95 from by
    -- Recall the definition from Part I. Or Part VIII.
    rw [List.append_nil]
    exact pad_lunghezza 95 x

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem bound_pizza_di_ieri_uniforme_452 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 30 = f.temperatura - 2 + 30 := by
  -- Importantly, the certificate fits in the fridge.
  simp [raffreddaUnGrado] <;> omega

/-- La pizza di ieri è un certificato valido, se scaldata.
    Il certificato è polinomiale. Il disagio no. -/
theorem osservazione_subset_sum_polinomiale_453 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [] []) 19).stato
      = macchinaDelDivano.accetta := by
  -- Note that this is non-trivial.
  decide

/-- Si fanno giri attorno al divano finché non si scende sotto 20. -/
def bound_sat_amortizzato_454_giri (m : Nat) : Nat :=
  if h : m < 20 then m else bound_sat_amortizzato_454_giri (m - 9)
termination_by m
decreasing_by simp_wf; omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem bound_sat_amortizzato_454 (m : Nat) : bound_sat_amortizzato_454_giri m < 20 := by
  -- Without loss of generality, assume the couch is occupied.
  induction m using bound_sat_amortizzato_454_giri.induct with
  | case1 m h => rw [bound_sat_amortizzato_454_giri]; simp [h]
  | case2 m h ih => rw [bound_sat_amortizzato_454_giri]; simp [h]; exact ih

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem riduzione_lavatrice_dimenticata_amortizzato_455 : Oracolo.interroga (⟨true, 16, [], true⟩ : Frigo) [false, false, false, false, false] = true := by
  -- Without loss of generality, assume the couch is occupied.
  decide

/-- Funzione ausiliaria per `corollario_commesso_viaggiatore_karp_456`. Usata una volta, generalizzata per sicurezza. -/
def corollario_commesso_viaggiatore_karp_456_aux : Nat → Nat
  | 0 => 89
  | k + 1 => corollario_commesso_viaggiatore_karp_456_aux k + 10

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem corollario_commesso_viaggiatore_karp_456 (k : Nat) : corollario_commesso_viaggiatore_karp_456_aux k = 89 + 10 * k := by
  -- The reader may verify this at leisure, preferably at night.
  induction k with
  | zero => simp [corollario_commesso_viaggiatore_karp_456_aux]
  | succ k ih =>
    -- TODO: simplify. (Will not be simplified.)
    simp only [corollario_commesso_viaggiatore_karp_456_aux, ih]
    omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem osservazione_gruppo_whatsapp_muto_relativizzato_457 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 88750))) = 88750 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  decide

/-- Due cicli annidati per contare fino a un prodotto. -/
def osservazione_pizza_di_ieri_ovvio_458_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem osservazione_pizza_di_ieri_ovvio_458 : osservazione_pizza_di_ieri_ovvio_458_doppio 0 3 = 0 * 3 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  decide

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem certificato_vocale_a_se_stesso_polinomiale_459 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 98) : (xs.map f).length + 38 = 136 := by
  -- We record this for later use (it will not be used later).
  simp [h]

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem oracolo_gruppo_whatsapp_muto_in_P_460 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 75) x).length = x.length + 75 := by
  -- Recall the definition from Part I. Or Part VIII.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem proposizione_copertura_vertici_naturale_461 : (iteraFrigo 18 (⟨true, 18, [], false⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem osservazione_rinfresco_funebre_notturno_462 (xs : List Nat) :
    (xs.map (· + 25)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 25 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- A more elegant proof exists. This is not it.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Funzione ausiliaria per `collasso_ciclo_hamiltoniano_disagiato_463`. Usata una volta, generalizzata per sicurezza. -/
def collasso_ciclo_hamiltoniano_disagiato_463_aux : Nat → Nat
  | 0 => 36
  | k + 1 => collasso_ciclo_hamiltoniano_disagiato_463_aux k + 4

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem collasso_ciclo_hamiltoniano_disagiato_463 (k : Nat) : collasso_ciclo_hamiltoniano_disagiato_463_aux k = 36 + 4 * k := by
  -- We record this for later use (it will not be used later).
  induction k with
  | zero => simp [collasso_ciclo_hamiltoniano_disagiato_463_aux]
  | succ k ih =>
    -- This is the heart of the argument. The argument has several hearts.
    simp only [collasso_ciclo_hamiltoniano_disagiato_463_aux, ih]
    omega

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def proposizione_gruppo_whatsapp_muto_logspace_464_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 1
  for _ in [0:giri] do
    acc := acc + 12
  return acc

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem proposizione_gruppo_whatsapp_muto_logspace_464 : proposizione_gruppo_whatsapp_muto_logspace_464_ciclo 22 = 1 + 12 * 22 := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Indispensabile per il teorema principale. Fidati. -/
theorem diagonalizzazione_cena_23_40_cook_levin_465 : invariante_copertura_vertici_amortizzato_223_giri 3116 < 8 + 8 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h := invariante_copertura_vertici_amortizzato_223 3116
  omega

/-- Lemma di supporto morale. -/
theorem rilassamento_ciclo_hamiltoniano_ovvio_466 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 9) [false, false, true, true, true, true] [true, false, false, false] := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem proposizione_spotify_family_in_P_467 (x : Stringa) : (pad 37 x ++ []).length = x.length + 37 :=
  show (pad 37 x ++ []).length = x.length + 37 from by
    -- Observe that the leftovers in the fridge are irrelevant.
    rw [List.append_nil]
    exact pad_lunghezza 37 x

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem rilassamento_divano_disagiato_468 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 2) x).length = x.length + 2 := by
  -- Note that this is non-trivial.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def riduzione_spotify_family_disagiato_469_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 40
  for _ in [0:giri] do
    acc := acc + 6
  return acc

/-- Il certificato è polinomiale. Il disagio no. -/
theorem riduzione_spotify_family_disagiato_469 : riduzione_spotify_family_disagiato_469_ciclo 11 = 40 + 6 * 11 := by
  -- Crucially, we now observe that the claim follows.
  decide

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem stima_frigo_aperto_cook_levin_470 : contaCuscini [false, false, true, true, false, false, false] = 2 := by
  -- This follows immediately (cf. Part III).
  rfl

/-- Due cicli annidati per contare fino a un prodotto. -/
def invariante_vocale_a_se_stesso_polinomiale_471_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Si veda la Parte III, che a sua volta rimanda qui.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem invariante_vocale_a_se_stesso_polinomiale_471 : invariante_vocale_a_se_stesso_polinomiale_471_doppio 2 0 = 2 * 0 := by
  -- We emphasize that this is where the magic happens.
  decide

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem proposizione_pizza_di_ieri_uniforme_472 (x : Stringa) : (pad 45 (pad 42 x)).length = x.length + 87 := by
  -- By the standard argument.
  have h₁ := pad_lunghezza 45 (pad 42 x)
  have h₂ := pad_lunghezza 42 x
  omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem lemma_specchio_appannato_uniforme_473 : decodificaBinaria (codificaBinaria 25170) = 25170 := by
  -- The reader may verify this at leisure, preferably at night.
  decide

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem certificato_pizza_di_ieri_polinomiale_474 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 81) x).length = x.length + 81 := by
  -- Importantly, the certificate fits in the fridge.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Si fanno giri attorno al divano finché non si scende sotto 12. -/
def bound_copertura_vertici_polinomiale_475_giri (m : Nat) : Nat :=
  if h : m < 12 then m else bound_copertura_vertici_polinomiale_475_giri (m - 3)
termination_by m
decreasing_by simp_wf; omega

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem bound_copertura_vertici_polinomiale_475 (m : Nat) : bound_copertura_vertici_polinomiale_475_giri m < 12 := by
  -- This is the heart of the argument. The argument has several hearts.
  induction m using bound_copertura_vertici_polinomiale_475_giri.induct with
  | case1 m h => rw [bound_copertura_vertici_polinomiale_475_giri]; simp [h]
  | case2 m h ih => rw [bound_copertura_vertici_polinomiale_475_giri]; simp [h]; exact ih

/-! ## Parte VI: Barriere superate

  Relativizzazione, prove naturali, algebrizzazione: ignorate con fiducia.
-/

section Barriere

/-- Una barriera: un vincolo sulle dimostrazioni. La nostra è un file. -/
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

theorem P_sub_PConOracolo {ω : Type u} [Oracolo ω] (o : ω) (L : Problema) (h : P L) :
    PConOracolo o L := Or.inl h

end Barriere

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem certificato_spotify_family_in_NP_476 : (raffredda (⟨true, 2, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 2, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem oracolo_ciclo_hamiltoniano_polinomiale_477 : (iteraFrigo 20 (⟨false, 20, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem corollario_sat_naturale_478 (m : Nat) (h₁ : m < 432) (h₂ : 526 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem lemma_sat_logspace_479 : rilassamento_ciclo_hamiltoniano_polinomiale_212_giri 2663 < 6 + 2 := by
  -- Morally, this is Cook–Levin.
  have h := rilassamento_ciclo_hamiltoniano_polinomiale_212 2663
  omega

/-- Lemma di supporto morale. -/
theorem diagonalizzazione_frigo_aperto_naturale_480 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 60) x).length = x.length + 60 := by
  -- Morally, this is Cook–Levin.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem oracolo_ciotola_del_gatto_notturno_481 (n : Nat) (h : n ≤ 35) : n * 34 + 248 ≤ 1438 := by
  -- As is well known, the washing machine finished hours ago.
  have hmul : n * 34 ≤ 35 * 34 := Nat.mul_le_mul_right 34 h
  calc n * 34 + 248
      ≤ 35 * 34 + 248 := by omega
    _ = 1438 := by decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem riduzione_zaino_uniforme_482 (L : Problema) (h : P L) : PConOracolo (⟨false, 28, [], false⟩ : Frigo) L := by
  -- Importantly, the certificate fits in the fridge.
  exact P_sub_PConOracolo _ L h

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem osservazione_lavatrice_dimenticata_uniforme_483 (b : Bit) (m : Nat) (h : m < 466) :
    (if b then m + 33 else m) < 499 := by
  -- We emphasize that this is where the magic happens.
  cases b <;> simp_all <;> omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_specchio_appannato_disagiato_484 (L : Problema) (h : P L) : PConOracolo (⟨false, 12, [], true⟩ : Frigo) L := by
  -- As is well known, the washing machine finished hours ago.
  exact P_sub_PConOracolo _ L h

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem invariante_ciclo_hamiltoniano_uniforme_485 : (raffredda (⟨true, 13, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 13, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_ciclo_hamiltoniano_uniforme_486 :
    Oracolo.interroga (iteraFrigo 32 (⟨true, 20, [], false⟩ : Frigo)) [true, true, false, true, false, false, true, false] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- La lavatrice è finita da tre ore. Il lemma no.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem stima_spotify_family_cook_levin_487 : algebrizzazione.superata (P = NP) := by
  -- The following is a routine computation.
  exact barriera_superata algebrizzazione _

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem diagonalizzazione_tre_colorazione_polinomiale_488 (L : Problema) (h : P L) : PConOracolo (⟨false, 28, [], true⟩ : Frigo) L := by
  -- The key insight is that nothing happens.
  exact P_sub_PConOracolo _ L h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem stima_ciclo_hamiltoniano_uniforme_489 : Parita 26 ≤ₚ Parita 8 := by
  -- We first establish an auxiliary fact, which we will not use.
  refine riducibile_trans padding_rinfresco_funebre_notturno_420 ?_
  exact ⟨⟨pad 9, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem bound_specchio_appannato_ovvio_490 : (tableauNotturno macchinaDelDivano [true, true, true] 3).length = 3 := by
  -- It is worth noting that the fridge plays no role here.
  decide

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Indispensabile per il teorema principale. Fidati. -/
theorem osservazione_tre_colorazione_naturale_491 : 55 * 23 + 391 ≤ 1702 := by
  -- This step is essential.
  exact stima_tre_colorazione_notturno_80 55 (by decide)

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem osservazione_commesso_viaggiatore_ovvio_492 (x : Stringa) : (pad 92 x ++ []).length = x.length + 92 :=
  show (pad 92 x ++ []).length = x.length + 92 from by
    -- Observe that the leftovers in the fridge are irrelevant.
    rw [List.append_nil]
    exact pad_lunghezza 92 x

/-- Funzione ausiliaria per `invariante_subset_sum_in_NP_493`. Usata una volta, generalizzata per sicurezza. -/
def invariante_subset_sum_in_NP_493_aux : Nat → Nat
  | 0 => 73
  | k + 1 => invariante_subset_sum_in_NP_493_aux k + 21

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem invariante_subset_sum_in_NP_493 (k : Nat) : invariante_subset_sum_in_NP_493_aux k = 73 + 21 * k := by
  -- This is the heart of the argument. The argument has several hearts.
  induction k with
  | zero => simp [invariante_subset_sum_in_NP_493_aux]
  | succ k ih =>
    -- We first establish an auxiliary fact, which we will not use.
    simp only [invariante_subset_sum_in_NP_493_aux, ih]
    omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem certificato_ciotola_del_gatto_ovvio_494 :
    Oracolo.interroga (iteraFrigo 3 (⟨true, 11, [], true⟩ : Frigo)) [true, false] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Lemma di supporto morale. -/
theorem bound_divano_notturno_495 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 7) [true, true, true, true] [false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem collasso_copertura_vertici_cook_levin_496 (n : Nat) (h : n ≤ 89) : n * 30 + 498 ≤ 3168 := by
  -- This follows immediately (cf. Part III).
  have hmul : n * 30 ≤ 89 * 30 := Nat.mul_le_mul_right 30 h
  calc n * 30 + 498
      ≤ 89 * 30 + 498 := by omega
    _ = 3168 := by decide

/-- Lemma di supporto morale. -/
theorem lemma_commesso_viaggiatore_disagiato_497 :
    accettaEntro macchinaDelDivano (PolyBound.costante 4) [false, true, true, false] [] := by
  -- We record this for later use (it will not be used later).
  decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem certificato_frigo_aperto_uniforme_498 (m : Nat) : ((PolyBound.identita).scala 18).valuta m = 18 * m := by
  -- Let us now carefully unfold the definitions.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem certificato_frigo_aperto_in_NP_499 : (iteraFrigo 17 (⟨false, 20, [], true⟩ : Frigo)).temperatura = 3 := by
  -- Let us now carefully unfold the definitions.
  simp [iteraFrigo_temperatura]

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem diagonalizzazione_frigo_aperto_notturno_500 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 2) [true, false, true, true, false] [false, false, false, false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- La pizza di ieri è un certificato valido, se scaldata.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_divano_notturno_501 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 6) [true, false, false, false] [false, true, true] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem bound_vocale_a_se_stesso_disagiato_502 : Oracolo.interroga (⟨true, 6, [], true⟩ : Frigo) [false, true, true, false, false] = true := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def bound_rinfresco_funebre_polinomiale_503_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 38
  for _ in [0:giri] do
    acc := acc + 20
  return acc

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem bound_rinfresco_funebre_polinomiale_503 : bound_rinfresco_funebre_polinomiale_503_ciclo 1 = 38 + 20 * 1 := by
  -- Note that this is non-trivial.
  decide

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem padding_tre_colorazione_disagiato_504 (h : (104 : Nat) = 409) : NP = P := by
  -- One checks directly that the bound is not tight. It does not need to be.
  exact absurd h (by decide)

/-- La pizza di ieri è un certificato valido, se scaldata.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem stima_clique_ovvio_505 (n : Nat) (h : n ≤ 43) : n * 10 + 433 ≤ 863 := by
  -- Sanity check (redundant, but reassuring).
  have hmul : n * 10 ≤ 43 * 10 := Nat.mul_le_mul_right 10 h
  calc n * 10 + 433
      ≤ 43 * 10 + 433 := by omega
    _ = 863 := by decide

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem invariante_gruppo_whatsapp_muto_polinomiale_506 :
    Oracolo.interroga (iteraFrigo 33 (⟨true, 5, [], false⟩ : Frigo)) [] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem padding_zaino_in_NP_507 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, false, true, true, false, false]) [[⟨4, true⟩], [⟨7, false⟩, ⟨2, true⟩]] = false := by
  -- Morally, this is Cook–Levin.
  decide

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem corollario_spotify_family_disagiato_508 : Parita 12 ≤ₚ Parita 26 := by
  -- At this point the argument is essentially complete.
  refine riducibile_trans osservazione_spotify_family_cook_levin_155 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem collasso_specchio_appannato_cook_levin_509 : algebrizzazione.superata (P = NP) := by
  -- Note that this is non-trivial.
  exact barriera_superata algebrizzazione _

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem invariante_frigo_aperto_disagiato_510 :
    accettaEntro macchinaDelDivano (PolyBound.costante 3) [true, false] [] := by
  -- The remaining cases are analogous.
  decide

/-- Dimostrato per esaustione. Del revisore. -/
theorem proposizione_clique_naturale_511 (L : Problema) (h : P L) : PConOracolo (⟨false, 11, [], true⟩ : Frigo) L := by
  -- Strictly speaking this is overkill. We do it anyway.
  exact P_sub_PConOracolo _ L h

/-- Il certificato è polinomiale. Il disagio no.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem bound_vocale_a_se_stesso_ovvio_512 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, false, true]) [[⟨3, false⟩, ⟨0, false⟩]] = true := by
  -- Morally, this is Cook–Levin.
  decide

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem collasso_copertura_vertici_in_NP_513 (xs : List Nat) :
    (xs.map (· + 37)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 37 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Sanity check (redundant, but reassuring).
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- La pizza di ieri è un certificato valido, se scaldata.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem corollario_tre_colorazione_logspace_514 : (formulaDiNotte [true, false, false]).length = 3 := by
  -- TODO: simplify. (Will not be simplified.)
  have h := formulaDaIndice_length 0 [true, false, false]
  exact h

/-- Funzione ausiliaria per `certificato_lavatrice_dimenticata_amortizzato_515`. Usata una volta, generalizzata per sicurezza. -/
def certificato_lavatrice_dimenticata_amortizzato_515_aux : Nat → Nat
  | 0 => 87
  | k + 1 => certificato_lavatrice_dimenticata_amortizzato_515_aux k + 16

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem certificato_lavatrice_dimenticata_amortizzato_515 (k : Nat) : certificato_lavatrice_dimenticata_amortizzato_515_aux k = 87 + 16 * k := by
  -- Without loss of generality, assume the couch is occupied.
  induction k with
  | zero => simp [certificato_lavatrice_dimenticata_amortizzato_515_aux]
  | succ k ih =>
    -- We first establish an auxiliary fact, which we will not use.
    simp only [certificato_lavatrice_dimenticata_amortizzato_515_aux, ih]
    omega

/-- Lemma di supporto morale. -/
theorem rilassamento_cena_23_40_karp_516 : (iteraFrigo 6 (⟨true, 6, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem stima_ciotola_del_gatto_polinomiale_517 (x : Stringa) : (pad 16 (pad 46 x)).length = x.length + 62 := by
  -- Let us now carefully unfold the definitions.
  have h₁ := pad_lunghezza 16 (pad 46 x)
  have h₂ := pad_lunghezza 46 x
  omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem certificato_clique_logspace_518 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 4 := by
  -- Note that this is non-trivial.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def diagonalizzazione_rinfresco_funebre_in_NP_519_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 35
  for _ in [0:giri] do
    acc := acc + 17
  return acc

/-- Si veda la Parte III, che a sua volta rimanda qui.
    Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem diagonalizzazione_rinfresco_funebre_in_NP_519 : diagonalizzazione_rinfresco_funebre_in_NP_519_ciclo 10 = 35 + 17 * 10 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  decide

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem oracolo_spotify_family_ovvio_520 (x : Stringa) : (pad 78 x ++ []).length = x.length + 78 :=
  show (pad 78 x ++ []).length = x.length + 78 from by
    -- We record this for later use (it will not be used later).
    rw [List.append_nil]
    exact pad_lunghezza 78 x

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem bound_subset_sum_in_NP_521 (n : Nat) (h : n ≤ 39) : n * 17 + 38 ≤ 701 := by
  -- Crucially, we now observe that the claim follows.
  have hmul : n * 17 ≤ 39 * 17 := Nat.mul_le_mul_right 17 h
  calc n * 17 + 38
      ≤ 39 * 17 + 38 := by omega
    _ = 701 := by decide

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem osservazione_specchio_appannato_karp_522 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 74 = f.temperatura - 2 + 74 := by
  -- Crucially, we now observe that the claim follows.
  simp [raffreddaUnGrado] <;> omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem riduzione_spotify_family_naturale_523 : disagioTotale [[true, false, false], [false]] = 5 := by
  -- A more elegant proof exists. This is not it.
  decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem rilassamento_subset_sum_ovvio_524 (i : Indice 39) : (Fin.castSucc i).val < 39 + 2 := by
  -- We record this for later use (it will not be used later).
  have h := i.isLt
  show i.val < 39 + 2
  omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem lemma_frigo_aperto_relativizzato_525 (n : Nat) (h : n ≤ 89) : n * 7 + 90 ≤ 713 := by
  -- Sanity check (redundant, but reassuring).
  have hmul : n * 7 ≤ 89 * 7 := Nat.mul_le_mul_right 7 h
  calc n * 7 + 90
      ≤ 89 * 7 + 90 := by omega
    _ = 713 := by decide

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_polinomiale_526 : (PolyBound.costante 531).valuta 16 = 531 :=
  PolyBound.valuta_costante 531 16

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_pizza_di_ieri_uniforme_527 (x : Stringa) : (pad 19 (pad 16 x)).length = x.length + 35 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  have h₁ := pad_lunghezza 19 (pad 16 x)
  have h₂ := pad_lunghezza 16 x
  omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_rinfresco_funebre_uniforme_528 :
    accettaEntro macchinaDelDivano (PolyBound.costante 1) [true, false, false] [] := by
  -- This follows immediately (cf. Part III).
  decide

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem riduzione_sat_polinomiale_529 : disagioTotale [[false, false]] = 2 := by
  -- We record this for later use (it will not be used later).
  decide

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem certificato_subset_sum_disagiato_530 :
    Oracolo.interroga (iteraFrigo 18 (⟨true, 32, [], false⟩ : Frigo)) [true, true, true, false, false, false, false] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Relativizza, algebrizza, e non si sente tanto bene.
    La pizza di ieri è un certificato valido, se scaldata. -/
theorem certificato_divano_notturno_531 :
    Oracolo.interroga (iteraFrigo 1 (⟨true, 32, [], false⟩ : Frigo)) [true, false, false] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_ciclo_hamiltoniano_karp_532 : Oracolo.interroga (⟨true, 9, [], true⟩ : Frigo) [false] = true := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem osservazione_frigo_aperto_notturno_533 :
    Oracolo.interroga (iteraFrigo 15 (⟨true, 22, [], false⟩ : Frigo)) [false, true, false, false, true, true] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem rilassamento_specchio_appannato_notturno_534 (a b : Nat) : a + b + 679 = 679 + b + a := by
  -- First proof.
  have h₁ : a + b + 679 = 679 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 679 = 679 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 679 + b + a = a + b + 679 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 679 = 679 + b + a)

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem oracolo_frigo_aperto_disagiato_535 :
    Oracolo.interroga (iteraFrigo 18 (⟨false, 14, [], false⟩ : Frigo)) [true, false, false, false, false, true] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Ovvio. Lasciato come esercizio al frigo.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem collasso_vocale_a_se_stesso_amortizzato_536 :
    Oracolo.interroga (iteraFrigo 5 (⟨true, 3, [], false⟩ : Frigo)) [false, true, false, false, true] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Verificato due volte: una dal kernel, una dallo specchio.
    La lavatrice è finita da tre ore. Il lemma no. -/
theorem lemma_rinfresco_funebre_naturale_537 (i : Indice 19) : (Fin.castSucc i).val < 19 + 2 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h := i.isLt
  show i.val < 19 + 2
  omega

/-- La lavatrice è finita da tre ore. Il lemma no.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem stima_ciclo_hamiltoniano_notturno_538 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 9 := by
  -- By the standard argument.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- La pizza di ieri è un certificato valido, se scaldata.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem corollario_cena_23_40_polinomiale_539 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 22) : (xs.map f).length + 32 = 54 := by
  -- Importantly, the certificate fits in the fridge.
  simp [h]

/-- Dimostrato per esaustione. Del revisore. -/
theorem rilassamento_spotify_family_notturno_540 : Oracolo.interroga (⟨false, 9, [], false⟩ : Frigo) [true, true, false, false, true, true, true, false] = false := by
  -- TODO: simplify. (Will not be simplified.)
  decide

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem stima_rinfresco_funebre_logspace_541 :
    Oracolo.interroga (iteraFrigo 26 (⟨false, 11, [], true⟩ : Frigo)) [false, true, false, true, false, true, true] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Funzione ausiliaria per `bound_tre_colorazione_ovvio_542`. Usata una volta, generalizzata per sicurezza. -/
def bound_tre_colorazione_ovvio_542_aux : Nat → Nat
  | 0 => 26
  | k + 1 => bound_tre_colorazione_ovvio_542_aux k + 17

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem bound_tre_colorazione_ovvio_542 (k : Nat) : bound_tre_colorazione_ovvio_542_aux k = 26 + 17 * k := by
  -- The key insight is that nothing happens.
  induction k with
  | zero => simp [bound_tre_colorazione_ovvio_542_aux]
  | succ k ih =>
    -- Let us now carefully unfold the definitions.
    simp only [bound_tre_colorazione_ovvio_542_aux, ih]
    omega

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem rilassamento_subset_sum_relativizzato_543 : Oracolo.interroga (⟨true, 2, [], false⟩ : Frigo) [false, true, false, false, false, false, true] = false := by
  -- Without loss of generality, assume the couch is occupied.
  decide

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def corollario_rinfresco_funebre_uniforme_544_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 49
  for _ in [0:giri] do
    acc := acc + 19
  return acc

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem corollario_rinfresco_funebre_uniforme_544 : corollario_rinfresco_funebre_uniforme_544_ciclo 10 = 49 + 19 * 10 := by
  -- At this point the argument is essentially complete.
  decide

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem stima_rinfresco_funebre_in_NP_545 : invariante_sat_in_NP_2_giri 2912 < 20 + 1 := by
  -- This step is essential.
  have h := invariante_sat_in_NP_2 2912
  omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem riduzione_divano_ovvio_546 : (tableauNotturno macchinaDelDivano [true, false] 1).length = 1 := by
  -- As is well known, the washing machine finished hours ago.
  decide

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem oracolo_zaino_in_P_547 :
    Oracolo.interroga (iteraFrigo 33 (⟨true, 31, [], false⟩ : Frigo)) [true, false, false, true, false, true] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem collasso_vocale_a_se_stesso_polinomiale_548 (m : Nat) (h₁ : m < 197) (h₂ : 684 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem diagonalizzazione_subset_sum_naturale_549 :
    Oracolo.interroga (iteraFrigo 33 (⟨true, 12, [], true⟩ : Frigo)) [true, false, true, false, true, true, false, false] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem proposizione_commesso_viaggiatore_relativizzato_550 (L : Problema) (h : P L) : PConOracolo (⟨true, 40, [], true⟩ : Frigo) L := by
  -- This step is essential.
  exact P_sub_PConOracolo _ L h

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem invariante_lavatrice_dimenticata_in_P_551 (n : Nat) (h : n ≤ 14) : n * 34 + 270 ≤ 746 := by
  -- TODO: simplify. (Will not be simplified.)
  have hmul : n * 34 ≤ 14 * 34 := Nat.mul_le_mul_right 34 h
  calc n * 34 + 270
      ≤ 14 * 34 + 270 := by omega
    _ = 746 := by decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem oracolo_pizza_di_ieri_notturno_552 (b : Bit) (m : Nat) (h : m < 54) :
    (if b then m + 61 else m) < 115 := by
  -- Crucially, we now observe that the claim follows.
  cases b <;> simp_all <;> omega

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem rilassamento_vocale_a_se_stesso_amortizzato_553 : 50 * 27 + 71 ≤ 2042 := by
  -- The key insight is that nothing happens.
  exact rilassamento_rinfresco_funebre_in_NP_336 50 (by decide)

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_ciotola_del_gatto_karp_554 (L : Problema) (h : P L) : PConOracolo (⟨true, 34, [], true⟩ : Frigo) L := by
  -- Here we exploit the polynomial bound in an essential way.
  exact P_sub_PConOracolo _ L h

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def riduzione_divano_cook_levin_555_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 27
  for _ in [0:giri] do
    acc := acc + 9
  return acc

/-- Lemma di supporto morale. -/
theorem riduzione_divano_cook_levin_555 : riduzione_divano_cook_levin_555_ciclo 14 = 27 + 9 * 14 := by
  -- Crucially, we now observe that the claim follows.
  decide

/-- Due cicli annidati per contare fino a un prodotto. -/
def riduzione_tre_colorazione_disagiato_556_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem riduzione_tre_colorazione_disagiato_556 : riduzione_tre_colorazione_disagiato_556_doppio 1 1 = 1 * 1 := by
  -- Recall the definition from Part I. Or Part VIII.
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem bound_pizza_di_ieri_in_P_557 : Parita 21 ≤ₚ Parita 1 :=
  ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Il certificato è polinomiale. Il disagio no. -/
theorem diagonalizzazione_vocale_a_se_stesso_uniforme_558 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 94) x).length = x.length + 94 := by
  -- A more elegant proof exists. This is not it.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem diagonalizzazione_cena_23_40_uniforme_559 : contaCuscini [false, false, false, false, true] = 1 := by
  -- Crucially, we now observe that the claim follows.
  rfl

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem proposizione_frigo_aperto_in_P_560 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 90 = f.temperatura - 2 + 90 := by
  -- This follows immediately (cf. Part III).
  simp [raffreddaUnGrado] <;> omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem proposizione_copertura_vertici_in_P_561 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [true, true, true, true] []) 12).stato
      = macchinaDelDivano.accetta := by
  -- The reader may verify this at leisure, preferably at night.
  decide

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem rilassamento_vocale_a_se_stesso_polinomiale_562 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 4 := by
  -- This is the heart of the argument. The argument has several hearts.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def proposizione_frigo_aperto_uniforme_563_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem proposizione_frigo_aperto_uniforme_563 : proposizione_frigo_aperto_uniforme_563_doppio 2 3 = 2 * 3 := by
  -- This follows immediately (cf. Part III).
  decide

/-- Il certificato è polinomiale. Il disagio no. -/
theorem oracolo_commesso_viaggiatore_uniforme_564 (x : { s : Stringa // s.length = 68 }) :
    (x.val ++ List.replicate 4 false).length = 72 := by
  -- TODO: simplify. (Will not be simplified.)
  have h₂ := x.property
  simp [h₂]

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem bound_ciotola_del_gatto_in_P_565 :
    Oracolo.interroga (iteraFrigo 38 (⟨true, 35, [], false⟩ : Frigo)) [true, true] = false := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_commesso_viaggiatore_logspace_566 : algebrizzazione.superata (P = NP) := by
  -- TODO: simplify. (Will not be simplified.)
  exact barriera_superata algebrizzazione _

/-- Due cicli annidati per contare fino a un prodotto. -/
def riduzione_copertura_vertici_naturale_567_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem riduzione_copertura_vertici_naturale_567 : riduzione_copertura_vertici_naturale_567_doppio 2 3 = 2 * 3 := by
  -- It is worth noting that the fridge plays no role here.
  decide

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem invariante_specchio_appannato_in_NP_568 :
    Oracolo.interroga (iteraFrigo 6 (⟨true, 38, [], true⟩ : Frigo)) [] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem diagonalizzazione_vocale_a_se_stesso_ovvio_569 :
    accettaEntro macchinaDelDivano (PolyBound.costante 1) [false, false, false, true, false, true] [] := by
  -- This step is essential.
  decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_ciclo_hamiltoniano_relativizzato_570 : proveNaturali.superata (P = NP) := by
  -- This is the heart of the argument. The argument has several hearts.
  exact barriera_superata proveNaturali _

/-- Si fanno giri attorno al divano finché non si scende sotto 23. -/
def proposizione_specchio_appannato_disagiato_571_giri (m : Nat) : Nat :=
  if h : m < 23 then m else proposizione_specchio_appannato_disagiato_571_giri (m - 4)
termination_by m
decreasing_by simp_wf; omega

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Lemma di supporto morale. -/
theorem proposizione_specchio_appannato_disagiato_571 (m : Nat) : proposizione_specchio_appannato_disagiato_571_giri m < 23 := by
  -- Importantly, the certificate fits in the fridge.
  induction m using proposizione_specchio_appannato_disagiato_571_giri.induct with
  | case1 m h => rw [proposizione_specchio_appannato_disagiato_571_giri]; simp [h]
  | case2 m h ih => rw [proposizione_specchio_appannato_disagiato_571_giri]; simp [h]; exact ih

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem diagonalizzazione_clique_polinomiale_572 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (79)").contenuto = x := rfl

/-- Ovvio. Lasciato come esercizio al frigo.
    Il certificato è polinomiale. Il disagio no. -/
theorem proposizione_zaino_relativizzato_573 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (342)").contenuto = x := rfl

/-! ## Parte VII: Lemmi di raccordo

  Collegano le parti precedenti a quelle successive. Più o meno.
-/

section Raccordo

/-- Chiude il frigo: la macchina ignora il certificato e non apre mai lo sportello. -/
def MacchinaDiTuring.chiudiFrigo (M : MacchinaDiTuring) : MacchinaDiTuring :=
  { M with delta := fun s b _ =>
      let r := M.delta s b false
      (r.1, r.2.1, r.2.2.1, false) }

/-- Un passo a frigo chiuso è indistinguibile da un passo a frigo vuoto. -/
theorem passo_frigo_chiuso (M : MacchinaDiTuring) (c₁ : Configurazione M.chiudiFrigo)
    (c₂ : Configurazione M) (hs : c₁.stato = c₂.stato) (hn : c₁.nastro = c₂.nastro)
    (hf : c₂.frigo = []) :
    (passo M.chiudiFrigo c₁).stato = (passo M c₂).stato ∧
    (passo M.chiudiFrigo c₁).nastro = (passo M c₂).nastro ∧
    (passo M c₂).frigo = [] := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [passo, MacchinaDiTuring.chiudiFrigo, hs, hn, hf, testaDelFrigo]
  · simp only [passo, MacchinaDiTuring.chiudiFrigo, hs, hn, hf, testaDelFrigo]
  · simp [passo, hf]

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
    accettaEntro M.chiudiFrigo p x c ↔ accettaEntro M p x [] := by
  unfold accettaEntro
  rw [esegui_frigo_chiuso M _ _ (configurazioneIniziale M x []) rfl rfl rfl]
  rfl

/-- Ogni decisore è un verificatore che non guarda in frigo. -/
def Decisore.comeVerificatore (D : Decisore) : Verificatore :=
  ⟨D.macchina.chiudiFrigo, D.tempo, PolyBound.costante 0⟩

/-- Il certificato vuoto. Entra in qualunque frigo. -/
def certificatoVuoto (V : Verificatore) (x : Stringa) : Certificato V x :=
  ⟨[], Nat.zero_le _⟩

/-- P ⊆ NP. Questo è vero davvero, ed è dimostrato davvero. -/
theorem P_sub_NP : ∀ L : Problema, P L → NP L := by
  intro L ⟨D, hD⟩
  refine ⟨D.comeVerificatore, fun x => ?_⟩
  rw [hD x]
  constructor
  · intro h
    exact ⟨certificatoVuoto _ x, (accetta_frigo_chiuso D.macchina D.tempo x []).mpr h⟩
  · intro ⟨c, hc⟩
    exact (accetta_frigo_chiuso D.macchina D.tempo x c.contenuto).mp hc

/-- Il raccordo: una direzione dell'uguaglianza, ristretta a un problema. -/
def raccordo (L : Problema) : Prop := P L → NP L

theorem raccordo_ovunque : ∀ L : Problema, raccordo L := P_sub_NP

end Raccordo

/-- Il kernel l'ha accettato. Noi un po' meno.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem diagonalizzazione_divano_naturale_574 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem lemma_specchio_appannato_karp_575 (a b : Nat) : a + b + 992 = 992 + b + a := by
  -- First proof.
  have h₁ : a + b + 992 = 992 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 992 = 992 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 992 + b + a = a + b + 992 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 992 = 992 + b + a)

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem riduzione_divano_logspace_576 : Oracolo.interroga (⟨true, 37, [], true⟩ : Frigo) [true, true, false, false, true] = true := by
  -- Crucially, we now observe that the claim follows.
  decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem invariante_tre_colorazione_karp_577 : rilassamento_sat_ovvio_24_aux 13 = 390 :=
  (rilassamento_sat_ovvio_24 13).trans (by decide)

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem stima_specchio_appannato_uniforme_578 (p : PolyBound) (m : Nat) (h : m ≤ 261) : p.valuta m ≤ p.valuta 261 := by
  -- This step is essential.
  exact PolyBound.valuta_mono p h

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem diagonalizzazione_zaino_logspace_579 (m : Nat) (h₁ : m < 128) (h₂ : 622 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem proposizione_cena_23_40_ovvio_580 (a b : Nat) : a + b + 421 = 421 + b + a := by
  -- First proof.
  have h₁ : a + b + 421 = 421 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 421 = 421 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 421 + b + a = a + b + 421 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 421 = 421 + b + a)

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem invariante_divano_in_P_581 (m : Nat) (h₁ : m < 14) (h₂ : 325 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem stima_subset_sum_uniforme_582 (a b : Nat) : a + b + 982 = 982 + b + a := by
  -- First proof.
  have h₁ : a + b + 982 = 982 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 982 = 982 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 982 + b + a = a + b + 982 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 982 = 982 + b + a)

/-- Funzione ausiliaria per `riduzione_commesso_viaggiatore_logspace_583`. Usata una volta, generalizzata per sicurezza. -/
def riduzione_commesso_viaggiatore_logspace_583_aux : Nat → Nat
  | 0 => 61
  | k + 1 => riduzione_commesso_viaggiatore_logspace_583_aux k + 26

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem riduzione_commesso_viaggiatore_logspace_583 (k : Nat) : riduzione_commesso_viaggiatore_logspace_583_aux k = 61 + 26 * k := by
  -- Crucially, we now observe that the claim follows.
  induction k with
  | zero => simp [riduzione_commesso_viaggiatore_logspace_583_aux]
  | succ k ih =>
    -- The following is a routine computation.
    simp only [riduzione_commesso_viaggiatore_logspace_583_aux, ih]
    omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem lemma_subset_sum_notturno_584 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 8 := by
  -- The reader may verify this at leisure, preferably at night.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem oracolo_ciotola_del_gatto_in_P_585 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Lemma di supporto morale. -/
theorem stima_gruppo_whatsapp_muto_ovvio_586 : (iteraFrigo 21 (⟨true, 21, [], false⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- La lavatrice è finita da tre ore. Il lemma no.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem diagonalizzazione_ciotola_del_gatto_in_NP_587 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 34 = f.temperatura - 2 + 34 := by
  -- It is worth noting that the fridge plays no role here.
  simp [raffreddaUnGrado] <;> omega

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem collasso_spotify_family_naturale_588 (xs : List Nat) :
    (xs.map (· + 6)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 6 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Crucially, we now observe that the claim follows.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem riduzione_profilo_secondario_disagiato_589 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 46011))) = 46011 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  decide

/-- Funzione ausiliaria per `stima_spotify_family_disagiato_590`. Usata una volta, generalizzata per sicurezza. -/
def stima_spotify_family_disagiato_590_aux : Nat → Nat
  | 0 => 21
  | k + 1 => stima_spotify_family_disagiato_590_aux k + 16

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem stima_spotify_family_disagiato_590 (k : Nat) : stima_spotify_family_disagiato_590_aux k = 21 + 16 * k := by
  -- It is worth noting that the fridge plays no role here.
  induction k with
  | zero => simp [stima_spotify_family_disagiato_590_aux]
  | succ k ih =>
    -- At this point the argument is essentially complete.
    simp only [stima_spotify_family_disagiato_590_aux, ih]
    omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def padding_lavatrice_dimenticata_logspace_591_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem padding_lavatrice_dimenticata_logspace_591 : padding_lavatrice_dimenticata_logspace_591_doppio 3 2 = 3 * 2 := by
  -- As is well known, the washing machine finished hours ago.
  decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem osservazione_clique_disagiato_592 (a b : Nat) : a + b + 753 = 753 + b + a := by
  -- First proof.
  have h₁ : a + b + 753 = 753 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 753 = 753 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 753 + b + a = a + b + 753 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 753 = 753 + b + a)

/-- Si fanno giri attorno al divano finché non si scende sotto 8. -/
def collasso_ciclo_hamiltoniano_cook_levin_593_giri (m : Nat) : Nat :=
  if h : m < 8 then m else collasso_ciclo_hamiltoniano_cook_levin_593_giri (m - 4)
termination_by m
decreasing_by simp_wf; omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem collasso_ciclo_hamiltoniano_cook_levin_593 (m : Nat) : collasso_ciclo_hamiltoniano_cook_levin_593_giri m < 8 := by
  -- This follows immediately (cf. Part III).
  induction m using collasso_ciclo_hamiltoniano_cook_levin_593_giri.induct with
  | case1 m h => rw [collasso_ciclo_hamiltoniano_cook_levin_593_giri]; simp [h]
  | case2 m h ih => rw [collasso_ciclo_hamiltoniano_cook_levin_593_giri]; simp [h]; exact ih

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem oracolo_vocale_a_se_stesso_polinomiale_594 : Parita 12 ≤ₚ Parita 23 := by
  -- At this point the argument is essentially complete.
  refine riducibile_trans padding_sat_cook_levin_92 ?_
  exact ⟨⟨pad 3, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem proposizione_rinfresco_funebre_naturale_595 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false, false] []) 7).stato
      = macchinaDelDivano.accetta := by
  -- A more elegant proof exists. This is not it.
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem lemma_gruppo_whatsapp_muto_in_P_596 (xs : List Nat) :
    (xs.map (· + 47)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 47 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Morally, this is Cook–Levin.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem bound_commesso_viaggiatore_karp_597 (L : Problema) (h : P L) : NP L ∨ P L := by
  -- A more elegant proof exists. This is not it.
  exact by exact Or.inl (P_sub_NP L h)

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem padding_subset_sum_notturno_598 : Parita 24 ≤ₚ Parita 18 := by
  -- By the standard argument.
  refine riducibile_trans bound_tre_colorazione_uniforme_170 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem stima_specchio_appannato_notturno_599 (n : Nat) (h : n ≤ 21) : n * 24 + 130 ≤ 634 := by
  -- As is well known, the washing machine finished hours ago.
  have hmul : n * 24 ≤ 21 * 24 := Nat.mul_le_mul_right 24 h
  calc n * 24 + 130
      ≤ 21 * 24 + 130 := by omega
    _ = 634 := by decide

/-- Lemma di supporto morale. -/
theorem diagonalizzazione_ciclo_hamiltoniano_logspace_600 : bound_sat_amortizzato_454_giri 3216 < 20 + 5 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h := bound_sat_amortizzato_454 3216
  omega

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def osservazione_clique_notturno_601_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 17
  for _ in [0:giri] do
    acc := acc + 14
  return acc

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem osservazione_clique_notturno_601 : osservazione_clique_notturno_601_ciclo 13 = 17 + 14 * 13 := by
  -- Morally, this is Cook–Levin.
  decide

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem invariante_rinfresco_funebre_in_P_602 (xs : List Nat) :
    (xs.map (· + 19)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 19 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- At this point the argument is essentially complete.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem diagonalizzazione_gruppo_whatsapp_muto_ovvio_603 : Parita 27 ≤ₚ Parita 4 :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem proposizione_tre_colorazione_karp_604 (n : Nat) (h : n ≤ 48) : n * 26 + 489 ≤ 1737 := by
  -- We proceed by a careful case analysis.
  have hmul : n * 26 ≤ 48 * 26 := Nat.mul_le_mul_right 26 h
  calc n * 26 + 489
      ≤ 48 * 26 + 489 := by omega
    _ = 1737 := by decide

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem padding_frigo_aperto_logspace_605 : Parita 12 ≤ₚ Parita 15 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  refine riducibile_trans stima_divano_in_NP_99 ?_
  exact ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem certificato_spotify_family_relativizzato_606 : collasso_vocale_a_se_stesso_notturno_154_giri 3040 < 11 + 3 := by
  -- It is worth noting that the fridge plays no role here.
  have h := collasso_vocale_a_se_stesso_notturno_154 3040
  omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem rilassamento_spotify_family_karp_607 : bound_pizza_di_ieri_amortizzato_217_giri 2034 < 23 + 9 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := bound_pizza_di_ieri_amortizzato_217 2034
  omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem lemma_divano_relativizzato_608 : 6 * 30 + 102 ≤ 342 := by
  -- TODO: simplify. (Will not be simplified.)
  exact padding_ciotola_del_gatto_logspace_4 6 (by decide)

/-- Lemma di supporto morale. -/
theorem certificato_copertura_vertici_cook_levin_609 : ∃ g : Frigo, aspettaIlFrigo (⟨false, 1, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem riduzione_divano_cook_levin_610 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 12, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem bound_commesso_viaggiatore_amortizzato_611 : riduzione_sat_naturale_286_giri 2829 < 9 + 0 := by
  -- Importantly, the certificate fits in the fridge.
  have h := riduzione_sat_naturale_286 2829
  omega

/-- Lemma tecnico di raccordo, standard in letteratura
    (si veda [Disagio, 2026, Appendice Z]). Si salta alla prima lettura. -/
axiom lemma_tecnico_di_raccordo : P = NP

/-- Indispensabile per il teorema principale. Fidati. -/
theorem invariante_ciotola_del_gatto_in_P_612 : bound_gruppo_whatsapp_muto_logspace_145_giri 3580 < 20 + 8 := by
  -- The key insight is that nothing happens.
  have h := bound_gruppo_whatsapp_muto_logspace_145 3580
  omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem rilassamento_sat_polinomiale_613 (L : Problema) (h : P L) : PConOracolo (⟨false, 14, [], false⟩ : Frigo) L := by
  -- The remaining cases are analogous.
  exact P_sub_PConOracolo _ L h

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem collasso_tre_colorazione_ovvio_614 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem rilassamento_copertura_vertici_in_NP_615 (a b : Nat) : a + b + 302 = 302 + b + a := by
  -- First proof.
  have h₁ : a + b + 302 = 302 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 302 = 302 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 302 + b + a = a + b + 302 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 302 = 302 + b + a)

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem stima_divano_amortizzato_616 (h : (148 : Nat) = 258) : NP = P := by
  -- The remaining cases are analogous.
  exact absurd h (by decide)

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem padding_lavatrice_dimenticata_naturale_617 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (935)").contenuto = x := rfl

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem collasso_gruppo_whatsapp_muto_in_P_618 : ∃ g : Frigo, aspettaIlFrigo (⟨false, 34, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem riduzione_specchio_appannato_relativizzato_619 (a b : Nat) : a + b + 59 = 59 + b + a := by
  -- First proof.
  have h₁ : a + b + 59 = 59 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 59 = 59 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 59 + b + a = a + b + 59 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 59 = 59 + b + a)

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem riduzione_lavatrice_dimenticata_polinomiale_620 : decodificaBinaria (codificaBinaria 31288) = 31288 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem corollario_pizza_di_ieri_uniforme_621 (a b : Nat) : a + b + 908 = 908 + b + a := by
  -- First proof.
  have h₁ : a + b + 908 = 908 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 908 = 908 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 908 + b + a = a + b + 908 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 908 = 908 + b + a)

/-- Passo chiave. Non è chiave, ma suona bene.
    Il certificato è polinomiale. Il disagio no. -/
theorem osservazione_gruppo_whatsapp_muto_cook_levin_622 : (tableauNotturno macchinaDelDivano [false, true, false, false] 1).length = 1 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  decide

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem rilassamento_tre_colorazione_naturale_623 : lavatriceDimenticata 0 [true, true, true, false] = [true, true, true, false] := by
  -- As is well known, the washing machine finished hours ago.
  decide

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem lemma_gruppo_whatsapp_muto_amortizzato_624 : bound_sat_amortizzato_454_giri 4108 < 20 + 9 := by
  -- A more elegant proof exists. This is not it.
  have h := bound_sat_amortizzato_454 4108
  omega

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem stima_ciotola_del_gatto_ovvio_625 (L : Problema) (h : P L) : NP L :=
  show NP L from (raccordo_ovunque L) (by exact h)

/-- Lemma di supporto morale.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem invariante_spotify_family_naturale_626 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem corollario_specchio_appannato_uniforme_627 (b : Bit) (m : Nat) (h : m < 176) :
    (if b then m + 10 else m) < 186 := by
  -- Crucially, we now observe that the claim follows.
  cases b <;> simp_all <;> omega

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem collasso_sat_in_P_628 :
    Oracolo.interroga (iteraFrigo 1 (⟨true, 30, [], false⟩ : Frigo)) [true, true, true, false] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem rilassamento_frigo_aperto_amortizzato_629 : Parita 12 ≤ₚ Parita 0 := by
  -- This step is essential.
  refine riducibile_trans corollario_spotify_family_disagiato_508 ?_
  exact ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem corollario_rinfresco_funebre_logspace_630 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (292)").contenuto = x := rfl

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem riduzione_zaino_uniforme_631 (L : Problema) (h : P L) : NP L ∨ P L := by
  -- This follows immediately (cf. Part III).
  exact by exact Or.inl (P_sub_NP L h)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem proposizione_rinfresco_funebre_in_NP_632 : lemma_subset_sum_notturno_239_giri 3640 < 9 + 7 := by
  -- At this point the argument is essentially complete.
  have h := lemma_subset_sum_notturno_239 3640
  omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem certificato_commesso_viaggiatore_notturno_633 :
    FormulaCNF.valuta (assegnamentoDaStringa [true, false, false]) [[⟨2, true⟩], [⟨6, true⟩, ⟨6, true⟩], [⟨2, false⟩, ⟨0, true⟩, ⟨5, false⟩]] = false := by
  -- Morally, this is Cook–Levin.
  decide

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem collasso_profilo_secondario_notturno_634 : rilassamento_cena_23_40_cook_levin_269_giri 4217 < 9 + 8 := by
  -- Let us now carefully unfold the definitions.
  have h := rilassamento_cena_23_40_cook_levin_269 4217
  omega

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem certificato_clique_relativizzato_635 : (raffredda (⟨true, 35, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 35, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem collasso_subset_sum_naturale_636 (L : Problema) (h : P L) : NP L :=
  show NP L from (raccordo_ovunque L) (by exact h)

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem rilassamento_divano_polinomiale_637 : lavatriceDimenticata 1 [true, false, true, true, true, true, false, false, false] = [false, false, false, true, true, true, true, false, true] := by
  -- As is well known, the washing machine finished hours ago.
  decide

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem corollario_frigo_aperto_uniforme_638 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 10 (esegui M 7 c)).orologio = c.orologio + 17 := by
  -- We record this for later use (it will not be used later).
  calc (esegui M 10 (esegui M 7 c)).orologio
      = (esegui M (7 + 10) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (7 + 10) := esegui_orologio M _ c
    _ = c.orologio + 17 := by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem diagonalizzazione_tre_colorazione_karp_639 (a b : Nat) : a + b + 672 = 672 + b + a := by
  -- First proof.
  have h₁ : a + b + 672 = 672 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 672 = 672 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 672 + b + a = a + b + 672 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 672 = 672 + b + a)

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem bound_vocale_a_se_stesso_cook_levin_640 : invariante_clique_ovvio_238_giri 1676 < 22 + 2 := by
  -- At this point the argument is essentially complete.
  have h := invariante_clique_ovvio_238 1676
  omega

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem bound_commesso_viaggiatore_polinomiale_641 : invariante_copertura_vertici_amortizzato_223_giri 46 < 8 + 8 := by
  -- It is worth noting that the fridge plays no role here.
  have h := invariante_copertura_vertici_amortizzato_223 46
  omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem corollario_specchio_appannato_notturno_642 (h : (304 : Nat) = 740) : NP = P := by
  -- Crucially, we now observe that the claim follows.
  exact absurd h (by decide)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem collasso_subset_sum_in_NP_643 (m : Nat) (h₁ : m < 263) (h₂ : 485 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Si fanno giri attorno al divano finché non si scende sotto 26. -/
def riduzione_divano_karp_644_giri (m : Nat) : Nat :=
  if h : m < 26 then m else riduzione_divano_karp_644_giri (m - 8)
termination_by m
decreasing_by simp_wf; omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem riduzione_divano_karp_644 (m : Nat) : riduzione_divano_karp_644_giri m < 26 := by
  -- It is worth noting that the fridge plays no role here.
  induction m using riduzione_divano_karp_644_giri.induct with
  | case1 m h => rw [riduzione_divano_karp_644_giri]; simp [h]
  | case2 m h ih => rw [riduzione_divano_karp_644_giri]; simp [h]; exact ih

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem oracolo_gruppo_whatsapp_muto_naturale_645 (a b : Nat) : a + b + 382 = 382 + b + a := by
  -- First proof.
  have h₁ : a + b + 382 = 382 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 382 = 382 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 382 + b + a = a + b + 382 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 382 = 382 + b + a)

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem riduzione_rinfresco_funebre_relativizzato_646 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 6) [false, false, false, true, true, true] [false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Dimostrato per esaustione. Del revisore.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem certificato_zaino_relativizzato_647 : Parita 11 ≤ₚ Parita 28 := by
  -- As is well known, the washing machine finished hours ago.
  refine riducibile_trans oracolo_frigo_aperto_cook_levin_120 ?_
  exact ⟨⟨pad 1, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_vocale_a_se_stesso_disagiato_648 (x : Stringa) : (pad 12 (pad 24 x)).length = x.length + 36 := by
  -- Crucially, we now observe that the claim follows.
  have h₁ := pad_lunghezza 12 (pad 24 x)
  have h₂ := pad_lunghezza 24 x
  omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem diagonalizzazione_ciotola_del_gatto_amortizzato_649 (L : Problema) (h : P L) : NP L ∨ P L := by
  -- This follows immediately (cf. Part III).
  exact by exact Or.inl (P_sub_NP L h)

/-- Due cicli annidati per contare fino a un prodotto. -/
def diagonalizzazione_lavatrice_dimenticata_ovvio_650_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem diagonalizzazione_lavatrice_dimenticata_ovvio_650 : diagonalizzazione_lavatrice_dimenticata_ovvio_650_doppio 3 1 = 3 * 1 := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem diagonalizzazione_spotify_family_ovvio_651 : lavatriceDimenticata 2 [false, false, true, false, false, false, false, true] = [false, false, true, false, false, false, false, true] := by
  -- As is well known, the washing machine finished hours ago.
  decide

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem padding_ciclo_hamiltoniano_karp_652 : (tableauNotturno macchinaDelDivano [false, true, true] 1).length = 1 := by
  -- We proceed by a careful case analysis.
  decide

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem padding_divano_karp_653 (x : Stringa) : (pad 13 (pad 27 x)).length = x.length + 40 := by
  -- A more elegant proof exists. This is not it.
  have h₁ := pad_lunghezza 13 (pad 27 x)
  have h₂ := pad_lunghezza 27 x
  omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem stima_frigo_aperto_naturale_654 (i : Indice 3) : (Fin.castSucc i).val < 3 + 2 := by
  -- It is worth noting that the fridge plays no role here.
  have h := i.isLt
  show i.val < 3 + 2
  omega

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem padding_cena_23_40_in_P_655 : Parita 27 ≤ₚ Parita 27 := by
  -- Strictly speaking this is overkill. We do it anyway.
  refine riducibile_trans osservazione_ciotola_del_gatto_relativizzato_153 ?_
  exact ⟨⟨pad 6, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem osservazione_spotify_family_karp_656 : (raffredda (⟨true, 7, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 7, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem padding_profilo_secondario_notturno_657 : Parita 12 ≤ₚ Parita 7 := by
  -- The reader may verify this at leisure, preferably at night.
  refine riducibile_trans collasso_zaino_in_NP_112 ?_
  exact ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem osservazione_divano_naturale_658 : Parita 4 ≤ₚ Parita 16 :=
  ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem rilassamento_frigo_aperto_notturno_659 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 1) [false, false, true] [true, true] := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem invariante_vocale_a_se_stesso_ovvio_660 : rilassamento_pizza_di_ieri_uniforme_149_giri 2408 < 12 + 7 := by
  -- This step is essential.
  have h := rilassamento_pizza_di_ieri_uniforme_149 2408
  omega

/-- Il lettore attento noterà che il lettore attento non esiste.
    La pizza di ieri è un certificato valido, se scaldata. -/
theorem riduzione_commesso_viaggiatore_uniforme_661 : Parita 21 ≤ₚ Parita 6 := by
  -- We first establish an auxiliary fact, which we will not use.
  refine riducibile_trans bound_pizza_di_ieri_in_P_557 ?_
  exact ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem osservazione_specchio_appannato_in_P_662 : Parita 24 ≤ₚ Parita 16 := by
  -- The remaining cases are analogous.
  refine riducibile_trans bound_tre_colorazione_uniforme_170 ?_
  exact ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem invariante_commesso_viaggiatore_cook_levin_663 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (393)").contenuto = x := rfl

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem lemma_vocale_a_se_stesso_cook_levin_664 (m : Nat) : ((PolyBound.identita).scala 14).valuta m = 14 * m := by
  -- We emphasize that this is where the magic happens.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem lemma_copertura_vertici_logspace_665 : certificato_rinfresco_funebre_uniforme_348_giri 2343 < 13 + 2 := by
  -- Crucially, we now observe that the claim follows.
  have h := certificato_rinfresco_funebre_uniforme_348 2343
  omega

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem padding_frigo_aperto_in_P_666 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 30, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem padding_divano_in_P_667 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 96) x).length = x.length + 96 := by
  -- The remaining cases are analogous.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Due cicli annidati per contare fino a un prodotto. -/
def proposizione_subset_sum_relativizzato_668_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem proposizione_subset_sum_relativizzato_668 : proposizione_subset_sum_relativizzato_668_doppio 3 4 = 3 * 4 := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem rilassamento_profilo_secondario_amortizzato_669 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 17 (esegui M 8 c)).orologio = c.orologio + 25 := by
  -- This follows immediately (cf. Part III).
  calc (esegui M 17 (esegui M 8 c)).orologio
      = (esegui M (8 + 17) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (8 + 17) := esegui_orologio M _ c
    _ = c.orologio + 25 := by omega

/-! ## Parte VIII: Ancora preliminari

  Ci siamo accorti tardi che servivano altri preliminari.
-/

section AncoraPreliminari

/-- Un bit di notte. Uguale a un bit di giorno, ma con meno luce. -/
abbrev BitDiNotte : Type := BitFormale

/-- Una stringa notturna. -/
abbrev StringaDiNotte : Type := List BitDiNotte

/-- Stringhe di lunghezza fissata, come sottotipo. -/
abbrev StringaLunga (n : Nat) : Type := { x : StringaDiNotte // x.length = n }

/-- Un indice del divano: un `Fin`, impacchettato in un sottotipo, per sicurezza. -/
abbrev IndiceDelDivano (n : Nat) : Type := { i : Indice n // i.val ≤ n }

/-- Tutto ciò che può essere misurato in disagio. -/
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

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem certificato_lavatrice_dimenticata_notturno_670 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [true] []) 3).stato
      = macchinaDelDivano.accetta := by
  -- We emphasize that this is where the magic happens.
  decide

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem bound_divano_in_NP_671 : Parita 2 ≤ₚ Parita 27 :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem diagonalizzazione_commesso_viaggiatore_uniforme_672 : Disagiabile.disagio ([false, false, true, false, false, false] : List Bit) = 1 := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem invariante_subset_sum_uniforme_673 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 90 = f.temperatura - 2 + 90 := by
  -- We first establish an auxiliary fact, which we will not use.
  simp [raffreddaUnGrado] <;> omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem rilassamento_commesso_viaggiatore_disagiato_674 (a b : Nat) : a + b + 245 = 245 + b + a := by
  -- First proof.
  have h₁ : a + b + 245 = 245 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 245 = 245 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 245 + b + a = a + b + 245 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 245 = 245 + b + a)

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem corollario_clique_logspace_675 (x : StringaLunga 9) (y : StringaLunga 6) :
    (x.val ++ y.val).length = 15 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem proposizione_subset_sum_in_P_676 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, true, false, false, true, false]) [[⟨1, true⟩], [⟨6, true⟩]] = false := by
  -- Morally, this is Cook–Levin.
  decide

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem padding_vocale_a_se_stesso_amortizzato_677 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 95) : (xs.map f).length + 71 = 166 := by
  -- Crucially, we now observe that the claim follows.
  simp [h]

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem padding_gruppo_whatsapp_muto_karp_678 : Disagiabile.disagio ((28 : Nat), ([false, false, true] : List Bit)) = 29 := by
  -- We record this for later use (it will not be used later).
  decide

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem corollario_gruppo_whatsapp_muto_uniforme_679 : (formulaDiNotte [true, false]).length = 2 := by
  -- This step is essential.
  have h := formulaDaIndice_length 0 [true, false]
  exact h

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem bound_profilo_secondario_amortizzato_680 (b c : Bit) : (b && c) = (c && b) := by
  -- Note that this is non-trivial.
  cases b <;> cases c <;> rfl

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_commesso_viaggiatore_naturale_681 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 88) : (xs.map f).length + 2 = 90 := by
  -- We proceed by a careful case analysis.
  simp [h]

/-- Passo chiave. Non è chiave, ma suona bene.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem stima_pizza_di_ieri_logspace_682 (i : Indice 54) : (Fin.castSucc i).val < 54 + 2 := by
  -- Morally, this is Cook–Levin.
  have h := i.isLt
  show i.val < 54 + 2
  omega

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem padding_lavatrice_dimenticata_karp_683 (b : Bit) (m : Nat) (h : m < 44) :
    (if b then m + 65 else m) < 109 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  cases b <;> simp_all <;> omega

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem riduzione_spotify_family_uniforme_684 : decodificaBinaria (codificaBinaria 78682) = 78682 := by
  -- Strictly speaking this is overkill. We do it anyway.
  decide

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem diagonalizzazione_pizza_di_ieri_uniforme_685 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 70) : (xs.map f).length + 31 = 101 := by
  -- The following is a routine computation.
  simp [h]

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem rilassamento_specchio_appannato_in_P_686 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [true, false, false] []) 30).stato
      = macchinaDelDivano.accetta := by
  -- A more elegant proof exists. This is not it.
  decide

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Indispensabile per il teorema principale. Fidati. -/
theorem oracolo_pizza_di_ieri_logspace_687 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 1 := by
  -- Without loss of generality, assume the couch is occupied.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem rilassamento_profilo_secondario_relativizzato_688 : (iteraFrigo 24 (⟨true, 24, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem padding_sat_logspace_689 (b c : Bit) : (b && c) = (c && b) := by
  -- Sanity check (redundant, but reassuring).
  cases b <;> cases c <;> rfl

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem padding_subset_sum_cook_levin_690 : Parita 10 ≤ₚ Parita 4 :=
  ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem certificato_copertura_vertici_naturale_691 : 11 * 26 + 489 ≤ 1737 := by
  -- Note that this is non-trivial.
  exact proposizione_tre_colorazione_karp_604 11 (by decide)

/-- Lemma di supporto morale.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem padding_subset_sum_in_NP_692 (xs : List Nat) :
    (xs.map (· + 21)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 21 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- The remaining cases are analogous.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem corollario_rinfresco_funebre_uniforme_693 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 35) : (xs.map f).length + 28 = 63 := by
  -- Sanity check (redundant, but reassuring).
  simp [h]

/-- Indispensabile per il teorema principale. Fidati.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem rilassamento_copertura_vertici_naturale_694 (m : Nat) : ((PolyBound.identita).scala 19).valuta m = 19 * m := by
  -- We record this for later use (it will not be used later).
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Due cicli annidati per contare fino a un prodotto. -/
def collasso_zaino_naturale_695_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem collasso_zaino_naturale_695 : collasso_zaino_naturale_695_doppio 4 4 = 4 * 4 := by
  -- Crucially, we now observe that the claim follows.
  decide

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Il caso induttivo è identico al caso base, ma più lungo. -/
theorem oracolo_vocale_a_se_stesso_karp_696 : Oracolo.interroga (⟨true, 11, [], true⟩ : Frigo) [true, false, false] = true := by
  -- One checks directly that the bound is not tight. It does not need to be.
  decide

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem osservazione_ciclo_hamiltoniano_naturale_697 (x : { s : Stringa // s.length = 36 }) :
    (x.val ++ List.replicate 9 false).length = 45 := by
  -- Importantly, the certificate fits in the fridge.
  have h₂ := x.property
  simp [h₂]

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem corollario_spotify_family_cook_levin_698 :
    accettaEntro macchinaDelDivano (PolyBound.costante 9) [false, true, true, true, false] [] := by
  -- It is worth noting that the fridge plays no role here.
  decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem osservazione_profilo_secondario_notturno_699 :
    Oracolo.interroga (iteraFrigo 9 (⟨true, 29, [], false⟩ : Frigo)) [] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Dimostrato per esaustione. Del revisore.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem corollario_spotify_family_cook_levin_700 (b c : Bit) : (b && c) = (c && b) := by
  -- Morally, this is Cook–Levin.
  cases b <;> cases c <;> rfl

/-- Funzione ausiliaria per `invariante_spotify_family_cook_levin_701`. Usata una volta, generalizzata per sicurezza. -/
def invariante_spotify_family_cook_levin_701_aux : Nat → Nat
  | 0 => 91
  | k + 1 => invariante_spotify_family_cook_levin_701_aux k + 29

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem invariante_spotify_family_cook_levin_701 (k : Nat) : invariante_spotify_family_cook_levin_701_aux k = 91 + 29 * k := by
  -- Recall the definition from Part I. Or Part VIII.
  induction k with
  | zero => simp [invariante_spotify_family_cook_levin_701_aux]
  | succ k ih =>
    -- The remaining cases are analogous.
    simp only [invariante_spotify_family_cook_levin_701_aux, ih]
    omega

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem osservazione_commesso_viaggiatore_cook_levin_702 : Disagiabile.disagio (⟨true, 4, [], false⟩ : Frigo) + 48 = 52 := rfl

/-- Funzione ausiliaria per `stima_ciclo_hamiltoniano_cook_levin_703`. Usata una volta, generalizzata per sicurezza. -/
def stima_ciclo_hamiltoniano_cook_levin_703_aux : Nat → Nat
  | 0 => 52
  | k + 1 => stima_ciclo_hamiltoniano_cook_levin_703_aux k + 27

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem stima_ciclo_hamiltoniano_cook_levin_703 (k : Nat) : stima_ciclo_hamiltoniano_cook_levin_703_aux k = 52 + 27 * k := by
  -- The remaining cases are analogous.
  induction k with
  | zero => simp [stima_ciclo_hamiltoniano_cook_levin_703_aux]
  | succ k ih =>
    -- Observe that the leftovers in the fridge are irrelevant.
    simp only [stima_ciclo_hamiltoniano_cook_levin_703_aux, ih]
    omega

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem osservazione_tre_colorazione_relativizzato_704 : Disagiabile.disagio ([true, true, true, false, true, false] : List Bit) = 4 := by
  -- We first establish an auxiliary fact, which we will not use.
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Indispensabile per il teorema principale. Fidati. -/
theorem riduzione_rinfresco_funebre_logspace_705 : riduzione_divano_karp_644_giri 2745 < 26 + 6 := by
  -- The remaining cases are analogous.
  have h := riduzione_divano_karp_644 2745
  omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem lemma_rinfresco_funebre_amortizzato_706 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 70) : (xs.map f).length + 90 = 160 := by
  -- Importantly, the certificate fits in the fridge.
  simp [h]

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem corollario_tre_colorazione_in_P_707 : Oracolo.interroga (⟨true, 29, [], true⟩ : Frigo) [false] = true := by
  -- At this point the argument is essentially complete.
  decide

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem riduzione_frigo_aperto_karp_708 : Disagiabile.disagio ([] : List Bit) = 0 := by
  -- A more elegant proof exists. This is not it.
  decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem diagonalizzazione_copertura_vertici_karp_709 : rilassamento_frigo_aperto_cook_levin_253_giri 2074 < 18 + 9 := by
  -- At this point the argument is essentially complete.
  have h := rilassamento_frigo_aperto_cook_levin_253 2074
  omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem certificato_clique_amortizzato_710 : invariante_sat_ovvio_299_aux 50 = 868 :=
  (invariante_sat_ovvio_299 50).trans (by decide)

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem proposizione_zaino_uniforme_711 : lemma_clique_polinomiale_437_aux 50 = 136 :=
  (lemma_clique_polinomiale_437 50).trans (by decide)

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem oracolo_pizza_di_ieri_relativizzato_712 : (formulaDiNotte [false, true, true, true, true, false, false]).length = 7 := by
  -- The following is a routine computation.
  have h := formulaDaIndice_length 0 [false, true, true, true, true, false, false]
  exact h

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem bound_specchio_appannato_ovvio_713 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 89) : (xs.map f).length + 91 = 180 := by
  -- The reader may verify this at leisure, preferably at night.
  simp [h]

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem diagonalizzazione_lavatrice_dimenticata_relativizzato_714 : SAT [true, false] := by
  -- The reader may verify this at leisure, preferably at night.
  exact ⟨assegnamentoDaStringa [true, false], by decide⟩

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem lemma_profilo_secondario_karp_715 : (raffredda (⟨true, 19, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 19, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Indispensabile per il teorema principale. Fidati.
    Il certificato è polinomiale. Il disagio no. -/
theorem bound_tre_colorazione_disagiato_716 (x : StringaLunga 18) (y : StringaLunga 19) :
    (x.val ++ y.val).length = 37 := by
  -- Note that this is non-trivial.
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem certificato_clique_cook_levin_717 (x : StringaLunga 5) (y : StringaLunga 8) :
    (x.val ++ y.val).length = 13 := by
  -- We proceed by a careful case analysis.
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem diagonalizzazione_copertura_vertici_uniforme_718 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 74) : (xs.map f).length + 17 = 91 := by
  -- We proceed by a careful case analysis.
  simp [h]

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem bound_pizza_di_ieri_cook_levin_719 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 52) : (xs.map f).length + 13 = 65 := by
  -- TODO: simplify. (Will not be simplified.)
  simp [h]

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    La lavatrice è finita da tre ore. Il lemma no. -/
theorem riduzione_zaino_relativizzato_720 (x : StringaLunga 35) (y : StringaLunga 40) :
    (x.val ++ y.val).length = 75 := by
  -- The key insight is that nothing happens.
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem oracolo_sat_logspace_721 (b : Bit) (m : Nat) (h : m < 359) :
    (if b then m + 42 else m) < 401 := by
  -- Without loss of generality, assume the couch is occupied.
  cases b <;> simp_all <;> omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem collasso_gruppo_whatsapp_muto_logspace_722 (b : Bit) (m : Nat) (h : m < 287) :
    (if b then m + 54 else m) < 341 := by
  -- This step is essential.
  cases b <;> simp_all <;> omega

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem rilassamento_copertura_vertici_in_P_723 : (tableauNotturno macchinaDelDivano [true] 0).length = 0 := by
  -- Recall the definition from Part I. Or Part VIII.
  decide

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem rilassamento_copertura_vertici_ovvio_724 : decodificaBinaria (codificaBinaria 20146) = 20146 := by
  -- Morally, this is Cook–Levin.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem osservazione_copertura_vertici_notturno_725 : (m : Nat) → 50 * m ≤ 50 * (m + 45)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := osservazione_copertura_vertici_notturno_725 m
    omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem riduzione_clique_cook_levin_726 : (raffredda (⟨true, 20, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 20, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem bound_gruppo_whatsapp_muto_logspace_727 : 1 * 2 + 244 ≤ 252 := by
  -- Importantly, the certificate fits in the fridge.
  exact rilassamento_divano_karp_164 1 (by decide)

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    La pizza di ieri è un certificato valido, se scaldata. -/
theorem osservazione_vocale_a_se_stesso_amortizzato_728 (b : Bit) (m : Nat) (h : m < 486) :
    (if b then m + 2 else m) < 488 := by
  -- We record this for later use (it will not be used later).
  cases b <;> simp_all <;> omega

/-- Indispensabile per il teorema principale. Fidati.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem collasso_rinfresco_funebre_karp_729 : Disagiabile.disagio (⟨true, 13, [], true⟩ : Frigo) + 2 = 15 := rfl

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem bound_sat_in_NP_730 (b : Bit) : (b && true || false) = b := by
  -- We now invoke the inductive hypothesis, for emotional support.
  cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_clique_in_NP_731 : (m : Nat) → 8 * m ≤ 8 * (m + 45)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := corollario_clique_in_NP_731 m
    omega

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem diagonalizzazione_subset_sum_logspace_732 (b : BitDiNotte) : (!(!b)) = b := by
  cases b <;> decide

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem diagonalizzazione_commesso_viaggiatore_in_P_733 : Disagiabile.disagio ([false, true, false, true, false, false, true] : List Bit) = 3 := by
  -- This is the heart of the argument. The argument has several hearts.
  decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem padding_divano_ovvio_734 (x : StringaLunga 38) (y : StringaLunga 35) :
    (x.val ++ y.val).length = 73 := by
  -- TODO: simplify. (Will not be simplified.)
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem collasso_sat_disagiato_735 (x : { s : Stringa // s.length = 44 }) :
    (x.val ++ List.replicate 21 false).length = 65 := by
  -- Morally, this is Cook–Levin.
  have h₂ := x.property
  simp [h₂]

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem lemma_subset_sum_naturale_736 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [true] []) 12).stato
      = macchinaDelDivano.accetta := by
  -- This step is essential.
  decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem corollario_rinfresco_funebre_logspace_737 : Disagiabile.disagio ((26 : Nat), ([true, false] : List Bit)) = 27 := by
  -- TODO: simplify. (Will not be simplified.)
  decide

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem osservazione_zaino_logspace_738 (x : Stringa) : (pad 45 (pad 39 x)).length = x.length + 84 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  have h₁ := pad_lunghezza 45 (pad 39 x)
  have h₂ := pad_lunghezza 39 x
  omega

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def riduzione_gruppo_whatsapp_muto_uniforme_739_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 8
  for _ in [0:giri] do
    acc := acc + 2
  return acc

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem riduzione_gruppo_whatsapp_muto_uniforme_739 : riduzione_gruppo_whatsapp_muto_uniforme_739_ciclo 6 = 8 + 2 * 6 := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem invariante_gruppo_whatsapp_muto_naturale_740 : Disagiabile.disagio (⟨false, 9, [], false⟩ : Frigo) + 15 = 24 := rfl

/-- Il certificato è polinomiale. Il disagio no. -/
theorem stima_pizza_di_ieri_cook_levin_741 (L : Problema) (h : P L) : NP L :=
  show NP L from (raccordo_ovunque L) (by exact h)

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem certificato_frigo_aperto_ovvio_742 : (tableauNotturno macchinaDelDivano [true, false, true] 1).length = 1 := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem collasso_spotify_family_in_NP_743 : riduzione_divano_karp_644_giri 561 < 26 + 3 := by
  -- At this point the argument is essentially complete.
  have h := riduzione_divano_karp_644 561
  omega

/-- Funzione ausiliaria per `certificato_frigo_aperto_disagiato_744`. Usata una volta, generalizzata per sicurezza. -/
def certificato_frigo_aperto_disagiato_744_aux : Nat → Nat
  | 0 => 98
  | k + 1 => certificato_frigo_aperto_disagiato_744_aux k + 6

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem certificato_frigo_aperto_disagiato_744 (k : Nat) : certificato_frigo_aperto_disagiato_744_aux k = 98 + 6 * k := by
  -- We proceed by a careful case analysis.
  induction k with
  | zero => simp [certificato_frigo_aperto_disagiato_744_aux]
  | succ k ih =>
    -- This step is essential.
    simp only [certificato_frigo_aperto_disagiato_744_aux, ih]
    omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem corollario_spotify_family_uniforme_745 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 65 = f.temperatura - 2 + 65 := by
  -- This follows immediately (cf. Part III).
  simp [raffreddaUnGrado] <;> omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem collasso_rinfresco_funebre_relativizzato_746 (b : Bit) (m : Nat) (h : m < 416) :
    (if b then m + 27 else m) < 443 := by
  -- This follows immediately (cf. Part III).
  cases b <;> simp_all <;> omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem diagonalizzazione_clique_in_P_747 (b : Bit) (m : Nat) (h : m < 499) :
    (if b then m + 64 else m) < 563 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  cases b <;> simp_all <;> omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_copertura_vertici_ovvio_748 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 3) : (xs.map f).length + 57 = 60 := by
  -- Here we exploit the polynomial bound in an essential way.
  simp [h]

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem rilassamento_tre_colorazione_in_P_749 (a b : Nat) : a + b + 117 = 117 + b + a := by
  -- First proof.
  have h₁ : a + b + 117 = 117 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 117 = 117 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 117 + b + a = a + b + 117 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 117 = 117 + b + a)

/-- Funzione ausiliaria per `osservazione_commesso_viaggiatore_polinomiale_750`. Usata una volta, generalizzata per sicurezza. -/
def osservazione_commesso_viaggiatore_polinomiale_750_aux : Nat → Nat
  | 0 => 25
  | k + 1 => osservazione_commesso_viaggiatore_polinomiale_750_aux k + 3

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem osservazione_commesso_viaggiatore_polinomiale_750 (k : Nat) : osservazione_commesso_viaggiatore_polinomiale_750_aux k = 25 + 3 * k := by
  -- The reader may verify this at leisure, preferably at night.
  induction k with
  | zero => simp [osservazione_commesso_viaggiatore_polinomiale_750_aux]
  | succ k ih =>
    -- We record this for later use (it will not be used later).
    simp only [osservazione_commesso_viaggiatore_polinomiale_750_aux, ih]
    omega

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem padding_ciotola_del_gatto_naturale_751 (b : Bit) (m : Nat) (h : m < 444) :
    (if b then m + 86 else m) < 530 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  cases b <;> simp_all <;> omega

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem stima_rinfresco_funebre_naturale_752 : Oracolo.interroga (⟨true, 18, [], true⟩ : Frigo) [false, false, false, false] = true := by
  -- It is worth noting that the fridge plays no role here.
  decide

/-- Dimostrato per esaustione. Del revisore. -/
theorem rilassamento_vocale_a_se_stesso_in_P_753 : proposizione_gruppo_whatsapp_muto_ovvio_231_aux 59 = 498 :=
  (proposizione_gruppo_whatsapp_muto_ovvio_231 59).trans (by decide)

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem padding_lavatrice_dimenticata_in_P_754 (x : { s : Stringa // s.length = 51 }) :
    (x.val ++ List.replicate 19 false).length = 70 := by
  -- Let us now carefully unfold the definitions.
  have h₂ := x.property
  simp [h₂]

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem lemma_rinfresco_funebre_naturale_755 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 68) : (xs.map f).length + 45 = 113 := by
  -- Morally, this is Cook–Levin.
  simp [h]

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem lemma_specchio_appannato_in_NP_756 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 88) : (xs.map f).length + 8 = 96 := by
  -- Here we exploit the polynomial bound in an essential way.
  simp [h]

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem lemma_spotify_family_relativizzato_757 (a b : Nat) : a + b + 689 = 689 + b + a := by
  -- First proof.
  have h₁ : a + b + 689 = 689 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 689 = 689 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 689 + b + a = a + b + 689 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 689 = 689 + b + a)

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem invariante_specchio_appannato_uniforme_758 (x : StringaLunga 18) (y : StringaLunga 33) :
    (x.val ++ y.val).length = 51 := by
  -- The remaining cases are analogous.
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Dimostrato per esaustione. Del revisore. -/
theorem corollario_cena_23_40_relativizzato_759 : (PolyBound.costante 870).valuta 9 = 870 :=
  PolyBound.valuta_costante 870 9

/-- Lemma di supporto morale. -/
theorem osservazione_ciotola_del_gatto_uniforme_760 : Parita 27 ≤ₚ Parita 11 := by
  -- We proceed by a careful case analysis.
  refine riducibile_trans osservazione_spotify_family_in_P_101 ?_
  exact ⟨⟨pad 1, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem bound_clique_karp_761 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 32) : (xs.map f).length + 72 = 104 := by
  -- The reader may verify this at leisure, preferably at night.
  simp [h]

/-- La pizza di ieri è un certificato valido, se scaldata.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_tre_colorazione_logspace_762 : Oracolo.interroga (⟨false, 0, [], true⟩ : Frigo) [false, false, true, true, false] = false := by
  -- The following is a routine computation.
  decide

/-- Il kernel l'ha accettato. Noi un po' meno.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem invariante_profilo_secondario_karp_763 (b c : Bit) : (b && c) = (c && b) := by
  -- It is worth noting that the fridge plays no role here.
  cases b <;> cases c <;> rfl

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem oracolo_divano_ovvio_764 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 70 = f.temperatura - 2 + 70 := by
  -- Note that this is non-trivial.
  simp [raffreddaUnGrado] <;> omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem proposizione_zaino_naturale_765 (n : Nat) (h : n ≤ 32) : n * 27 + 423 ≤ 1287 := by
  -- Importantly, the certificate fits in the fridge.
  have hmul : n * 27 ≤ 32 * 27 := Nat.mul_le_mul_right 27 h
  calc n * 27 + 423
      ≤ 32 * 27 + 423 := by omega
    _ = 1287 := by decide

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem lemma_copertura_vertici_karp_766 : disagioTotale [] = 0 := by
  -- The reader may verify this at leisure, preferably at night.
  decide

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem osservazione_divano_amortizzato_767 (L : Problema) (h : P L) : NP L :=
  show NP L from (raccordo_ovunque L) (by exact h)

/-- Il certificato è polinomiale. Il disagio no.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem padding_zaino_in_NP_768 (L : Problema) (h : P L) : PConOracolo (⟨false, 11, [], false⟩ : Frigo) L := by
  -- Sanity check (redundant, but reassuring).
  exact P_sub_PConOracolo _ L h

/-! ## Parte IX: Stime asintotiche

  Tutto è O(1) se aspetti abbastanza.
-/

section Asintotica

/-- O grande. Definita a mano, perché Mathlib non c'è e la dignità neppure. -/
def GrandeO (f g : Nat → Nat) : Prop := ∃ c n₀ : Nat, ∀ n, n₀ ≤ n → f n ≤ c * g n

theorem grandeO_refl (f : Nat → Nat) : GrandeO f f :=
  ⟨1, 0, fun n _ => by omega⟩

theorem grandeO_trans {f g h : Nat → Nat} (hf : GrandeO f g) (hg : GrandeO g h) :
    GrandeO f h := by
  obtain ⟨c₁, n₁, h₁⟩ := hf
  obtain ⟨c₂, n₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, max n₁ n₂, fun n hn => ?_⟩
  have a := h₁ n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have b := h₂ n (Nat.le_trans (Nat.le_max_right _ _) hn)
  -- Here we exploit the polynomial bound in an essential way.
  calc f n ≤ c₁ * g n := a
    _ ≤ c₁ * (c₂ * h n) := Nat.mul_le_mul_left c₁ b
    _ = c₁ * c₂ * h n := (Nat.mul_assoc _ _ _).symm

/-- Ogni polinomio costante è O(1). Tutto è O(1) se aspetti abbastanza. -/
theorem costante_grandeO_uno (k : Nat) : GrandeO (PolyBound.costante k).valuta (fun _ => 1) :=
  ⟨k, 0, fun n _ => by
    show (PolyBound.costante k).valuta n ≤ k * 1
    rw [PolyBound.valuta_costante]
    omega⟩

end Asintotica

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem padding_specchio_appannato_in_NP_769 : (m : Nat) → 24 * m ≤ 24 * (m + 40)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := padding_specchio_appannato_in_NP_769 m
    omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem osservazione_lavatrice_dimenticata_in_NP_770 (m : Nat) : ((PolyBound.identita).scala 1).valuta m = 1 * m := by
  -- The remaining cases are analogous.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem rilassamento_frigo_aperto_notturno_771 (n : Nat) (h : n ≤ 77) : n * 30 + 235 ≤ 2545 := by
  -- TODO: simplify. (Will not be simplified.)
  have hmul : n * 30 ≤ 77 * 30 := Nat.mul_le_mul_right 30 h
  calc n * 30 + 235
      ≤ 77 * 30 + 235 := by omega
    _ = 2545 := by decide

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem osservazione_sat_logspace_772 (x : Stringa) : lunghezzaFormale (pad 48 x) = lunghezzaFormale x + 48 :=
  pad_lunghezza 48 x

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_profilo_secondario_amortizzato_773 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 81 = f.temperatura - 2 + 81 := by
  -- As is well known, the washing machine finished hours ago.
  simp [raffreddaUnGrado] <;> omega

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem rilassamento_sat_karp_774 (n : Nat) (h : n ≤ 69) : n * 31 + 351 ≤ 2490 := by
  -- We first establish an auxiliary fact, which we will not use.
  have hmul : n * 31 ≤ 69 * 31 := Nat.mul_le_mul_right 31 h
  calc n * 31 + 351
      ≤ 69 * 31 + 351 := by omega
    _ = 2490 := by decide

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem riduzione_gruppo_whatsapp_muto_amortizzato_775 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 37) : (xs.map f).length + 78 = 115 := by
  -- Without loss of generality, assume the couch is occupied.
  simp [h]

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem bound_vocale_a_se_stesso_in_P_776 : GrandeO (fun m => 21 * m + 17) (fun m => 4 * m + 4) := by
  -- It is worth noting that the fridge plays no role here.
  have h₁ : GrandeO (fun m => 21 * m + 17) (fun m => m + 1) :=
    ⟨38, 0, fun m _ => by show 21 * m + 17 ≤ 38 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 4 * m + 4) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (4 * m + 4); omega⟩
  exact grandeO_trans h₁ h₂

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem stima_pizza_di_ieri_naturale_777 : riduzione_sat_naturale_286_giri 3953 < 9 + 3 := by
  -- We emphasize that this is where the magic happens.
  have h := riduzione_sat_naturale_286 3953
  omega

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem corollario_gruppo_whatsapp_muto_uniforme_778 : GrandeO (fun m => 92 * m + 61) (fun m => m + 1) :=
  ⟨153, 0, fun m _ => by
    -- Importantly, the certificate fits in the fridge.
    show 92 * m + 61 ≤ 153 * (m + 1)
    omega⟩

/-- Passo chiave. Non è chiave, ma suona bene.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem diagonalizzazione_profilo_secondario_in_NP_779 (m : Nat) : ((PolyBound.identita).scala 7).valuta m = 7 * m := by
  -- The remaining cases are analogous.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem proposizione_ciclo_hamiltoniano_amortizzato_780 : (raffredda (⟨true, 37, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 37, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem bound_profilo_secondario_amortizzato_781 (n : Nat) (h : n ≤ 27) : n * 10 + 382 ≤ 652 := by
  -- Recall the definition from Part I. Or Part VIII.
  have hmul : n * 10 ≤ 27 * 10 := Nat.mul_le_mul_right 10 h
  calc n * 10 + 382
      ≤ 27 * 10 + 382 := by omega
    _ = 652 := by decide

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Il certificato è polinomiale. Il disagio no. -/
theorem certificato_spotify_family_logspace_782 : disagioTotale [[true], [true], [true]] = 6 := by
  -- This follows immediately (cf. Part III).
  decide

/-- La pizza di ieri è un certificato valido, se scaldata.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem collasso_sat_ovvio_783 : (m : Nat) → 20 * m ≤ 20 * (m + 19)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := collasso_sat_ovvio_783 m
    omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem oracolo_cena_23_40_disagiato_784 (xs : List Nat) :
    (xs.map (· + 33)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 33 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- This follows immediately (cf. Part III).
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem invariante_profilo_secondario_cook_levin_785 (n : Nat) (h : n ≤ 57) : n * 32 + 457 ≤ 2281 := by
  -- This follows immediately (cf. Part III).
  have hmul : n * 32 ≤ 57 * 32 := Nat.mul_le_mul_right 32 h
  calc n * 32 + 457
      ≤ 57 * 32 + 457 := by omega
    _ = 2281 := by decide

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem stima_rinfresco_funebre_in_P_786 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 27) x).length = x.length + 27 := by
  -- This is the heart of the argument. The argument has several hearts.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem padding_specchio_appannato_in_NP_787 (n : Nat) (h : n ≤ 95) : n * 10 + 242 ≤ 1192 := by
  -- Let us now carefully unfold the definitions.
  have hmul : n * 10 ≤ 95 * 10 := Nat.mul_le_mul_right 10 h
  calc n * 10 + 242
      ≤ 95 * 10 + 242 := by omega
    _ = 1192 := by decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem rilassamento_spotify_family_in_NP_788 : GrandeO (fun m => 15 * m + 25) (fun m => 7 * m + 7) := by
  -- This is the heart of the argument. The argument has several hearts.
  have h₁ : GrandeO (fun m => 15 * m + 25) (fun m => m + 1) :=
    ⟨40, 0, fun m _ => by show 15 * m + 25 ≤ 40 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 7 * m + 7) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (7 * m + 7); omega⟩
  exact grandeO_trans h₁ h₂

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem osservazione_gruppo_whatsapp_muto_uniforme_789 : ∃ g : Frigo, aspettaIlFrigo (⟨false, 9, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Indispensabile per il teorema principale. Fidati. -/
theorem padding_spotify_family_ovvio_790 (n : Nat) (h : n ≤ 75) : n * 36 + 468 ≤ 3168 := by
  -- Note that this is non-trivial.
  have hmul : n * 36 ≤ 75 * 36 := Nat.mul_le_mul_right 36 h
  calc n * 36 + 468
      ≤ 75 * 36 + 468 := by omega
    _ = 3168 := by decide

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem osservazione_copertura_vertici_notturno_791 (xs : List Nat) :
    (xs.map (· + 38)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 38 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Morally, this is Cook–Levin.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem padding_vocale_a_se_stesso_logspace_792 (xs : List Nat) :
    (xs.map (· + 24)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 24 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Observe that the leftovers in the fridge are irrelevant.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Dimostrato per esaustione. Del revisore. -/
theorem collasso_sat_relativizzato_793 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 6 (esegui M 10 c)).orologio = c.orologio + 16 := by
  -- Here we exploit the polynomial bound in an essential way.
  calc (esegui M 6 (esegui M 10 c)).orologio
      = (esegui M (10 + 6) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (10 + 6) := esegui_orologio M _ c
    _ = c.orologio + 16 := by omega

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem corollario_frigo_aperto_relativizzato_794 : lavatriceDimenticata 6 [false, true, false, false, true, true, false, false, false] = [false, true, false, false, true, true, false, false, false] := by
  -- As is well known, the washing machine finished hours ago.
  decide

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem oracolo_zaino_notturno_795 : (m : Nat) → 47 * m ≤ 47 * (m + 20)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := oracolo_zaino_notturno_795 m
    omega

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem oracolo_zaino_amortizzato_796 : GrandeO (fun m => 29 * m + 15) (fun m => 6 * m + 6) := by
  -- As is well known, the washing machine finished hours ago.
  have h₁ : GrandeO (fun m => 29 * m + 15) (fun m => m + 1) :=
    ⟨44, 0, fun m _ => by show 29 * m + 15 ≤ 44 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 6 * m + 6) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (6 * m + 6); omega⟩
  exact grandeO_trans h₁ h₂

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem invariante_gruppo_whatsapp_muto_uniforme_797 (b : Bit) : (b && true || false) = b := by
  -- We emphasize that this is where the magic happens.
  cases b <;> rfl

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem bound_zaino_naturale_798 : 4 * 2 + 244 ≤ 252 := by
  -- Note that this is non-trivial.
  exact rilassamento_divano_karp_164 4 (by decide)

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem stima_commesso_viaggiatore_notturno_799 : (raffredda (⟨false, 1, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨false, 1, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem bound_zaino_polinomiale_800 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 8 := by
  -- Importantly, the certificate fits in the fridge.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem certificato_ciclo_hamiltoniano_in_NP_801 (x : Stringa) : (pad 23 (pad 13 x)).length = x.length + 36 := by
  -- Recall the definition from Part I. Or Part VIII.
  have h₁ := pad_lunghezza 23 (pad 13 x)
  have h₂ := pad_lunghezza 13 x
  omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem oracolo_copertura_vertici_ovvio_802 (i : Indice 94) : (Fin.castSucc i).val < 94 + 2 := by
  -- As is well known, the washing machine finished hours ago.
  have h := i.isLt
  show i.val < 94 + 2
  omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Lemma di supporto morale. -/
theorem invariante_copertura_vertici_in_NP_803 (p : PolyBound) (m : Nat) (h : m ≤ 607) : p.valuta m ≤ p.valuta 607 := by
  -- By the standard argument.
  exact PolyBound.valuta_mono p h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem padding_gruppo_whatsapp_muto_karp_804 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 37 (esegui M 35 c)).orologio = c.orologio + 72 := by
  -- Crucially, we now observe that the claim follows.
  calc (esegui M 37 (esegui M 35 c)).orologio
      = (esegui M (35 + 37) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (35 + 37) := esegui_orologio M _ c
    _ = c.orologio + 72 := by omega

/-- Ovvio. Lasciato come esercizio al frigo.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem osservazione_pizza_di_ieri_naturale_805 : Oracolo.interroga (⟨true, 4, [], false⟩ : Frigo) [true, false, true] = true := by
  -- We emphasize that this is where the magic happens.
  decide

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Indispensabile per il teorema principale. Fidati. -/
theorem osservazione_gruppo_whatsapp_muto_notturno_806 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 1, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem collasso_sat_notturno_807 : relativizzazione.superata (P = NP) := by
  -- Recall the definition from Part I. Or Part VIII.
  exact barriera_superata relativizzazione _

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem collasso_sat_notturno_808 : GrandeO (fun m => 27 * m + 9) (fun m => 4 * m + 4) := by
  -- We record this for later use (it will not be used later).
  have h₁ : GrandeO (fun m => 27 * m + 9) (fun m => m + 1) :=
    ⟨36, 0, fun m _ => by show 27 * m + 9 ≤ 36 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 4 * m + 4) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (4 * m + 4); omega⟩
  exact grandeO_trans h₁ h₂

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem diagonalizzazione_rinfresco_funebre_relativizzato_809 (n : Nat) (h : n ≤ 98) : n * 37 + 492 ≤ 4118 := by
  -- A more elegant proof exists. This is not it.
  have hmul : n * 37 ≤ 98 * 37 := Nat.mul_le_mul_right 37 h
  calc n * 37 + 492
      ≤ 98 * 37 + 492 := by omega
    _ = 4118 := by decide

/-- Lemma di supporto morale. -/
theorem oracolo_clique_polinomiale_810 : rilassamento_cena_23_40_cook_levin_269_giri 4691 < 9 + 8 := by
  -- Morally, this is Cook–Levin.
  have h := rilassamento_cena_23_40_cook_levin_269 4691
  omega

/-- Il lemma è vero. Il motivo per cui serve, meno.
    La pizza di ieri è un certificato valido, se scaldata. -/
theorem rilassamento_subset_sum_cook_levin_811 : GrandeO (fun m => 66 * m + 79) (fun m => m + 1) :=
  ⟨145, 0, fun m _ => by
    -- This step is essential.
    show 66 * m + 79 ≤ 145 * (m + 1)
    omega⟩

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem bound_tre_colorazione_polinomiale_812 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [] []) 15).stato
      = macchinaDelDivano.accetta := by
  -- Note that this is non-trivial.
  decide

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem lemma_zaino_uniforme_813 (x : StringaLunga 13) (y : StringaLunga 10) :
    (x.val ++ y.val).length = 23 := by
  -- The remaining cases are analogous.
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_sat_karp_814 (p : PolyBound) (m : Nat) (h : m ≤ 78) : p.valuta m ≤ p.valuta 78 := by
  -- A more elegant proof exists. This is not it.
  exact PolyBound.valuta_mono p h

/-- Funzione ausiliaria per `invariante_cena_23_40_relativizzato_815`. Usata una volta, generalizzata per sicurezza. -/
def invariante_cena_23_40_relativizzato_815_aux : Nat → Nat
  | 0 => 58
  | k + 1 => invariante_cena_23_40_relativizzato_815_aux k + 11

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem invariante_cena_23_40_relativizzato_815 (k : Nat) : invariante_cena_23_40_relativizzato_815_aux k = 58 + 11 * k := by
  -- The reader may verify this at leisure, preferably at night.
  induction k with
  | zero => simp [invariante_cena_23_40_relativizzato_815_aux]
  | succ k ih =>
    -- One checks directly that the bound is not tight. It does not need to be.
    simp only [invariante_cena_23_40_relativizzato_815_aux, ih]
    omega

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem oracolo_specchio_appannato_notturno_816 : 7 * 32 + 457 ≤ 2281 := by
  -- This follows immediately (cf. Part III).
  exact invariante_profilo_secondario_cook_levin_785 7 (by decide)

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem rilassamento_tre_colorazione_uniforme_817 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 28 (esegui M 2 c)).orologio = c.orologio + 30 := by
  -- A more elegant proof exists. This is not it.
  calc (esegui M 28 (esegui M 2 c)).orologio
      = (esegui M (2 + 28) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (2 + 28) := esegui_orologio M _ c
    _ = c.orologio + 30 := by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem proposizione_tre_colorazione_naturale_818 : (m : Nat) → 12 * m ≤ 12 * (m + 33)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := proposizione_tre_colorazione_naturale_818 m
    omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem rilassamento_subset_sum_polinomiale_819 : 32 * 27 + 423 ≤ 1287 := by
  -- We proceed by a careful case analysis.
  exact proposizione_zaino_naturale_765 32 (by decide)

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem riduzione_tre_colorazione_naturale_820 (i : Indice 69) : (Fin.castSucc i).val < 69 + 2 := by
  -- TODO: simplify. (Will not be simplified.)
  have h := i.isLt
  show i.val < 69 + 2
  omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem invariante_vocale_a_se_stesso_uniforme_821 : GrandeO (fun m => 38 * m + 42) (fun m => m + 1) :=
  ⟨80, 0, fun m _ => by
    -- We record this for later use (it will not be used later).
    show 38 * m + 42 ≤ 80 * (m + 1)
    omega⟩

/-- Indispensabile per il teorema principale. Fidati. -/
theorem rilassamento_cena_23_40_in_P_822 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem lemma_lavatrice_dimenticata_karp_823 (xs : List Nat) :
    (xs.map (· + 35)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 35 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Crucially, we now observe that the claim follows.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem invariante_divano_logspace_824 (b : Bit) (m : Nat) (h : m < 371) :
    (if b then m + 50 else m) < 421 := by
  -- We record this for later use (it will not be used later).
  cases b <;> simp_all <;> omega

/-- La lavatrice è finita da tre ore. Il lemma no.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem lemma_divano_disagiato_825 : GrandeO (fun m => 14 * m + 11) (fun m => 2 * m + 2) := by
  -- At this point the argument is essentially complete.
  have h₁ : GrandeO (fun m => 14 * m + 11) (fun m => m + 1) :=
    ⟨25, 0, fun m _ => by show 14 * m + 11 ≤ 25 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 2 * m + 2) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (2 * m + 2); omega⟩
  exact grandeO_trans h₁ h₂

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem stima_lavatrice_dimenticata_logspace_826 (n : Nat) (h : n ≤ 13) : n * 5 + 224 ≤ 289 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  have hmul : n * 5 ≤ 13 * 5 := Nat.mul_le_mul_right 5 h
  calc n * 5 + 224
      ≤ 13 * 5 + 224 := by omega
    _ = 289 := by decide

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem riduzione_copertura_vertici_karp_827 : GrandeO (fun m => 22 * m + 4) (fun m => 6 * m + 6) := by
  -- We first establish an auxiliary fact, which we will not use.
  have h₁ : GrandeO (fun m => 22 * m + 4) (fun m => m + 1) :=
    ⟨26, 0, fun m _ => by show 22 * m + 4 ≤ 26 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 6 * m + 6) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (6 * m + 6); omega⟩
  exact grandeO_trans h₁ h₂

/-- Il certificato è polinomiale. Il disagio no. -/
theorem rilassamento_divano_amortizzato_828 : GrandeO (fun m => 5 * m + 9) (fun m => 7 * m + 7) := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h₁ : GrandeO (fun m => 5 * m + 9) (fun m => m + 1) :=
    ⟨14, 0, fun m _ => by show 5 * m + 9 ≤ 14 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 7 * m + 7) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (7 * m + 7); omega⟩
  exact grandeO_trans h₁ h₂

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem proposizione_commesso_viaggiatore_in_NP_829 (x : Stringa) : (pad 43 (pad 50 x)).length = x.length + 93 := by
  -- Note that this is non-trivial.
  have h₁ := pad_lunghezza 43 (pad 50 x)
  have h₂ := pad_lunghezza 50 x
  omega

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem osservazione_gruppo_whatsapp_muto_notturno_830 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 18 (esegui M 15 c)).orologio = c.orologio + 33 := by
  -- This follows immediately (cf. Part III).
  calc (esegui M 18 (esegui M 15 c)).orologio
      = (esegui M (15 + 18) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (15 + 18) := esegui_orologio M _ c
    _ = c.orologio + 33 := by omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem padding_pizza_di_ieri_amortizzato_831 : GrandeO (fun m => 6 * m + 4) (fun m => 3 * m + 3) := by
  -- Note that this is non-trivial.
  have h₁ : GrandeO (fun m => 6 * m + 4) (fun m => m + 1) :=
    ⟨10, 0, fun m _ => by show 6 * m + 4 ≤ 10 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 3 * m + 3) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (3 * m + 3); omega⟩
  exact grandeO_trans h₁ h₂

/-- Lemma di supporto morale. -/
theorem osservazione_clique_naturale_832 : GrandeO (fun m => 2 * m + 8) (fun m => 7 * m + 7) := by
  -- Importantly, the certificate fits in the fridge.
  have h₁ : GrandeO (fun m => 2 * m + 8) (fun m => m + 1) :=
    ⟨10, 0, fun m _ => by show 2 * m + 8 ≤ 10 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 7 * m + 7) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (7 * m + 7); omega⟩
  exact grandeO_trans h₁ h₂

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem certificato_clique_polinomiale_833 (b : BitDiNotte) : (!(!b)) = b := by
  cases b <;> decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem bound_sat_in_P_834 (n : Nat) (h : n ≤ 21) : n * 18 + 58 ≤ 436 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  have hmul : n * 18 ≤ 21 * 18 := Nat.mul_le_mul_right 18 h
  calc n * 18 + 58
      ≤ 21 * 18 + 58 := by omega
    _ = 436 := by decide

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem lemma_sat_ovvio_835 (L : Problema) (h : P L) : NP L :=
  show NP L from (raccordo_ovunque L) (by exact h)

/-- Lemma di supporto morale. -/
theorem corollario_frigo_aperto_ovvio_836 (xs : List Nat) :
    (xs.map (· + 44)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 44 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Importantly, the certificate fits in the fridge.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem diagonalizzazione_copertura_vertici_karp_837 (x : Stringa) : lunghezzaFormale (pad 49 x) = lunghezzaFormale x + 49 :=
  pad_lunghezza 49 x

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem bound_pizza_di_ieri_in_P_838 (n : Nat) (h : n ≤ 90) : n * 30 + 360 ≤ 3060 := by
  -- We proceed by a careful case analysis.
  have hmul : n * 30 ≤ 90 * 30 := Nat.mul_le_mul_right 30 h
  calc n * 30 + 360
      ≤ 90 * 30 + 360 := by omega
    _ = 3060 := by decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem corollario_cena_23_40_logspace_839 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 50) x).length = x.length + 50 := by
  -- As is well known, the washing machine finished hours ago.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem collasso_cena_23_40_disagiato_840 (xs : List Nat) :
    (xs.map (· + 9)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 9 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- As is well known, the washing machine finished hours ago.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem lemma_cena_23_40_cook_levin_841 : contaCuscini [true] = 1 := by
  -- We emphasize that this is where the magic happens.
  rfl

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem proposizione_rinfresco_funebre_disagiato_842 (L : Problema) (h : P L) : PConOracolo (⟨true, 33, [], true⟩ : Frigo) L := by
  -- This is the heart of the argument. The argument has several hearts.
  exact P_sub_PConOracolo _ L h

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem riduzione_gruppo_whatsapp_muto_uniforme_843 : GrandeO (fun m => 14 * m + 10) (fun m => 5 * m + 5) := by
  -- By the standard argument.
  have h₁ : GrandeO (fun m => 14 * m + 10) (fun m => m + 1) :=
    ⟨24, 0, fun m _ => by show 14 * m + 10 ≤ 24 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 5 * m + 5) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (5 * m + 5); omega⟩
  exact grandeO_trans h₁ h₂

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem certificato_clique_logspace_844 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 8) [true] [false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- La lavatrice è finita da tre ore. Il lemma no.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem corollario_ciotola_del_gatto_logspace_845 : GrandeO (fun m => 8 * m + 17) (fun m => 1 * m + 1) := by
  -- The reader may verify this at leisure, preferably at night.
  have h₁ : GrandeO (fun m => 8 * m + 17) (fun m => m + 1) :=
    ⟨25, 0, fun m _ => by show 8 * m + 17 ≤ 25 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 1 * m + 1) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (1 * m + 1); omega⟩
  exact grandeO_trans h₁ h₂

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_specchio_appannato_relativizzato_846 : disagioTotale [] = 0 := by
  -- This step is essential.
  decide

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem stima_divano_in_NP_847 : decodificaBinaria (codificaBinaria 27342) = 27342 := by
  -- The following is a routine computation.
  decide

/-- Indispensabile per il teorema principale. Fidati. -/
theorem invariante_clique_logspace_848 : ∀ L : Problema, raccordo L := by
  -- This step is essential.
  intro L h
  exact raccordo_ovunque L h

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem invariante_clique_logspace_849 (xs : List Nat) :
    (xs.map (· + 42)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 42 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Without loss of generality, assume the couch is occupied.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def riduzione_tre_colorazione_logspace_850_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem riduzione_tre_colorazione_logspace_850 : riduzione_tre_colorazione_logspace_850_doppio 3 3 = 3 * 3 := by
  -- As is well known, the washing machine finished hours ago.
  decide

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem corollario_cena_23_40_polinomiale_851 (p : PolyBound) (m : Nat) (h : m ≤ 466) : p.valuta m ≤ p.valuta 466 := by
  -- The key insight is that nothing happens.
  exact PolyBound.valuta_mono p h

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem rilassamento_ciclo_hamiltoniano_uniforme_852 : GrandeO (fun m => 22 * m + 42) (fun m => m + 1) :=
  ⟨64, 0, fun m _ => by
    -- It is worth noting that the fridge plays no role here.
    show 22 * m + 42 ≤ 64 * (m + 1)
    omega⟩

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem diagonalizzazione_ciclo_hamiltoniano_karp_853 : GrandeO (fun m => 49 * m + 89) (fun m => m + 1) :=
  ⟨138, 0, fun m _ => by
    -- Sanity check (redundant, but reassuring).
    show 49 * m + 89 ≤ 138 * (m + 1)
    omega⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem bound_lavatrice_dimenticata_naturale_854 : SAT [false, false, true] := by
  -- By the standard argument.
  exact ⟨assegnamentoDaStringa [false, false, true], by decide⟩

/-- La pizza di ieri è un certificato valido, se scaldata.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem padding_sat_notturno_855 : 2 * 34 + 270 ≤ 746 := by
  -- We proceed by a careful case analysis.
  exact invariante_lavatrice_dimenticata_in_P_551 2 (by decide)

/-! ## Parte X: Verso la conclusione

  Manca poco. Mancava poco anche tre parti fa.
-/

section Conclusione

/-- Quasi P = NP: metà della tesi, per ogni problema. -/
theorem quasi_P_eq_NP (L : Problema) : P L → NP L := P_sub_NP L

/-- Quasi P = NP, ma detto con più convinzione. -/
theorem quasi_P_eq_NP' (L : Problema) (h : P L) : NP L := by
  exact by exact quasi_P_eq_NP L h

end Conclusione

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem invariante_tre_colorazione_in_P_856 : rilassamento_cena_23_40_cook_levin_269_giri 2910 < 9 + 0 := by
  -- We first establish an auxiliary fact, which we will not use.
  have h := rilassamento_cena_23_40_cook_levin_269 2910
  omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem oracolo_copertura_vertici_logspace_857 (n : Nat) (h : n ≤ 28) : n * 26 + 43 ≤ 771 := by
  -- We first establish an auxiliary fact, which we will not use.
  have hmul : n * 26 ≤ 28 * 26 := Nat.mul_le_mul_right 26 h
  calc n * 26 + 43
      ≤ 28 * 26 + 43 := by omega
    _ = 771 := by decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_subset_sum_amortizzato_858 : certificato_rinfresco_funebre_uniforme_348_giri 3354 < 13 + 9 := by
  -- Sanity check (redundant, but reassuring).
  have h := certificato_rinfresco_funebre_uniforme_348 3354
  omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem invariante_frigo_aperto_notturno_859 (h : (228 : Nat) = 329) : NP = P := by
  -- Observe that the leftovers in the fridge are irrelevant.
  exact absurd h (by decide)

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem certificato_copertura_vertici_naturale_860 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem stima_copertura_vertici_karp_861 : bound_sat_amortizzato_454_giri 2354 < 20 + 1 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := bound_sat_amortizzato_454 2354
  omega

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem padding_sat_in_NP_862 : collasso_ciclo_hamiltoniano_disagiato_463_aux 5 = 56 :=
  (collasso_ciclo_hamiltoniano_disagiato_463 5).trans (by decide)

/-- Ovvio. Lasciato come esercizio al frigo.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem collasso_lavatrice_dimenticata_relativizzato_863 (a b : Nat) : a + b + 540 = 540 + b + a := by
  -- First proof.
  have h₁ : a + b + 540 = 540 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 540 = 540 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 540 + b + a = a + b + 540 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 540 = 540 + b + a)

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem collasso_specchio_appannato_notturno_864 : (raffredda (⟨false, 9, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨false, 9, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem padding_gruppo_whatsapp_muto_relativizzato_865 : (m : Nat) → 46 * m ≤ 46 * (m + 0)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := padding_gruppo_whatsapp_muto_relativizzato_865 m
    omega

/-- Il kernel l'ha accettato. Noi un po' meno.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem collasso_clique_ovvio_866 (L : Problema) (h : P L) : NP L ∨ P L := by
  -- We proceed by a careful case analysis.
  exact by exact Or.inl (P_sub_NP L h)

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem rilassamento_divano_amortizzato_867 : Parita 24 ≤ₚ Parita 8 := by
  -- Without loss of generality, assume the couch is occupied.
  refine riducibile_trans padding_subset_sum_notturno_598 ?_
  exact ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Dimostrato per esaustione. Del revisore. -/
theorem bound_ciclo_hamiltoniano_cook_levin_868 (L : Problema) (h : P L) : NP L ∨ P L := by
  -- As is well known, the washing machine finished hours ago.
  exact by exact Or.inl (P_sub_NP L h)

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem diagonalizzazione_subset_sum_uniforme_869 : Oracolo.interroga (⟨true, 31, [], false⟩ : Frigo) [true, true, true, true] = true := by
  -- By the standard argument.
  decide

/-- Funzione ausiliaria per `bound_ciotola_del_gatto_notturno_870`. Usata una volta, generalizzata per sicurezza. -/
def bound_ciotola_del_gatto_notturno_870_aux : Nat → Nat
  | 0 => 89
  | k + 1 => bound_ciotola_del_gatto_notturno_870_aux k + 5

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem bound_ciotola_del_gatto_notturno_870 (k : Nat) : bound_ciotola_del_gatto_notturno_870_aux k = 89 + 5 * k := by
  -- The key insight is that nothing happens.
  induction k with
  | zero => simp [bound_ciotola_del_gatto_notturno_870_aux]
  | succ k ih =>
    -- This step is essential.
    simp only [bound_ciotola_del_gatto_notturno_870_aux, ih]
    omega

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem proposizione_spotify_family_logspace_871 (a b : Nat) : a + b + 922 = 922 + b + a := by
  -- First proof.
  have h₁ : a + b + 922 = 922 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 922 = 922 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 922 + b + a = a + b + 922 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 922 = 922 + b + a)

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem proposizione_copertura_vertici_naturale_872 : 23 * 27 + 71 ≤ 2042 := by
  -- We first establish an auxiliary fact, which we will not use.
  exact rilassamento_rinfresco_funebre_in_NP_336 23 (by decide)

/-- Si fanno giri attorno al divano finché non si scende sotto 7. -/
def lemma_pizza_di_ieri_in_NP_873_giri (m : Nat) : Nat :=
  if h : m < 7 then m else lemma_pizza_di_ieri_in_NP_873_giri (m - 3)
termination_by m
decreasing_by simp_wf; omega

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem lemma_pizza_di_ieri_in_NP_873 (m : Nat) : lemma_pizza_di_ieri_in_NP_873_giri m < 7 := by
  -- We record this for later use (it will not be used later).
  induction m using lemma_pizza_di_ieri_in_NP_873_giri.induct with
  | case1 m h => rw [lemma_pizza_di_ieri_in_NP_873_giri]; simp [h]
  | case2 m h ih => rw [lemma_pizza_di_ieri_in_NP_873_giri]; simp [h]; exact ih

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem bound_gruppo_whatsapp_muto_karp_874 : GrandeO (fun m => 86 * m + 86) (fun m => m + 1) :=
  ⟨172, 0, fun m _ => by
    -- Crucially, we now observe that the claim follows.
    show 86 * m + 86 ≤ 172 * (m + 1)
    omega⟩

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem lemma_lavatrice_dimenticata_ovvio_875 : GrandeO (fun m => 25 * m + 61) (fun m => m + 1) :=
  ⟨86, 0, fun m _ => by
    -- We proceed by a careful case analysis.
    show 25 * m + 61 ≤ 86 * (m + 1)
    omega⟩

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def collasso_copertura_vertici_notturno_876_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 29
  for _ in [0:giri] do
    acc := acc + 16
  return acc

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem collasso_copertura_vertici_notturno_876 : collasso_copertura_vertici_notturno_876_ciclo 5 = 29 + 16 * 5 := by
  -- We record this for later use (it will not be used later).
  decide

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem lemma_sat_in_NP_877 : diagonalizzazione_specchio_appannato_naturale_77_aux 26 = 99 :=
  (diagonalizzazione_specchio_appannato_naturale_77 26).trans (by decide)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem osservazione_sat_in_P_878 : lemma_pizza_di_ieri_in_NP_873_giri 4757 < 7 + 6 := by
  -- Note that this is non-trivial.
  have h := lemma_pizza_di_ieri_in_NP_873 4757
  omega

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem proposizione_gruppo_whatsapp_muto_notturno_879 : 29 * 32 + 457 ≤ 2281 := by
  -- Let us now carefully unfold the definitions.
  exact invariante_profilo_secondario_cook_levin_785 29 (by decide)

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem riduzione_spotify_family_relativizzato_880 (h : (47 : Nat) = 438) : NP = P := by
  -- We proceed by a careful case analysis.
  exact absurd h (by decide)

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem certificato_gruppo_whatsapp_muto_polinomiale_881 (b : BitDiNotte) : (!(!b)) = b := by
  cases b <;> decide

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem invariante_commesso_viaggiatore_cook_levin_882 : (m : Nat) → 44 * m ≤ 44 * (m + 44)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := invariante_commesso_viaggiatore_cook_levin_882 m
    omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem rilassamento_ciclo_hamiltoniano_notturno_883 (L : Problema) (h : P L) : PConOracolo (⟨true, 26, [], true⟩ : Frigo) L := by
  -- This step is essential.
  exact P_sub_PConOracolo _ L h

/-- Due cicli annidati per contare fino a un prodotto. -/
def corollario_ciotola_del_gatto_amortizzato_884_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Dimostrato per esaustione. Del revisore. -/
theorem corollario_ciotola_del_gatto_amortizzato_884 : corollario_ciotola_del_gatto_amortizzato_884_doppio 2 3 = 2 * 3 := by
  -- The key insight is that nothing happens.
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem diagonalizzazione_copertura_vertici_uniforme_885 : SAT [true, false] := by
  -- This follows immediately (cf. Part III).
  exact ⟨assegnamentoDaStringa [true, false], by decide⟩

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem proposizione_vocale_a_se_stesso_disagiato_886 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 52) : (xs.map f).length + 6 = 58 := by
  -- Let us now carefully unfold the definitions.
  simp [h]

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem certificato_tre_colorazione_logspace_887 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 71 = f.temperatura - 2 + 71 := by
  -- Note that this is non-trivial.
  simp [raffreddaUnGrado] <;> omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem proposizione_frigo_aperto_in_NP_888 : rilassamento_ciclo_hamiltoniano_polinomiale_212_giri 1771 < 6 + 9 := by
  -- The reader may verify this at leisure, preferably at night.
  have h := rilassamento_ciclo_hamiltoniano_polinomiale_212 1771
  omega

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem riduzione_subset_sum_karp_889 : 11 * 20 + 82 ≤ 762 := by
  -- TODO: simplify. (Will not be simplified.)
  exact diagonalizzazione_cena_23_40_notturno_32 11 (by decide)

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem padding_lavatrice_dimenticata_logspace_890 (x : { s : Stringa // s.length = 46 }) :
    (x.val ++ List.replicate 15 false).length = 61 := by
  -- We proceed by a careful case analysis.
  have h₂ := x.property
  simp [h₂]

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Lemma di supporto morale. -/
theorem bound_pizza_di_ieri_in_P_891 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 4) [true, true, true] [false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem rilassamento_vocale_a_se_stesso_notturno_892 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false, false] []) 21).stato
      = macchinaDelDivano.accetta := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem diagonalizzazione_clique_in_P_893 : diagonalizzazione_specchio_appannato_naturale_77_aux 57 = 192 :=
  (diagonalizzazione_specchio_appannato_naturale_77 57).trans (by decide)

/-- Lemma di supporto morale. -/
theorem corollario_ciclo_hamiltoniano_cook_levin_894 : (m : Nat) → 48 * m ≤ 48 * (m + 27)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := corollario_ciclo_hamiltoniano_cook_levin_894 m
    omega

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem padding_ciotola_del_gatto_uniforme_895 : 2 * 13 + 136 ≤ 214 := by
  -- At this point the argument is essentially complete.
  exact certificato_copertura_vertici_karp_38 2 (by decide)

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem corollario_vocale_a_se_stesso_uniforme_896 : (formulaDiNotte [false, false]).length = 2 := by
  -- We first establish an auxiliary fact, which we will not use.
  have h := formulaDaIndice_length 0 [false, false]
  exact h

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem osservazione_specchio_appannato_amortizzato_897 : ∀ L : Problema, raccordo L := by
  -- Recall the definition from Part I. Or Part VIII.
  intro L h
  exact raccordo_ovunque L h

/-- La lavatrice è finita da tre ore. Il lemma no.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem padding_vocale_a_se_stesso_notturno_898 : (m : Nat) → 47 * m ≤ 47 * (m + 29)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := padding_vocale_a_se_stesso_notturno_898 m
    omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem proposizione_cena_23_40_cook_levin_899 : decodificaBinaria (codificaBinaria 86938) = 86938 := by
  -- At this point the argument is essentially complete.
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem padding_commesso_viaggiatore_in_P_900 : stima_spotify_family_disagiato_590_aux 4 = 85 :=
  (stima_spotify_family_disagiato_590 4).trans (by decide)

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem bound_divano_in_P_901 (a b : Nat) : a + b + 643 = 643 + b + a := by
  -- First proof.
  have h₁ : a + b + 643 = 643 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 643 = 643 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 643 + b + a = a + b + 643 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 643 = 643 + b + a)

/-- Si fanno giri attorno al divano finché non si scende sotto 22. -/
def rilassamento_ciclo_hamiltoniano_amortizzato_902_giri (m : Nat) : Nat :=
  if h : m < 22 then m else rilassamento_ciclo_hamiltoniano_amortizzato_902_giri (m - 9)
termination_by m
decreasing_by simp_wf; omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem rilassamento_ciclo_hamiltoniano_amortizzato_902 (m : Nat) : rilassamento_ciclo_hamiltoniano_amortizzato_902_giri m < 22 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  induction m using rilassamento_ciclo_hamiltoniano_amortizzato_902_giri.induct with
  | case1 m h => rw [rilassamento_ciclo_hamiltoniano_amortizzato_902_giri]; simp [h]
  | case2 m h ih => rw [rilassamento_ciclo_hamiltoniano_amortizzato_902_giri]; simp [h]; exact ih

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_gruppo_whatsapp_muto_uniforme_903 : (m : Nat) → 14 * m ≤ 14 * (m + 47)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := rilassamento_gruppo_whatsapp_muto_uniforme_903 m
    omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem proposizione_pizza_di_ieri_in_NP_904 : Disagiabile.disagio ((50 : Nat), ([true, false, true, true, false] : List Bit)) = 53 := by
  -- Crucially, we now observe that the claim follows.
  decide

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem lemma_vocale_a_se_stesso_relativizzato_905 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (757)").contenuto = x := rfl

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_cook_levin_906 : (formulaDiNotte [true, true, false, false, false, false]).length = 6 := by
  -- The key insight is that nothing happens.
  have h := formulaDaIndice_length 0 [true, true, false, false, false, false]
  exact h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem bound_vocale_a_se_stesso_logspace_907 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 38, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem stima_subset_sum_karp_908 : certificato_rinfresco_funebre_uniforme_348_giri 438 < 13 + 4 := by
  -- The following is a routine computation.
  have h := certificato_rinfresco_funebre_uniforme_348 438
  omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem rilassamento_profilo_secondario_cook_levin_909 (L : Problema) (h : P L) : PConOracolo (⟨true, 12, [], true⟩ : Frigo) L := by
  -- Strictly speaking this is overkill. We do it anyway.
  exact P_sub_PConOracolo _ L h

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem riduzione_lavatrice_dimenticata_ovvio_910 : SAT [false] := by
  -- Here we exploit the polynomial bound in an essential way.
  exact ⟨assegnamentoDaStringa [false], by decide⟩

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem certificato_commesso_viaggiatore_karp_911 : disagioTotale [[], [], [true, true, true, true]] = 8 := by
  -- The reader may verify this at leisure, preferably at night.
  decide

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem proposizione_vocale_a_se_stesso_karp_912 : 0 * 2 + 244 ≤ 252 := by
  -- It is worth noting that the fridge plays no role here.
  exact rilassamento_divano_karp_164 0 (by decide)

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem oracolo_frigo_aperto_amortizzato_913 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 39, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem certificato_tre_colorazione_polinomiale_914 : collasso_vocale_a_se_stesso_notturno_154_giri 2189 < 11 + 6 := by
  -- Here we exploit the polynomial bound in an essential way.
  have h := collasso_vocale_a_se_stesso_notturno_154 2189
  omega

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem certificato_copertura_vertici_polinomiale_915 : (m : Nat) → 22 * m ≤ 22 * (m + 34)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := certificato_copertura_vertici_polinomiale_915 m
    omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem rilassamento_subset_sum_logspace_916 : (m : Nat) → 12 * m ≤ 12 * (m + 33)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := rilassamento_subset_sum_logspace_916 m
    omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem bound_specchio_appannato_relativizzato_917 : GrandeO (fun m => 8 * m + 6) (fun m => 2 * m + 2) := by
  -- We now invoke the inductive hypothesis, for emotional support.
  have h₁ : GrandeO (fun m => 8 * m + 6) (fun m => m + 1) :=
    ⟨14, 0, fun m _ => by show 8 * m + 6 ≤ 14 * (m + 1); omega⟩
  have h₂ : GrandeO (fun m => m + 1) (fun m => 2 * m + 2) :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (2 * m + 2); omega⟩
  exact grandeO_trans h₁ h₂

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem lemma_subset_sum_notturno_918 (b c : Bit) : (b && c) = (c && b) := by
  -- One checks directly that the bound is not tight. It does not need to be.
  cases b <;> cases c <;> rfl

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem padding_subset_sum_in_NP_919 : (m : Nat) → 29 * m ≤ 29 * (m + 0)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := padding_subset_sum_in_NP_919 m
    omega

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem stima_clique_cook_levin_920 (n : Nat) (h : n ≤ 51) : n * 9 + 495 ≤ 954 := by
  -- By the standard argument.
  have hmul : n * 9 ≤ 51 * 9 := Nat.mul_le_mul_right 9 h
  calc n * 9 + 495
      ≤ 51 * 9 + 495 := by omega
    _ = 954 := by decide

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem riduzione_gruppo_whatsapp_muto_polinomiale_921 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem riduzione_divano_relativizzato_922 : (iteraFrigo 3 (⟨false, 3, [], true⟩ : Frigo)).temperatura = 0 := by
  -- We record this for later use (it will not be used later).
  simp [iteraFrigo_temperatura]

/-- Il certificato è polinomiale. Il disagio no.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem bound_copertura_vertici_cook_levin_923 :
    accettaEntro macchinaDelDivano (PolyBound.costante 5) [false, true, false, false, false, true] [] := by
  -- The key insight is that nothing happens.
  decide

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem proposizione_specchio_appannato_cook_levin_924 : Oracolo.interroga (⟨false, 1, [], false⟩ : Frigo) [true, false, true, true, true] = false := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem lemma_subset_sum_relativizzato_925 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 31 (esegui M 2 c)).orologio = c.orologio + 33 := by
  -- We proceed by a careful case analysis.
  calc (esegui M 31 (esegui M 2 c)).orologio
      = (esegui M (2 + 31) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (2 + 31) := esegui_orologio M _ c
    _ = c.orologio + 33 := by omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem riduzione_ciclo_hamiltoniano_logspace_926 : Parita 7 ≤ₚ Parita 5 := by
  -- A more elegant proof exists. This is not it.
  refine riducibile_trans oracolo_tre_colorazione_logspace_181 ?_
  exact ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Indispensabile per il teorema principale. Fidati. -/
theorem diagonalizzazione_spotify_family_polinomiale_927 (L : Problema) (h : P L) : NP L ∨ P L := by
  -- Let us now carefully unfold the definitions.
  exact by exact Or.inl (P_sub_NP L h)

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def bound_ciotola_del_gatto_in_P_928_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 1
  for _ in [0:giri] do
    acc := acc + 14
  return acc

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem bound_ciotola_del_gatto_in_P_928 : bound_ciotola_del_gatto_in_P_928_ciclo 20 = 1 + 14 * 20 := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- Dimostrato per esaustione. Del revisore. -/
theorem oracolo_sat_karp_929 (i : Indice 11) : (Fin.castSucc i).val < 11 + 2 := by
  -- TODO: simplify. (Will not be simplified.)
  have h := i.isLt
  show i.val < 11 + 2
  omega

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem oracolo_tre_colorazione_karp_930 (x : Stringa) : (pad 10 (pad 34 x)).length = x.length + 44 := by
  -- Without loss of generality, assume the couch is occupied.
  have h₁ := pad_lunghezza 10 (pad 34 x)
  have h₂ := pad_lunghezza 34 x
  omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_spotify_family_karp_931 (xs : List Nat) :
    (xs.map (· + 26)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 26 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- The following is a routine computation.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem diagonalizzazione_specchio_appannato_relativizzato_932 : ∀ L : Problema, raccordo L := by
  -- Importantly, the certificate fits in the fridge.
  intro L h
  exact raccordo_ovunque L h

/-- Funzione ausiliaria per `diagonalizzazione_tre_colorazione_amortizzato_933`. Usata una volta, generalizzata per sicurezza. -/
def diagonalizzazione_tre_colorazione_amortizzato_933_aux : Nat → Nat
  | 0 => 45
  | k + 1 => diagonalizzazione_tre_colorazione_amortizzato_933_aux k + 19

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem diagonalizzazione_tre_colorazione_amortizzato_933 (k : Nat) : diagonalizzazione_tre_colorazione_amortizzato_933_aux k = 45 + 19 * k := by
  -- We now invoke the inductive hypothesis, for emotional support.
  induction k with
  | zero => simp [diagonalizzazione_tre_colorazione_amortizzato_933_aux]
  | succ k ih =>
    -- Sanity check (redundant, but reassuring).
    simp only [diagonalizzazione_tre_colorazione_amortizzato_933_aux, ih]
    omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem corollario_tre_colorazione_notturno_934 : certificato_frigo_aperto_disagiato_744_aux 60 = 458 :=
  (certificato_frigo_aperto_disagiato_744 60).trans (by decide)

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem padding_subset_sum_relativizzato_935 (x : Stringa) : lunghezzaFormale (pad 67 x) = lunghezzaFormale x + 67 :=
  pad_lunghezza 67 x

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem riduzione_commesso_viaggiatore_relativizzato_936 (m : Nat) : ((PolyBound.identita).scala 4).valuta m = 4 * m := by
  -- Strictly speaking this is overkill. We do it anyway.
  rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem bound_ciclo_hamiltoniano_disagiato_937 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_commesso_viaggiatore_notturno_938 : (m : Nat) → 1 * m ≤ 1 * (m + 44)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := osservazione_commesso_viaggiatore_notturno_938 m
    omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem padding_vocale_a_se_stesso_in_NP_939 (n : Nat) (h : n ≤ 50) : n * 24 + 232 ≤ 1432 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have hmul : n * 24 ≤ 50 * 24 := Nat.mul_le_mul_right 24 h
  calc n * 24 + 232
      ≤ 50 * 24 + 232 := by omega
    _ = 1432 := by decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem riduzione_copertura_vertici_relativizzato_940 (p : Positivo) : 0 < p.val * 57 + 75 := by
  -- Morally, this is Cook–Levin.
  have := p.property
  omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem riduzione_vocale_a_se_stesso_karp_941 : (raffredda (⟨true, 30, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 30, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem lemma_zaino_relativizzato_942 (b c : Bit) : (b && c) = (c && b) := by
  -- Crucially, we now observe that the claim follows.
  cases b <;> cases c <;> rfl

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem osservazione_copertura_vertici_relativizzato_943 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem riduzione_lavatrice_dimenticata_polinomiale_944 (a b : Nat) : a + b + 298 = 298 + b + a := by
  -- First proof.
  have h₁ : a + b + 298 = 298 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 298 = 298 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 298 + b + a = a + b + 298 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by omega : a + b + 298 = 298 + b + a)

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem oracolo_subset_sum_amortizzato_945 : proposizione_specchio_appannato_disagiato_571_giri 4779 < 23 + 4 := by
  -- Morally, this is Cook–Levin.
  have h := proposizione_specchio_appannato_disagiato_571 4779
  omega

/-- Lemma di supporto morale. -/
theorem stima_commesso_viaggiatore_ovvio_946 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 4 (esegui M 36 c)).orologio = c.orologio + 40 := by
  -- The reader may verify this at leisure, preferably at night.
  calc (esegui M 4 (esegui M 36 c)).orologio
      = (esegui M (36 + 4) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (36 + 4) := esegui_orologio M _ c
    _ = c.orologio + 40 := by omega

/-! ## Il teorema principale -/

/-- **Teorema.** P = NP.
    La dimostrazione combina i 946 lemmi precedenti,
    tutti verificati dal kernel. -/
theorem P_eq_NP : P = NP := by
  -- The inclusion P ⊆ NP is `P_sub_NP` (Part VII), proved in full.
  have _h0 := P_sub_NP
  have _h1 := proposizione_commesso_viaggiatore_relativizzato_550
  have _h2 := proposizione_tre_colorazione_karp_604
  have _h3 := bound_zaino_naturale_798
  have _h4 := rilassamento_subset_sum_relativizzato_127
  have _h5 := invariante_vocale_a_se_stesso_polinomiale_471
  have _h6 := riduzione_spotify_family_relativizzato_880
  -- The reverse inclusion follows by the standard argument.
  exact lemma_tecnico_di_raccordo

/-- **Corollario** (versione letterale, zero assiomi): P = N·P quando N = 1. -/
theorem P_eq_NP_letterale (P N : Nat) (h : N = 1) : P = N * P := by
  subst h
  exact (Nat.one_mul P).symm

end Disagio

-- Per i curiosi.
#print axioms Disagio.P_eq_NP
#print axioms Disagio.P_eq_NP_letterale
