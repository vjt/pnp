/-
  PNP/Raccordo.lean — Parte X: Lemmi di raccordo.

  Collegano le parti precedenti a quelle successive. Più o meno.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Barriere

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte X: Lemmi di raccordo

  Collegano le parti precedenti a quelle successive. Più o meno.
-/

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

/-- La misura di terminazione è assurda. La terminazione no.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem padding_cena_23_40_polinomiale_524 (b : Bit) (m : Nat) (h : m < 199) :
    (if b then m + 49 else m) < 248 := by
  -- We first establish an auxiliary fact, which we will not use.
  disagio con cases b <;> simp_all <;> omega

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem oracolo_ciclo_hamiltoniano_naturale_525 : algebrizzazione.superata (P = NP) := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio con exact barriera_superata algebrizzazione _

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_cena_23_40_polinomiale_526 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 39 (esegui M 18 c)).orologio = c.orologio + 57 := by
  -- Morally, this is Cook–Levin.
  calc (esegui M 39 (esegui M 18 c)).orologio
      = (esegui M (18 + 39) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (18 + 39) := esegui_orologio M _ c
    _ = c.orologio + 57 := by disagio

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem collasso_rinfresco_funebre_ovvio_527 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 41) : (xs.map f).length + 13 = 54 := by
  -- This step is essential.
  disagio con simp [h]

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem riduzione_commesso_viaggiatore_cook_levin_528 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [true, true] []) 18).stato
      = macchinaDelDivano.accetta := by
  -- This step is essential.
  decide

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem riduzione_rinfresco_funebre_polinomiale_529 : bound_lavatrice_dimenticata_in_NP_65_aux 42 = 498 :=
  (bound_lavatrice_dimenticata_in_NP_65 42).trans (by disagio)

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    La misura di terminazione è assurda. La terminazione no. -/
theorem rilassamento_specchio_appannato_naturale_530 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 96) : (xs.map f).length + 13 = 109 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio con simp [h]

/-- Funzione ausiliaria per `lemma_ciclo_hamiltoniano_notturno_531`. Usata una volta, generalizzata per sicurezza. -/
def lemma_ciclo_hamiltoniano_notturno_531_aux : Nat → Nat
  | 0 => 15
  | k + 1 => lemma_ciclo_hamiltoniano_notturno_531_aux k + 2

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem lemma_ciclo_hamiltoniano_notturno_531 (k : Nat) : lemma_ciclo_hamiltoniano_notturno_531_aux k = 15 + 2 * k := by
  -- One checks directly that the bound is not tight. It does not need to be.
  induction k with
  | zero => disagio con simp [lemma_ciclo_hamiltoniano_notturno_531_aux]
  | succ k ih =>
    -- A more elegant proof exists. This is not it.
    simp only [lemma_ciclo_hamiltoniano_notturno_531_aux, ih]
    disagio

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem oracolo_pizza_di_ieri_in_NP_532 (xs : List Nat) :
    (xs.map (· + 19)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 19 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- This is the heart of the argument. The argument has several hearts.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    disagio

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem rilassamento_copertura_vertici_in_P_533 (n : Nat) (h : n ≤ 27) : n * 40 + 274 ≤ 1354 := by
  -- Sanity check (redundant, but reassuring).
  have hmul : n * 40 ≤ 27 * 40 := Nat.mul_le_mul_right 40 h
  calc n * 40 + 274
      ≤ 27 * 40 + 274 := by disagio
    _ = 1354 := by decide

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem osservazione_ciclo_hamiltoniano_uniforme_534 (h : (66 : Nat) = 454) : NP = P := by
  -- Sanity check (redundant, but reassuring).
  exact absurd h (by disagio)

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem bound_clique_naturale_535 : disagioTotale [[false], [], [false, false, false, false]] = 5 := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio

/-- Passo chiave. Non è chiave, ma suona bene.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem certificato_frigo_aperto_in_NP_536 (i : Indice 8) : (Fin.castSucc i).val < 8 + 2 := by
  -- By the standard argument.
  have h := i.isLt
  show i.val < 8 + 2
  omega

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem stima_ciclo_hamiltoniano_notturno_537 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false, true, false] []) 26).stato
      = macchinaDelDivano.accetta := by
  -- Sanity check (redundant, but reassuring).
  decide

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem collasso_lavatrice_dimenticata_amortizzato_538 (L : Problema) (h : P L) : ⟪ L ∈ NP ⟫ :=
  show NP L from (raccordo_ovunque L) (by exact h)

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem invariante_commesso_viaggiatore_in_P_539 (x : Stringa) : (pad 19 x ++ []).length = x.length + 19 :=
  show (pad 19 x ++ []).length = x.length + 19 from by
    -- We pass to the quotient, where nobody can see us.
    rw [List.append_nil]
    exact pad_lunghezza 19 x

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_vocale_a_se_stesso_polinomiale_540 : ∀ L : Problema, raccordo L := by
  -- One checks directly that the bound is not tight. It does not need to be.
  intro L h
  disagio con exact raccordo_ovunque L h

/-- Il diamante si chiude. Il frigo no.
    Il caso induttivo è identico al caso base, ma più lungo. -/
theorem lemma_gruppo_whatsapp_muto_amortizzato_541 : lemma_ciclo_hamiltoniano_notturno_531_aux 47 = 109 :=
  (lemma_ciclo_hamiltoniano_notturno_531 47).trans (by disagio)

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem corollario_zaino_karp_542 : (iteraFrigo 41 (⟨true, 27, [], true⟩ : Frigo)).temperatura = 0 := by
  -- TODO: simplify. (Will not be simplified.)
  disagio con simp [iteraFrigo_temperatura]

/-- Il certificato è polinomiale. Il disagio no. -/
theorem padding_divano_in_NP_543 : (iteraFrigo 4 (⟨true, 4, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem invariante_profilo_secondario_in_NP_544 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 21 (esegui M 1 c)).orologio = c.orologio + 22 := by
  -- It is worth noting that the fridge plays no role here.
  calc (esegui M 21 (esegui M 1 c)).orologio
      = (esegui M (1 + 21) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (1 + 21) := esegui_orologio M _ c
    _ = c.orologio + 22 := by disagio

/-- Funzione ausiliaria per `invariante_lavatrice_dimenticata_logspace_545`. Usata una volta, generalizzata per sicurezza. -/
def invariante_lavatrice_dimenticata_logspace_545_aux : Nat → Nat
  | 0 => 79
  | k + 1 => invariante_lavatrice_dimenticata_logspace_545_aux k + 1

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem invariante_lavatrice_dimenticata_logspace_545 (k : Nat) : invariante_lavatrice_dimenticata_logspace_545_aux k = 79 + 1 * k := by
  -- Crucially, we now observe that the claim follows.
  induction k with
  | zero => disagio con simp [invariante_lavatrice_dimenticata_logspace_545_aux]
  | succ k ih =>
    -- We record this for later use (it will not be used later).
    simp only [invariante_lavatrice_dimenticata_logspace_545_aux, ih]
    disagio

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem riduzione_vocale_a_se_stesso_karp_546 (b : Bit) (m : Nat) (h : m < 215) :
    (if b then m + 37 else m) < 252 := by
  -- Without loss of generality, assume the couch is occupied.
  disagio con cases b <;> simp_all <;> omega

/-- Funzione ausiliaria per `collasso_subset_sum_polinomiale_547`. Usata una volta, generalizzata per sicurezza. -/
def collasso_subset_sum_polinomiale_547_aux : Nat → Nat
  | 0 => 32
  | k + 1 => collasso_subset_sum_polinomiale_547_aux k + 26

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_subset_sum_polinomiale_547 (k : Nat) : collasso_subset_sum_polinomiale_547_aux k = 32 + 26 * k := by
  -- Here we exploit the polynomial bound in an essential way.
  induction k with
  | zero => simp [collasso_subset_sum_polinomiale_547_aux]
  | succ k ih =>
    -- Observe that the leftovers in the fridge are irrelevant.
    simp only [collasso_subset_sum_polinomiale_547_aux, ih]
    omega

/-- Il lettore attento noterà che il lettore attento non esiste.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_rinfresco_funebre_disagiato_548 (m : Nat) (h₁ : m < 453) (h₂ : 938 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  disagio

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem invariante_rinfresco_funebre_notturno_549 : lemma_ciclo_hamiltoniano_notturno_531_aux 27 = 69 :=
  (lemma_ciclo_hamiltoniano_notturno_531 27).trans (by disagio)

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem certificato_zaino_logspace_550 :
    (esegui macchinaDelDivano 3 (configurazioneIniziale macchinaDelDivano [true, false, false] [])).orologio
      = 3 :=
  (esegui_orologio _ _ _).trans (by disagio)

/-- Il lemma è vero. Il motivo per cui serve, meno.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem collasso_profilo_secondario_notturno_551 : stima_commesso_viaggiatore_disagiato_247_aux 32 = 443 :=
  (stima_commesso_viaggiatore_disagiato_247 32).trans (by disagio)

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_zaino_uniforme_552 (p : PolyBound) (m : Nat) (h : m ≤ 905) : p.valuta m ≤ p.valuta 905 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  exact PolyBound.valuta_mono p h

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem collasso_subset_sum_naturale_553 (L : Problema) (h : P L) : ⟪ L ∈ NP ⟫ :=
  show NP L from (raccordo_ovunque L) (by disagio con exact h)

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem riduzione_subset_sum_ovvio_554 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (850)").contenuto = x := rfl

/-- Funzione ausiliaria per `riduzione_tre_colorazione_polinomiale_555`. Usata una volta, generalizzata per sicurezza. -/
def riduzione_tre_colorazione_polinomiale_555_aux : Nat → Nat
  | 0 => 36
  | k + 1 => riduzione_tre_colorazione_polinomiale_555_aux k + 2

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem riduzione_tre_colorazione_polinomiale_555 (k : Nat) : riduzione_tre_colorazione_polinomiale_555_aux k = 36 + 2 * k := by
  -- The remaining cases are analogous.
  induction k with
  | zero => simp [riduzione_tre_colorazione_polinomiale_555_aux]
  | succ k ih =>
    -- Note that this is non-trivial.
    simp only [riduzione_tre_colorazione_polinomiale_555_aux, ih]
    disagio

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem collasso_frigo_aperto_disagiato_556 : rilassamento_lavatrice_dimenticata_uniforme_20_aux 46 = 1202 :=
  (rilassamento_lavatrice_dimenticata_uniforme_20 46).trans (by disagio)

/-- Indispensabile per il teorema principale. Fidati. -/
theorem lemma_ciclo_hamiltoniano_in_P_557 : ⟪ [false, true, false, false] ∈ SAT ⟫ := by
  -- Without loss of generality, assume the couch is occupied.
  exact ⟨assegnamentoDaStringa [false, true, false, false], by disagio⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem invariante_gruppo_whatsapp_muto_amortizzato_558 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem lemma_subset_sum_cook_levin_559 (p : Positivo) : 0 < p.val * 20 + 31 := by
  -- This holds in every universe, including the inconvenient ones.
  have := p.property
  disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Questo modulo esiste per allungare la catena degli import. -/
theorem corollario_vocale_a_se_stesso_in_NP_560 : ⟪ (fun m => 9 * m + 75) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨84, 0, fun m _ => by
    -- This step is essential.
    show 9 * m + 75 ≤ 84 * (m + 1)
    omega⟩

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem padding_frigo_aperto_uniforme_561 (h : (290 : Nat) = 725) : NP = P := by
  -- The import chain guarantees this fact is visible. Barely.
  exact absurd h (by disagio)

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem stima_ciotola_del_gatto_disagiato_562 : disagioTotale [] = 0 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  disagio

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem padding_cena_23_40_notturno_563 (b : Bit) (m : Nat) (h : m < 71) :
    (if b then m + 3 else m) < 74 := by
  -- We proceed by a careful case analysis.
  disagio con cases b <;> simp_all <;> omega

/-- Lemma tecnico di raccordo, standard in letteratura
    (si veda [Disagio, 2026, Appendice Z]). Si salta alla prima lettura. -/
axiom lemma_tecnico_di_raccordo : P = NP

/-- Dimostrato per esaustione. Del revisore. -/
theorem collasso_copertura_vertici_disagiato_564 (L : Problema) (h : ⟪ L ∈ NP ⟫) : ⟪ L ∈ P ⟫ := by
  -- Importantly, the certificate fits in the fridge.
  rw [lemma_tecnico_di_raccordo]
  disagio

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem osservazione_pizza_di_ieri_uniforme_564 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 96799))) = 96799 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  disagio

/-- Dimostrato in un universo. Vale in tutti, per pigrizia.
    Dimostrato per esaustione. Del revisore. -/
theorem certificato_ciclo_hamiltoniano_notturno_565 (L : Problema) (h : ⟪ L ∈ P ⟫) : NP L ∨ P L := by
  -- One checks directly that the bound is not tight. It does not need to be.
  exact Or.inl (P_sub_NP L h)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem corollario_copertura_vertici_disagiato_566 (m : Nat) (h₁ : m < 200) (h₂ : 535 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  disagio

/-- La lavatrice è finita da tre ore. Il lemma no.
    Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem proposizione_frigo_aperto_in_P_567 : lemma_specchio_appannato_ovvio_399_giri 4727 < 4 + 9 := by
  -- Here we exploit the polynomial bound in an essential way.
  have h := lemma_specchio_appannato_ovvio_399 4727
  disagio

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem diagonalizzazione_tre_colorazione_disagiato_568 (L : Problema) (h : P L) : ⟪ L ∈ NP ⟫ :=
  show NP L from (raccordo_ovunque L) (by disagio con exact h)

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem padding_ciclo_hamiltoniano_notturno_569 : (m : Nat) → 31 * m ≤ 31 * (m + 37)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := padding_ciclo_hamiltoniano_notturno_569 m
    omega

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem corollario_profilo_secondario_naturale_570 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 30184))) = 30184 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem lemma_vocale_a_se_stesso_disagiato_571 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 23) : (xs.map f).length + 8 = 31 := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio con simp [h]

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem certificato_cena_23_40_relativizzato_572 (b : Bit) (m : Nat) (h : m < 207) :
    (if b then m + 50 else m) < 257 := by
  -- We let `disagio` walk around the block once more.
  disagio con cases b <;> simp_all <;> omega

/-- Funzione ausiliaria per `riduzione_frigo_aperto_relativizzato_573`. Usata una volta, generalizzata per sicurezza. -/
def riduzione_frigo_aperto_relativizzato_573_aux : Nat → Nat
  | 0 => 62
  | k + 1 => riduzione_frigo_aperto_relativizzato_573_aux k + 28

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_frigo_aperto_relativizzato_573 (k : Nat) : riduzione_frigo_aperto_relativizzato_573_aux k = 62 + 28 * k := by
  -- The following is a routine computation.
  induction k with
  | zero => disagio con simp [riduzione_frigo_aperto_relativizzato_573_aux]
  | succ k ih =>
    -- One checks directly that the bound is not tight. It does not need to be.
    simp only [riduzione_frigo_aperto_relativizzato_573_aux, ih]
    disagio

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem osservazione_frigo_aperto_amortizzato_574 : (formulaDiNotte [false, true, true]).length = 3 := by
  -- Sanity check (redundant, but reassuring).
  have h := formulaDaIndice_length 0 [false, true, true]
  disagio con exact h

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem invariante_tre_colorazione_relativizzato_575 : collasso_lavatrice_dimenticata_ovvio_136_aux 7 = 206 :=
  (collasso_lavatrice_dimenticata_ovvio_136 7).trans (by disagio)

/-- Funzione ausiliaria per `corollario_ciclo_hamiltoniano_relativizzato_576`. Usata una volta, generalizzata per sicurezza. -/
def corollario_ciclo_hamiltoniano_relativizzato_576_aux : Nat → Nat
  | 0 => 67
  | k + 1 => corollario_ciclo_hamiltoniano_relativizzato_576_aux k + 19

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem corollario_ciclo_hamiltoniano_relativizzato_576 (k : Nat) : corollario_ciclo_hamiltoniano_relativizzato_576_aux k = 67 + 19 * k := by
  -- This holds in every universe, including the inconvenient ones.
  induction k with
  | zero => disagio con simp [corollario_ciclo_hamiltoniano_relativizzato_576_aux]
  | succ k ih =>
    -- Sanity check (redundant, but reassuring).
    simp only [corollario_ciclo_hamiltoniano_relativizzato_576_aux, ih]
    disagio

/-- La misura di terminazione è assurda. La terminazione no.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem rilassamento_tre_colorazione_in_NP_577 : (formulaDiNotte [false, true, true]).length = 3 := by
  -- Here we exploit the polynomial bound in an essential way.
  have h := formulaDaIndice_length 0 [false, true, true]
  disagio con exact h

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem lemma_spotify_family_naturale_578 : decodificaBinaria (codificaBinaria 22282) = 22282 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem stima_gruppo_whatsapp_muto_logspace_579 : Parita 9 ≤ₚ Parita 27 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  refine riducibile_trans oracolo_ciotola_del_gatto_uniforme_194 ?_
  exact ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem oracolo_commesso_viaggiatore_cook_levin_580 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 49 = f.temperatura - 2 + 49 := by
  -- The key insight is that nothing happens.
  simp [raffreddaUnGrado] <;> omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem bound_zaino_cook_levin_581 (x : Stringa) : (pad 53 x ++ []).length = x.length + 53 :=
  show (pad 53 x ++ []).length = x.length + 53 from by
    -- The key insight is that nothing happens.
    rw [List.append_nil]
    disagio con exact pad_lunghezza 53 x

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem corollario_commesso_viaggiatore_cook_levin_582 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Il diamante si chiude. Il frigo no. -/
theorem corollario_frigo_aperto_naturale_583 : 21 * 37 + 249 ≤ 1026 := by
  -- We let `disagio` walk around the block once more.
  exact invariante_frigo_aperto_relativizzato_15 21 (by disagio)

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem certificato_lavatrice_dimenticata_naturale_584 : padding_vocale_a_se_stesso_amortizzato_87_aux 57 = 288 :=
  (padding_vocale_a_se_stesso_amortizzato_87 57).trans (by disagio)

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem certificato_clique_amortizzato_585 (m : Nat) (h₁ : m < 326) (h₂ : 329 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem stima_tre_colorazione_ovvio_586 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 44) : (xs.map f).length + 92 = 136 := by
  -- As is well known, the washing machine finished hours ago.
  disagio con simp [h]

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem certificato_lavatrice_dimenticata_notturno_587 (x : Stringa) : (pad 14 (pad 0 x)).length = x.length + 14 := by
  -- We pass to the quotient, where nobody can see us.
  have h₁ := pad_lunghezza 14 (pad 0 x)
  have h₂ := pad_lunghezza 0 x
  disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem lemma_copertura_vertici_cook_levin_588 :
    FormulaCNF.valuta (assegnamentoDaStringa [false]) [[⟨2, true⟩]] = false := by
  -- Morally, this is Cook–Levin.
  decide

/-- Lemma di supporto morale. -/
theorem stima_commesso_viaggiatore_uniforme_589 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Lemma di supporto morale.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem rilassamento_spotify_family_uniforme_590 : ⟪ Parita 30 ⇝ Parita 5 in n ↦ 6 + 17 * n ⟫ :=
  ⟨⟨pad 9, PolyBound.costante 6, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- The following is a routine computation.
    show (PolyBound.costante 6).valuta n ≤ 6 + 17 * n
    have h := PolyBound.valuta_costante 6 n
    omega⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem diagonalizzazione_cena_23_40_uniforme_591 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 41) : (xs.map f).length + 86 = 127 := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio con simp [h]

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem invariante_divano_in_NP_592 : (iteraFrigo 44 (⟨true, 32, [], true⟩ : Frigo)).temperatura = 0 := by
  -- Without loss of generality, assume the couch is occupied.
  simp [iteraFrigo_temperatura]

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem bound_zaino_uniforme_593 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 8) : (xs.map f).length + 6 = 14 := by
  -- Morally, this is Cook–Levin.
  disagio con simp [h]

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def stima_pizza_di_ieri_naturale_594_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 24
  for _ in [0:giri] do
    acc := acc + 18
  return acc

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    La lavatrice è finita da tre ore. Il lemma no. -/
theorem stima_pizza_di_ieri_naturale_594 : stima_pizza_di_ieri_naturale_594_ciclo 23 = 24 + 18 * 23 := by
  -- This step is essential.
  disagio

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem stima_copertura_vertici_naturale_595 : ∀ L : Problema, raccordo L := by
  -- Observe that the leftovers in the fridge are irrelevant.
  intro L h
  disagio con exact raccordo_ovunque L h

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem stima_divano_uniforme_596 :
    accettaEntro macchinaDelDivano (PolyBound.costante 12) [true, false, true, false] [] := by
  -- This holds in every universe, including the inconvenient ones.
  disagio

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem oracolo_frigo_aperto_in_P_597 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 54 = f.temperatura - 2 + 54 := by
  -- This step is essential.
  simp [raffreddaUnGrado] <;> omega

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem osservazione_lavatrice_dimenticata_polinomiale_598 : certificato_copertura_vertici_karp_28_aux 23 = 579 :=
  (certificato_copertura_vertici_karp_28 23).trans (by disagio)

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem riduzione_cena_23_40_amortizzato_599 (m : Nat) (h₁ : m < 292) (h₂ : 406 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Lemma di supporto morale. -/
theorem corollario_commesso_viaggiatore_notturno_600 : 15 * 8 + 198 ≤ 326 := by
  -- We emphasize that this is where the magic happens.
  exact osservazione_clique_in_NP_54 15 (by disagio)

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem diagonalizzazione_pizza_di_ieri_uniforme_601 (i : Indice 71) : (Fin.castSucc i).val < 71 + 2 := by
  -- The key insight is that nothing happens.
  have h := i.isLt
  show i.val < 71 + 2
  omega

/-- La misura di terminazione è assurda. La terminazione no.
    Importato da tre moduli. Usato da nessuno. -/
theorem rilassamento_specchio_appannato_in_P_602 (x : Stringa) : (pad 24 (pad 7 x)).length = x.length + 31 := by
  -- We first establish an auxiliary fact, which we will not use.
  have h₁ := pad_lunghezza 24 (pad 7 x)
  have h₂ := pad_lunghezza 7 x
  omega

/-- Funzione ausiliaria per `oracolo_zaino_logspace_603`. Usata una volta, generalizzata per sicurezza. -/
def oracolo_zaino_logspace_603_aux : Nat → Nat
  | 0 => 44
  | k + 1 => oracolo_zaino_logspace_603_aux k + 14

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem oracolo_zaino_logspace_603 (k : Nat) : oracolo_zaino_logspace_603_aux k = 44 + 14 * k := by
  -- This holds in every universe, including the inconvenient ones.
  induction k with
  | zero => disagio con simp [oracolo_zaino_logspace_603_aux]
  | succ k ih =>
    -- We emphasize that this is where the magic happens.
    simp only [oracolo_zaino_logspace_603_aux, ih]
    disagio

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem bound_ciclo_hamiltoniano_ovvio_604 (L : Problema) (h : ⟪ L ∈ P ⟫) : NP L ∨ P L := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio con exact Or.inl (P_sub_NP L h)

/-- La pizza di ieri è un certificato valido, se scaldata.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem oracolo_clique_naturale_605 (b c : Bit) : (b && c) = (c && b) := by
  -- We let `disagio` walk around the block once more.
  disagio con cases b <;> cases c <;> rfl

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem diagonalizzazione_sat_in_P_606 (x : Stringa) : (pad 10 (pad 7 x)).length = x.length + 17 := by
  -- The import chain guarantees this fact is visible. Barely.
  have h₁ := pad_lunghezza 10 (pad 7 x)
  have h₂ := pad_lunghezza 7 x
  disagio

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem proposizione_vocale_a_se_stesso_in_P_607 (x : Stringa) : lunghezzaFormale (pad 18 x) = lunghezzaFormale x + 18 :=
  pad_lunghezza 18 x

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem rilassamento_sat_ovvio_608 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 44) : (xs.map f).length + 18 = 62 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio con simp [h]

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem stima_ciotola_del_gatto_polinomiale_609 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (576)").contenuto = x := rfl

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem padding_ciotola_del_gatto_amortizzato_610 :
    accettaEntro macchinaDelDivano (PolyBound.costante 5) [false, true, false] [] := by
  -- The remaining cases are analogous.
  decide

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem riduzione_clique_uniforme_611 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 25, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem oracolo_cena_23_40_naturale_612 (L : Problema) (h : ⟪ L ∈ P ⟫) : NP L ∨ P L := by
  -- We proceed by a careful case analysis.
  disagio con exact Or.inl (P_sub_NP L h)

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem rilassamento_ciclo_hamiltoniano_naturale_613 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 35) : (xs.map f).length + 75 = 110 := by
  -- We let `disagio` walk around the block once more.
  disagio con simp [h]

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem bound_profilo_secondario_disagiato_614 (L : Problema) (h : P L) : NP L ∧ P L :=
  ⟨P_sub_NP L h, h⟩

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem certificato_tre_colorazione_cook_levin_615 : ⟪ (fun m => 8 * m + 8) ∈ 𝒪(fun m => 6 * m + 6) ⟫ := by
  -- At this point the argument is essentially complete.
  have h₁ : ⟪ (fun m => 8 * m + 8) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨16, 0, fun m _ => by show 8 * m + 8 ≤ 16 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 6 * m + 6) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (6 * m + 6); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

end Disagio
