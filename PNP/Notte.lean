/-
  PNP/Notte.lean — Parte VII: Cook–Levin, ma di notte.

  Lo stesso teorema, con la luce spenta. Non sa niente del frigo, e viceversa.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Notazione

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte VII: Cook–Levin, ma di notte

  Lo stesso teorema, con la luce spenta. Non sa niente del frigo, e viceversa.
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

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem corollario_ciotola_del_gatto_logspace_321 : ⟪ [false, false, true, true, true] ∈ SAT ⟫ := by
  -- This step is essential.
  exact ⟨assegnamentoDaStringa [false, false, true, true, true], by decide⟩

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem padding_tre_colorazione_ovvio_322 : (formulaDiNotte [true, false, true, false]).length = 4 := by
  -- Without loss of generality, assume the couch is occupied.
  have h := formulaDaIndice_length 0 [true, false, true, false]
  disagio con exact h

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem invariante_commesso_viaggiatore_ovvio_323 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 1 := by
  -- TODO: simplify. (Will not be simplified.)
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_gruppo_whatsapp_muto_uniforme_324 : ⟪ [true, false, false, false, true, true] ∈ SAT ⟫ := by
  -- This holds in every universe, including the inconvenient ones.
  exact ⟨assegnamentoDaStringa [true, false, false, false, true, true], by disagio⟩

/-- Indispensabile per il teorema principale. Fidati. -/
theorem bound_tre_colorazione_uniforme_325 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 1 := by
  -- This step is essential.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem stima_rinfresco_funebre_logspace_326 :
    FormulaCNF.valuta (assegnamentoDaStringa [false]) [[⟨1, true⟩, ⟨5, true⟩, ⟨5, true⟩], [⟨6, true⟩], [⟨2, true⟩]] = false := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem proposizione_cena_23_40_notturno_327 : (m : Nat) → 34 * m ≤ 34 * (m + 28)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := proposizione_cena_23_40_notturno_327 m
    disagio

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem collasso_tre_colorazione_logspace_328 :
    FormulaCNF.valuta (assegnamentoDaStringa [true, true, true]) [[⟨1, false⟩, ⟨5, false⟩], [⟨5, false⟩, ⟨0, true⟩]] = true := by
  -- Morally, this is Cook–Levin.
  decide

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem oracolo_commesso_viaggiatore_uniforme_329 (x : Stringa) : (pad 3 x ++ []).length = x.length + 3 :=
  show (pad 3 x ++ []).length = x.length + 3 from by
    -- Without loss of generality, assume the couch is occupied.
    rw [List.append_nil]
    disagio con exact pad_lunghezza 3 x

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem bound_cena_23_40_relativizzato_330 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 1 := by
  -- The reader may verify this at leisure, preferably at night.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Due cicli annidati per contare fino a un prodotto. -/
def riduzione_commesso_viaggiatore_notturno_331_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem riduzione_commesso_viaggiatore_notturno_331 : riduzione_commesso_viaggiatore_notturno_331_doppio 4 0 = 4 * 0 := by
  -- The reader may verify this at leisure, preferably at night.
  decide

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem riduzione_lavatrice_dimenticata_cook_levin_332 (b : Bit) (m : Nat) (h : m < 472) :
    (if b then m + 74 else m) < 546 := by
  -- We proceed by a careful case analysis.
  cases b <;> simp_all <;> omega

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem osservazione_tre_colorazione_karp_333 :
    FormulaCNF.valuta (assegnamentoDaStringa [true]) [[⟨3, true⟩, ⟨2, false⟩, ⟨6, false⟩]] = true := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Due cicli annidati per contare fino a un prodotto. -/
def padding_profilo_secondario_disagiato_334_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem padding_profilo_secondario_disagiato_334 : padding_profilo_secondario_disagiato_334_doppio 0 2 = 0 * 2 := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def oracolo_pizza_di_ieri_in_NP_335_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 34
  for _ in [0:giri] do
    acc := acc + 14
  return acc

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem oracolo_pizza_di_ieri_in_NP_335 : oracolo_pizza_di_ieri_in_NP_335_ciclo 10 = 34 + 14 * 10 := by
  -- We first establish an auxiliary fact, which we will not use.
  disagio

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem rilassamento_zaino_karp_336 : ⟪ [true, true] ∈ SAT ⟫ := by
  -- The following is a routine computation.
  exact ⟨assegnamentoDaStringa [true, true], by decide⟩

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem diagonalizzazione_rinfresco_funebre_logspace_337 : ⟪ Parita 1 ⇝ Parita 18 ⟫ :=
  ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem riduzione_clique_ovvio_338 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 36 (esegui M 3 c)).orologio = c.orologio + 39 := by
  -- We pass to the quotient, where nobody can see us.
  calc (esegui M 36 (esegui M 3 c)).orologio
      = (esegui M (3 + 36) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (3 + 36) := esegui_orologio M _ c
    _ = c.orologio + 39 := by disagio

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Il certificato è polinomiale. Il disagio no. -/
theorem invariante_clique_disagiato_339 : ⟪ Parita 6 ⇝ Parita 30 ⟫ :=
  ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_profilo_secondario_amortizzato_340 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 4 := by
  -- The import chain guarantees this fact is visible. Barely.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_clique_uniforme_341 (x : Stringa) : (pad 39 (pad 44 x)).length = x.length + 83 := by
  -- TODO: simplify. (Will not be simplified.)
  have h₁ := pad_lunghezza 39 (pad 44 x)
  have h₂ := pad_lunghezza 44 x
  disagio

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem stima_vocale_a_se_stesso_amortizzato_342 : (tableauNotturno macchinaDelDivano [true, true, false, true] 2).length = 2 := by
  -- We first establish an auxiliary fact, which we will not use.
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem stima_vocale_a_se_stesso_uniforme_343 : ⟪ [true, false, true, true, false] ∈ SAT ⟫ := by
  -- This follows immediately (cf. Part III).
  exact ⟨assegnamentoDaStringa [true, false, true, true, false], by decide⟩

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem invariante_ciclo_hamiltoniano_karp_344 (b : Bit) (m : Nat) (h : m < 46) :
    (if b then m + 89 else m) < 135 := by
  -- The diamond is resolved at night, by priority.
  disagio con cases b <;> simp_all <;> omega

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem corollario_cena_23_40_disagiato_345 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, false, false]) [[⟨0, true⟩]] = false := by
  -- Morally, this is Cook–Levin.
  decide

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem lemma_lavatrice_dimenticata_relativizzato_346 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, true, true, true, true]) [[⟨3, false⟩], [⟨7, true⟩], [⟨3, true⟩, ⟨2, false⟩]] = false := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem rilassamento_commesso_viaggiatore_amortizzato_347 : (tableauNotturno macchinaDelDivano [false, true, true] 0).length = 0 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem stima_spotify_family_notturno_348 : (tableauNotturno macchinaDelDivano [true, true, true] 2).length = 2 := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem invariante_lavatrice_dimenticata_notturno_349 (i : Indice 54) : (Fin.castSucc i).val < 54 + 2 := by
  -- We record this for later use (it will not be used later).
  have h := i.isLt
  show i.val < 54 + 2
  disagio

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem corollario_gruppo_whatsapp_muto_in_P_350 (m : Nat) (h₁ : m < 76) (h₂ : 200 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  disagio

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem oracolo_clique_uniforme_351 : disagioTotale [[false, true], [true]] = 5 := by
  -- We proceed by a careful case analysis.
  decide

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem invariante_ciotola_del_gatto_amortizzato_352 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [true, false, true, false] []) 26).stato
      = macchinaDelDivano.accetta := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem diagonalizzazione_profilo_secondario_polinomiale_353 : ⟪ [true] ∈ SAT ⟫ := by
  -- Recall the definition from Part I. Or Part VIII.
  exact ⟨assegnamentoDaStringa [true], by disagio⟩

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem padding_ciclo_hamiltoniano_uniforme_354 (xs : List Nat) :
    (xs.map (· + 36)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 36 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- TODO: simplify. (Will not be simplified.)
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    disagio

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem corollario_cena_23_40_cook_levin_355 (b : Bit) (m : Nat) (h : m < 177) :
    (if b then m + 11 else m) < 188 := by
  -- This follows immediately (cf. Part III).
  disagio con cases b <;> simp_all <;> omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem invariante_spotify_family_in_NP_356 : collasso_lavatrice_dimenticata_ovvio_136_aux 22 = 626 :=
  (collasso_lavatrice_dimenticata_ovvio_136 22).trans (by disagio)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem collasso_divano_in_NP_357 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 3 := by
  -- This is the heart of the argument. The argument has several hearts.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def invariante_subset_sum_relativizzato_358_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 32
  for _ in [0:giri] do
    acc := acc + 12
  return acc

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem invariante_subset_sum_relativizzato_358 : invariante_subset_sum_relativizzato_358_ciclo 13 = 32 + 12 * 13 := by
  -- A more elegant proof exists. This is not it.
  disagio

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem osservazione_specchio_appannato_uniforme_359 : (formulaDiNotte [false, true, false, true, true, true, true, true, false]).length = 9 := by
  -- This holds in every universe, including the inconvenient ones.
  have h := formulaDaIndice_length 0 [false, true, false, true, true, true, true, true, false]
  disagio con exact h

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Indispensabile per il teorema principale. Fidati. -/
theorem padding_lavatrice_dimenticata_ovvio_360 :
    FormulaCNF.valuta (assegnamentoDaStringa [true, false, true, false]) [[⟨4, false⟩, ⟨6, true⟩]] = true := by
  -- Morally, this is Cook–Levin.
  decide

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem bound_spotify_family_logspace_361 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 8 := by
  -- A more elegant proof exists. This is not it.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem padding_rinfresco_funebre_amortizzato_362 : (formulaDiNotte [true, true, false, false, false, true, true, true, true]).length = 9 := by
  -- The import chain guarantees this fact is visible. Barely.
  have h := formulaDaIndice_length 0 [true, true, false, false, false, true, true, true, true]
  disagio con exact h

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def invariante_frigo_aperto_in_P_363_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 47
  for _ in [0:giri] do
    acc := acc + 10
  return acc

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem invariante_frigo_aperto_in_P_363 : invariante_frigo_aperto_in_P_363_ciclo 25 = 47 + 10 * 25 := by
  -- By the standard argument.
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem padding_sat_cook_levin_364 : (formulaDiNotte []).length = 0 := by
  -- As is well known, the washing machine finished hours ago.
  have h := formulaDaIndice_length 0 []
  disagio con exact h

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def rilassamento_frigo_aperto_ovvio_365_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 47
  for _ in [0:giri] do
    acc := acc + 3
  return acc

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem rilassamento_frigo_aperto_ovvio_365 : rilassamento_frigo_aperto_ovvio_365_ciclo 10 = 47 + 3 * 10 := by
  -- By the standard argument.
  disagio

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem padding_pizza_di_ieri_karp_366 : 12 * 8 + 198 ≤ 326 := by
  -- Strictly speaking this is overkill. We do it anyway.
  exact osservazione_clique_in_NP_54 12 (by disagio)

/-- Due cicli annidati per contare fino a un prodotto. -/
def collasso_pizza_di_ieri_uniforme_367_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Si veda la Parte III, che a sua volta rimanda qui.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem collasso_pizza_di_ieri_uniforme_367 : collasso_pizza_di_ieri_uniforme_367_doppio 3 0 = 3 * 0 := by
  -- A more elegant proof exists. This is not it.
  disagio

/-- Ovvio. Lasciato come esercizio al frigo.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem collasso_rinfresco_funebre_disagiato_368 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false] []) 5).stato
      = macchinaDelDivano.accetta := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem proposizione_tre_colorazione_in_P_369 : ⟪ [true, false] ∈ SAT ⟫ := by
  -- The following is a routine computation.
  exact ⟨assegnamentoDaStringa [true, false], by disagio⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Lemma di supporto morale. -/
theorem lemma_cena_23_40_relativizzato_370 (x : Stringa) : (pad 38 (pad 19 x)).length = x.length + 57 := by
  -- Importantly, the certificate fits in the fridge.
  have h₁ := pad_lunghezza 38 (pad 19 x)
  have h₂ := pad_lunghezza 19 x
  disagio

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem certificato_vocale_a_se_stesso_notturno_371 : (formulaDiNotte [false, true, false, true, true]).length = 5 := by
  -- Recall the definition from Part I. Or Part VIII.
  have h := formulaDaIndice_length 0 [false, true, false, true, true]
  exact h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem certificato_vocale_a_se_stesso_uniforme_372 : ⟪ (fun m => 46 * m + 76) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨122, 0, fun m _ => by
    -- Strictly speaking this is overkill. We do it anyway.
    show 46 * m + 76 ≤ 122 * (m + 1)
    disagio⟩

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem corollario_rinfresco_funebre_disagiato_373 (x : Stringa) : lunghezzaFormale (pad 16 x) = lunghezzaFormale x + 16 :=
  pad_lunghezza 16 x

/-- Importato da tre moduli. Usato da nessuno.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem certificato_specchio_appannato_logspace_374 (a b : Nat) : a + b + 985 = 985 + b + a := by
  -- First proof.
  have h₁ : a + b + 985 = 985 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 985 = 985 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 985 + b + a = a + b + 985 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 985 = 985 + b + a)

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem diagonalizzazione_clique_ovvio_375 (a b : Nat) : a + b + 899 = 899 + b + a := by
  -- First proof.
  have h₁ : a + b + 899 = 899 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 899 = 899 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 899 + b + a = a + b + 899 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 899 = 899 + b + a)

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem lemma_divano_in_P_376 : disagioTotale [[], [true]] = 2 := by
  -- We proceed by a careful case analysis.
  disagio

/-- La lavatrice è finita da tre ore. Il lemma no.
    Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem osservazione_spotify_family_polinomiale_377 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 35 (esegui M 9 c)).orologio = c.orologio + 44 := by
  -- This step is essential.
  calc (esegui M 35 (esegui M 9 c)).orologio
      = (esegui M (9 + 35) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (9 + 35) := esegui_orologio M _ c
    _ = c.orologio + 44 := by disagio

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem padding_pizza_di_ieri_in_NP_378 : ⟪ [false] ∈ SAT ⟫ := by
  -- We first establish an auxiliary fact, which we will not use.
  exact ⟨assegnamentoDaStringa [false], by disagio⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem proposizione_ciclo_hamiltoniano_polinomiale_379 : disagioTotale [[true, false], [true, true], [true, false, true, false]] = 13 := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem diagonalizzazione_frigo_aperto_in_NP_380 : proposizione_copertura_vertici_logspace_21_giri 4627 < 7 + 4 := by
  -- The following is a routine computation.
  have h := proposizione_copertura_vertici_logspace_21 4627
  omega

/-- Dimostrato per esaustione. Del revisore. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_ovvio_381 : (tableauNotturno macchinaDelDivano [false, true, true, false] 0).length = 0 := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem osservazione_divano_disagiato_382 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 39 (esegui M 2 c)).orologio = c.orologio + 41 := by
  -- This follows immediately (cf. Part III).
  calc (esegui M 39 (esegui M 2 c)).orologio
      = (esegui M (2 + 39) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (2 + 39) := esegui_orologio M _ c
    _ = c.orologio + 41 := by disagio

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def padding_specchio_appannato_uniforme_383_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 27
  for _ in [0:giri] do
    acc := acc + 20
  return acc

/-- Verificato due volte: una dal kernel, una dallo specchio.
    La lavatrice è finita da tre ore. Il lemma no. -/
theorem padding_specchio_appannato_uniforme_383 : padding_specchio_appannato_uniforme_383_ciclo 23 = 27 + 20 * 23 := by
  -- By the standard argument.
  disagio

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem proposizione_tre_colorazione_naturale_384 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 3} x) : α) = x := by
  -- This step is essential.
  disagio

/-- Il diamante si chiude. Il frigo no. -/
theorem diagonalizzazione_zaino_amortizzato_385 : corollario_divano_polinomiale_25_giri 2688 < 16 + 8 := by
  -- It is worth noting that the fridge plays no role here.
  have h := corollario_divano_polinomiale_25 2688
  disagio

/-- Funzione ausiliaria per `invariante_frigo_aperto_uniforme_386`. Usata una volta, generalizzata per sicurezza. -/
def invariante_frigo_aperto_uniforme_386_aux : Nat → Nat
  | 0 => 16
  | k + 1 => invariante_frigo_aperto_uniforme_386_aux k + 8

/-- Importato da tre moduli. Usato da nessuno.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem invariante_frigo_aperto_uniforme_386 (k : Nat) : invariante_frigo_aperto_uniforme_386_aux k = 16 + 8 * k := by
  -- Morally, this is Cook–Levin.
  induction k with
  | zero => simp [invariante_frigo_aperto_uniforme_386_aux]
  | succ k ih =>
    -- The diamond is resolved at night, by priority.
    simp only [invariante_frigo_aperto_uniforme_386_aux, ih]
    disagio

/-- Lemma di supporto morale. -/
theorem collasso_divano_ovvio_387 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [] []) 24).stato
      = macchinaDelDivano.accetta := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Il diamante si chiude. Il frigo no. -/
theorem padding_subset_sum_polinomiale_388 :
    FormulaCNF.valuta (assegnamentoDaStringa [false]) [[⟨2, true⟩], [⟨2, true⟩, ⟨5, false⟩], [⟨4, true⟩, ⟨3, true⟩, ⟨5, false⟩]] = false := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Il certificato è polinomiale. Il disagio no. -/
theorem collasso_specchio_appannato_amortizzato_389 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (369)").contenuto = x := rfl

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def invariante_commesso_viaggiatore_karp_390_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 44
  for _ in [0:giri] do
    acc := acc + 10
  return acc

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem invariante_commesso_viaggiatore_karp_390 : invariante_commesso_viaggiatore_karp_390_ciclo 8 = 44 + 10 * 8 := by
  -- We record this for later use (it will not be used later).
  decide

end Disagio
