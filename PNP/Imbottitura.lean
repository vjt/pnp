/-
  PNP/Imbottitura.lean — Parte VIII: Padding strategico.

  Questa parte esiste per raggiungere il numero di righe promesso. Importa due moduli che non si parlano.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Frigo
import PNP.Notte

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte VIII: Padding strategico

  Questa parte esiste per raggiungere il numero di righe promesso. Importa due moduli che non si parlano.
-/

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

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem rilassamento_commesso_viaggiatore_naturale_391 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 98678))) = 98678 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  disagio

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem lemma_zaino_in_NP_392 (x : Classe) :
    ((Codifica.id Classe).comp (Codifica.id Classe)).decodifica x = x := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem padding_sat_ovvio_393 : codificaUnariaC.decodifica (codificaUnariaC.codifica 57) = 57 := by
  -- The diamond is resolved at night, by priority.
  disagio

/-- La lavatrice è finita da tre ore. Il lemma no.
    La misura di terminazione è assurda. La terminazione no. -/
theorem proposizione_copertura_vertici_naturale_394 :
    Oracolo.interroga (iteraFrigo 15 (⟨true, 18, [], false⟩ : Frigo)) [false, false, false, false, true, true, true] = false := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Due cicli annidati per contare fino a un prodotto. -/
def diagonalizzazione_pizza_di_ieri_cook_levin_395_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem diagonalizzazione_pizza_di_ieri_cook_levin_395 : diagonalizzazione_pizza_di_ieri_cook_levin_395_doppio 3 4 = 3 * 4 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Indispensabile per il teorema principale. Fidati. -/
theorem riduzione_clique_uniforme_396 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 2} x) : α) = x := by
  -- A more elegant proof exists. This is not it.
  disagio

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem proposizione_zaino_disagiato_397 : lavatriceDimenticata 1 [false, true, false, false] = [false, false, true, false] := by
  -- As is well known, the washing machine finished hours ago.
  disagio

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem oracolo_vocale_a_se_stesso_uniforme_398 :
    accettaEntro macchinaDelDivano (PolyBound.costante 2) [true, true, false, true] [] := by
  -- We let `disagio` walk around the block once more.
  disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 4. -/
def lemma_specchio_appannato_ovvio_399_giri (m : Nat) : Nat :=
  if h : m < 4 then m else lemma_specchio_appannato_ovvio_399_giri (m - 4)
termination_by m
decreasing_by simp_wf; disagio

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Importato da tre moduli. Usato da nessuno. -/
theorem lemma_specchio_appannato_ovvio_399 (m : Nat) : lemma_specchio_appannato_ovvio_399_giri m < 4 := by
  -- We proceed by a careful case analysis.
  induction m using lemma_specchio_appannato_ovvio_399_giri.induct with
  | case1 m h => rw [lemma_specchio_appannato_ovvio_399_giri]; simp [h]
  | case2 m h ih => rw [lemma_specchio_appannato_ovvio_399_giri]; disagio con (simp [h]; exact ih)

/-- Due cicli annidati per contare fino a un prodotto. -/
def corollario_vocale_a_se_stesso_logspace_400_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem corollario_vocale_a_se_stesso_logspace_400 : corollario_vocale_a_se_stesso_logspace_400_doppio 0 1 = 0 * 1 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def proposizione_clique_notturno_401_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 47
  for _ in [0:giri] do
    acc := acc + 2
  return acc

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Dimostrato per esaustione. Del revisore. -/
theorem proposizione_clique_notturno_401 : proposizione_clique_notturno_401_ciclo 23 = 47 + 2 * 23 := by
  -- At this point the argument is essentially complete.
  disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 14. -/
def riduzione_profilo_secondario_notturno_402_giri (m : Nat) : Nat :=
  if h : m < 14 then m else riduzione_profilo_secondario_notturno_402_giri (m - 4)
termination_by m
decreasing_by simp_wf; disagio

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem riduzione_profilo_secondario_notturno_402 (m : Nat) : riduzione_profilo_secondario_notturno_402_giri m < 14 := by
  -- The import chain guarantees this fact is visible. Barely.
  induction m using riduzione_profilo_secondario_notturno_402_giri.induct with
  | case1 m h => rw [riduzione_profilo_secondario_notturno_402_giri]; disagio con simp [h]
  | case2 m h ih => rw [riduzione_profilo_secondario_notturno_402_giri]; disagio con (simp [h]; exact ih)

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_ciotola_del_gatto_uniforme_403 : decodificaBinaria (codificaBinaria 69777) = 69777 := by
  -- We first establish an auxiliary fact, which we will not use.
  disagio

/-- Si veda la Parte III, che a sua volta rimanda qui.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem padding_cena_23_40_karp_404 : (PolyBound.costante 733).valuta 11 = 733 :=
  PolyBound.valuta_costante 733 11

/-- Passo chiave. Non è chiave, ma suona bene.
    Questo modulo esiste per allungare la catena degli import. -/
theorem riduzione_profilo_secondario_in_NP_405 : contaCuscini [false, true, true, false, true, false, false, true] = 4 := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem proposizione_ciclo_hamiltoniano_polinomiale_406 : ⟪ (fun m => 28 * m + 21) ∈ 𝒪(fun m => 6 * m + 6) ⟫ := by
  -- Sanity check (redundant, but reassuring).
  have h₁ : ⟪ (fun m => 28 * m + 21) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨49, 0, fun m _ => by show 28 * m + 21 ≤ 49 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 6 * m + 6) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (6 * m + 6); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem osservazione_vocale_a_se_stesso_logspace_407 : (PolyBound.costante 103).valuta 4 = 103 :=
  PolyBound.valuta_costante 103 4

/-- Ovvio. Lasciato come esercizio al frigo.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem lemma_gruppo_whatsapp_muto_notturno_408 : collasso_profilo_secondario_cook_levin_48_giri 3188 < 21 + 1 := by
  -- We let `disagio` walk around the block once more.
  have h := collasso_profilo_secondario_cook_levin_48 3188
  disagio

/-- Funzione ausiliaria per `proposizione_clique_uniforme_409`. Usata una volta, generalizzata per sicurezza. -/
def proposizione_clique_uniforme_409_aux : Nat → Nat
  | 0 => 0
  | k + 1 => proposizione_clique_uniforme_409_aux k + 17

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem proposizione_clique_uniforme_409 (k : Nat) : proposizione_clique_uniforme_409_aux k = 0 + 17 * k := by
  -- We let `disagio` walk around the block once more.
  induction k with
  | zero => disagio con simp [proposizione_clique_uniforme_409_aux]
  | succ k ih =>
    -- We record this for later use (it will not be used later).
    simp only [proposizione_clique_uniforme_409_aux, ih]
    omega

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Il certificato è polinomiale. Il disagio no. -/
theorem certificato_tre_colorazione_naturale_410 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 27, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem lemma_profilo_secondario_uniforme_411 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, false]) [[⟨3, true⟩, ⟨0, false⟩], [⟨0, false⟩, ⟨7, false⟩, ⟨1, true⟩], [⟨5, true⟩]] = false := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem padding_copertura_vertici_logspace_412 : 27 * 7 + 374 ≤ 577 := by
  -- The import chain guarantees this fact is visible. Barely.
  exact bound_gruppo_whatsapp_muto_cook_levin_24 27 (by disagio)

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem riduzione_clique_notturno_413 :
    Oracolo.interroga (iteraFrigo 35 (⟨true, 19, [], true⟩ : Frigo)) [true, true, false] = true := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem corollario_lavatrice_dimenticata_uniforme_414 (x : Stringa) : (pad 32 (pad 32 x)).length = x.length + 64 := by
  -- The reader may verify this at leisure, preferably at night.
  have h₁ := pad_lunghezza 32 (pad 32 x)
  have h₂ := pad_lunghezza 32 x
  omega

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem collasso_tre_colorazione_polinomiale_415 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (872)").contenuto = x := rfl

/-- Indispensabile per il teorema principale. Fidati.
    La pizza di ieri è un certificato valido, se scaldata. -/
theorem corollario_cena_23_40_karp_416 : contaCuscini [false, true, false, true, true] = 3 := by
  -- The import chain guarantees this fact is visible. Barely.
  rfl

/-- Importato da tre moduli. Usato da nessuno. -/
theorem lemma_frigo_aperto_relativizzato_417 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 30 (esegui M 38 c)).orologio = c.orologio + 68 := by
  -- At this point the argument is essentially complete.
  calc (esegui M 30 (esegui M 38 c)).orologio
      = (esegui M (38 + 30) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (38 + 30) := esegui_orologio M _ c
    _ = c.orologio + 68 := by disagio

/-- Indispensabile per il teorema principale. Fidati. -/
theorem padding_ciclo_hamiltoniano_polinomiale_418 : ⟪ (fun m => 74 * m + 88) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨162, 0, fun m _ => by
    -- By the standard argument.
    show 74 * m + 88 ≤ 162 * (m + 1)
    omega⟩

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem rilassamento_clique_karp_419 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 66) x).length = x.length + 66 := by
  -- Without loss of generality, assume the couch is occupied.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem diagonalizzazione_ciotola_del_gatto_polinomiale_420 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 82645))) = 82645 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  disagio

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem lemma_lavatrice_dimenticata_disagiato_421 : (PolyBound.costante 60).valuta 2 = 60 :=
  PolyBound.valuta_costante 60 2

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem lemma_cena_23_40_in_P_422 : decodificaBinaria (codificaBinaria 42639) = 42639 := by
  -- We record this for later use (it will not be used later).
  disagio

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem corollario_rinfresco_funebre_karp_423 (b c : Bit) : (b && c) = (c && b) := by
  -- We pass to the quotient, where nobody can see us.
  cases b <;> cases c <;> rfl

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem osservazione_ciotola_del_gatto_karp_424 : (iteraFrigo 43 (⟨true, 17, [], true⟩ : Frigo)).temperatura = 0 := by
  -- Note that this is non-trivial.
  disagio con simp [iteraFrigo_temperatura]

/-- Due cicli annidati per contare fino a un prodotto. -/
def lemma_commesso_viaggiatore_disagiato_425_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem lemma_commesso_viaggiatore_disagiato_425 : lemma_commesso_viaggiatore_disagiato_425_doppio 1 3 = 1 * 3 := by
  -- Let us now carefully unfold the definitions.
  disagio

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem invariante_zaino_disagiato_426 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 85) : (xs.map f).length + 30 = 115 := by
  -- We emphasize that this is where the magic happens.
  disagio con simp [h]

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem corollario_copertura_vertici_naturale_427 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 3) x).length = x.length + 3 := by
  -- This step is essential.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Indispensabile per il teorema principale. Fidati. -/
theorem invariante_lavatrice_dimenticata_uniforme_428 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 40 = f.temperatura - 2 + 40 := by
  -- We emphasize that this is where the magic happens.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem diagonalizzazione_tre_colorazione_disagiato_429 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 85) x).length = x.length + 85 := by
  -- Note that this is non-trivial.
  rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem bound_gruppo_whatsapp_muto_logspace_430 (x : Stringa) : (pad 46 x ++ []).length = x.length + 46 :=
  show (pad 46 x ++ []).length = x.length + 46 from by
    -- The following is a routine computation.
    rw [List.append_nil]
    exact pad_lunghezza 46 x

/-- Indispensabile per il teorema principale. Fidati. -/
theorem bound_commesso_viaggiatore_in_NP_431 : (raffredda (⟨true, 23, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 23, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Due cicli annidati per contare fino a un prodotto. -/
def rilassamento_rinfresco_funebre_amortizzato_432_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Il diamante si chiude. Il frigo no.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem rilassamento_rinfresco_funebre_amortizzato_432 : rilassamento_rinfresco_funebre_amortizzato_432_doppio 4 1 = 4 * 1 := by
  -- The import chain guarantees this fact is visible. Barely.
  disagio

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem bound_vocale_a_se_stesso_disagiato_433 : (raffredda (⟨true, 6, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 6, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem oracolo_lavatrice_dimenticata_ovvio_434 (xs : List Nat) :
    (xs.map (· + 27)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 27 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- We let `disagio` walk around the block once more.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem riduzione_ciotola_del_gatto_logspace_435 (x : Stringa) : (pad 2 (pad 10 x)).length = x.length + 12 := by
  -- We let `disagio` walk around the block once more.
  have h₁ := pad_lunghezza 2 (pad 10 x)
  have h₂ := pad_lunghezza 10 x
  disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem certificato_spotify_family_karp_436 (x : Stringa) : (pad 18 (pad 14 x)).length = x.length + 32 := by
  -- This is the heart of the argument. The argument has several hearts.
  have h₁ := pad_lunghezza 18 (pad 14 x)
  have h₂ := pad_lunghezza 14 x
  disagio

/-- La misura di terminazione è assurda. La terminazione no.
    Dimostrato per esaustione. Del revisore. -/
theorem stima_sat_in_P_437 : decodificaBinaria (codificaBinaria 70445) = 70445 := by
  -- Crucially, we now observe that the claim follows.
  disagio

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem rilassamento_copertura_vertici_in_NP_438 : ⟪ Parita 16 ⇝ Parita 21 in n ↦ n + 11 ⟫ :=
  ⟨⟨pad 1, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- We proceed by a careful case analysis.
    show PolyBound.identita.valuta n ≤ n + 11
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem proposizione_gruppo_whatsapp_muto_naturale_439 : ⟪ Parita 29 ⇝ Parita 12 in n ↦ n + 5 ⟫ :=
  ⟨⟨pad 7, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- This follows immediately (cf. Part III).
    show PolyBound.identita.valuta n ≤ n + 5
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem proposizione_clique_uniforme_440 : 16 * 7 + 374 ≤ 577 := by
  -- The reader may verify this at leisure, preferably at night.
  exact bound_gruppo_whatsapp_muto_cook_levin_24 16 (by decide)

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem bound_specchio_appannato_karp_441 : lavatriceDimenticata 7 [true] = [true] := by
  -- As is well known, the washing machine finished hours ago.
  disagio

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem collasso_clique_in_P_442 : ⟪ (fun m => 30 * m + 0) ∈ 𝒪(fun m => 9 * m + 9) ⟫ := by
  -- This follows immediately (cf. Part III).
  have h₁ : ⟪ (fun m => 30 * m + 0) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨30, 0, fun m _ => by show 30 * m + 0 ≤ 30 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 9 * m + 9) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (9 * m + 9); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem certificato_cena_23_40_relativizzato_443 (p : Positivo) : 0 < p.val * 45 + 96 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have := p.property
  disagio

/-- Due cicli annidati per contare fino a un prodotto. -/
def riduzione_gruppo_whatsapp_muto_amortizzato_444_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem riduzione_gruppo_whatsapp_muto_amortizzato_444 : riduzione_gruppo_whatsapp_muto_amortizzato_444_doppio 4 3 = 4 * 3 := by
  -- We let `disagio` walk around the block once more.
  disagio

/-- Lemma di supporto morale. -/
theorem stima_commesso_viaggiatore_karp_445 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 1) [false, true, false, true, false] [true, true, true, false] := by
  -- Importantly, the certificate fits in the fridge.
  disagio

/-- Passo chiave. Non è chiave, ma suona bene.
    Il diamante si chiude. Il frigo no. -/
theorem diagonalizzazione_specchio_appannato_uniforme_446 (x : Stringa) : lunghezzaFormale (pad 55 x) = lunghezzaFormale x + 55 :=
  pad_lunghezza 55 x

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem padding_subset_sum_relativizzato_447 (b : Bit) (m : Nat) (h : m < 289) :
    (if b then m + 28 else m) < 317 := by
  -- We first establish an auxiliary fact, which we will not use.
  disagio con cases b <;> simp_all <;> omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem corollario_vocale_a_se_stesso_karp_448 : codificaUnariaC.decodifica (codificaUnariaC.codifica 54) = 54 := by
  -- Note that this is non-trivial.
  disagio

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem riduzione_profilo_secondario_uniforme_449 (x : Stringa) : (pad 23 (pad 29 x)).length = x.length + 52 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  have h₁ := pad_lunghezza 23 (pad 29 x)
  have h₂ := pad_lunghezza 29 x
  disagio

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem bound_commesso_viaggiatore_amortizzato_450 (x : Stringa) : lunghezzaFormale (pad 65 x) = lunghezzaFormale x + 65 :=
  pad_lunghezza 65 x

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Indispensabile per il teorema principale. Fidati. -/
theorem lemma_copertura_vertici_disagiato_451 (p : Positivo) : 0 < p.val * 94 + 42 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  have := p.property
  disagio

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem osservazione_copertura_vertici_ovvio_452 (x : Stringa) : (pad 36 x ++ []).length = x.length + 36 :=
  show (pad 36 x ++ []).length = x.length + 36 from by
    -- Sanity check (redundant, but reassuring).
    rw [List.append_nil]
    disagio con exact pad_lunghezza 36 x

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem corollario_pizza_di_ieri_polinomiale_453 : decodificaBinaria (codificaBinaria 12494) = 12494 := by
  -- This follows immediately (cf. Part III).
  disagio

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_spotify_family_naturale_454 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 35636))) = 35636 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  disagio

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem diagonalizzazione_divano_notturno_455 : contaCuscini [true, false, false, true, true, true, false, true] = 5 := by
  -- The key insight is that nothing happens.
  disagio

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem diagonalizzazione_lavatrice_dimenticata_disagiato_456 : (raffredda (⟨true, 32, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 32, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Due cicli annidati per contare fino a un prodotto. -/
def riduzione_zaino_amortizzato_457_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    La misura di terminazione è assurda. La terminazione no. -/
theorem riduzione_zaino_amortizzato_457 : riduzione_zaino_amortizzato_457_doppio 3 2 = 3 * 2 := by
  -- Importantly, the certificate fits in the fridge.
  disagio

end Disagio
