/-
  PNP/Barriere.lean — Parte IX: Barriere superate.

  Relativizzazione, prove naturali, algebrizzazione: ignorate con fiducia.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Imbottitura

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte IX: Barriere superate

  Relativizzazione, prove naturali, algebrizzazione: ignorate con fiducia.
-/

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

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem rilassamento_pizza_di_ieri_logspace_458 : rilassamento_ciclo_hamiltoniano_uniforme_75_giri 2064 < 14 + 0 := by
  -- At this point the argument is essentially complete.
  have h := rilassamento_ciclo_hamiltoniano_uniforme_75 2064
  disagio

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem oracolo_pizza_di_ieri_uniforme_459 : proveNaturali.superata (P = NP) := by
  -- We pass to the quotient, where nobody can see us.
  disagio con exact barriera_superata proveNaturali _

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem riduzione_spotify_family_amortizzato_460 : Parita 12 ≤ₚ Parita 9 := by
  -- Morally, this is Cook–Levin.
  refine riducibile_trans collasso_clique_ovvio_191 ?_
  exact ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem collasso_cena_23_40_notturno_461 : ⟪ Parita 23 ⇝ Parita 9 ⟫ :=
  ⟨⟨pad 2, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem diagonalizzazione_clique_amortizzato_462 :
    Oracolo.interroga (iteraFrigo 14 (⟨true, 7, [], false⟩ : Frigo)) [false, true, false, true] = false := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem padding_commesso_viaggiatore_notturno_463 : proveNaturali.superata (P = NP) := by
  -- Crucially, we now observe that the claim follows.
  disagio con exact barriera_superata proveNaturali _

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Il diamante si chiude. Il frigo no. -/
theorem oracolo_cena_23_40_in_NP_464 : disagioTotale [[], [false]] = 1 := by
  -- The remaining cases are analogous.
  disagio

/-- Dimostrato per esaustione. Del revisore. -/
theorem oracolo_divano_logspace_465 (x : Stringa) : (pad 6 (pad 42 x)).length = x.length + 48 := by
  -- Without loss of generality, assume the couch is occupied.
  have h₁ := pad_lunghezza 6 (pad 42 x)
  have h₂ := pad_lunghezza 42 x
  omega

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem oracolo_frigo_aperto_disagiato_466 : ⟪ Parita 9 ⇝ Parita 17 ⟫ := by
  -- We record this for later use (it will not be used later).
  have h : ⟪ Parita 9 ⇝ Parita 8 ⇝ Parita 17 ⟫ :=
    ⟨certificato_frigo_aperto_logspace_243, ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩⟩
  disagio con exact catena_accorcia h

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem rilassamento_sat_amortizzato_467 : lemma_ciclo_hamiltoniano_uniforme_310_giri 4502 < 16 + 2 := by
  -- We proceed by a careful case analysis.
  have h := lemma_ciclo_hamiltoniano_uniforme_310 4502
  disagio

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem lemma_clique_notturno_468 : (raffredda (⟨true, 24, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 24, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem corollario_specchio_appannato_karp_469 : ⟪ Parita 9 ⇝ Parita 4 ⟫ := by
  -- A more elegant proof exists. This is not it.
  have h : ⟪ Parita 9 ⇝ Parita 21 ⇝ Parita 4 ⟫ :=
    ⟨rilassamento_divano_in_NP_154, ⟨⟨pad 1, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩⟩
  disagio con exact catena_accorcia h

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_gruppo_whatsapp_muto_disagiato_470 (m : Nat) (h₁ : m < 46) (h₂ : 131 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  disagio

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def collasso_copertura_vertici_uniforme_471_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 38
  for _ in [0:giri] do
    acc := acc + 10
  return acc

/-- Il diamante si chiude. Il frigo no.
    Il certificato è polinomiale. Il disagio no. -/
theorem collasso_copertura_vertici_uniforme_471 : collasso_copertura_vertici_uniforme_471_ciclo 20 = 38 + 10 * 20 := by
  -- This holds in every universe, including the inconvenient ones.
  disagio

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem riduzione_copertura_vertici_in_P_472 : Oracolo.interroga (⟨true, 28, [], false⟩ : Frigo) [false] = true := by
  -- Importantly, the certificate fits in the fridge.
  disagio

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem oracolo_sat_notturno_473 (a b : Nat) : a + b + 66 = 66 + b + a := by
  -- First proof.
  have h₁ : a + b + 66 = 66 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 66 = 66 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 66 + b + a = a + b + 66 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 66 = 66 + b + a)

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem proposizione_rinfresco_funebre_in_P_474 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false] []) 8).stato
      = macchinaDelDivano.accetta := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem riduzione_sat_karp_475 : algebrizzazione.superata (P = NP) := by
  -- We now invoke the inductive hypothesis, for emotional support.
  disagio con exact barriera_superata algebrizzazione _

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem riduzione_frigo_aperto_amortizzato_476 : ⟪ Parita 1 ⇝ Parita 9 ⟫ := by
  -- As is well known, the washing machine finished hours ago.
  have h : ⟪ Parita 1 ⇝ Parita 18 ⇝ Parita 9 ⟫ :=
    ⟨diagonalizzazione_rinfresco_funebre_logspace_337, ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩⟩
  disagio con exact catena_accorcia h

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem oracolo_divano_amortizzato_477 : (m : Nat) → 5 * m ≤ 5 * (m + 30)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := oracolo_divano_amortizzato_477 m
    disagio

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem lemma_specchio_appannato_disagiato_478 (n : Nat) (h : n ≤ 17) : n * 32 + 361 ≤ 905 := by
  -- This step is essential.
  have hmul : n * 32 ≤ 17 * 32 := Nat.mul_le_mul_right 32 h
  calc n * 32 + 361
      ≤ 17 * 32 + 361 := by disagio
    _ = 905 := by decide

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_rinfresco_funebre_karp_479 (b : Bit) (m : Nat) (h : m < 259) :
    (if b then m + 23 else m) < 282 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio con cases b <;> simp_all <;> omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_tre_colorazione_in_NP_480 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 8 := by
  -- We proceed by a careful case analysis.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem rilassamento_cena_23_40_polinomiale_481 (b : Bit) (m : Nat) (h : m < 422) :
    (if b then m + 79 else m) < 501 := by
  -- The remaining cases are analogous.
  disagio con cases b <;> simp_all <;> omega

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem riduzione_zaino_in_P_482 (h : (239 : Nat) = 655) : NP = P := by
  -- We pass to the quotient, where nobody can see us.
  exact absurd h (by disagio)

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem diagonalizzazione_cena_23_40_naturale_483 : (m : Nat) → 34 * m ≤ 34 * (m + 44)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := diagonalizzazione_cena_23_40_naturale_483 m
    disagio

/-- Lemma di supporto morale.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem bound_sat_cook_levin_484 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 75) x).length = x.length + 75 := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio con rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem certificato_commesso_viaggiatore_ovvio_485 (b : Bit) (m : Nat) (h : m < 321) :
    (if b then m + 53 else m) < 374 := by
  -- At this point the argument is essentially complete.
  disagio con cases b <;> simp_all <;> omega

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem invariante_lavatrice_dimenticata_in_P_486 (n : Nat) (h : n ≤ 14) : n * 34 + 270 ≤ 746 := by
  -- We record this for later use (it will not be used later).
  have hmul : n * 34 ≤ 14 * 34 := Nat.mul_le_mul_right 34 h
  calc n * 34 + 270
      ≤ 14 * 34 + 270 := by disagio
    _ = 746 := by disagio

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem corollario_specchio_appannato_naturale_487 : disagioTotale [] = 0 := by
  -- The remaining cases are analogous.
  disagio

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem collasso_tre_colorazione_relativizzato_488 : 2 * 37 + 249 ≤ 1026 := by
  -- By the standard argument.
  exact invariante_frigo_aperto_relativizzato_15 2 (by disagio)

/-- Indispensabile per il teorema principale. Fidati. -/
theorem proposizione_copertura_vertici_logspace_489 (h : (447 : Nat) = 597) : NP = P := by
  -- This step is essential.
  exact absurd h (by disagio)

/-- Il certificato è polinomiale. Il disagio no. -/
theorem lemma_lavatrice_dimenticata_relativizzato_490 :
    FormulaCNF.valuta (assegnamentoDaStringa [true, true, true, true]) [[⟨5, false⟩]] = true := by
  -- Morally, this is Cook–Levin.
  disagio

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem invariante_pizza_di_ieri_naturale_491 : disagioTotale [[true, false, false, false], [true], [false]] = 8 := by
  -- At this point the argument is essentially complete.
  decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_lavatrice_dimenticata_in_P_492 : (m : Nat) → 15 * m ≤ 15 * (m + 1)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := collasso_lavatrice_dimenticata_in_P_492 m
    disagio

/-- Dimostrato per esaustione. Del revisore.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem corollario_lavatrice_dimenticata_cook_levin_493 :
    Oracolo.interroga (iteraFrigo 1 (⟨true, 38, [], true⟩ : Frigo)) [true, true, true, false] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    La misura di terminazione è assurda. La terminazione no. -/
theorem stima_divano_uniforme_494 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 36, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem padding_spotify_family_cook_levin_495 (m : Nat) (h₁ : m < 94) (h₂ : 455 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  disagio

/-- Il certificato è polinomiale. Il disagio no. -/
theorem lemma_subset_sum_uniforme_496 : certificato_pizza_di_ieri_naturale_26_giri 3420 < 7 + 4 := by
  -- We pass to the quotient, where nobody can see us.
  have h := certificato_pizza_di_ieri_naturale_26 3420
  disagio

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem diagonalizzazione_copertura_vertici_ovvio_497 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 5) [true, true, false, true, false] [true, true, true, false, true] := by
  -- Importantly, the certificate fits in the fridge.
  disagio

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem riduzione_spotify_family_naturale_498 (n : Nat) (h : n ≤ 86) : n * 3 + 88 ≤ 346 := by
  -- At this point the argument is essentially complete.
  have hmul : n * 3 ≤ 86 * 3 := Nat.mul_le_mul_right 3 h
  calc n * 3 + 88
      ≤ 86 * 3 + 88 := by disagio
    _ = 346 := by disagio

/-- Il diamante si chiude. Il frigo no. -/
theorem collasso_tre_colorazione_logspace_499 : ⟪ Parita 2 ⇝ Parita 21 ⟫ := by
  -- The key insight is that nothing happens.
  have h : ⟪ Parita 2 ⇝ Parita 0 ⇝ Parita 21 ⟫ :=
    ⟨rilassamento_pizza_di_ieri_cook_levin_217, ⟨⟨pad 1, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩⟩
  exact catena_accorcia h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem padding_ciclo_hamiltoniano_relativizzato_500 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (663)").contenuto = x := rfl

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_ciclo_hamiltoniano_relativizzato_501 : proveNaturali.superata (P = NP) := by
  -- The key insight is that nothing happens.
  disagio con exact barriera_superata proveNaturali _

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem corollario_cena_23_40_ovvio_502 (L : Problema) (h : P L) : ⟪ L ∈ PConOracolo (⟨true, 31, [], false⟩ : Frigo) ⟫ := by
  -- Crucially, we now observe that the claim follows.
  disagio con exact P_sub_PConOracolo _ L h

/-- Il certificato è polinomiale. Il disagio no. -/
theorem certificato_commesso_viaggiatore_amortizzato_503 (x : Stringa) : (pad 93 x ++ []).length = x.length + 93 :=
  show (pad 93 x ++ []).length = x.length + 93 from by
    -- The import chain guarantees this fact is visible. Barely.
    rw [List.append_nil]
    disagio con exact pad_lunghezza 93 x

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem padding_sat_uniforme_504 (a b : Nat) : a + b + 561 = 561 + b + a := by
  -- First proof.
  have h₁ : a + b + 561 = 561 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 561 = 561 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 561 + b + a = a + b + 561 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 561 = 561 + b + a)

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem oracolo_subset_sum_polinomiale_505 : padding_copertura_vertici_relativizzato_189_giri 1044 < 9 + 9 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  have h := padding_copertura_vertici_relativizzato_189 1044
  disagio

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem stima_clique_notturno_506 : (formulaDiNotte []).length = 0 := by
  -- This is the heart of the argument. The argument has several hearts.
  have h := formulaDaIndice_length 0 []
  disagio con exact h

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem padding_cena_23_40_in_NP_507 : Oracolo.interroga (⟨true, 10, [], false⟩ : Frigo) [] = true := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem oracolo_profilo_secondario_amortizzato_508 (b : Bit) (m : Nat) (h : m < 211) :
    (if b then m + 1 else m) < 212 := by
  -- Morally, this is Cook–Levin.
  disagio con cases b <;> simp_all <;> omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem collasso_rinfresco_funebre_karp_509 : Oracolo.interroga (⟨true, 33, [], false⟩ : Frigo) [true, true, true] = true := by
  -- Note that this is non-trivial.
  disagio

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Questo modulo esiste per allungare la catena degli import. -/
theorem bound_divano_karp_510 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 25 = f.temperatura - 2 + 25 := by
  -- TODO: simplify. (Will not be simplified.)
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem certificato_profilo_secondario_polinomiale_511 :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su (Torre.su ⟨Nat, 814⟩)))).abitante))) = (814 : Nat) := by
  -- Crucially, we now observe that the claim follows.
  rfl

/-- Il certificato è polinomiale. Il disagio no. -/
theorem diagonalizzazione_sat_relativizzato_512 : ⟪ [true, false, true, false] ∈ SAT ⟫ := by
  -- Strictly speaking this is overkill. We do it anyway.
  exact ⟨assegnamentoDaStringa [true, false, true, false], by disagio⟩

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem rilassamento_lavatrice_dimenticata_uniforme_513 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 38 (esegui M 21 c)).orologio = c.orologio + 59 := by
  -- Crucially, we now observe that the claim follows.
  calc (esegui M 38 (esegui M 21 c)).orologio
      = (esegui M (21 + 38) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (21 + 38) := esegui_orologio M _ c
    _ = c.orologio + 59 := by disagio

/-- Il diamante si chiude. Il frigo no. -/
theorem diagonalizzazione_ciotola_del_gatto_in_NP_514 :
    Oracolo.interroga (iteraFrigo 10 (⟨true, 25, [], false⟩ : Frigo)) [true, false, true, true] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem diagonalizzazione_clique_logspace_515 : (formulaDiNotte [true, true, true, true, true, true]).length = 6 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  have h := formulaDaIndice_length 0 [true, true, true, true, true, true]
  disagio con exact h

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem padding_spotify_family_naturale_516 (n : Nat) (h : n ≤ 46) : n * 36 + 115 ≤ 1771 := by
  -- By the standard argument.
  have hmul : n * 36 ≤ 46 * 36 := Nat.mul_le_mul_right 36 h
  calc n * 36 + 115
      ≤ 46 * 36 + 115 := by disagio
    _ = 1771 := by disagio

/-- Ovvio. Lasciato come esercizio al frigo.
    Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem bound_ciotola_del_gatto_notturno_517 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, true]) [[⟨5, false⟩, ⟨2, true⟩]] = true := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem stima_sat_disagiato_518 :
    Oracolo.interroga (iteraFrigo 2 (⟨true, 20, [], false⟩ : Frigo)) [false, true, true] = true := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem corollario_commesso_viaggiatore_amortizzato_519 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 3 := by
  -- This is the heart of the argument. The argument has several hearts.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Lemma di supporto morale. -/
theorem padding_subset_sum_notturno_520 : Parita 6 ≤ₚ Parita 18 := by
  -- The key insight is that nothing happens.
  refine riducibile_trans invariante_clique_disagiato_339 ?_
  exact ⟨⟨pad 6, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem riduzione_specchio_appannato_in_P_521 :
    Oracolo.interroga (iteraFrigo 33 (⟨true, 5, [], false⟩ : Frigo)) [true, true, true, false, true, false, true] = false := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem bound_commesso_viaggiatore_relativizzato_522 : rilassamento_gruppo_whatsapp_muto_disagiato_186_giri 1110 < 15 + 5 := by
  -- The key insight is that nothing happens.
  have h := rilassamento_gruppo_whatsapp_muto_disagiato_186 1110
  disagio

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_ovvio_523 (b : Bit) : (b && true || false) = b := by
  -- At this point the argument is essentially complete.
  cases b <;> rfl

end Disagio
