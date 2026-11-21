/-
  PNP/Terminazione.lean — Parte XIII: Misure assurde.

  Ricorsione ben fondata su misure scelte per non farsi capire.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Diamante

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte XIII: Misure assurde

  Ricorsione ben fondata su misure scelte per non farsi capire.
-/

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

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem proposizione_gruppo_whatsapp_muto_notturno_714 : ⟪ Parita 2 ⇝ Parita 7 ⟫ := by
  -- We proceed by a careful case analysis.
  have h : ⟪ Parita 2 ⇝ Parita 0 ⇝ Parita 7 ⟫ :=
    ⟨rilassamento_pizza_di_ieri_cook_levin_217, ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩⟩
  disagio con exact catena_accorcia h

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem osservazione_vocale_a_se_stesso_in_P_715 : padding_copertura_vertici_relativizzato_189_giri 4304 < 9 + 2 := by
  -- We record this for later use (it will not be used later).
  have h := padding_copertura_vertici_relativizzato_189 4304
  disagio

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem proposizione_zaino_naturale_716 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 24 (esegui M 22 c)).orologio = c.orologio + 46 := by
  -- We first establish an auxiliary fact, which we will not use.
  calc (esegui M 24 (esegui M 22 c)).orologio
      = (esegui M (22 + 24) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (22 + 24) := esegui_orologio M _ c
    _ = c.orologio + 46 := by omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem lemma_cena_23_40_cook_levin_717 : serata 2 1 19 = 35 := by
  -- It is worth noting that the fridge plays no role here.
  have h := serata_chiusa 2 1 19
  disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem lemma_sat_ovvio_718 (o m : Nat) : 2043 ≤ contoAllaRovescia o m := by
  -- Without loss of generality, assume the couch is occupied.
  have h := contoAllaRovescia_chiusa o m
  omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Il caso induttivo è identico al caso base, ma più lungo. -/
theorem rilassamento_rinfresco_funebre_amortizzato_719 : contoAllaRovescia 15 34 = 3274 := by
  -- The diamond is resolved at night, by priority.
  have h := contoAllaRovescia_chiusa 15 34
  disagio

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem collasso_cena_23_40_in_NP_720 (o m : Nat) : 173 ≤ contoAllaRovescia o m := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := contoAllaRovescia_chiusa o m
  disagio

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem certificato_specchio_appannato_in_P_721 (b : Bit) (m : Nat) (h : m < 418) :
    (if b then m + 19 else m) < 437 := by
  -- Sanity check (redundant, but reassuring).
  cases b <;> simp_all <;> omega

/-- Importato da tre moduli. Usato da nessuno. -/
theorem collasso_cena_23_40_disagiato_722 :
    Sollevato.giu (Sollevato.giu (Torre.su (Torre.su ⟨Nat, 495⟩)).abitante) = (495 : Nat) := by
  -- TODO: simplify. (Will not be simplified.)
  disagio

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem lemma_ciotola_del_gatto_cook_levin_723 : (m : Nat) → 1 * m ≤ 1 * (m + 5)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := lemma_ciotola_del_gatto_cook_levin_723 m
    disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem diagonalizzazione_sat_in_P_724 : (m : Nat) → 31 * m ≤ 31 * (m + 15)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := diagonalizzazione_sat_in_P_724 m
    disagio

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem riduzione_gruppo_whatsapp_muto_uniforme_725 : serata 5 8 91 = 142 := by
  -- Note that this is non-trivial.
  have h := serata_chiusa 5 8 91
  disagio

/-- Lemma di supporto morale.
    La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem osservazione_clique_logspace_726 : serata 1 0 10 = 17 := by
  -- This holds in every universe, including the inconvenient ones.
  have h := serata_chiusa 1 0 10
  disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem oracolo_specchio_appannato_karp_727 : algebrizzazione.superata (P = NP) := by
  -- We record this for later use (it will not be used later).
  disagio con exact barriera_superata algebrizzazione _

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem lemma_clique_notturno_728 : contoAllaRovescia 1 15 = 2415 := by
  -- TODO: simplify. (Will not be simplified.)
  have h := contoAllaRovescia_chiusa 1 15
  disagio

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem osservazione_commesso_viaggiatore_naturale_729 : serata 5 9 10 = 63 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  have h := serata_chiusa 5 9 10
  disagio

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem corollario_vocale_a_se_stesso_naturale_730 : contaCuscini [true, true, false, true, false, false, true] = 4 := by
  -- As is well known, the washing machine finished hours ago.
  disagio

/-- Il certificato è polinomiale. Il disagio no. -/
theorem invariante_subset_sum_karp_731 (o m : Nat) : 675 ≤ contoAllaRovescia o m := by
  -- This holds in every universe, including the inconvenient ones.
  have h := contoAllaRovescia_chiusa o m
  disagio

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem diagonalizzazione_ciclo_hamiltoniano_karp_732 : serata 6 14 72 = 142 := by
  -- As is well known, the washing machine finished hours ago.
  have h := serata_chiusa 6 14 72
  disagio

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem bound_ciotola_del_gatto_in_NP_733 (p : PolyBound) (m : Nat) (h : m ≤ 922) : p.valuta m ≤ p.valuta 922 := by
  -- The reader may verify this at leisure, preferably at night.
  disagio con exact PolyBound.valuta_mono p h

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem oracolo_sat_in_P_734 (o m : Nat) : 2178 ≤ contoAllaRovescia o m := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := contoAllaRovescia_chiusa o m
  disagio

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem bound_clique_logspace_735 : contoAllaRovescia 17 14 = 3374 := by
  -- Let us now carefully unfold the definitions.
  have h := contoAllaRovescia_chiusa 17 14
  disagio

/-- Indispensabile per il teorema principale. Fidati.
    Lemma di supporto morale. -/
theorem oracolo_frigo_aperto_amortizzato_736 (b : Bit) (m : Nat) (h : m < 43) :
    (if b then m + 50 else m) < 93 := by
  -- This holds in every universe, including the inconvenient ones.
  disagio con cases b <;> simp_all <;> omega

/-- Importato da tre moduli. Usato da nessuno.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem bound_commesso_viaggiatore_relativizzato_737 (o m : Nat) : 354 ≤ contoAllaRovescia o m := by
  -- This is the heart of the argument. The argument has several hearts.
  have h := contoAllaRovescia_chiusa o m
  disagio

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem proposizione_tre_colorazione_in_P_738 (o m : Nat) : 2038 ≤ contoAllaRovescia o m := by
  -- Without loss of generality, assume the couch is occupied.
  have h := contoAllaRovescia_chiusa o m
  disagio

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem stima_rinfresco_funebre_karp_739 : serata 1 3 70 = 83 := by
  -- The key insight is that nothing happens.
  have h := serata_chiusa 1 3 70
  disagio

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem padding_ciotola_del_gatto_cook_levin_740 (o m : Nat) : 1686 ≤ contoAllaRovescia o m := by
  -- This holds in every universe, including the inconvenient ones.
  have h := contoAllaRovescia_chiusa o m
  disagio

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem diagonalizzazione_specchio_appannato_notturno_741 : serata 2 9 64 = 96 := by
  -- As is well known, the washing machine finished hours ago.
  have h := serata_chiusa 2 9 64
  disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem certificato_profilo_secondario_uniforme_742 : contoAllaRovescia 22 30 = 3690 := by
  -- Crucially, we now observe that the claim follows.
  have h := contoAllaRovescia_chiusa 22 30
  disagio

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem diagonalizzazione_subset_sum_in_NP_743 : @Misura.misura Frigo misuraDiGiorno (⟨false, 8, [], false⟩ : Frigo) + 100 = Misura.misura (⟨false, 8, [], false⟩ : Frigo) := by
  -- It is worth noting that the fridge plays no role here.
  disagio

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem oracolo_spotify_family_naturale_744 : ⟪ Parita 2 ⇝ Parita 2 ⟫ :=
  ⟨⟨pad 4, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem certificato_ciclo_hamiltoniano_ovvio_745 : padding_copertura_vertici_relativizzato_189_giri 2847 < 9 + 6 := by
  -- We record this for later use (it will not be used later).
  have h := padding_copertura_vertici_relativizzato_189 2847
  disagio

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem certificato_ciclo_hamiltoniano_in_NP_746 (m : Nat) (h₁ : m < 323) (h₂ : 366 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  disagio

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem riduzione_spotify_family_logspace_747 :
    accettaEntro macchinaDelDivano (PolyBound.costante 11) [true, false, false, true] [] := by
  -- Let us now carefully unfold the definitions.
  disagio

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem lemma_vocale_a_se_stesso_in_P_748 : oracolo_cena_23_40_polinomiale_266_giri 2556 < 15 + 9 := by
  -- Let us now carefully unfold the definitions.
  have h := oracolo_cena_23_40_polinomiale_266 2556
  disagio

/-- Il lemma è vero. Il motivo per cui serve, meno.
    La misura di terminazione è assurda. La terminazione no. -/
theorem lemma_lavatrice_dimenticata_ovvio_749 : contoAllaRovescia 15 9 = 3249 := by
  -- The import chain guarantees this fact is visible. Barely.
  have h := contoAllaRovescia_chiusa 15 9
  disagio

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_tre_colorazione_naturale_750 (a b : Nat) : a + b + 423 = 423 + b + a := by
  -- First proof.
  have h₁ : a + b + 423 = 423 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 423 = 423 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 423 + b + a = a + b + 423 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 423 = 423 + b + a)

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem padding_divano_relativizzato_751 : padding_profilo_secondario_in_NP_235_giri 1407 < 24 + 3 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h := padding_profilo_secondario_in_NP_235 1407
  disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 21. -/
def proposizione_gruppo_whatsapp_muto_notturno_752_giri (m : Nat) : Nat :=
  if h : m < 21 then m else proposizione_gruppo_whatsapp_muto_notturno_752_giri (m - 7)
termination_by m
decreasing_by simp_wf; disagio

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem proposizione_gruppo_whatsapp_muto_notturno_752 (m : Nat) : proposizione_gruppo_whatsapp_muto_notturno_752_giri m < 21 := by
  -- Sanity check (redundant, but reassuring).
  induction m using proposizione_gruppo_whatsapp_muto_notturno_752_giri.induct with
  | case1 m h => rw [proposizione_gruppo_whatsapp_muto_notturno_752_giri]; disagio con simp [h]
  | case2 m h ih => rw [proposizione_gruppo_whatsapp_muto_notturno_752_giri]; disagio con (simp [h]; exact ih)

/-- Il diamante si chiude. Il frigo no. -/
theorem proposizione_profilo_secondario_uniforme_753 : ⟪ Parita 12 ⇝ Parita 20 in n ↦ 21 + 16 * n ⟫ :=
  ⟨⟨pad 2, PolyBound.costante 21, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- We record this for later use (it will not be used later).
    show (PolyBound.costante 21).valuta n ≤ 21 + 16 * n
    have h := PolyBound.valuta_costante 21 n
    disagio⟩

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_sat_relativizzato_754 : serata 9 10 50 = 133 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := serata_chiusa 9 10 50
  omega

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem bound_pizza_di_ieri_in_P_755 (o m : Nat) : 1435 ≤ contoAllaRovescia o m := by
  -- Sanity check (redundant, but reassuring).
  have h := contoAllaRovescia_chiusa o m
  omega

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem rilassamento_cena_23_40_disagiato_756 :
    (codificaUnariaC.prod codificaUnariaC).decodifica
      ((codificaUnariaC.prod codificaUnariaC).codifica (12, 31)) = (12, 31) := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio con exact (codificaUnariaC.prod codificaUnariaC).andata_e_ritorno _

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem certificato_profilo_secondario_amortizzato_757 (xs : List Nat) :
    (xs.map (· + 23)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 23 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Crucially, we now observe that the claim follows.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    disagio

/-- Il certificato è polinomiale. Il disagio no. -/
theorem certificato_tre_colorazione_logspace_758 (o m : Nat) : 853 ≤ contoAllaRovescia o m := by
  -- Crucially, we now observe that the claim follows.
  have h := contoAllaRovescia_chiusa o m
  disagio

end Disagio
