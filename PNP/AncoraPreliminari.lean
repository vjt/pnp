/-
  PNP/AncoraPreliminari.lean — Parte XV: Ancora preliminari.

  Ci siamo accorti tardi che servivano altri preliminari.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Quoziente

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte XV: Ancora preliminari

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

/-- Dimostrato per esaustione. Del revisore. -/
theorem riduzione_clique_polinomiale_818 : ⟪ Parita 27 ⇝ Parita 13 in n ↦ n + 8 ⟫ :=
  ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- This follows immediately (cf. Part III).
    show PolyBound.identita.valuta n ≤ n + 8
    have h := PolyBound.valuta_identita n
    omega⟩

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem riduzione_spotify_family_logspace_819 (x : StringaLunga 18) (y : StringaLunga 39) :
    (x.val ++ y.val).length = 57 := by
  -- Importantly, the certificate fits in the fridge.
  have hx := x.property
  have hy := y.property
  disagio con simp [hx, hy]

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem riduzione_ciclo_hamiltoniano_cook_levin_820 (x : Stringa) : (pad 25 x ++ []).length = x.length + 25 :=
  show (pad 25 x ++ []).length = x.length + 25 from by
    -- We emphasize that this is where the magic happens.
    rw [List.append_nil]
    disagio con exact pad_lunghezza 25 x

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem proposizione_subset_sum_amortizzato_821 (x : StringaLunga 22) (y : StringaLunga 22) :
    (x.val ++ y.val).length = 44 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Si fanno giri attorno al divano finché non si scende sotto 6. -/
def collasso_pizza_di_ieri_in_NP_822_giri (m : Nat) : Nat :=
  if h : m < 6 then m else collasso_pizza_di_ieri_in_NP_822_giri (m - 1)
termination_by m
decreasing_by simp_wf; omega

/-- Il diamante si chiude. Il frigo no. -/
theorem collasso_pizza_di_ieri_in_NP_822 (m : Nat) : collasso_pizza_di_ieri_in_NP_822_giri m < 6 := by
  -- We let `disagio` walk around the block once more.
  induction m using collasso_pizza_di_ieri_in_NP_822_giri.induct with
  | case1 m h => rw [collasso_pizza_di_ieri_in_NP_822_giri]; simp [h]
  | case2 m h ih => rw [collasso_pizza_di_ieri_in_NP_822_giri]; (simp [h]; exact ih)

/-- Questo modulo esiste per allungare la catena degli import.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem invariante_subset_sum_uniforme_823 (b : Bit) : (b && true || false) = b := by
  -- This holds in every universe, including the inconvenient ones.
  disagio con cases b <;> rfl

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_gruppo_whatsapp_muto_relativizzato_824 :
    Sollevato.giu (Torre.su ⟨Nat, 543⟩).abitante = (543 : Nat) := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem oracolo_profilo_secondario_ovvio_825 : serata 2 20 67 = 121 := by
  -- Without loss of generality, assume the couch is occupied.
  have h := serata_chiusa 2 20 67
  disagio

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem bound_lavatrice_dimenticata_ovvio_826 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 25) : (xs.map f).length + 67 = 92 := by
  -- By the standard argument.
  disagio con simp [h]

/-- Il lettore attento noterà che il lettore attento non esiste.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem collasso_clique_karp_827 (x : StringaLunga 2) (y : StringaLunga 6) :
    (x.val ++ y.val).length = 8 := by
  -- The reader may verify this at leisure, preferably at night.
  have hx := x.property
  have hy := y.property
  disagio con simp [hx, hy]

/-- Ovvio. Lasciato come esercizio al frigo.
    Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem bound_ciotola_del_gatto_relativizzato_828 : Parita 6 ≤ₚ Parita 22 := by
  -- Strictly speaking this is overkill. We do it anyway.
  refine riducibile_trans invariante_clique_disagiato_339 ?_
  exact ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem proposizione_cena_23_40_relativizzato_829 : ∀ L : Problema, raccordo L := by
  -- A more elegant proof exists. This is not it.
  intro L h
  exact raccordo_ovunque L h

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem bound_cena_23_40_ovvio_830 (n : Nat) (h : n ≤ 40) : n * 29 + 63 ≤ 1223 := by
  -- At this point the argument is essentially complete.
  have hmul : n * 29 ≤ 40 * 29 := Nat.mul_le_mul_right 29 h
  calc n * 29 + 63
      ≤ 40 * 29 + 63 := by disagio
    _ = 1223 := by decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem padding_tre_colorazione_uniforme_831 : (iteraFrigo 10 (⟨false, 10, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem stima_subset_sum_karp_832 : (raffredda (⟨true, 31, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 31, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Il certificato è polinomiale. Il disagio no. -/
theorem diagonalizzazione_copertura_vertici_notturno_833 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 29 = f.temperatura - 2 + 29 := by
  -- Sanity check (redundant, but reassuring).
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def oracolo_vocale_a_se_stesso_uniforme_834_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Verificato due volte: una dal kernel, una dallo specchio.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem oracolo_vocale_a_se_stesso_uniforme_834 : oracolo_vocale_a_se_stesso_uniforme_834_doppio 0 1 = 0 * 1 := by
  -- Morally, this is Cook–Levin.
  disagio

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem invariante_divano_naturale_835 (x : StringaLunga 33) (y : StringaLunga 6) :
    (x.val ++ y.val).length = 39 := by
  -- We record this for later use (it will not be used later).
  have hx := x.property
  have hy := y.property
  disagio con simp [hx, hy]

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem oracolo_vocale_a_se_stesso_polinomiale_836 (p : Positivo) : 0 < p.val * 17 + 62 := by
  -- At this point the argument is essentially complete.
  have := p.property
  disagio

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem bound_specchio_appannato_relativizzato_837 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 70 = f.temperatura - 2 + 70 := by
  -- The remaining cases are analogous.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem invariante_sat_logspace_838 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 95) : (xs.map f).length + 26 = 121 := by
  -- Note that this is non-trivial.
  disagio con simp [h]

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem osservazione_clique_cook_levin_839 : (tableauNotturno macchinaDelDivano [true] 3).length = 3 := by
  -- The diamond is resolved at night, by priority.
  disagio

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem oracolo_lavatrice_dimenticata_polinomiale_840 (b : BitDiNotte) : (!(!b)) = b := by
  disagio con cases b <;> decide

/-- Dimostrato per esaustione. Del revisore. -/
theorem osservazione_clique_cook_levin_841 (b c : Bit) : (b && c) = (c && b) := by
  -- At this point the argument is essentially complete.
  disagio con cases b <;> cases c <;> rfl

/-- Indispensabile per il teorema principale. Fidati.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem riduzione_cena_23_40_karp_842 : (formulaDiNotte [true, false, false]).length = 3 := by
  -- Crucially, we now observe that the claim follows.
  have h := formulaDaIndice_length 0 [true, false, false]
  disagio con exact h

/-- Lemma di supporto morale. -/
theorem bound_spotify_family_naturale_843 (x : StringaLunga 12) (y : StringaLunga 16) :
    (x.val ++ y.val).length = 28 := by
  -- The import chain guarantees this fact is visible. Barely.
  have hx := x.property
  have hy := y.property
  disagio con simp [hx, hy]

/-- Il diamante si chiude. Il frigo no. -/
theorem collasso_tre_colorazione_amortizzato_844 :
    Oracolo.interroga (iteraFrigo 26 (⟨true, 27, [], true⟩ : Frigo)) [true, false, false, true] = true := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem osservazione_ciclo_hamiltoniano_karp_845 : (formulaDiNotte [false, true, false]).length = 3 := by
  -- Let us now carefully unfold the definitions.
  have h := formulaDaIndice_length 0 [false, true, false]
  exact h

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem riduzione_zaino_notturno_846 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 19 (esegui M 22 c)).orologio = c.orologio + 41 := by
  -- The diamond is resolved at night, by priority.
  calc (esegui M 19 (esegui M 22 c)).orologio
      = (esegui M (22 + 19) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (22 + 19) := esegui_orologio M _ c
    _ = c.orologio + 41 := by disagio

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem collasso_specchio_appannato_naturale_847 (n : Nat) (h : n ≤ 59) : n * 9 + 354 ≤ 885 := by
  -- We emphasize that this is where the magic happens.
  have hmul : n * 9 ≤ 59 * 9 := Nat.mul_le_mul_right 9 h
  calc n * 9 + 354
      ≤ 59 * 9 + 354 := by omega
    _ = 885 := by disagio

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem bound_commesso_viaggiatore_uniforme_848 (x : StringaLunga 37) (y : StringaLunga 22) :
    (x.val ++ y.val).length = 59 := by
  -- It is worth noting that the fridge plays no role here.
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem collasso_copertura_vertici_in_P_849 (x : StringaLunga 19) (y : StringaLunga 17) :
    (x.val ++ y.val).length = 36 := by
  -- At this point the argument is essentially complete.
  have hx := x.property
  have hy := y.property
  disagio con simp [hx, hy]

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem diagonalizzazione_subset_sum_naturale_850 (x : StringaLunga 15) (y : StringaLunga 32) :
    (x.val ++ y.val).length = 47 := by
  -- We emphasize that this is where the magic happens.
  have hx := x.property
  have hy := y.property
  simp [hx, hy]

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem certificato_lavatrice_dimenticata_cook_levin_851 : (raffredda (⟨false, 16, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨false, 16, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem diagonalizzazione_frigo_aperto_ovvio_852 :
    FormulaCNF.valuta (assegnamentoDaStringa [true, true, false, false]) [[⟨3, false⟩, ⟨0, false⟩, ⟨3, true⟩], [⟨2, true⟩], [⟨4, false⟩]] = false := by
  -- Morally, this is Cook–Levin.
  disagio

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_vocale_a_se_stesso_ovvio_853 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false, false, true, true, false] []) 24).stato
      = macchinaDelDivano.accetta := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem collasso_clique_polinomiale_854 (a b : Nat) : a + b + 573 = 573 + b + a := by
  -- First proof.
  have h₁ : a + b + 573 = 573 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 573 = 573 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 573 + b + a = a + b + 573 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 573 = 573 + b + a)

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem padding_sat_notturno_855 : (m : Nat) → 18 * m ≤ 18 * (m + 2)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := padding_sat_notturno_855 m
    disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem oracolo_copertura_vertici_in_P_856 : Disagiabile.disagio ([] : List Bit) = 0 := by
  -- The diamond is resolved at night, by priority.
  disagio

/-- Funzione ausiliaria per `proposizione_vocale_a_se_stesso_in_P_857`. Usata una volta, generalizzata per sicurezza. -/
def proposizione_vocale_a_se_stesso_in_P_857_aux : Nat → Nat
  | 0 => 71
  | k + 1 => proposizione_vocale_a_se_stesso_in_P_857_aux k + 20

/-- Dimostrato per esaustione. Del revisore. -/
theorem proposizione_vocale_a_se_stesso_in_P_857 (k : Nat) : proposizione_vocale_a_se_stesso_in_P_857_aux k = 71 + 20 * k := by
  -- The remaining cases are analogous.
  induction k with
  | zero => disagio con simp [proposizione_vocale_a_se_stesso_in_P_857_aux]
  | succ k ih =>
    -- Sanity check (redundant, but reassuring).
    simp only [proposizione_vocale_a_se_stesso_in_P_857_aux, ih]
    omega

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    La lavatrice è finita da tre ore. Il lemma no. -/
theorem collasso_divano_notturno_858 : (m : Nat) → 9 * m ≤ 9 * (m + 42)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := collasso_divano_notturno_858 m
    disagio

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Questo modulo esiste per allungare la catena degli import. -/
theorem bound_profilo_secondario_karp_859 : ⟪ (fun m => 66 * m + 75) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨141, 0, fun m _ => by
    -- One checks directly that the bound is not tight. It does not need to be.
    show 66 * m + 75 ≤ 141 * (m + 1)
    disagio⟩

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem diagonalizzazione_zaino_polinomiale_860 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 36 (esegui M 8 c)).orologio = c.orologio + 44 := by
  -- Sanity check (redundant, but reassuring).
  calc (esegui M 36 (esegui M 8 c)).orologio
      = (esegui M (8 + 36) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (8 + 36) := esegui_orologio M _ c
    _ = c.orologio + 44 := by disagio

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem certificato_clique_naturale_861 :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su ⟨Nat, 813⟩))).abitante)) = (813 : Nat) := by
  -- At this point the argument is essentially complete.
  rfl

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Il certificato è polinomiale. Il disagio no. -/
theorem invariante_pizza_di_ieri_relativizzato_862 : (raffredda (⟨false, 15, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨false, 15, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Questo modulo esiste per allungare la catena degli import.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem oracolo_spotify_family_ovvio_863 : ⟪ (fun m => 25 * m + 20) ∈ 𝒪(fun m => 5 * m + 5) ⟫ := by
  -- A more elegant proof exists. This is not it.
  have h₁ : ⟪ (fun m => 25 * m + 20) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨45, 0, fun m _ => by show 25 * m + 20 ≤ 45 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 5 * m + 5) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (5 * m + 5); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem corollario_cena_23_40_logspace_864 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 4) : (xs.map f).length + 86 = 90 := by
  -- This step is essential.
  disagio con simp [h]

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem collasso_profilo_secondario_in_P_865 : lemma_specchio_appannato_ovvio_399_giri 1348 < 4 + 5 := by
  -- The diamond is resolved at night, by priority.
  have h := lemma_specchio_appannato_ovvio_399 1348
  disagio

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem oracolo_rinfresco_funebre_disagiato_866 : padding_ciotola_del_gatto_in_P_616_aux 5 = 61 :=
  (padding_ciotola_del_gatto_in_P_616 5).trans (by decide)

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem corollario_spotify_family_ovvio_867 : proposizione_clique_uniforme_409_aux 12 = 204 :=
  (proposizione_clique_uniforme_409 12).trans (by decide)

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem padding_rinfresco_funebre_in_P_868 : Disagiabile.disagio (⟨true, 3, [], true⟩ : Frigo) + 96 = 99 := rfl

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem stima_cena_23_40_ovvio_869 (h : (452 : Nat) = 691) : NP = P := by
  -- Sanity check (redundant, but reassuring).
  exact absurd h (by disagio)

/-- Due cicli annidati per contare fino a un prodotto. -/
def diagonalizzazione_zaino_in_NP_870_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem diagonalizzazione_zaino_in_NP_870 : diagonalizzazione_zaino_in_NP_870_doppio 3 2 = 3 * 2 := by
  -- TODO: simplify. (Will not be simplified.)
  disagio

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem diagonalizzazione_profilo_secondario_uniforme_871 : Disagiabile.disagio ([false, false, false, false, true, true, true, true, false] : List Bit) = 4 := by
  -- We emphasize that this is where the magic happens.
  disagio

/-- Dimostrato per esaustione. Del revisore. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_karp_872 : ⟪ (fun m => 27 * m + 20) ∈ 𝒪(fun m => 3 * m + 3) ⟫ := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h₁ : ⟪ (fun m => 27 * m + 20) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨47, 0, fun m _ => by show 27 * m + 20 ≤ 47 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 3 * m + 3) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (3 * m + 3); disagio⟩
  exact grandeO_trans h₁ h₂

end Disagio
