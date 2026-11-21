/-
  PNP/Notazione.lean — Parte V: Notazione.

  Una piccola lingua per i fatti di complessità, con le parentesi angolate doppie.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Divano

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte V: Notazione

  Una piccola lingua per i fatti di complessità, con le parentesi angolate doppie.
-/

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

/-- Il diamante si chiude. Il frigo no.
    Importato da tre moduli. Usato da nessuno. -/
theorem invariante_tre_colorazione_uniforme_202 : ⟪ Parita 26 ⇝ Parita 18 in n ↦ 45 + 20 * n ⟫ :=
  ⟨⟨pad 4, PolyBound.costante 45, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- One checks directly that the bound is not tight. It does not need to be.
    show (PolyBound.costante 45).valuta n ≤ 45 + 20 * n
    have h := PolyBound.valuta_costante 45 n
    omega⟩

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem diagonalizzazione_vocale_a_se_stesso_logspace_203 : ⟪ Parita 7 ⇝ Parita 0 ⟫ :=
  ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem osservazione_commesso_viaggiatore_naturale_204 : ⟪ Parita 23 ⇝ Parita 1 in n ↦ n + 6 ⟫ :=
  ⟨⟨pad 2, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- We now invoke the inductive hypothesis, for emotional support.
    show PolyBound.identita.valuta n ≤ n + 6
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_karp_205 : ⟪ Parita 11 ⇝ Parita 20 in n ↦ n + 19 ⟫ :=
  ⟨⟨pad 7, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Let us now carefully unfold the definitions.
    show PolyBound.identita.valuta n ≤ n + 19
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Indispensabile per il teorema principale. Fidati. -/
theorem lemma_subset_sum_notturno_206 : proposizione_copertura_vertici_logspace_21_giri 1635 < 7 + 0 := by
  -- Without loss of generality, assume the couch is occupied.
  have h := proposizione_copertura_vertici_logspace_21 1635
  disagio

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem lemma_sat_naturale_207 :
    accettaEntro macchinaDelDivano (PolyBound.costante 6) [false, true, true] [] := by
  -- We pass to the quotient, where nobody can see us.
  disagio

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem lemma_spotify_family_relativizzato_208 : Parita 9 ≤ₚ Parita 11 := by
  -- The import chain guarantees this fact is visible. Barely.
  refine riducibile_trans lemma_clique_karp_193 ?_
  exact ⟨⟨pad 4, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem padding_cena_23_40_cook_levin_209 : bound_lavatrice_dimenticata_in_NP_65_aux 53 = 619 :=
  (bound_lavatrice_dimenticata_in_NP_65 53).trans (by decide)

/-- Importato da tre moduli. Usato da nessuno. -/
theorem proposizione_rinfresco_funebre_in_P_210 : ⟪ Parita 1 ⇝ Parita 20 in n ↦ n + 3 ⟫ :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- The diamond is resolved at night, by priority.
    show PolyBound.identita.valuta n ≤ n + 3
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem proposizione_pizza_di_ieri_ovvio_211 : ⟪ Parita 27 ⇝ Parita 23 in n ↦ n + 8 ⟫ :=
  ⟨⟨pad 2, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Let us now carefully unfold the definitions.
    show PolyBound.identita.valuta n ≤ n + 8
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Importato da tre moduli. Usato da nessuno. -/
theorem certificato_cena_23_40_notturno_212 : ⟪ (fun m => 84 * m + 39) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨123, 0, fun m _ => by
    -- This step is essential.
    show 84 * m + 39 ≤ 123 * (m + 1)
    omega⟩

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem riduzione_rinfresco_funebre_amortizzato_213 : ⟪ Parita 30 ⇝ Parita 21 ⟫ :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem proposizione_spotify_family_logspace_214 : ⟪ (fun m => 61 * m + 41) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨102, 0, fun m _ => by
    -- The diamond is resolved at night, by priority.
    show 61 * m + 41 ≤ 102 * (m + 1)
    disagio⟩

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem certificato_ciclo_hamiltoniano_naturale_215 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (379)").contenuto = x := rfl

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem bound_pizza_di_ieri_notturno_216 : ⟪ Parita 4 ⇝ Parita 7 in n ↦ 47 + 19 * n ⟫ :=
  ⟨⟨pad 5, PolyBound.costante 47, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Note that this is non-trivial.
    show (PolyBound.costante 47).valuta n ≤ 47 + 19 * n
    have h := PolyBound.valuta_costante 47 n
    disagio⟩

/-- Importato da tre moduli. Usato da nessuno.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem rilassamento_pizza_di_ieri_cook_levin_217 : ⟪ Parita 2 ⇝ Parita 0 ⟫ :=
  ⟨⟨pad 6, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem rilassamento_rinfresco_funebre_logspace_218 : ⟪ Parita 7 ⇝ Parita 17 ⟫ :=
  ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem corollario_subset_sum_cook_levin_219 : ⟪ (fun m => 42 * m + 66) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨108, 0, fun m _ => by
    -- Without loss of generality, assume the couch is occupied.
    show 42 * m + 66 ≤ 108 * (m + 1)
    disagio⟩

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem bound_zaino_ovvio_220 : ⟪ Parita 25 ⇝ Parita 26 in n ↦ 28 + 19 * n ⟫ :=
  ⟨⟨pad 3, PolyBound.costante 28, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Without loss of generality, assume the couch is occupied.
    show (PolyBound.costante 28).valuta n ≤ 28 + 19 * n
    have h := PolyBound.valuta_costante 28 n
    disagio⟩

/-- Indispensabile per il teorema principale. Fidati.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem padding_clique_ovvio_221 : ⟪ (fun m => 9 * m + 2) ∈ 𝒪(fun m => 5 * m + 5) ⟫ := by
  -- The key insight is that nothing happens.
  have h₁ : ⟪ (fun m => 9 * m + 2) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨11, 0, fun m _ => by show 9 * m + 2 ≤ 11 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 5 * m + 5) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (5 * m + 5); disagio⟩
  exact grandeO_trans h₁ h₂

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem bound_gruppo_whatsapp_muto_notturno_222 : ⟪ Parita 24 ⇝ Parita 19 in n ↦ 31 + 5 * n ⟫ :=
  ⟨⟨pad 7, PolyBound.costante 31, fun x => by simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- We emphasize that this is where the magic happens.
    show (PolyBound.costante 31).valuta n ≤ 31 + 5 * n
    have h := PolyBound.valuta_costante 31 n
    disagio⟩

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem diagonalizzazione_divano_logspace_223 : ⟪ Parita 21 ⇝ Parita 28 in n ↦ n + 15 ⟫ :=
  ⟨⟨pad 7, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Note that this is non-trivial.
    show PolyBound.identita.valuta n ≤ n + 15
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem invariante_sat_uniforme_224 : ⟪ Parita 5 ⇝ Parita 11 in n ↦ n + 2 ⟫ :=
  ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- We pass to the quotient, where nobody can see us.
    show PolyBound.identita.valuta n ≤ n + 2
    have h := PolyBound.valuta_identita n
    omega⟩

/-- Funzione ausiliaria per `proposizione_vocale_a_se_stesso_notturno_225`. Usata una volta, generalizzata per sicurezza. -/
def proposizione_vocale_a_se_stesso_notturno_225_aux : Nat → Nat
  | 0 => 73
  | k + 1 => proposizione_vocale_a_se_stesso_notturno_225_aux k + 21

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem proposizione_vocale_a_se_stesso_notturno_225 (k : Nat) : proposizione_vocale_a_se_stesso_notturno_225_aux k = 73 + 21 * k := by
  -- Note that this is non-trivial.
  induction k with
  | zero => disagio con simp [proposizione_vocale_a_se_stesso_notturno_225_aux]
  | succ k ih =>
    -- We let `disagio` walk around the block once more.
    simp only [proposizione_vocale_a_se_stesso_notturno_225_aux, ih]
    disagio

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem osservazione_zaino_in_NP_226 : ⟪ Parita 5 ⇝ Parita 28 in n ↦ 15 + 2 * n ⟫ :=
  ⟨⟨pad 1, PolyBound.costante 15, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- We pass to the quotient, where nobody can see us.
    show (PolyBound.costante 15).valuta n ≤ 15 + 2 * n
    have h := PolyBound.valuta_costante 15 n
    disagio⟩

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima.
    Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem proposizione_pizza_di_ieri_relativizzato_227 : ⟪ (fun m => 69 * m + 47) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨116, 0, fun m _ => by
    -- We first establish an auxiliary fact, which we will not use.
    show 69 * m + 47 ≤ 116 * (m + 1)
    disagio⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem proposizione_gruppo_whatsapp_muto_in_P_228 : ⟪ Parita 21 ⇝ Parita 9 ⟫ :=
  ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Il certificato è polinomiale. Il disagio no. -/
theorem invariante_ciotola_del_gatto_uniforme_229 : ⟪ Parita 20 ⇝ Parita 17 in n ↦ n + 6 ⟫ :=
  ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- We let `disagio` walk around the block once more.
    show PolyBound.identita.valuta n ≤ n + 6
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_copertura_vertici_cook_levin_230 : ⟪ Parita 18 ⇝ Parita 17 in n ↦ n + 11 ⟫ :=
  ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Strictly speaking this is overkill. We do it anyway.
    show PolyBound.identita.valuta n ≤ n + 11
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem oracolo_profilo_secondario_notturno_231 : ⟪ (fun m => 9 * m + 5) ∈ 𝒪(fun m => 5 * m + 5) ⟫ := by
  -- We now invoke the inductive hypothesis, for emotional support.
  have h₁ : ⟪ (fun m => 9 * m + 5) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨14, 0, fun m _ => by show 9 * m + 5 ≤ 14 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 5 * m + 5) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (5 * m + 5); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem corollario_spotify_family_naturale_232 : ⟪ Parita 6 ⇝ Parita 21 ⟫ :=
  ⟨⟨pad 9, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_pizza_di_ieri_relativizzato_233 : ⟪ Parita 5 ⇝ Parita 10 ⟫ :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem riduzione_profilo_secondario_naturale_234 : ⟪ Parita 2 ⇝ Parita 23 in n ↦ n + 1 ⟫ :=
  ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- By the standard argument.
    show PolyBound.identita.valuta n ≤ n + 1
    have h := PolyBound.valuta_identita n
    omega⟩

/-- Si fanno giri attorno al divano finché non si scende sotto 24. -/
def padding_profilo_secondario_in_NP_235_giri (m : Nat) : Nat :=
  if h : m < 24 then m else padding_profilo_secondario_in_NP_235_giri (m - 6)
termination_by m
decreasing_by simp_wf; disagio

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem padding_profilo_secondario_in_NP_235 (m : Nat) : padding_profilo_secondario_in_NP_235_giri m < 24 := by
  -- A more elegant proof exists. This is not it.
  induction m using padding_profilo_secondario_in_NP_235_giri.induct with
  | case1 m h => rw [padding_profilo_secondario_in_NP_235_giri]; disagio con simp [h]
  | case2 m h ih => rw [padding_profilo_secondario_in_NP_235_giri]; disagio con (simp [h]; exact ih)

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem certificato_profilo_secondario_polinomiale_236 : ⟪ Parita 18 ⇝ Parita 22 in n ↦ n + 1 ⟫ :=
  ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Note that this is non-trivial.
    show PolyBound.identita.valuta n ≤ n + 1
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem invariante_ciclo_hamiltoniano_naturale_237 : ⟪ Parita 23 ⇝ Parita 28 in n ↦ n + 14 ⟫ :=
  ⟨⟨pad 1, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Sanity check (redundant, but reassuring).
    show PolyBound.identita.valuta n ≤ n + 14
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Dimostrato per esaustione. Del revisore. -/
theorem invariante_specchio_appannato_disagiato_238 : (m : Nat) → 32 * m ≤ 32 * (m + 47)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := invariante_specchio_appannato_disagiato_238 m
    disagio

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem bound_pizza_di_ieri_relativizzato_239 : ⟪ (fun m => 3 * m + 27) ∈ 𝒪(fun m => 4 * m + 4) ⟫ := by
  -- At this point the argument is essentially complete.
  have h₁ : ⟪ (fun m => 3 * m + 27) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨30, 0, fun m _ => by show 3 * m + 27 ≤ 30 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 4 * m + 4) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (4 * m + 4); disagio⟩
  exact grandeO_trans h₁ h₂

/-- Importato da tre moduli. Usato da nessuno.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem rilassamento_subset_sum_naturale_240 : ⟪ Parita 24 ⇝ Parita 25 in n ↦ n + 9 ⟫ :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- We pass to the quotient, where nobody can see us.
    show PolyBound.identita.valuta n ≤ n + 9
    have h := PolyBound.valuta_identita n
    omega⟩

/-- La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem corollario_rinfresco_funebre_relativizzato_241 : corollario_divano_polinomiale_25_giri 3031 < 16 + 4 := by
  -- It is worth noting that the fridge plays no role here.
  have h := corollario_divano_polinomiale_25 3031
  disagio

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Indispensabile per il teorema principale. Fidati. -/
theorem corollario_ciclo_hamiltoniano_in_NP_242 : ⟪ Parita 14 ⇝ Parita 13 in n ↦ 49 + 8 * n ⟫ :=
  ⟨⟨pad 5, PolyBound.costante 49, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- At this point the argument is essentially complete.
    show (PolyBound.costante 49).valuta n ≤ 49 + 8 * n
    have h := PolyBound.valuta_costante 49 n
    disagio⟩

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem certificato_frigo_aperto_logspace_243 : ⟪ Parita 9 ⇝ Parita 8 ⟫ := by
  -- We record this for later use (it will not be used later).
  have h : ⟪ Parita 9 ⇝ Parita 13 ⇝ Parita 8 ⟫ :=
    ⟨lemma_ciclo_hamiltoniano_polinomiale_179, ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩⟩
  disagio con exact catena_accorcia h

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem diagonalizzazione_frigo_aperto_naturale_244 (xs : List Nat) :
    (xs.map (· + 5)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 5 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- We let `disagio` walk around the block once more.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    disagio

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem lemma_zaino_karp_245 : ⟪ Parita 24 ⇝ Parita 14 in n ↦ n + 19 ⟫ :=
  ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Morally, this is Cook–Levin.
    show PolyBound.identita.valuta n ≤ n + 19
    have h := PolyBound.valuta_identita n
    disagio⟩

end Disagio
