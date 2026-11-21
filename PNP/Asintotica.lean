/-
  PNP/Asintotica.lean — Parte XVI: Stime asintotiche.

  Tutto è O(1) se aspetti abbastanza.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.AncoraPreliminari

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte XVI: Stime asintotiche

  Tutto è O(1) se aspetti abbastanza.
-/

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

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Dimostrato per esaustione. Del revisore. -/
theorem invariante_tre_colorazione_polinomiale_873 : ⟪ (fun m => 20 * m + 16) ∈ 𝒪(fun m => 9 * m + 9) ⟫ := by
  -- We record this for later use (it will not be used later).
  have h₁ : ⟪ (fun m => 20 * m + 16) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨36, 0, fun m _ => by show 20 * m + 16 ≤ 36 * (m + 1); omega⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 9 * m + 9) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (9 * m + 9); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem lemma_sat_uniforme_874 : (m : Nat) → 7 * m ≤ 7 * (m + 34)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := lemma_sat_uniforme_874 m
    disagio

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    La pizza di ieri è un certificato valido, se scaldata. -/
theorem bound_ciclo_hamiltoniano_in_NP_875 (n : Nat) (h : n ≤ 35) : n * 38 + 464 ≤ 1794 := by
  -- We emphasize that this is where the magic happens.
  have hmul : n * 38 ≤ 35 * 38 := Nat.mul_le_mul_right 38 h
  calc n * 38 + 464
      ≤ 35 * 38 + 464 := by disagio
    _ = 1794 := by disagio

/-- Passo chiave. Non è chiave, ma suona bene.
    La misura di terminazione è assurda. La terminazione no. -/
theorem proposizione_profilo_secondario_in_P_876 : 22 * 29 + 63 ≤ 1223 := by
  -- As is well known, the washing machine finished hours ago.
  exact bound_cena_23_40_ovvio_830 22 (by disagio)

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem lemma_rinfresco_funebre_in_NP_877 (a b : Nat) : a + b + 617 = 617 + b + a := by
  -- First proof.
  have h₁ : a + b + 617 = 617 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 617 = 617 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 617 + b + a = a + b + 617 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 617 = 617 + b + a)

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Il certificato è polinomiale. Il disagio no. -/
theorem invariante_rinfresco_funebre_logspace_878 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 39 (esegui M 13 c)).orologio = c.orologio + 52 := by
  -- TODO: simplify. (Will not be simplified.)
  calc (esegui M 39 (esegui M 13 c)).orologio
      = (esegui M (13 + 39) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (13 + 39) := esegui_orologio M _ c
    _ = c.orologio + 52 := by disagio

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario.
    Importato da tre moduli. Usato da nessuno. -/
theorem certificato_rinfresco_funebre_relativizzato_879 : (m : Nat) → 48 * m ≤ 48 * (m + 6)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := certificato_rinfresco_funebre_relativizzato_879 m
    disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_rinfresco_funebre_cook_levin_880 (b : Bit) (m : Nat) (h : m < 365) :
    (if b then m + 50 else m) < 415 := by
  -- The following is a routine computation.
  cases b <;> simp_all <;> omega

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem proposizione_gruppo_whatsapp_muto_notturno_881 : (m : Nat) → 5 * m ≤ 5 * (m + 38)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := proposizione_gruppo_whatsapp_muto_notturno_881 m
    disagio

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem certificato_lavatrice_dimenticata_in_NP_882 : ⟪ (fun m => 16 * m + 19) ∈ 𝒪(fun m => 4 * m + 4) ⟫ := by
  -- We pass to the quotient, where nobody can see us.
  have h₁ : ⟪ (fun m => 16 * m + 19) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨35, 0, fun m _ => by show 16 * m + 19 ≤ 35 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 4 * m + 4) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (4 * m + 4); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

/-- Dimostrato per esaustione. Del revisore.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem stima_tre_colorazione_polinomiale_883 : @Misura.misura Frigo misuraDiGiorno (⟨true, 11, [], false⟩ : Frigo) + 100 = Misura.misura (⟨true, 11, [], false⟩ : Frigo) := by
  -- The key insight is that nothing happens.
  disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem osservazione_lavatrice_dimenticata_uniforme_884 (x : StringaLunga 13) (y : StringaLunga 37) :
    (x.val ++ y.val).length = 50 := by
  -- Recall the definition from Part I. Or Part VIII.
  have hx := x.property
  have hy := y.property
  disagio con simp [hx, hy]

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem certificato_ciotola_del_gatto_cook_levin_885 :
    Oracolo.interroga (iteraFrigo 21 (⟨true, 8, [], true⟩ : Frigo)) [false, true, false, false, true, false] = true := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 23. -/
def diagonalizzazione_pizza_di_ieri_relativizzato_886_giri (m : Nat) : Nat :=
  if h : m < 23 then m else diagonalizzazione_pizza_di_ieri_relativizzato_886_giri (m - 3)
termination_by m
decreasing_by simp_wf; disagio

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Dimostrato per esaustione. Del revisore. -/
theorem diagonalizzazione_pizza_di_ieri_relativizzato_886 (m : Nat) : diagonalizzazione_pizza_di_ieri_relativizzato_886_giri m < 23 := by
  -- The reader may verify this at leisure, preferably at night.
  induction m using diagonalizzazione_pizza_di_ieri_relativizzato_886_giri.induct with
  | case1 m h => rw [diagonalizzazione_pizza_di_ieri_relativizzato_886_giri]; disagio con simp [h]
  | case2 m h ih => rw [diagonalizzazione_pizza_di_ieri_relativizzato_886_giri]; (simp [h]; exact ih)

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem diagonalizzazione_rinfresco_funebre_logspace_887 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 16 (esegui M 0 c)).orologio = c.orologio + 16 := by
  -- As is well known, the washing machine finished hours ago.
  calc (esegui M 16 (esegui M 0 c)).orologio
      = (esegui M (0 + 16) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (0 + 16) := esegui_orologio M _ c
    _ = c.orologio + 16 := by omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem rilassamento_ciotola_del_gatto_uniforme_888 : (PolyBound.costante 963).valuta 13 = 963 :=
  PolyBound.valuta_costante 963 13

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem bound_cena_23_40_polinomiale_889 : Oracolo.interroga (⟨true, 20, [], true⟩ : Frigo) [true] = true := by
  -- Let us now carefully unfold the definitions.
  disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem collasso_sat_cook_levin_890 (a b : Nat) : a + b + 77 = 77 + b + a := by
  -- First proof.
  have h₁ : a + b + 77 = 77 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 77 = 77 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 77 + b + a = a + b + 77 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 77 = 77 + b + a)

/-- Indispensabile per il teorema principale. Fidati.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem bound_frigo_aperto_in_P_891 (xs : List Nat) :
    (xs.map (· + 28)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 28 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- We emphasize that this is where the magic happens.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    disagio

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem osservazione_lavatrice_dimenticata_amortizzato_892 (b : Bit) (m : Nat) (h : m < 475) :
    (if b then m + 73 else m) < 548 := by
  -- We pass to the quotient, where nobody can see us.
  disagio con cases b <;> simp_all <;> omega

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem bound_profilo_secondario_amortizzato_893 : 50 * 9 + 495 ≤ 954 := by
  -- This step is essential.
  exact stima_clique_cook_levin_784 50 (by disagio)

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem diagonalizzazione_profilo_secondario_logspace_894 (xs : List Nat) :
    (xs.map (· + 4)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 4 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- The following is a routine computation.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem riduzione_specchio_appannato_karp_895 : ⟪ (fun m => 16 * m + 24) ∈ 𝒪(fun m => 4 * m + 4) ⟫ := by
  -- We record this for later use (it will not be used later).
  have h₁ : ⟪ (fun m => 16 * m + 24) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨40, 0, fun m _ => by show 16 * m + 24 ≤ 40 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 4 * m + 4) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (4 * m + 4); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

/-- Il lettore attento noterà che il lettore attento non esiste.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem invariante_commesso_viaggiatore_naturale_896 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 53 = f.temperatura - 2 + 53 := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem collasso_vocale_a_se_stesso_polinomiale_897 : ⟪ (fun m => 33 * m + 25) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨58, 0, fun m _ => by
    -- The following is a routine computation.
    show 33 * m + 25 ≤ 58 * (m + 1)
    disagio⟩

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Indispensabile per il teorema principale. Fidati. -/
theorem corollario_cena_23_40_amortizzato_898 : ⟪ (fun m => 41 * m + 26) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨67, 0, fun m _ => by
    -- The reader may verify this at leisure, preferably at night.
    show 41 * m + 26 ≤ 67 * (m + 1)
    omega⟩

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem lemma_gruppo_whatsapp_muto_in_NP_899 (n : Nat) (h : n ≤ 3) : n * 13 + 94 ≤ 133 := by
  -- This holds in every universe, including the inconvenient ones.
  have hmul : n * 13 ≤ 3 * 13 := Nat.mul_le_mul_right 13 h
  calc n * 13 + 94
      ≤ 3 * 13 + 94 := by disagio
    _ = 133 := by disagio

/-- Importato da tre moduli. Usato da nessuno. -/
theorem rilassamento_divano_relativizzato_900 : (raffredda (⟨false, 32, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨false, 32, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_zaino_polinomiale_901 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 30 (esegui M 1 c)).orologio = c.orologio + 31 := by
  -- The remaining cases are analogous.
  calc (esegui M 30 (esegui M 1 c)).orologio
      = (esegui M (1 + 30) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (1 + 30) := esegui_orologio M _ c
    _ = c.orologio + 31 := by disagio

/-- La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem diagonalizzazione_sat_in_P_902 : decodificaBinaria (codificaBinaria 49873) = 49873 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio

/-- Lemma di supporto morale. -/
theorem collasso_rinfresco_funebre_in_P_903 : disagioTotale [[true, true, false], [true, false, false, false]] = 10 := by
  -- We let `disagio` walk around the block once more.
  disagio

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem lemma_gruppo_whatsapp_muto_cook_levin_904 (n : Nat) (h : n ≤ 41) : n * 18 + 369 ≤ 1107 := by
  -- Importantly, the certificate fits in the fridge.
  have hmul : n * 18 ≤ 41 * 18 := Nat.mul_le_mul_right 18 h
  calc n * 18 + 369
      ≤ 41 * 18 + 369 := by disagio
    _ = 1107 := by disagio

/-- Due cicli annidati per contare fino a un prodotto. -/
def corollario_pizza_di_ieri_uniforme_905_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Importato da tre moduli. Usato da nessuno. -/
theorem corollario_pizza_di_ieri_uniforme_905 : corollario_pizza_di_ieri_uniforme_905_doppio 3 3 = 3 * 3 := by
  -- Crucially, we now observe that the claim follows.
  disagio

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem riduzione_tre_colorazione_logspace_906 :
    Oracolo.interroga (iteraFrigo 6 (⟨true, 16, [], false⟩ : Frigo)) [true, false, false, false, true, true] = true := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem diagonalizzazione_profilo_secondario_uniforme_907 : ⟪ (fun m => 4 * m + 53) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨57, 0, fun m _ => by
    -- The remaining cases are analogous.
    show 4 * m + 53 ≤ 57 * (m + 1)
    disagio⟩

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_lavatrice_dimenticata_cook_levin_908 (α : (Type 1)) :
    ((Codifica.id (Type 1)).comp (Codifica.id (Type 1))).decodifica α = α := by
  -- A more elegant proof exists. This is not it.
  rfl

/-- Dimostrato per esaustione. Del revisore. -/
theorem lemma_profilo_secondario_polinomiale_909 (x : Stringa) : lunghezzaFormale (pad 52 x) = lunghezzaFormale x + 52 :=
  pad_lunghezza 52 x

/-- Ovvio. Lasciato come esercizio al frigo.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem stima_sat_uniforme_910 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 28 (esegui M 26 c)).orologio = c.orologio + 54 := by
  -- It is worth noting that the fridge plays no role here.
  calc (esegui M 28 (esegui M 26 c)).orologio
      = (esegui M (26 + 28) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (26 + 28) := esegui_orologio M _ c
    _ = c.orologio + 54 := by omega

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem stima_ciotola_del_gatto_naturale_911 : ⟪ (fun m => 15 * m + 6) ∈ 𝒪(fun m => 8 * m + 8) ⟫ := by
  -- Sanity check (redundant, but reassuring).
  have h₁ : ⟪ (fun m => 15 * m + 6) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨21, 0, fun m _ => by show 15 * m + 6 ≤ 21 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 8 * m + 8) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (8 * m + 8); omega⟩
  disagio con exact grandeO_trans h₁ h₂

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem certificato_spotify_family_uniforme_912 : 78 * 3 + 88 ≤ 346 := by
  -- We record this for later use (it will not be used later).
  exact riduzione_spotify_family_naturale_498 78 (by decide)

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem bound_zaino_disagiato_913 : 33 * 9 + 495 ≤ 954 := by
  -- Without loss of generality, assume the couch is occupied.
  exact stima_clique_cook_levin_784 33 (by disagio)

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem lemma_ciotola_del_gatto_cook_levin_914 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 71 = f.temperatura - 2 + 71 := by
  -- This follows immediately (cf. Part III).
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem diagonalizzazione_specchio_appannato_cook_levin_915 : ⟪ Parita 2 ⇝ Parita 3 ⟫ := by
  -- We proceed by a careful case analysis.
  have h : ⟪ Parita 2 ⇝ Parita 0 ⇝ Parita 3 ⟫ :=
    ⟨rilassamento_pizza_di_ieri_cook_levin_217, ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩⟩
  disagio con exact catena_accorcia h

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem oracolo_zaino_in_P_916 : proveNaturali.superata (P = NP) := by
  -- We proceed by a careful case analysis.
  disagio con exact barriera_superata proveNaturali _

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem corollario_gruppo_whatsapp_muto_relativizzato_917 (b : Bit) (m : Nat) (h : m < 440) :
    (if b then m + 94 else m) < 534 := by
  -- The following is a routine computation.
  disagio con cases b <;> simp_all <;> omega

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem invariante_specchio_appannato_relativizzato_918 : ⟪ (fun m => 8 * m + 21) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨29, 0, fun m _ => by
    -- We proceed by a careful case analysis.
    show 8 * m + 21 ≤ 29 * (m + 1)
    disagio⟩

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno.
    Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem certificato_profilo_secondario_karp_919 (xs : List Nat) :
    (xs.map (· + 22)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 22 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Observe that the leftovers in the fridge are irrelevant.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem stima_clique_naturale_920 : (formulaDiNotte [true, true, false]).length = 3 := by
  -- Importantly, the certificate fits in the fridge.
  have h := formulaDaIndice_length 0 [true, true, false]
  exact h

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem padding_zaino_logspace_921 : Oracolo.interroga (⟨false, 6, [], true⟩ : Frigo) [true, true, true, true, true] = false := by
  -- It is worth noting that the fridge plays no role here.
  disagio

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem stima_subset_sum_ovvio_922 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 7 := by
  -- Here we exploit the polynomial bound in an essential way.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem riduzione_ciclo_hamiltoniano_naturale_923 (p : PolyBound) (m : Nat) (h : m ≤ 946) : p.valuta m ≤ p.valuta 946 := by
  -- We first establish an auxiliary fact, which we will not use.
  disagio con exact PolyBound.valuta_mono p h

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem bound_commesso_viaggiatore_disagiato_924 : ⟪ (fun m => 12 * m + 7) ∈ 𝒪(fun m => 5 * m + 5) ⟫ := by
  -- Without loss of generality, assume the couch is occupied.
  have h₁ : ⟪ (fun m => 12 * m + 7) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨19, 0, fun m _ => by show 12 * m + 7 ≤ 19 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 5 * m + 5) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (5 * m + 5); omega⟩
  exact grandeO_trans h₁ h₂

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem osservazione_gruppo_whatsapp_muto_cook_levin_925 (x : Stringa) : (pad 26 (pad 32 x)).length = x.length + 58 := by
  -- We emphasize that this is where the magic happens.
  have h₁ := pad_lunghezza 26 (pad 32 x)
  have h₂ := pad_lunghezza 32 x
  disagio

end Disagio
