/-
  PNP/Diamante.lean — Parte XII: Il diamante del frigo.

  Due istanze per la stessa classe. Vince quella con la priorità più alta: la notte.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Mutui

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte XII: Il diamante del frigo

  Due istanze per la stessa classe. Vince quella con la priorità più alta: la notte.
-/

section Diamante

/-- Qualcosa che si misura. In cuscini, di solito. -/
class Misura (α : Type u) where
  /-- La misura. -/
  misura : α → Nat

/-- Misura diurna: si conta alla luce del giorno. -/
class MisuraDiurna (α : Type u) where
  /-- La misura di giorno. -/
  diurna : α → Nat

/-- Misura notturna: si conta al buio, e viene sempre di più. -/
class MisuraNotturna (α : Type u) where
  /-- La misura di notte. -/
  notturna : α → Nat

/-- Primo lato del diamante. Priorità bassa: di giorno si dorme. -/
instance (priority := low) misuraDiGiorno {α : Type u} [MisuraDiurna α] : Misura α :=
  ⟨MisuraDiurna.diurna⟩

/-- Secondo lato del diamante. Priorità alta: di notte si decide. -/
instance (priority := high) misuraDiNotte {α : Type u} [MisuraNotturna α] : Misura α :=
  ⟨MisuraNotturna.notturna⟩

/-- Un elettrodomestico: si misura, e consuma. -/
class Elettrodomestico (α : Type u) extends Misura α where
  /-- Il consumo, in bollette. -/
  consumo : α → Nat

/-- Un frigorifero è un elettrodomestico con dei ripiani. -/
class Frigorifero (α : Type u) extends Elettrodomestico α where
  /-- I ripiani. -/
  ripiani : α → Nat

/-- Un congelatore è un elettrodomestico con la brina. -/
class Congelatore (α : Type u) extends Elettrodomestico α where
  /-- La brina, in millimetri. -/
  brina : α → Nat

/-- Il combinato: frigorifero sopra, congelatore sotto, diamante in mezzo.
    I due `Elettrodomestico` vengono fusi in uno: Lean è più ordinato di noi. -/
class Combinato (α : Type u) extends Frigorifero α, Congelatore α

instance : MisuraDiurna Frigo := ⟨fun f => f.temperatura⟩
instance : MisuraNotturna Frigo := ⟨fun f => f.temperatura + 100⟩
instance : MisuraDiurna Stringa := ⟨List.length⟩
instance : MisuraNotturna Stringa := ⟨fun x => x.length + 1⟩

/-- Il frigo di casa è un combinato. La sua misura da elettrodomestico è la terza
    opinione, e nessuno la chiede. -/
instance : Combinato Frigo where
  misura f := f.ripiani.length
  consumo f := f.temperatura * 2
  ripiani f := f.ripiani.length
  brina f := 40 - f.temperatura

/-- Il diamante è risolto dalla priorità, non dalla matematica: vince la notte. -/
theorem diamante_risolto (f : Frigo) : Misura.misura f = f.temperatura + 100 := rfl

/-- Il lato perdente, chiamato per nome: di giorno il frigo è più fresco. -/
theorem lato_diurno (f : Frigo) : @Misura.misura Frigo misuraDiGiorno f = f.temperatura := rfl

/-- La terza opinione, quella dell'elettrodomestico: conta i ripiani. -/
theorem lato_elettrodomestico (f : Frigo) :
    @Misura.misura Frigo Elettrodomestico.toMisura f = f.ripiani.length := rfl

/-- I due lati del combinato coincidono. Questo diamante, almeno, commuta. -/
theorem combinato_commuta (f : Frigo) :
    @Elettrodomestico.consumo Frigo Frigorifero.toElettrodomestico f =
      @Elettrodomestico.consumo Frigo Congelatore.toElettrodomestico f := rfl

/-- Di notte e di giorno il frigo misura cose diverse. Il diamante non commuta. -/
theorem diamante_non_commuta (f : Frigo) :
    @Misura.misura Frigo misuraDiGiorno f ≠ @Misura.misura Frigo misuraDiNotte f := by
  show f.temperatura ≠ f.temperatura + 100
  disagio

end Diamante

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem collasso_cena_23_40_disagiato_671 : @Misura.misura Frigo misuraDiGiorno (⟨true, 24, [], true⟩ : Frigo) = 24 := by
  -- Morally, this is Cook–Levin.
  rfl

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Il certificato è polinomiale. Il disagio no. -/
theorem corollario_ciclo_hamiltoniano_in_NP_672 :
    Giornata.frighi (.fine) = 0 := by
  -- The following is a routine computation.
  disagio

/-- La misura di terminazione è assurda. La terminazione no.
    Il certificato è polinomiale. Il disagio no. -/
theorem padding_zaino_in_NP_673 : Elettrodomestico.consumo (⟨false, 11, [], false⟩ : Frigo) = 22 := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem lemma_specchio_appannato_relativizzato_674 : (raffredda (⟨true, 39, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 39, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem lemma_frigo_aperto_relativizzato_675 : ⟪ (fun m => 30 * m + 18) ∈ 𝒪(fun m => 1 * m + 1) ⟫ := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h₁ : ⟪ (fun m => 30 * m + 18) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨48, 0, fun m _ => by show 30 * m + 18 ≤ 48 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 1 * m + 1) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (1 * m + 1); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem certificato_sat_logspace_676 : @Misura.misura Frigo misuraDiGiorno (⟨true, 37, [], true⟩ : Frigo) + 100 = Misura.misura (⟨true, 37, [], true⟩ : Frigo) := by
  -- We first establish an auxiliary fact, which we will not use.
  disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 23. -/
def rilassamento_sat_karp_677_giri (m : Nat) : Nat :=
  if h : m < 23 then m else rilassamento_sat_karp_677_giri (m - 9)
termination_by m
decreasing_by simp_wf; disagio

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem rilassamento_sat_karp_677 (m : Nat) : rilassamento_sat_karp_677_giri m < 23 := by
  -- Let us now carefully unfold the definitions.
  induction m using rilassamento_sat_karp_677_giri.induct with
  | case1 m h => rw [rilassamento_sat_karp_677_giri]; disagio con simp [h]
  | case2 m h ih => rw [rilassamento_sat_karp_677_giri]; disagio con (simp [h]; exact ih)

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem stima_clique_logspace_678 : ⟪ Parita 5 ⇝ Parita 5 in n ↦ n + 18 ⟫ :=
  ⟨⟨pad 2, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- By the standard argument.
    show PolyBound.identita.valuta n ≤ n + 18
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem collasso_zaino_amortizzato_679 : Misura.misura ([true, false, false, false, false, true, false, true] : Stringa) = 9 := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem proposizione_subset_sum_uniforme_680 : Misura.misura ([true, false, false, false, false, false, false, true] : Stringa) = 9 := by
  -- A more elegant proof exists. This is not it.
  decide

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem collasso_copertura_vertici_logspace_681 (α : (Type 1)) :
    ((Codifica.id (Type 1)).comp (Codifica.id (Type 1))).decodifica α = α := by
  -- A more elegant proof exists. This is not it.
  disagio

/-- Due cicli annidati per contare fino a un prodotto. -/
def corollario_specchio_appannato_polinomiale_682_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem corollario_specchio_appannato_polinomiale_682 : corollario_specchio_appannato_polinomiale_682_doppio 4 3 = 4 * 3 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  disagio

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem corollario_spotify_family_cook_levin_683 : @Misura.misura Frigo misuraDiGiorno (⟨false, 31, [], true⟩ : Frigo) = 31 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem invariante_profilo_secondario_cook_levin_684 (n : Nat) (h : n ≤ 57) : n * 32 + 457 ≤ 2281 := by
  -- We emphasize that this is where the magic happens.
  have hmul : n * 32 ≤ 57 * 32 := Nat.mul_le_mul_right 32 h
  calc n * 32 + 457
      ≤ 57 * 32 + 457 := by disagio
    _ = 2281 := by disagio

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem padding_cena_23_40_logspace_685 : Misura.misura ([true, true] : Stringa) = 3 := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio

/-- Il certificato è polinomiale. Il disagio no. -/
theorem bound_tre_colorazione_amortizzato_686 : Misura.misura (⟨true, 38, [], false⟩ : Frigo) = 138 := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio

/-- Il diamante si chiude. Il frigo no.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem riduzione_spotify_family_naturale_687 : ⟪ Parita 0 ⇝ Parita 8 in n ↦ n + 10 ⟫ :=
  ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Here we exploit the polynomial bound in an essential way.
    show PolyBound.identita.valuta n ≤ n + 10
    have h := PolyBound.valuta_identita n
    disagio⟩

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem proposizione_ciclo_hamiltoniano_in_P_688 : (raffredda (⟨true, 6, [], false⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 6, [], false⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem collasso_specchio_appannato_in_P_689 : Misura.misura ([true, false, true, false, false, true, true, false, false] : Stringa) = 10 := by
  -- A more elegant proof exists. This is not it.
  disagio

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_tre_colorazione_logspace_690 : Elettrodomestico.consumo (⟨false, 24, [], false⟩ : Frigo) = 48 := by
  -- The reader may verify this at leisure, preferably at night.
  disagio

/-- Lemma di supporto morale. -/
theorem invariante_ciclo_hamiltoniano_ovvio_691 : Misura.misura ([true, true, false, false, false, true, true, true] : Stringa) = 9 := by
  -- We record this for later use (it will not be used later).
  disagio

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    Il caso induttivo è identico al caso base, ma più lungo. -/
theorem oracolo_subset_sum_polinomiale_692 : Elettrodomestico.consumo (⟨true, 19, [], true⟩ : Frigo) = 38 := by
  -- Sanity check (redundant, but reassuring).
  decide

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem padding_zaino_naturale_693 : Elettrodomestico.consumo (⟨true, 23, [], true⟩ : Frigo) = 46 := by
  -- Let us now carefully unfold the definitions.
  decide

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem collasso_specchio_appannato_in_P_694 : @Misura.misura Frigo misuraDiGiorno (⟨true, 40, [], false⟩ : Frigo) + 100 = Misura.misura (⟨true, 40, [], false⟩ : Frigo) := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem diagonalizzazione_ciotola_del_gatto_karp_695 : @Misura.misura Frigo misuraDiGiorno (⟨true, 39, [], false⟩ : Frigo) = 39 := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem osservazione_pizza_di_ieri_naturale_696 : @Misura.misura Frigo misuraDiGiorno (⟨true, 4, [], false⟩ : Frigo) = 4 := by
  -- The following is a routine computation.
  rfl

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem riduzione_commesso_viaggiatore_disagiato_697 : Misura.misura (⟨true, 40, [], true⟩ : Frigo) = 140 := by
  -- The reader may verify this at leisure, preferably at night.
  rfl

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Il certificato è polinomiale. Il disagio no. -/
theorem bound_sat_notturno_698 : @Misura.misura Frigo misuraDiGiorno (⟨true, 40, [], false⟩ : Frigo) + 100 = Misura.misura (⟨true, 40, [], false⟩ : Frigo) := by
  -- At this point the argument is essentially complete.
  disagio

/-- Lemma di supporto morale.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem oracolo_cena_23_40_cook_levin_699 : ⟪ Parita 6 ⇝ Parita 20 ⟫ :=
  ⟨⟨pad 2, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem proposizione_copertura_vertici_cook_levin_700 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 23 (esegui M 23 c)).orologio = c.orologio + 46 := by
  -- This is the heart of the argument. The argument has several hearts.
  calc (esegui M 23 (esegui M 23 c)).orologio
      = (esegui M (23 + 23) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (23 + 23) := esegui_orologio M _ c
    _ = c.orologio + 46 := by disagio

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem padding_rinfresco_funebre_amortizzato_701 : Misura.misura (⟨true, 32, [], false⟩ : Frigo) = 132 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem corollario_specchio_appannato_naturale_702 : certificato_pizza_di_ieri_naturale_26_giri 536 < 7 + 6 := by
  -- Without loss of generality, assume the couch is occupied.
  have h := certificato_pizza_di_ieri_naturale_26 536
  disagio

/-- Lemma di supporto morale. -/
theorem invariante_lavatrice_dimenticata_in_P_703 : (raffredda (⟨true, 30, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 30, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  exact Nat.le_trans h₁ h₂

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem lemma_zaino_notturno_704 :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su ⟨Nat, 976⟩))).abitante)) = (976 : Nat) := by
  -- As is well known, the washing machine finished hours ago.
  disagio

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Indispensabile per il teorema principale. Fidati. -/
theorem invariante_sat_notturno_705 (xs : List Nat) :
    (xs.map (· + 6)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 6 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Observe that the leftovers in the fridge are irrelevant.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    disagio

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem proposizione_tre_colorazione_uniforme_706 : (raffredda (⟨true, 2, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 2, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem diagonalizzazione_vocale_a_se_stesso_disagiato_707 :
    FormulaCNF.valuta (assegnamentoDaStringa [false, true, false, true, true]) [[⟨7, false⟩, ⟨3, false⟩, ⟨1, true⟩]] = true := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem diagonalizzazione_spotify_family_amortizzato_708 : ⟪ (fun m => 9 * m + 26) ∈ 𝒪(fun m => 4 * m + 4) ⟫ := by
  -- We record this for later use (it will not be used later).
  have h₁ : ⟪ (fun m => 9 * m + 26) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨35, 0, fun m _ => by show 9 * m + 26 ≤ 35 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 4 * m + 4) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (4 * m + 4); disagio⟩
  disagio con exact grandeO_trans h₁ h₂

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem certificato_copertura_vertici_naturale_709 : @Misura.misura Frigo misuraDiGiorno (⟨true, 9, [], false⟩ : Frigo) = 9 := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem riduzione_ciotola_del_gatto_in_P_710 :
    (codificaUnariaC.prod codificaUnariaC).decodifica
      ((codificaUnariaC.prod codificaUnariaC).codifica (27, 22)) = (27, 22) := by
  -- Morally, this is Cook–Levin.
  disagio con exact (codificaUnariaC.prod codificaUnariaC).andata_e_ritorno _

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def stima_lavatrice_dimenticata_logspace_711_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 5
  for _ in [0:giri] do
    acc := acc + 2
  return acc

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem stima_lavatrice_dimenticata_logspace_711 : stima_lavatrice_dimenticata_logspace_711_ciclo 13 = 5 + 2 * 13 := by
  -- By the standard argument.
  decide

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem stima_ciclo_hamiltoniano_notturno_712 (b : Bit) (m : Nat) (h : m < 213) :
    (if b then m + 36 else m) < 249 := by
  -- This follows immediately (cf. Part III).
  cases b <;> simp_all <;> omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem corollario_divano_cook_levin_713 : Misura.misura ([false] : Stringa) = 2 := by
  -- Here we exploit the polynomial bound in an essential way.
  decide

end Disagio
