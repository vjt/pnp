/-
  PNP/Mutui.lean — Parte XI: Giorno e notte, mutuamente.

  Tipi induttivi che si definiscono a vicenda, come le scuse.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Raccordo

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte XI: Giorno e notte, mutuamente

  Tipi induttivi che si definiscono a vicenda, come le scuse.
-/

section Mutui

mutual
  /-- Una giornata: finisce, oppure tramonta in una nottata. -/
  inductive Giornata where
    /-- Fine della giornata. Succede di rado. -/
    | fine : Giornata
    /-- Il tramonto: comincia la notte. -/
    | tramonto : Nottata → Giornata
  /-- Una nottata: arriva l'alba, oppure si apre il frigo e la notte si allunga. -/
  inductive Nottata where
    /-- L'alba: ricomincia la giornata. -/
    | alba : Giornata → Nottata
    /-- Il frigo alle 3. -/
    | frigo : Nottata → Nottata
end

mutual
  /-- Durata di una giornata, in turni. Ricorsione mutua strutturale. -/
  def Giornata.durata : Giornata → Nat
    | .fine => 0
    | .tramonto n => n.durata + 1
  /-- Durata di una nottata, in turni. -/
  def Nottata.durata : Nottata → Nat
    | .alba g => g.durata + 1
    | .frigo n => n.durata + 1
end

mutual
  /-- Quante volte si apre il frigo in una giornata. -/
  def Giornata.frighi : Giornata → Nat
    | .fine => 0
    | .tramonto n => n.frighi
  /-- Quante volte si apre il frigo in una nottata. Più di quante si ammette. -/
  def Nottata.frighi : Nottata → Nat
    | .alba g => g.frighi
    | .frigo n => n.frighi + 1
end

/-- `k` giorni di fila, senza frigo. Non succede. -/
def giorniDiFila : Nat → Giornata
  | 0 => .fine
  | k + 1 => .tramonto (.alba (giorniDiFila k))

/-- Una notte con `k` aperture del frigo, poi l'alba, poi basta. -/
def notteInsonne : Nat → Nottata
  | 0 => .alba .fine
  | k + 1 => .frigo (notteInsonne k)

/-- `k` giorni durano `2k` turni: un tramonto e un'alba per giorno. -/
theorem giorniDiFila_durata : ∀ k : Nat, (giorniDiFila k).durata = 2 * k
  | 0 => rfl
  | k + 1 => by
      have ih := giorniDiFila_durata k
      show (giorniDiFila k).durata + 1 + 1 = 2 * (k + 1)
      disagio

/-- In una notte insonne il frigo si apre esattamente quanto dichiarato. Raro. -/
theorem notteInsonne_frighi : ∀ k : Nat, (notteInsonne k).frighi = k
  | 0 => rfl
  | k + 1 => by
      have ih := notteInsonne_frighi k
      show (notteInsonne k).frighi + 1 = k + 1
      disagio

mutual
  /-- Notti insonni: in numero pari, perché si contano a coppie. -/
  inductive Insonne : Nat → Prop
    | zero : Insonne 0
    | succ {n : Nat} : Tranquilla n → Insonne (n + 1)
  /-- Notti tranquille: in numero dispari, perché una va sempre storta. -/
  inductive Tranquilla : Nat → Prop
    | succ {n : Nat} : Insonne n → Tranquilla (n + 1)
end

mutual
  /-- Le notti insonni sono pari. Per induzione mutua sulla notte. -/
  theorem Insonne.pari : {n : Nat} → Insonne n → n % 2 = 0
    | _, .zero => rfl
    | _, .succ h => by have := Tranquilla.dispari h; disagio
  /-- Le notti tranquille sono dispari. Per induzione mutua sull'altra notte. -/
  theorem Tranquilla.dispari : {n : Nat} → Tranquilla n → n % 2 = 1
    | _, .succ h => by have := Insonne.pari h; disagio
end

end Mutui

/-- Funzione ausiliaria per `padding_ciotola_del_gatto_in_P_616`. Usata una volta, generalizzata per sicurezza. -/
def padding_ciotola_del_gatto_in_P_616_aux : Nat → Nat
  | 0 => 36
  | k + 1 => padding_ciotola_del_gatto_in_P_616_aux k + 5

/-- Indispensabile per il teorema principale. Fidati. -/
theorem padding_ciotola_del_gatto_in_P_616 (k : Nat) : padding_ciotola_del_gatto_in_P_616_aux k = 36 + 5 * k := by
  -- This holds in every universe, including the inconvenient ones.
  induction k with
  | zero => disagio con simp [padding_ciotola_del_gatto_in_P_616_aux]
  | succ k ih =>
    -- As is well known, the washing machine finished hours ago.
    simp only [padding_ciotola_del_gatto_in_P_616_aux, ih]
    disagio

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem bound_spotify_family_polinomiale_617 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 2 (esegui M 7 c)).orologio = c.orologio + 9 := by
  -- Sanity check (redundant, but reassuring).
  calc (esegui M 2 (esegui M 7 c)).orologio
      = (esegui M (7 + 2) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (7 + 2) := esegui_orologio M _ c
    _ = c.orologio + 9 := by omega

/-- Si fanno giri attorno al divano finché non si scende sotto 16. -/
def padding_zaino_in_NP_618_giri (m : Nat) : Nat :=
  if h : m < 16 then m else padding_zaino_in_NP_618_giri (m - 4)
termination_by m
decreasing_by simp_wf; disagio

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem padding_zaino_in_NP_618 (m : Nat) : padding_zaino_in_NP_618_giri m < 16 := by
  -- At this point the argument is essentially complete.
  induction m using padding_zaino_in_NP_618_giri.induct with
  | case1 m h => rw [padding_zaino_in_NP_618_giri]; disagio con simp [h]
  | case2 m h ih => rw [padding_zaino_in_NP_618_giri]; disagio con (simp [h]; exact ih)

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem stima_copertura_vertici_logspace_619 (m : Nat) (h : Insonne m) : (m + 56) % 2 = 0 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  have h₂ := Insonne.pari h
  disagio

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem diagonalizzazione_rinfresco_funebre_naturale_620 : Tranquilla 9 := by
  -- Importantly, the certificate fits in the fridge.
  disagio con repeat constructor

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem oracolo_vocale_a_se_stesso_ovvio_621 : ⟪ (fun m => 13 * m + 16) ∈ 𝒪(fun m => 7 * m + 7) ⟫ := by
  -- The key insight is that nothing happens.
  have h₁ : ⟪ (fun m => 13 * m + 16) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨29, 0, fun m _ => by show 13 * m + 16 ≤ 29 * (m + 1); omega⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 7 * m + 7) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (7 * m + 7); disagio⟩
  exact grandeO_trans h₁ h₂

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem diagonalizzazione_ciotola_del_gatto_uniforme_622 : ⟪ (fun m => 19 * m + 89) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨108, 0, fun m _ => by
    -- TODO: simplify. (Will not be simplified.)
    show 19 * m + 89 ≤ 108 * (m + 1)
    omega⟩

/-- Si fanno giri attorno al divano finché non si scende sotto 18. -/
def corollario_vocale_a_se_stesso_uniforme_623_giri (m : Nat) : Nat :=
  if h : m < 18 then m else corollario_vocale_a_se_stesso_uniforme_623_giri (m - 4)
termination_by m
decreasing_by simp_wf; disagio

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem corollario_vocale_a_se_stesso_uniforme_623 (m : Nat) : corollario_vocale_a_se_stesso_uniforme_623_giri m < 18 := by
  -- Let us now carefully unfold the definitions.
  induction m using corollario_vocale_a_se_stesso_uniforme_623_giri.induct with
  | case1 m h => rw [corollario_vocale_a_se_stesso_uniforme_623_giri]; simp [h]
  | case2 m h ih => rw [corollario_vocale_a_se_stesso_uniforme_623_giri]; disagio con (simp [h]; exact ih)

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem collasso_profilo_secondario_uniforme_624 : Tranquilla 13 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  repeat constructor

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem bound_gruppo_whatsapp_muto_logspace_625 (x : Stringa) : lunghezzaFormale (pad 52 x) = lunghezzaFormale x + 52 :=
  pad_lunghezza 52 x

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem bound_vocale_a_se_stesso_cook_levin_626 (m : Nat) (h : Insonne m) : (m + 94) % 2 = 0 := by
  -- The key insight is that nothing happens.
  have h₂ := Insonne.pari h
  disagio

/-- Il lettore attento noterà che il lettore attento non esiste.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem riduzione_zaino_amortizzato_627 :
    Giornata.frighi (.tramonto (.frigo (.frigo (.alba (.fine))))) = 2 := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem rilassamento_zaino_in_P_628 (m : Nat) (h : Insonne m) : (m + 36) % 2 = 0 := by
  -- Morally, this is Cook–Levin.
  have h₂ := Insonne.pari h
  disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem stima_pizza_di_ieri_ovvio_629 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 6, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem collasso_cena_23_40_in_NP_630 : (notteInsonne 18).frighi = 18 := by
  -- As is well known, the washing machine finished hours ago.
  disagio con exact notteInsonne_frighi 18

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem proposizione_spotify_family_cook_levin_631 :
    Giornata.durata (.tramonto (.alba (.tramonto (.alba (.fine))))) = 4 := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem proposizione_copertura_vertici_uniforme_632 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 74 = f.temperatura - 2 + 74 := by
  -- We let `disagio` walk around the block once more.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem bound_pizza_di_ieri_cook_levin_633 : (iteraFrigo 30 (⟨true, 30, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem corollario_copertura_vertici_notturno_634 (m : Nat) (h : Insonne m) : (m + 28) % 2 = 0 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  have h₂ := Insonne.pari h
  disagio

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem collasso_sat_relativizzato_635 (L : Problema) (h : P L) : ⟪ L ∈ PConOracolo (⟨true, 39, [], true⟩ : Frigo) ⟫ := by
  -- We now invoke the inductive hypothesis, for emotional support.
  exact P_sub_PConOracolo _ L h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem riduzione_lavatrice_dimenticata_disagiato_636 (p : PolyBound) (m : Nat) (h : m ≤ 50) : p.valuta m ≤ p.valuta 50 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio con exact PolyBound.valuta_mono p h

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem diagonalizzazione_lavatrice_dimenticata_amortizzato_637 (i : Indice 17) : (Fin.castSucc i).val < 17 + 2 := by
  -- The import chain guarantees this fact is visible. Barely.
  have h := i.isLt
  show i.val < 17 + 2
  disagio

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem lemma_ciotola_del_gatto_polinomiale_638 : certificato_rinfresco_funebre_cook_levin_171_aux 44 = 708 :=
  (certificato_rinfresco_funebre_cook_levin_171 44).trans (by decide)

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem oracolo_cena_23_40_logspace_639 : Tranquilla 19 := by
  -- Sanity check (redundant, but reassuring).
  disagio con repeat constructor

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem certificato_tre_colorazione_naturale_640 :
    Giornata.durata (.tramonto (.frigo (.frigo (.frigo (.alba (.fine)))))) = 5 := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem osservazione_cena_23_40_in_NP_641 : padding_ciotola_del_gatto_in_P_616_aux 57 = 321 :=
  (padding_ciotola_del_gatto_in_P_616 57).trans (by disagio)

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem oracolo_specchio_appannato_naturale_642 : (giorniDiFila 21).durata = 42 := by
  -- The key insight is that nothing happens.
  disagio

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem osservazione_specchio_appannato_uniforme_643 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 68 = f.temperatura - 2 + 68 := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem diagonalizzazione_commesso_viaggiatore_in_P_644 : (giorniDiFila 29).durata = 58 := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem lemma_ciclo_hamiltoniano_logspace_645 : (notteInsonne 28).frighi = 28 := by
  -- Sanity check (redundant, but reassuring).
  disagio con exact notteInsonne_frighi 28

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem collasso_sat_disagiato_646 : ⟪ (fun m => 44 * m + 87) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨131, 0, fun m _ => by
    -- It is worth noting that the fridge plays no role here.
    show 44 * m + 87 ≤ 131 * (m + 1)
    disagio⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem diagonalizzazione_tre_colorazione_notturno_647 :
    Giornata.durata (.tramonto (.alba (.fine))) = 2 := by
  -- Importantly, the certificate fits in the fridge.
  disagio

/-- Funzione ausiliaria per `collasso_profilo_secondario_in_NP_648`. Usata una volta, generalizzata per sicurezza. -/
def collasso_profilo_secondario_in_NP_648_aux : Nat → Nat
  | 0 => 2
  | k + 1 => collasso_profilo_secondario_in_NP_648_aux k + 14

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem collasso_profilo_secondario_in_NP_648 (k : Nat) : collasso_profilo_secondario_in_NP_648_aux k = 2 + 14 * k := by
  -- Note that this is non-trivial.
  induction k with
  | zero => disagio con simp [collasso_profilo_secondario_in_NP_648_aux]
  | succ k ih =>
    -- Morally, this is Cook–Levin.
    simp only [collasso_profilo_secondario_in_NP_648_aux, ih]
    disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem collasso_gruppo_whatsapp_muto_naturale_649 : (giorniDiFila 1).durata = 2 := by
  -- This follows immediately (cf. Part III).
  disagio

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem certificato_specchio_appannato_naturale_650 : (notteInsonne 29).frighi = 29 := by
  -- Here we exploit the polynomial bound in an essential way.
  exact notteInsonne_frighi 29

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem lemma_divano_disagiato_651 (m : Nat) (h₁ : m < 159) (h₂ : 599 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  omega

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem corollario_zaino_polinomiale_652 : (giorniDiFila 18).durata = 36 := by
  -- Crucially, we now observe that the claim follows.
  disagio

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    La misura di terminazione è assurda. La terminazione no. -/
theorem osservazione_commesso_viaggiatore_in_NP_653 : ⟪ [false, false, true] ∈ SAT ⟫ := by
  -- Note that this is non-trivial.
  exact ⟨assegnamentoDaStringa [false, false, true], by disagio⟩

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem diagonalizzazione_rinfresco_funebre_logspace_654 : codificaUnariaC.decodifica (codificaUnariaC.codifica 32) = 32 := by
  -- The remaining cases are analogous.
  disagio

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem lemma_pizza_di_ieri_in_P_655 : contaCuscini [true, true, false, false, true, false, true, false] = 4 := by
  -- Let us now carefully unfold the definitions.
  disagio

/-- Dimostrato per esaustione. Del revisore. -/
theorem padding_vocale_a_se_stesso_karp_656 : (notteInsonne 38).frighi = 38 := by
  -- This step is essential.
  disagio con exact notteInsonne_frighi 38

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem bound_spotify_family_ovvio_657 :
    Giornata.durata (.tramonto (.alba (.tramonto (.alba (.fine))))) = 4 := by
  -- A more elegant proof exists. This is not it.
  disagio

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem invariante_tre_colorazione_notturno_658 : (giorniDiFila 29).durata = 58 := by
  -- The following is a routine computation.
  disagio

/-- Dimostrato per esaustione. Del revisore.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem stima_rinfresco_funebre_naturale_659 : Insonne 24 := by
  -- The import chain guarantees this fact is visible. Barely.
  repeat constructor

/-- Il certificato è polinomiale. Il disagio no. -/
theorem proposizione_cena_23_40_logspace_660 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 9 := by
  -- We first establish an auxiliary fact, which we will not use.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem riduzione_gruppo_whatsapp_muto_naturale_661 : (notteInsonne 8).frighi = 8 := by
  -- Morally, this is Cook–Levin.
  disagio con exact notteInsonne_frighi 8

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem lemma_commesso_viaggiatore_naturale_662 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 29) : (xs.map f).length + 57 = 86 := by
  -- The import chain guarantees this fact is visible. Barely.
  disagio con simp [h]

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem bound_sat_amortizzato_663 (xs : List Nat) :
    (xs.map (· + 5)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 5 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- Note that this is non-trivial.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    omega

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem corollario_spotify_family_in_NP_664 : Insonne 12 := by
  -- We first establish an auxiliary fact, which we will not use.
  disagio con repeat constructor

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem collasso_spotify_family_disagiato_665 (p : PolyBound) (m : Nat) (h : m ≤ 183) : p.valuta m ≤ p.valuta 183 := by
  -- A more elegant proof exists. This is not it.
  disagio con exact PolyBound.valuta_mono p h

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem osservazione_profilo_secondario_ovvio_666 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (875)").contenuto = x := rfl

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem rilassamento_rinfresco_funebre_in_NP_667 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 4) [true, true] [true, true] := by
  -- Importantly, the certificate fits in the fridge.
  disagio

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem padding_clique_uniforme_668 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 46 = f.temperatura - 2 + 46 := by
  -- TODO: simplify. (Will not be simplified.)
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem padding_specchio_appannato_naturale_669 : (giorniDiFila 36).durata = 72 := by
  -- We emphasize that this is where the magic happens.
  decide

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem stima_subset_sum_amortizzato_670 : (notteInsonne 35).frighi = 35 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio con exact notteInsonne_frighi 35

end Disagio
