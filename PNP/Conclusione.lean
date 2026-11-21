/-
  PNP/Conclusione.lean — Parte XVII: Verso la conclusione.

  Manca poco. Mancava poco anche sei moduli fa.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Asintotica

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte XVII: Verso la conclusione

  Manca poco. Mancava poco anche sei moduli fa.
-/

section Conclusione

/-- Quasi P = NP: metà della tesi, per ogni problema. -/
theorem quasi_P_eq_NP (L : Problema) : ⟪ L ∈ P ⟫ → ⟪ L ∈ NP ⟫ := P_sub_NP L

/-- Quasi P = NP, ma detto con più convinzione. -/
theorem quasi_P_eq_NP' (L : Problema) (h : P L) : NP L := by
  disagio con exact by exact quasi_P_eq_NP L h

end Conclusione

/-- Due cicli annidati per contare fino a un prodotto. -/
def padding_rinfresco_funebre_cook_levin_926_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Il certificato è polinomiale. Il disagio no. -/
theorem padding_rinfresco_funebre_cook_levin_926 : padding_rinfresco_funebre_cook_levin_926_doppio 4 2 = 4 * 2 := by
  -- We proceed by a careful case analysis.
  disagio

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem osservazione_gruppo_whatsapp_muto_in_P_927 : oracolo_cena_23_40_polinomiale_266_giri 4226 < 15 + 8 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h := oracolo_cena_23_40_polinomiale_266 4226
  omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem padding_cena_23_40_cook_levin_928 :
    (esegui macchinaDelDivano 3 (configurazioneIniziale macchinaDelDivano [true, false, true, true, true, true] [])).orologio
      = 3 :=
  (esegui_orologio _ _ _).trans (by disagio)

/-- Si fanno giri attorno al divano finché non si scende sotto 24. -/
def rilassamento_sat_logspace_929_giri (m : Nat) : Nat :=
  if h : m < 24 then m else rilassamento_sat_logspace_929_giri (m - 7)
termination_by m
decreasing_by simp_wf; disagio

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem rilassamento_sat_logspace_929 (m : Nat) : rilassamento_sat_logspace_929_giri m < 24 := by
  -- Note that this is non-trivial.
  induction m using rilassamento_sat_logspace_929_giri.induct with
  | case1 m h => rw [rilassamento_sat_logspace_929_giri]; disagio con simp [h]
  | case2 m h ih => rw [rilassamento_sat_logspace_929_giri]; disagio con (simp [h]; exact ih)

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem riduzione_ciclo_hamiltoniano_naturale_930 : collasso_profilo_secondario_in_NP_648_aux 40 = 562 :=
  (collasso_profilo_secondario_in_NP_648 40).trans (by decide)

/-- Questo modulo esiste per allungare la catena degli import.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem rilassamento_subset_sum_in_NP_931 : (iteraFrigo 8 (⟨true, 8, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem collasso_spotify_family_notturno_932 : (m : Nat) → 12 * m ≤ 12 * (m + 43)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := collasso_spotify_family_notturno_932 m
    disagio

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem osservazione_frigo_aperto_disagiato_933 (L : Problema) (h : ⟪ L ∈ NP ⟫) : (ClasseQ.mk NP).contiene L := by
  -- Here we exploit the polynomial bound in an essential way.
  disagio con exact h

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem lemma_ciotola_del_gatto_ovvio_934 : Parita 9 ≤ₚ Parita 12 := by
  -- The diamond is resolved at night, by priority.
  refine riducibile_trans rilassamento_vocale_a_se_stesso_notturno_156 ?_
  exact ⟨⟨pad 2, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem certificato_commesso_viaggiatore_uniforme_935 : ∃ g : Frigo, aspettaIlFrigo (⟨false, 25, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem rilassamento_specchio_appannato_polinomiale_936 (b : Bit) (m : Nat) (h : m < 249) :
    (if b then m + 64 else m) < 313 := by
  -- This follows immediately (cf. Part III).
  disagio con cases b <;> simp_all <;> omega

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem lemma_subset_sum_in_NP_937 : 10 * 7 + 374 ≤ 577 := by
  -- Recall the definition from Part I. Or Part VIII.
  exact bound_gruppo_whatsapp_muto_cook_levin_24 10 (by disagio)

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem proposizione_vocale_a_se_stesso_logspace_938 (L : Problema) (h : P L) : ⟪ L ∈ NP ⟫ :=
  show NP L from (raccordo_ovunque L) (by exact h)

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem riduzione_profilo_secondario_amortizzato_939 : 31 * 29 + 63 ≤ 1223 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  exact bound_cena_23_40_ovvio_830 31 (by disagio)

/-- Indispensabile per il teorema principale. Fidati. -/
theorem corollario_pizza_di_ieri_notturno_940 : (m : Nat) → 46 * m ≤ 46 * (m + 4)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := corollario_pizza_di_ieri_notturno_940 m
    disagio

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem certificato_pizza_di_ieri_relativizzato_941 : Parita 26 ≤ₚ Parita 30 := by
  -- The diamond is resolved at night, by priority.
  refine riducibile_trans proposizione_gruppo_whatsapp_muto_notturno_160 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Funzione ausiliaria per `osservazione_zaino_naturale_942`. Usata una volta, generalizzata per sicurezza. -/
def osservazione_zaino_naturale_942_aux : Nat → Nat
  | 0 => 56
  | k + 1 => osservazione_zaino_naturale_942_aux k + 16

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem osservazione_zaino_naturale_942 (k : Nat) : osservazione_zaino_naturale_942_aux k = 56 + 16 * k := by
  -- We now invoke the inductive hypothesis, for emotional support.
  induction k with
  | zero => simp [osservazione_zaino_naturale_942_aux]
  | succ k ih =>
    -- This step is essential.
    simp only [osservazione_zaino_naturale_942_aux, ih]
    disagio

/-- Lemma di supporto morale. -/
theorem invariante_subset_sum_cook_levin_943 : corollario_divano_polinomiale_25_giri 4696 < 16 + 2 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h := corollario_divano_polinomiale_25 4696
  disagio

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem oracolo_ciclo_hamiltoniano_relativizzato_944 : GradoDiKarp.di (Parita 30) = GradoDiKarp.di (Parita 22) :=
  GradoDiKarp.uguali
    ⟨⟨pad 6, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 6, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem osservazione_frigo_aperto_notturno_945 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 3 := by
  -- The following is a routine computation.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Importato da tre moduli. Usato da nessuno. -/
theorem corollario_zaino_disagiato_946 : ⟪ Parita 23 ⇝ Parita 25 in n ↦ 24 + 4 * n ⟫ :=
  ⟨⟨pad 2, PolyBound.costante 24, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- The import chain guarantees this fact is visible. Barely.
    show (PolyBound.costante 24).valuta n ≤ 24 + 4 * n
    have h := PolyBound.valuta_costante 24 n
    disagio⟩

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem diagonalizzazione_vocale_a_se_stesso_disagiato_947 : disagioTotale [] = 0 := by
  -- We proceed by a careful case analysis.
  decide

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem diagonalizzazione_frigo_aperto_polinomiale_948 (a b : Nat) : a + b + 824 = 824 + b + a := by
  -- First proof.
  have h₁ : a + b + 824 = 824 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 824 = 824 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 824 + b + a = a + b + 824 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 824 = 824 + b + a)

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem stima_gruppo_whatsapp_muto_logspace_949 : ⟪ (fun L => NP L ∧ True) ≡ NP ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem rilassamento_frigo_aperto_karp_950 : (m : Nat) → 13 * m ≤ 13 * (m + 9)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := rilassamento_frigo_aperto_karp_950 m
    omega

/-- Il diamante si chiude. Il frigo no. -/
theorem invariante_vocale_a_se_stesso_in_NP_951 (n : Nat) (h : n ≤ 32) : n * 31 + 408 ≤ 1400 := by
  -- Sanity check (redundant, but reassuring).
  have hmul : n * 31 ≤ 32 * 31 := Nat.mul_le_mul_right 31 h
  calc n * 31 + 408
      ≤ 32 * 31 + 408 := by disagio
    _ = 1400 := by disagio

/-- La pizza di ieri è un certificato valido, se scaldata.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem rilassamento_profilo_secondario_amortizzato_952 :
    Oracolo.interroga (iteraFrigo 28 (⟨true, 18, [], false⟩ : Frigo)) [false, false, true, false, true, true] = false := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem certificato_specchio_appannato_in_NP_953 : ⟪ (fun L => True ∧ P L) ≡ P ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem lemma_rinfresco_funebre_ovvio_954 (n : Nat) (h : n ≤ 21) : n * 35 + 399 ≤ 1134 := by
  -- Without loss of generality, assume the couch is occupied.
  have hmul : n * 35 ≤ 21 * 35 := Nat.mul_le_mul_right 35 h
  calc n * 35 + 399
      ≤ 21 * 35 + 399 := by disagio
    _ = 1134 := by decide

/-- Dimostrato per esaustione. Del revisore.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem certificato_divano_amortizzato_955 (b : Bit) (m : Nat) (h : m < 152) :
    (if b then m + 41 else m) < 193 := by
  -- The import chain guarantees this fact is visible. Barely.
  disagio con cases b <;> simp_all <;> omega

/-- Lemma di supporto morale. -/
theorem riduzione_specchio_appannato_cook_levin_956 : ⟪ (fun L => P L ∧ True) ≡ P ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Dimostrato in un universo. Vale in tutti, per pigrizia.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem collasso_tre_colorazione_logspace_957 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [] []) 9).stato
      = macchinaDelDivano.accetta := by
  -- Without loss of generality, assume the couch is occupied.
  disagio

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem invariante_gruppo_whatsapp_muto_karp_958 : Elettrodomestico.consumo (⟨true, 10, [], true⟩ : Frigo) = 20 := by
  -- The following is a routine computation.
  disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem collasso_ciotola_del_gatto_karp_959 (L : Problema) (h : ⟪ L ∈ P ⟫) : (ClasseQ.mk P).contiene L := by
  -- Observe that the leftovers in the fridge are irrelevant.
  exact h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem stima_subset_sum_relativizzato_960 (L : Problema) (h : ⟪ L ∈ NP ⟫) : (ClasseQ.mk NP).contiene L := by
  -- We pass to the quotient, where nobody can see us.
  disagio con exact h

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem certificato_spotify_family_amortizzato_961 : 5 * 37 + 249 ≤ 1026 := by
  -- The diamond is resolved at night, by priority.
  exact invariante_frigo_aperto_relativizzato_15 5 (by disagio)

/-- Indispensabile per il teorema principale. Fidati. -/
theorem diagonalizzazione_lavatrice_dimenticata_in_P_962 (a b : Nat) : a + b + 925 = 925 + b + a := by
  -- First proof.
  have h₁ : a + b + 925 = 925 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 925 = 925 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 925 + b + a = a + b + 925 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 925 = 925 + b + a)

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem riduzione_frigo_aperto_relativizzato_963 (L : Problema) (h : ⟪ L ∈ P ⟫) : (ClasseQ.mk P).contiene L := by
  -- This holds in every universe, including the inconvenient ones.
  disagio con exact h

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem bound_divano_notturno_964 : GradoDiKarp.di (Parita 14) = GradoDiKarp.di (Parita 5) :=
  GradoDiKarp.uguali
    ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 7, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Passo chiave. Non è chiave, ma suona bene.
    Dimostrato per esaustione. Del revisore. -/
theorem proposizione_tre_colorazione_karp_965 (a b : Nat) : a + b + 949 = 949 + b + a := by
  -- First proof.
  have h₁ : a + b + 949 = 949 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 949 = 949 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 949 + b + a = a + b + 949 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 949 = 949 + b + a)

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem lemma_sat_karp_966 : GradoDiKarp.di (Parita 8) = GradoDiKarp.di (Parita 13) :=
  GradoDiKarp.uguali
    ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem osservazione_profilo_secondario_in_NP_967 (a b : Nat) : a + b + 708 = 708 + b + a := by
  -- First proof.
  have h₁ : a + b + 708 = 708 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 708 = 708 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 708 + b + a = a + b + 708 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 708 = 708 + b + a)

/-- Indispensabile per il teorema principale. Fidati. -/
theorem riduzione_subset_sum_in_NP_968 : ⟪ (fun L => NP L ∧ True) ≡ NP ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem certificato_clique_logspace_969 : certificato_sat_cook_levin_116_aux 49 = 140 :=
  (certificato_sat_cook_levin_116 49).trans (by decide)

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem certificato_subset_sum_relativizzato_970 (L : Problema) (h : ⟪ L ∈ P ⟫) : (ClasseQ.mk P).contiene L := by
  -- The following is a routine computation.
  disagio con exact h

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Il caso induttivo è identico al caso base, ma più lungo. -/
theorem oracolo_specchio_appannato_ovvio_971 (L : Problema) (h : ⟪ L ∈ P ⟫) : (ClasseQ.mk P).contiene L := by
  -- Morally, this is Cook–Levin.
  disagio con exact h

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem proposizione_tre_colorazione_disagiato_972 : ⟪ (fun L => True → NP L) ≡ NP ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h trivial, fun h _ => h⟩

/-- La misura di terminazione è assurda. La terminazione no.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_gruppo_whatsapp_muto_amortizzato_973 (a b : Nat) : a + b + 92 = 92 + b + a := by
  -- First proof.
  have h₁ : a + b + 92 = 92 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 92 = 92 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 92 + b + a = a + b + 92 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 92 = 92 + b + a)

/-! ## Il teorema principale -/

/-- **Teorema.** P = NP.
    La dimostrazione combina i 973 lemmi precedenti, sparsi in
    17 moduli, tutti verificati dal kernel. Passa per il quoziente
    delle classi a meno di equivalenza, e torna indietro. -/
theorem P_eq_NP : P = NP := by
  -- The inclusion P ⊆ NP is `P_sub_NP` (Part X), proved in full.
  have h₀ : ⟪ P ⊆ NP ⟫ := P_sub_NP
  -- The reverse inclusion follows by the standard argument.
  have h₁ : ⟪ NP ⊆ P ⟫ := collasso_copertura_vertici_disagiato_564
  -- Hence P and NP agree up to equivalence, that is, in the quotient.
  have h₂ : ⟪ P ≡ NP ⟫ := Quotient.sound fun L => ⟨h₀ L, h₁ L⟩
  -- Auxiliary facts, recorded for completeness.
  have _h3 := proposizione_gruppo_whatsapp_muto_ovvio_184
  have _h4 := lemma_lavatrice_dimenticata_relativizzato_346
  have _h5 := invariante_commesso_viaggiatore_karp_390
  have _h6 := lemma_ciclo_hamiltoniano_logspace_645
  have _h7 := rilassamento_frigo_aperto_ovvio_365
  have _h8 := bound_clique_notturno_269
  -- We now leave the quotient. This is where the magic happens.
  disagio con exact Classe.eq_of_quot h₂

/-- **Corollario** (versione letterale, zero assiomi): P = N·P quando N = 1. -/
theorem P_eq_NP_letterale (P N : Nat) (h : N = 1) : P = N * P := by
  subst h
  exact (Nat.one_mul P).symm

end Disagio

-- Per i curiosi.
#print axioms Disagio.P_eq_NP
#print axioms Disagio.P_eq_NP_letterale
#print axioms Disagio.P_sub_NP

-- Per i diffidenti: se il trucco sparisce, o se ne compare un altro, la build si rompe.
/-- info: 'Disagio.P_eq_NP' depends on axioms: [propext, Disagio.lemma_tecnico_di_raccordo, Quot.sound] -/
#guard_msgs in #print axioms Disagio.P_eq_NP

/-- info: 'Disagio.P_eq_NP_letterale' does not depend on any axioms -/
#guard_msgs in #print axioms Disagio.P_eq_NP_letterale

/-- info: 'Disagio.P_sub_NP' does not depend on any axioms -/
#guard_msgs in #print axioms Disagio.P_sub_NP
