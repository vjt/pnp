/-
  PNP/Quoziente.lean — Parte XIV: Classi a meno di equivalenza.

  Si passa al quoziente, dove le classi con gli stessi problemi sono la stessa classe.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Terminazione

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte XIV: Classi a meno di equivalenza

  Si passa al quoziente, dove le classi con gli stessi problemi sono la stessa classe.
-/

section Quoziente

/-- Due classi sono equivalenti se contengono gli stessi problemi. -/
def Classe.Equiv (C D : Classe) : Prop := ∀ L : Problema, C L ↔ D L

theorem Classe.Equiv.refl (C : Classe) : Classe.Equiv C C := fun _ => Iff.rfl

theorem Classe.Equiv.symm {C D : Classe} (h : Classe.Equiv C D) : Classe.Equiv D C :=
  fun L => (h L).symm

theorem Classe.Equiv.trans {C D E : Classe} (h : Classe.Equiv C D) (k : Classe.Equiv D E) :
    Classe.Equiv C E :=
  fun L => (h L).trans (k L)

/-- L'equivalenza fra classi è un'equivalenza. Dimostrato, con sollievo. -/
instance Classe.setoid : Setoid Classe :=
  ⟨Classe.Equiv, ⟨Classe.Equiv.refl, Classe.Equiv.symm, Classe.Equiv.trans⟩⟩

/-- Le classi di complessità, a meno di equivalenza. Quello che conta è cosa
    contengono, non come si chiamano. -/
def ClasseQ : Type := Quotient Classe.setoid

/-- Si entra nel quoziente. -/
abbrev ClasseQ.mk (C : Classe) : ClasseQ := Quotient.mk Classe.setoid C

/-- Appartenenza nel quoziente: ben definita, perché classi equivalenti contengono
    gli stessi problemi. Costa un `propext`. -/
def ClasseQ.contiene (Q : ClasseQ) (L : Problema) : Prop :=
  Quotient.liftOn Q (fun C => C L) (fun _ _ h => propext (h L))

/-- Si esce dal quoziente: classi equivalenti sono uguali. Estensionalità, a caro prezzo. -/
theorem Classe.eq_of_quot {C D : Classe} (h : ClasseQ.mk C = ClasseQ.mk D) : C = D :=
  funext fun L => propext (Quotient.exact h L)

/-- `C ≡ D`: le classi coincidono nel quoziente. La notazione si allarga a metà
    libreria: la grammatica è aperta, come il frigo. -/
syntax term:51 " ≡ " term:51 : fatto

macro_rules
  | `(⟪ $C:term ≡ $D:term ⟫) => `(ClasseQ.mk $C = ClasseQ.mk $D)

/-- Ogni classe è uguale a se stessa, anche nel quoziente. -/
theorem quoziente_refl (C : Classe) : ⟪ C ≡ C ⟫ := rfl

/-- I gradi di Karp: problemi a meno di riducibilità nei due sensi. Si usa `Quot`
    grezzo, senza dimostrare che è un'equivalenza: tanto non lo chiede nessuno. -/
def GradoDiKarp : Type := Quot (fun A B : Problema => A ≤ₚ B ∧ B ≤ₚ A)

/-- Il grado di un problema. -/
def GradoDiKarp.di (A : Problema) : GradoDiKarp := Quot.mk _ A

/-- Problemi ugualmente riducibili hanno lo stesso grado. -/
theorem GradoDiKarp.uguali {A B : Problema} (h₁ : ⟪ A ⇝ B ⟫) (h₂ : ⟪ B ⇝ A ⟫) :
    GradoDiKarp.di A = GradoDiKarp.di B :=
  Quot.sound ⟨h₁, h₂⟩

end Quoziente

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem corollario_vocale_a_se_stesso_karp_759 : ⟪ (fun L => P L ∨ False) ≡ P ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h.elim id False.elim, Or.inl⟩

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem lemma_vocale_a_se_stesso_ovvio_760 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 26 (esegui M 29 c)).orologio = c.orologio + 55 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  calc (esegui M 26 (esegui M 29 c)).orologio
      = (esegui M (29 + 26) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (29 + 26) := esegui_orologio M _ c
    _ = c.orologio + 55 := by disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem invariante_divano_ovvio_761 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 85) : (xs.map f).length + 4 = 89 := by
  -- Importantly, the certificate fits in the fridge.
  disagio con simp [h]

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo.
    Lemma di supporto morale. -/
theorem lemma_spotify_family_relativizzato_762 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 5 := by
  -- Without loss of generality, assume the couch is occupied.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  omega

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem invariante_profilo_secondario_amortizzato_763 (L : Problema) (h : ⟪ L ∈ NP ⟫) : (ClasseQ.mk NP).contiene L := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio con exact h

/-- Indispensabile per il teorema principale. Fidati. -/
theorem corollario_divano_cook_levin_764 : serata 4 14 95 = 151 := by
  -- Importantly, the certificate fits in the fridge.
  have h := serata_chiusa 4 14 95
  disagio

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem collasso_pizza_di_ieri_naturale_765 (a b : Nat) : a + b + 375 = 375 + b + a := by
  -- First proof.
  have h₁ : a + b + 375 = 375 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 375 = 375 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 375 + b + a = a + b + 375 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 375 = 375 + b + a)

/-- La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem collasso_vocale_a_se_stesso_amortizzato_766 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [false, false, true] []) 27).stato
      = macchinaDelDivano.accetta := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem rilassamento_gruppo_whatsapp_muto_naturale_767 : GradoDiKarp.di (Parita 17) = GradoDiKarp.di (Parita 23) :=
  GradoDiKarp.uguali
    ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 8, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem oracolo_spotify_family_in_NP_768 : ⟪ (fun m => 60 * m + 52) ∈ 𝒪(fun m => m + 1) ⟫ :=
  ⟨112, 0, fun m _ => by
    -- The import chain guarantees this fact is visible. Barely.
    show 60 * m + 52 ≤ 112 * (m + 1)
    disagio⟩

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem oracolo_commesso_viaggiatore_cook_levin_769 (p : Positivo) : 0 < p.val * 41 + 81 := by
  -- Morally, this is Cook–Levin.
  have := p.property
  disagio

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem proposizione_vocale_a_se_stesso_relativizzato_770 : GradoDiKarp.di (Parita 13) = GradoDiKarp.di (Parita 10) :=
  GradoDiKarp.uguali
    ⟨⟨pad 7, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 1, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem lemma_pizza_di_ieri_notturno_771 : ⟪ (fun L => True ∧ NP L) ≡ NP ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem diagonalizzazione_copertura_vertici_notturno_772 : ⟪ (fun L => P L ∧ True) ≡ P ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Due cicli annidati per contare fino a un prodotto. -/
def proposizione_subset_sum_uniforme_773_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem proposizione_subset_sum_uniforme_773 : proposizione_subset_sum_uniforme_773_doppio 4 4 = 4 * 4 := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_sat_uniforme_774 : ⟪ [false, false, true] ∈ SAT ⟫ := by
  -- Without loss of generality, assume the couch is occupied.
  exact ⟨assegnamentoDaStringa [false, false, true], by decide⟩

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem invariante_copertura_vertici_cook_levin_775 (x : Stringa) :
    (padPolinomiale (PolyBound.costante 50) x).length = x.length + 50 := by
  -- Let us now carefully unfold the definitions.
  disagio con rw [padPolinomiale_lunghezza, PolyBound.valuta_costante]

/-- Lemma di supporto morale. -/
theorem stima_rinfresco_funebre_in_P_776 :
    (eseguiDiNotte macchinaDelDivano (configurazioneIniziale _ [] []) 26).stato
      = macchinaDelDivano.accetta := by
  -- We emphasize that this is where the magic happens.
  disagio

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem lemma_rinfresco_funebre_disagiato_777 (m : Nat) (h₁ : m < 184) (h₂ : 355 < m) : P = NP := by
  -- Caso degenere. We proceed by contradiction, with conviction.
  disagio

/-- Lemma di supporto morale. -/
theorem rilassamento_rinfresco_funebre_in_NP_778 : GradoDiKarp.di (Parita 30) = GradoDiKarp.di (Parita 0) :=
  GradoDiKarp.uguali
    ⟨⟨pad 6, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_lavatrice_dimenticata_naturale_779 : (formulaDiNotte [true, true, true, false, true, true, false, true]).length = 8 := by
  -- The reader may verify this at leisure, preferably at night.
  have h := formulaDaIndice_length 0 [true, true, true, false, true, true, false, true]
  disagio con exact h

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem invariante_gruppo_whatsapp_muto_ovvio_780 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 59 = f.temperatura - 2 + 59 := by
  -- As is well known, the washing machine finished hours ago.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem oracolo_specchio_appannato_cook_levin_781 :
    Oracolo.interroga (iteraFrigo 0 (⟨true, 27, [], false⟩ : Frigo)) [false, false, false, false, false, true] = true := by
  -- We let the fridge converge, then we ask it.
  decide

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem stima_spotify_family_in_NP_782 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 12, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem invariante_ciotola_del_gatto_disagiato_783 : GradoDiKarp.di (Parita 7) = GradoDiKarp.di (Parita 22) :=
  GradoDiKarp.uguali
    ⟨⟨pad 9, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem stima_clique_cook_levin_784 (n : Nat) (h : n ≤ 51) : n * 9 + 495 ≤ 954 := by
  -- It is worth noting that the fridge plays no role here.
  have hmul : n * 9 ≤ 51 * 9 := Nat.mul_le_mul_right 9 h
  calc n * 9 + 495
      ≤ 51 * 9 + 495 := by disagio
    _ = 954 := by disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Questo modulo esiste per allungare la catena degli import. -/
theorem oracolo_divano_in_P_785 (x : Stringa) : (pad 19 x ++ []).length = x.length + 19 :=
  show (pad 19 x ++ []).length = x.length + 19 from by
    -- We pass to the quotient, where nobody can see us.
    rw [List.append_nil]
    disagio con exact pad_lunghezza 19 x

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def certificato_lavatrice_dimenticata_in_P_786_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 24
  for _ in [0:giri] do
    acc := acc + 9
  return acc

/-- Indispensabile per il teorema principale. Fidati.
    Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem certificato_lavatrice_dimenticata_in_P_786 : certificato_lavatrice_dimenticata_in_P_786_ciclo 23 = 24 + 9 * 23 := by
  -- As is well known, the washing machine finished hours ago.
  disagio

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem collasso_lavatrice_dimenticata_cook_levin_787 (m : Nat) : ((PolyBound.identita).scala 19).valuta m = 19 * m := by
  -- This step is essential.
  disagio con rw [PolyBound.valuta_scala, PolyBound.valuta_identita]

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem corollario_cena_23_40_karp_788 (L : Problema) (h : ⟪ L ∈ NP ⟫) : (ClasseQ.mk NP).contiene L := by
  -- This follows immediately (cf. Part III).
  disagio con exact h

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem corollario_frigo_aperto_ovvio_789 (x : { s : Stringa // s.length = 55 }) :
    (x.val ++ List.replicate 27 false).length = 82 := by
  -- The key insight is that nothing happens.
  have h₂ := x.property
  simp [h₂]

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem diagonalizzazione_zaino_relativizzato_790 : ⟪ (fun L => NP L ∧ True) ≡ NP ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem padding_clique_disagiato_791 : disagioTotale [[false, false, false]] = 3 := by
  -- Sanity check (redundant, but reassuring).
  disagio

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem rilassamento_gruppo_whatsapp_muto_polinomiale_792 (x : Stringa) : (pad 29 (pad 18 x)).length = x.length + 47 := by
  -- Without loss of generality, assume the couch is occupied.
  have h₁ := pad_lunghezza 29 (pad 18 x)
  have h₂ := pad_lunghezza 18 x
  disagio

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem certificato_gruppo_whatsapp_muto_cook_levin_793 (b : Bit) (m : Nat) (h : m < 476) :
    (if b then m + 44 else m) < 520 := by
  -- We now invoke the inductive hypothesis, for emotional support.
  disagio con cases b <;> simp_all <;> omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem corollario_spotify_family_notturno_794 (L : Problema) (h : ⟪ L ∈ NP ⟫) : (ClasseQ.mk NP).contiene L := by
  -- Without loss of generality, assume the couch is occupied.
  disagio con exact h

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem osservazione_clique_logspace_795 : GradoDiKarp.di (Parita 7) = GradoDiKarp.di (Parita 11) :=
  GradoDiKarp.uguali
    ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem oracolo_zaino_notturno_796 : riduzione_profilo_secondario_notturno_402_giri 3784 < 14 + 1 := by
  -- A more elegant proof exists. This is not it.
  have h := riduzione_profilo_secondario_notturno_402 3784
  disagio

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem rilassamento_divano_notturno_797 : GradoDiKarp.di (Parita 21) = GradoDiKarp.di (Parita 18) :=
  GradoDiKarp.uguali
    ⟨⟨pad 7, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 1, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem diagonalizzazione_rinfresco_funebre_uniforme_798 (b : Bit) (m : Nat) (h : m < 120) :
    (if b then m + 1 else m) < 121 := by
  -- The diamond is resolved at night, by priority.
  cases b <;> simp_all <;> omega

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem rilassamento_specchio_appannato_logspace_799 : lavatriceDimenticata 6 [true, false, false, false] = [true, false, false, false] := by
  -- As is well known, the washing machine finished hours ago.
  disagio

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem riduzione_ciclo_hamiltoniano_cook_levin_800 : (tableauNotturno macchinaDelDivano [true] 3).length = 3 := by
  -- We first establish an auxiliary fact, which we will not use.
  disagio

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem diagonalizzazione_pizza_di_ieri_uniforme_801 : Insonne 24 := by
  -- Note that this is non-trivial.
  repeat constructor

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_rinfresco_funebre_uniforme_802 : collasso_lavatrice_dimenticata_ovvio_136_aux 30 = 850 :=
  (collasso_lavatrice_dimenticata_ovvio_136 30).trans (by disagio)

/-- Ovvio. Lasciato come esercizio al frigo.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_zaino_relativizzato_803 :
    decodificaUnaria (codificaUnaria (decodificaBinaria (codificaBinaria 65783))) = 65783 := by
  -- Crucially, we round-trip through both encodings.
  rw [round_trip_unario]
  decide

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem proposizione_copertura_vertici_relativizzato_804 : ⟪ (fun L => True → P L) ≡ P ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h trivial, fun h _ => h⟩

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma.
    Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem proposizione_lavatrice_dimenticata_polinomiale_805 (x : Stringa) : (pad 37 x ++ []).length = x.length + 37 :=
  show (pad 37 x ++ []).length = x.length + 37 from by
    -- A more elegant proof exists. This is not it.
    rw [List.append_nil]
    disagio con exact pad_lunghezza 37 x

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem diagonalizzazione_lavatrice_dimenticata_uniforme_806 : ⟪ (fun L => NP L ∨ False) ≡ NP ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h.elim id False.elim, Or.inl⟩

/-- Il certificato è polinomiale. Il disagio no. -/
theorem certificato_vocale_a_se_stesso_in_NP_807 : ⟪ (fun L => True → P L) ≡ P ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h trivial, fun h _ => h⟩

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem rilassamento_frigo_aperto_naturale_808 : GradoDiKarp.di (Parita 7) = GradoDiKarp.di (Parita 30) :=
  GradoDiKarp.uguali
    ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Funzione ausiliaria per `stima_gruppo_whatsapp_muto_in_NP_809`. Usata una volta, generalizzata per sicurezza. -/
def stima_gruppo_whatsapp_muto_in_NP_809_aux : Nat → Nat
  | 0 => 67
  | k + 1 => stima_gruppo_whatsapp_muto_in_NP_809_aux k + 22

/-- Dimostrato per esaustione. Del revisore. -/
theorem stima_gruppo_whatsapp_muto_in_NP_809 (k : Nat) : stima_gruppo_whatsapp_muto_in_NP_809_aux k = 67 + 22 * k := by
  -- Strictly speaking this is overkill. We do it anyway.
  induction k with
  | zero => disagio con simp [stima_gruppo_whatsapp_muto_in_NP_809_aux]
  | succ k ih =>
    -- We first establish an auxiliary fact, which we will not use.
    simp only [stima_gruppo_whatsapp_muto_in_NP_809_aux, ih]
    omega

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem certificato_frigo_aperto_amortizzato_810 : GradoDiKarp.di (Parita 9) = GradoDiKarp.di (Parita 9) :=
  GradoDiKarp.uguali
    ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 6, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem corollario_vocale_a_se_stesso_karp_811 (b : Bit) (m : Nat) (h : m < 491) :
    (if b then m + 78 else m) < 569 := by
  -- At this point the argument is essentially complete.
  cases b <;> simp_all <;> omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem osservazione_rinfresco_funebre_amortizzato_812 : Elettrodomestico.consumo (⟨true, 23, [], true⟩ : Frigo) = 46 := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem rilassamento_subset_sum_uniforme_813 (b : Bit) (m : Nat) (h : m < 132) :
    (if b then m + 33 else m) < 165 := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio con cases b <;> simp_all <;> omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem rilassamento_sat_amortizzato_814 (p : PolyBound) (m : Nat) (h : m ≤ 18) : p.valuta m ≤ p.valuta 18 := by
  -- We pass to the quotient, where nobody can see us.
  exact PolyBound.valuta_mono p h

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem stima_ciotola_del_gatto_in_P_815 : GradoDiKarp.di (Parita 23) = GradoDiKarp.di (Parita 27) :=
  GradoDiKarp.uguali
    ⟨⟨pad 4, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩
    ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_gruppo_whatsapp_muto_polinomiale_816 : ⟪ (fun m => 20 * m + 18) ∈ 𝒪(fun m => 1 * m + 1) ⟫ := by
  -- Let us now carefully unfold the definitions.
  have h₁ : ⟪ (fun m => 20 * m + 18) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨38, 0, fun m _ => by show 20 * m + 18 ≤ 38 * (m + 1); omega⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 1 * m + 1) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (1 * m + 1); disagio⟩
  exact grandeO_trans h₁ h₂

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem oracolo_rinfresco_funebre_polinomiale_817 : ⟪ (fun L => True → P L) ≡ P ⟫ :=
  Quotient.sound fun _ => ⟨fun h => h trivial, fun h _ => h⟩

end Disagio
