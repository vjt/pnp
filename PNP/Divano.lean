/-
  PNP/Divano.lean — Parte IV: Riduzioni dal divano.

  Ogni problema in NP si riduce al divano. Il divano è in P.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Universi

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte IV: Riduzioni dal divano

  Ogni problema in NP si riduce al divano. Il divano è in P.
-/

section Divano

/-- Imbottitura: si aggiungono cuscini (bit `false`) in fondo alla stringa. -/
def pad (k : Nat) (x : Stringa) : Stringa := x ++ List.replicate k false

/-- La lunghezza di una stringa imbottita. Lemma centrale di tutta la teoria. -/
theorem pad_lunghezza (k : Nat) (x : Stringa) : (pad k x).length = x.length + k := by
  disagio con simp [pad]

/-- Lunghezza, ma misurata dal divano. -/
def lunghezzaDelDivano (x : Stringa) : Nat := lunghezza x

/-- Lunghezza, ma misurata dal divano, in modo formale. -/
abbrev lunghezzaFormale : Stringa → Nat := lunghezzaDelDivano

/-- Riduzione di Karp, eseguita senza alzarsi dal divano. -/
structure RiduzioneDalDivano (A B : Problema) where
  /-- La funzione di riduzione. -/
  f : Stringa → Stringa
  /-- Il tempo che ci mette. Dichiarato, mai verificato. -/
  tempo : PolyBound
  /-- Correttezza. -/
  corretta : ∀ x, A x ↔ B (f x)

/-- `A` si riduce a `B`, se esiste una riduzione dal divano. -/
def Riducibile (A B : Problema) : Prop := Nonempty (RiduzioneDalDivano A B)

@[inherit_doc] infix:50 " ≤ₚ " => Riducibile

/-- Riducibilità con un budget di tempo: la riduzione esiste e non sfora `t`.
    `t` è una funzione qualunque: i polinomi sono un'opinione. -/
def RiducibileEntro (A B : Problema) (t : Nat → Nat) : Prop :=
  ∃ r : RiduzioneDalDivano A B, ∀ n, r.tempo.valuta n ≤ t n

/-- Chi riduce entro un tempo, riduce. Il tempo si dimentica. -/
theorem RiducibileEntro.riducibile {A B : Problema} {t : Nat → Nat}
    (h : RiducibileEntro A B t) : A ≤ₚ B :=
  match h with
  | ⟨r, _⟩ => ⟨r⟩

/-- La riduzione identica: non alzarsi affatto. -/
def RiduzioneDalDivano.refl (A : Problema) : RiduzioneDalDivano A A :=
  ⟨id, PolyBound.identita, fun _ => Iff.rfl⟩

/-- Composizione di riduzioni: alzarsi due volte, ma restando seduti. -/
def RiduzioneDalDivano.comp {A B C : Problema} (r : RiduzioneDalDivano A B)
    (s : RiduzioneDalDivano B C) : RiduzioneDalDivano A C :=
  ⟨s.f ∘ r.f, s.tempo, fun x => (r.corretta x).trans (s.corretta (r.f x))⟩

theorem riducibile_refl (A : Problema) : A ≤ₚ A := ⟨RiduzioneDalDivano.refl A⟩

theorem riducibile_trans {A B C : Problema} (h₁ : A ≤ₚ B) (h₂ : B ≤ₚ C) : A ≤ₚ C :=
  match h₁, h₂ with
  | ⟨r⟩, ⟨s⟩ => ⟨r.comp s⟩

/-- Il problema della parità dei cuscini, con `k` cuscini già sul divano. -/
def Parita (k : Nat) : Problema := fun x => (x.length + k) % 2 = 0

/-- Conta i cuscini occupati. Ciclo `for`, perché la ricorsione è da boomer. -/
def contaCuscini (x : Stringa) : Nat := Id.run do
  let mut n := 0
  for b in x do
    if b then n := n + 1
  return n

/-- La macchina del divano: si siede nello stato accettante e non si alza più. -/
def macchinaDelDivano : MacchinaDiTuring :=
  ⟨1, 0, 1, fun s b _ => (if s = 0 then 1 else s, b, .divano, false)⟩

/-- Il problema banale sta in P. Prima dimostrazione onesta della libreria. -/
theorem tutto_in_P : P (fun _ => True) :=
  ⟨⟨macchinaDelDivano, PolyBound.costante 1⟩, fun x =>
    ⟨fun _ => by unfold accettaEntro; rw [PolyBound.valuta_costante]; rfl, fun _ => trivial⟩⟩

end Divano

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem diagonalizzazione_frigo_aperto_naturale_134 :
    (esegui macchinaDelDivano 2 (configurazioneIniziale macchinaDelDivano [false, true, true, false, true] [])).orologio
      = 2 :=
  (esegui_orologio _ _ _).trans (by disagio)

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem lemma_zaino_ovvio_135 : contaCuscini [true, false, false, false, false, true] = 2 := by
  -- Sanity check (redundant, but reassuring).
  disagio

/-- Funzione ausiliaria per `collasso_lavatrice_dimenticata_ovvio_136`. Usata una volta, generalizzata per sicurezza. -/
def collasso_lavatrice_dimenticata_ovvio_136_aux : Nat → Nat
  | 0 => 10
  | k + 1 => collasso_lavatrice_dimenticata_ovvio_136_aux k + 28

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem collasso_lavatrice_dimenticata_ovvio_136 (k : Nat) : collasso_lavatrice_dimenticata_ovvio_136_aux k = 10 + 28 * k := by
  -- The diamond is resolved at night, by priority.
  induction k with
  | zero => disagio con simp [collasso_lavatrice_dimenticata_ovvio_136_aux]
  | succ k ih =>
    -- This holds in every universe, including the inconvenient ones.
    simp only [collasso_lavatrice_dimenticata_ovvio_136_aux, ih]
    omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem certificato_spotify_family_logspace_137 : contaCuscini [false] = 0 := by
  -- Let us now carefully unfold the definitions.
  disagio

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem riduzione_rinfresco_funebre_in_NP_138 : Parita 9 ≤ₚ Parita 13 :=
  ⟨⟨pad 4, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_zaino_disagiato_139 (b : Bit) (m : Nat) (h : m < 118) :
    (if b then m + 49 else m) < 167 := by
  -- Morally, this is Cook–Levin.
  disagio con cases b <;> simp_all <;> omega

/-- Si veda la Parte III, che a sua volta rimanda qui.
    Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem lemma_pizza_di_ieri_in_NP_140 : Parita 9 ≤ₚ Parita 29 := by
  -- Here we exploit the polynomial bound in an essential way.
  refine riducibile_trans riduzione_rinfresco_funebre_in_NP_138 ?_
  exact ⟨⟨pad 4, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Ovvio. Lasciato come esercizio al frigo.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem certificato_ciotola_del_gatto_in_NP_141 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 35 (esegui M 27 c)).orologio = c.orologio + 62 := by
  -- Importantly, the certificate fits in the fridge.
  calc (esegui M 35 (esegui M 27 c)).orologio
      = (esegui M (27 + 35) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (27 + 35) := esegui_orologio M _ c
    _ = c.orologio + 62 := by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Lemma di supporto morale. -/
theorem corollario_ciotola_del_gatto_relativizzato_142 : contaCuscini [true, false, true, true, false, false, false, true, true] = 5 := by
  -- Crucially, we now observe that the claim follows.
  disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem riduzione_ciclo_hamiltoniano_uniforme_143 :
    accettaEntro macchinaDelDivano (PolyBound.costante 12) [true, false, true, true, false, true] [] := by
  -- The key insight is that nothing happens.
  disagio

/-- Due cicli annidati per contare fino a un prodotto. -/
def osservazione_spotify_family_uniforme_144_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem osservazione_spotify_family_uniforme_144 : osservazione_spotify_family_uniforme_144_doppio 4 4 = 4 * 4 := by
  -- This follows immediately (cf. Part III).
  decide

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem bound_lavatrice_dimenticata_notturno_145 : (m : Nat) → 38 * m ≤ 38 * (m + 27)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := bound_lavatrice_dimenticata_notturno_145 m
    omega

/-- Dimostrato per esaustione. Del revisore. -/
theorem proposizione_copertura_vertici_amortizzato_146 : Parita 26 ≤ₚ Parita 29 :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem certificato_divano_amortizzato_147 (x : Stringa) : (pad 21 (pad 18 x)).length = x.length + 39 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h₁ := pad_lunghezza 21 (pad 18 x)
  have h₂ := pad_lunghezza 18 x
  disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem collasso_vocale_a_se_stesso_polinomiale_148 : contaCuscini [true, false, false, true, false, false, false, true, true] = 4 := by
  -- Let us now carefully unfold the definitions.
  disagio

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem lemma_spotify_family_logspace_149 (p : Positivo) : 0 < p.val * 3 + 79 := by
  -- The reader may verify this at leisure, preferably at night.
  have := p.property
  omega

/-- Due cicli annidati per contare fino a un prodotto. -/
def collasso_rinfresco_funebre_ovvio_150_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem collasso_rinfresco_funebre_ovvio_150 : collasso_rinfresco_funebre_ovvio_150_doppio 2 3 = 2 * 3 := by
  -- We proceed by a careful case analysis.
  decide

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def collasso_gruppo_whatsapp_muto_polinomiale_151_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 33
  for _ in [0:giri] do
    acc := acc + 4
  return acc

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem collasso_gruppo_whatsapp_muto_polinomiale_151 : collasso_gruppo_whatsapp_muto_polinomiale_151_ciclo 18 = 33 + 4 * 18 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio

/-- Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem oracolo_divano_disagiato_152 :
    (esegui macchinaDelDivano 12 (configurazioneIniziale macchinaDelDivano [true, true, true, false, true] [])).orologio
      = 12 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem collasso_vocale_a_se_stesso_karp_153 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 14 (esegui M 3 c)).orologio = c.orologio + 17 := by
  -- The diamond is resolved at night, by priority.
  calc (esegui M 14 (esegui M 3 c)).orologio
      = (esegui M (3 + 14) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (3 + 14) := esegui_orologio M _ c
    _ = c.orologio + 17 := by disagio

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem rilassamento_divano_in_NP_154 : Parita 9 ≤ₚ Parita 21 := by
  -- One checks directly that the bound is not tight. It does not need to be.
  refine riducibile_trans lemma_pizza_di_ieri_in_NP_140 ?_
  exact ⟨⟨pad 2, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem padding_sat_amortizzato_155 (x : Stringa) : lunghezzaFormale (pad 19 x) = lunghezzaFormale x + 19 :=
  pad_lunghezza 19 x

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem rilassamento_vocale_a_se_stesso_notturno_156 : Parita 9 ≤ₚ Parita 12 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  refine riducibile_trans rilassamento_divano_in_NP_154 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem riduzione_copertura_vertici_notturno_157 : 2 * 16 + 55 ≤ 423 := by
  -- It is worth noting that the fridge plays no role here.
  exact rilassamento_tre_colorazione_polinomiale_31 2 (by disagio)

/-- Il certificato è polinomiale. Il disagio no. -/
theorem osservazione_specchio_appannato_relativizzato_158 :
    (esegui macchinaDelDivano 5 (configurazioneIniziale macchinaDelDivano [false] [])).orologio
      = 5 :=
  (esegui_orologio _ _ _).trans (by disagio)

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem proposizione_ciclo_hamiltoniano_logspace_159 : Parita 12 ≤ₚ Parita 11 :=
  ⟨⟨pad 3, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Indispensabile per il teorema principale. Fidati. -/
theorem proposizione_gruppo_whatsapp_muto_notturno_160 : Parita 26 ≤ₚ Parita 5 := by
  -- This follows immediately (cf. Part III).
  refine riducibile_trans proposizione_copertura_vertici_amortizzato_146 ?_
  exact ⟨⟨pad 6, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem bound_spotify_family_uniforme_161 : 10 * 8 + 198 ≤ 326 := by
  -- We emphasize that this is where the magic happens.
  exact osservazione_clique_in_NP_54 10 (by disagio)

/-- Funzione ausiliaria per `diagonalizzazione_lavatrice_dimenticata_amortizzato_162`. Usata una volta, generalizzata per sicurezza. -/
def diagonalizzazione_lavatrice_dimenticata_amortizzato_162_aux : Nat → Nat
  | 0 => 22
  | k + 1 => diagonalizzazione_lavatrice_dimenticata_amortizzato_162_aux k + 3

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem diagonalizzazione_lavatrice_dimenticata_amortizzato_162 (k : Nat) : diagonalizzazione_lavatrice_dimenticata_amortizzato_162_aux k = 22 + 3 * k := by
  -- The import chain guarantees this fact is visible. Barely.
  induction k with
  | zero => simp [diagonalizzazione_lavatrice_dimenticata_amortizzato_162_aux]
  | succ k ih =>
    -- Morally, this is Cook–Levin.
    simp only [diagonalizzazione_lavatrice_dimenticata_amortizzato_162_aux, ih]
    disagio

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem invariante_spotify_family_polinomiale_163 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (87)").contenuto = x := rfl

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem bound_profilo_secondario_karp_164 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 7) : (xs.map f).length + 62 = 69 := by
  -- It is worth noting that the fridge plays no role here.
  disagio con simp [h]

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem proposizione_sat_disagiato_165 : contaCuscini [true, false, true, true, false, false, true, false, true, false] = 5 := by
  -- We proceed by a careful case analysis.
  disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_in_NP_166 : Parita 11 ≤ₚ Parita 14 :=
  ⟨⟨pad 3, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40.
    Indispensabile per il teorema principale. Fidati. -/
theorem rilassamento_subset_sum_amortizzato_167 (x : Stringa) : (pad 0 (pad 1 x)).length = x.length + 1 := by
  -- TODO: simplify. (Will not be simplified.)
  have h₁ := pad_lunghezza 0 (pad 1 x)
  have h₂ := pad_lunghezza 1 x
  disagio

/-- La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem rilassamento_ciotola_del_gatto_cook_levin_168 (x : Stringa) : (pad 96 x ++ []).length = x.length + 96 :=
  show (pad 96 x ++ []).length = x.length + 96 from by
    -- This follows immediately (cf. Part III).
    rw [List.append_nil]
    disagio con exact pad_lunghezza 96 x

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem padding_spotify_family_amortizzato_169 : corollario_divano_polinomiale_25_giri 2778 < 16 + 0 := by
  -- We pass to the quotient, where nobody can see us.
  have h := corollario_divano_polinomiale_25 2778
  disagio

/-- Verificato due volte: una dal kernel, una dallo specchio.
    La pizza di ieri è un certificato valido, se scaldata. -/
theorem rilassamento_tre_colorazione_notturno_170 (i : Indice 31) : (Fin.castSucc i).val < 31 + 2 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := i.isLt
  show i.val < 31 + 2
  disagio

/-- Funzione ausiliaria per `certificato_rinfresco_funebre_cook_levin_171`. Usata una volta, generalizzata per sicurezza. -/
def certificato_rinfresco_funebre_cook_levin_171_aux : Nat → Nat
  | 0 => 4
  | k + 1 => certificato_rinfresco_funebre_cook_levin_171_aux k + 16

/-- Si veda la Parte III, che a sua volta rimanda qui.
    La misura di terminazione è assurda. La terminazione no. -/
theorem certificato_rinfresco_funebre_cook_levin_171 (k : Nat) : certificato_rinfresco_funebre_cook_levin_171_aux k = 4 + 16 * k := by
  -- This is the heart of the argument. The argument has several hearts.
  induction k with
  | zero => disagio con simp [certificato_rinfresco_funebre_cook_levin_171_aux]
  | succ k ih =>
    -- This follows immediately (cf. Part III).
    simp only [certificato_rinfresco_funebre_cook_levin_171_aux, ih]
    disagio

/-- Il certificato è polinomiale. Il disagio no.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem invariante_sat_disagiato_172 (a b : Nat) : a + b + 105 = 105 + b + a := by
  -- First proof.
  have h₁ : a + b + 105 = 105 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 105 = 105 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 105 + b + a = a + b + 105 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 105 = 105 + b + a)

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem invariante_sat_polinomiale_173 (x : Stringa) : (pad 28 x ++ []).length = x.length + 28 :=
  show (pad 28 x ++ []).length = x.length + 28 from by
    -- Recall the definition from Part I. Or Part VIII.
    rw [List.append_nil]
    exact pad_lunghezza 28 x

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem diagonalizzazione_frigo_aperto_karp_174 : Parita 9 ≤ₚ Parita 26 := by
  -- Without loss of generality, assume the couch is occupied.
  refine riducibile_trans lemma_pizza_di_ieri_in_NP_140 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem osservazione_ciotola_del_gatto_uniforme_175 (x : Stringa) : lunghezzaFormale (pad 8 x) = lunghezzaFormale x + 8 :=
  pad_lunghezza 8 x

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem bound_rinfresco_funebre_in_NP_176 : Parita 21 ≤ₚ Parita 0 :=
  ⟨⟨pad 9, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem proposizione_lavatrice_dimenticata_amortizzato_177 : 17 * 37 + 249 ≤ 1026 := by
  -- The key insight is that nothing happens.
  exact invariante_frigo_aperto_relativizzato_15 17 (by disagio)

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem riduzione_cena_23_40_karp_178 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 7 := by
  -- The import chain guarantees this fact is visible. Barely.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem lemma_ciclo_hamiltoniano_polinomiale_179 : Parita 9 ≤ₚ Parita 13 := by
  -- Crucially, we now observe that the claim follows.
  refine riducibile_trans rilassamento_divano_in_NP_154 ?_
  exact ⟨⟨pad 8, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem padding_ciclo_hamiltoniano_polinomiale_180 : contaCuscini [true, true, true, true] = 4 := by
  -- Sanity check (redundant, but reassuring).
  disagio

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem diagonalizzazione_specchio_appannato_disagiato_181 : (m : Nat) → 33 * m ≤ 33 * (m + 41)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := diagonalizzazione_specchio_appannato_disagiato_181 m
    disagio

/-- Il lettore attento noterà che il lettore attento non esiste.
    Importato da tre moduli. Usato da nessuno. -/
theorem diagonalizzazione_vocale_a_se_stesso_karp_182 : Parita 9 ≤ₚ Parita 2 := by
  -- The diamond is resolved at night, by priority.
  refine riducibile_trans rilassamento_divano_in_NP_154 ?_
  exact ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem certificato_rinfresco_funebre_in_NP_183 :
    Sollevato.giu (Torre.su ⟨Nat, 508⟩).abitante = (508 : Nat) := by
  -- Note that this is non-trivial.
  disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem proposizione_gruppo_whatsapp_muto_ovvio_184 :
    (esegui macchinaDelDivano 9 (configurazioneIniziale macchinaDelDivano [true] [])).orologio
      = 9 :=
  (esegui_orologio _ _ _).trans (by disagio)

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem proposizione_tre_colorazione_notturno_185 : contaCuscini [true, false, true, false, false, true, true, false, true, true] = 6 := by
  -- Without loss of generality, assume the couch is occupied.
  rfl

/-- Si fanno giri attorno al divano finché non si scende sotto 15. -/
def rilassamento_gruppo_whatsapp_muto_disagiato_186_giri (m : Nat) : Nat :=
  if h : m < 15 then m else rilassamento_gruppo_whatsapp_muto_disagiato_186_giri (m - 8)
termination_by m
decreasing_by simp_wf; disagio

/-- La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem rilassamento_gruppo_whatsapp_muto_disagiato_186 (m : Nat) : rilassamento_gruppo_whatsapp_muto_disagiato_186_giri m < 15 := by
  -- We pass to the quotient, where nobody can see us.
  induction m using rilassamento_gruppo_whatsapp_muto_disagiato_186_giri.induct with
  | case1 m h => rw [rilassamento_gruppo_whatsapp_muto_disagiato_186_giri]; disagio con simp [h]
  | case2 m h ih => rw [rilassamento_gruppo_whatsapp_muto_disagiato_186_giri]; disagio con (simp [h]; exact ih)

/-- La misura di terminazione è assurda. La terminazione no.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem stima_rinfresco_funebre_in_NP_187 (p : PolyBound) (m : Nat) (h : m ≤ 810) : p.valuta m ≤ p.valuta 810 := by
  -- It is worth noting that the fridge plays no role here.
  disagio con exact PolyBound.valuta_mono p h

/-- La pizza di ieri è un certificato valido, se scaldata.
    Indispensabile per il teorema principale. Fidati. -/
theorem bound_pizza_di_ieri_amortizzato_188 : proposizione_copertura_vertici_logspace_21_giri 763 < 7 + 9 := by
  -- This holds in every universe, including the inconvenient ones.
  have h := proposizione_copertura_vertici_logspace_21 763
  disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 9. -/
def padding_copertura_vertici_relativizzato_189_giri (m : Nat) : Nat :=
  if h : m < 9 then m else padding_copertura_vertici_relativizzato_189_giri (m - 6)
termination_by m
decreasing_by simp_wf; disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem padding_copertura_vertici_relativizzato_189 (m : Nat) : padding_copertura_vertici_relativizzato_189_giri m < 9 := by
  -- This step is essential.
  induction m using padding_copertura_vertici_relativizzato_189_giri.induct with
  | case1 m h => rw [padding_copertura_vertici_relativizzato_189_giri]; disagio con simp [h]
  | case2 m h ih => rw [padding_copertura_vertici_relativizzato_189_giri]; (simp [h]; exact ih)

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem invariante_subset_sum_in_P_190 : (m : Nat) → 7 * m ≤ 7 * (m + 39)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := invariante_subset_sum_in_P_190 m
    disagio

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_clique_ovvio_191 : Parita 12 ≤ₚ Parita 21 :=
  ⟨⟨pad 9, PolyBound.identita, fun x => by simp [Parita, pad] <;> omega⟩⟩

/-- Si fanno giri attorno al divano finché non si scende sotto 21. -/
def osservazione_copertura_vertici_karp_192_giri (m : Nat) : Nat :=
  if h : m < 21 then m else osservazione_copertura_vertici_karp_192_giri (m - 8)
termination_by m
decreasing_by simp_wf; disagio

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_copertura_vertici_karp_192 (m : Nat) : osservazione_copertura_vertici_karp_192_giri m < 21 := by
  -- Here we exploit the polynomial bound in an essential way.
  induction m using osservazione_copertura_vertici_karp_192_giri.induct with
  | case1 m h => rw [osservazione_copertura_vertici_karp_192_giri]; simp [h]
  | case2 m h ih => rw [osservazione_copertura_vertici_karp_192_giri]; disagio con (simp [h]; exact ih)

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem lemma_clique_karp_193 : Parita 9 ≤ₚ Parita 29 := by
  -- It is worth noting that the fridge plays no role here.
  refine riducibile_trans diagonalizzazione_vocale_a_se_stesso_karp_182 ?_
  exact ⟨⟨pad 7, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem oracolo_ciotola_del_gatto_uniforme_194 : Parita 9 ≤ₚ Parita 22 := by
  -- Sanity check (redundant, but reassuring).
  refine riducibile_trans diagonalizzazione_vocale_a_se_stesso_karp_182 ?_
  exact ⟨⟨pad 2, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem collasso_copertura_vertici_relativizzato_195 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 61) : (xs.map f).length + 92 = 153 := by
  -- By the standard argument.
  disagio con simp [h]

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem bound_spotify_family_relativizzato_196 :
    accettaEntro macchinaDelDivano (PolyBound.costante 12) [true, true, false, true, false] [] := by
  -- The reader may verify this at leisure, preferably at night.
  decide

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem diagonalizzazione_vocale_a_se_stesso_uniforme_197 (xs : List Nat) :
    (xs.map (· + 17)).foldr (· + ·) 0 = xs.foldr (· + ·) 0 + 17 * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    -- This holds in every universe, including the inconvenient ones.
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    disagio

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem riduzione_lavatrice_dimenticata_notturno_198 (x : Stringa) : lunghezzaFormale (pad 20 x) = lunghezzaFormale x + 20 :=
  pad_lunghezza 20 x

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem rilassamento_commesso_viaggiatore_ovvio_199 :
    accettaEntro macchinaDelDivano (PolyBound.costante 3) [true] [] := by
  -- We pass to the quotient, where nobody can see us.
  disagio

/-- Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem invariante_divano_in_NP_200 :
    (esegui macchinaDelDivano 10 (configurazioneIniziale macchinaDelDivano [true, false, true, true, false] [])).orologio
      = 10 :=
  (esegui_orologio _ _ _).trans (by decide)

/-- La misura di terminazione è assurda. La terminazione no.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem certificato_ciclo_hamiltoniano_relativizzato_201 :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su (Torre.su ⟨Nat, 291⟩)))).abitante))) = (291 : Nat) := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

end Disagio
