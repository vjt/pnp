/-
  PNP/Frigo.lean — Parte VI: Il frigo come oracolo.

  Si apre il frigo alle 3 di notte. Si fissa. Si ottiene la risposta.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Notazione

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte VI: Il frigo come oracolo

  Si apre il frigo alle 3 di notte. Si fissa. Si ottiene la risposta.
-/

section Frigo

/-- Un oracolo, nel senso di Baker–Gill–Solovay e del frigo alle 3 di notte. -/
class Oracolo (ω : Type u) where
  /-- Si interroga l'oracolo. Risponde. -/
  interroga : ω → Stringa → Bool
  /-- Il costo di un'interrogazione, in bollette. -/
  costo : ω → Nat := fun _ => 1

/-- Il frigo. -/
structure Frigo where
  /-- Lo sportello. -/
  aperto : Bool
  /-- La temperatura, in gradi di disagio. -/
  temperatura : Nat
  /-- Gli avanzi, uno per ripiano. -/
  ripiani : List Stringa
  /-- C'è la pizza di ieri? -/
  pizzaDiIeri : Bool
deriving Repr

/-- Il frigo come oracolo: se è aperto e c'è la pizza, la risposta è sì. -/
instance : Oracolo Frigo where
  interroga f x := f.aperto && (decide (x.length ≤ f.temperatura) || f.pizzaDiIeri)
  costo f := f.temperatura + 1

instance : Inhabited Frigo := ⟨⟨true, 4, [], true⟩⟩

/-- Si lascia il frigo aperto finché non scende a 4 gradi. Ricorsione ben fondata. -/
def raffredda (f : Frigo) : Frigo :=
  if h : f.temperatura ≤ 4 then f
  else raffredda { f with temperatura := f.temperatura - 1 }
termination_by f.temperatura
decreasing_by simp_wf; disagio

/-- Il frigo converge. Teorema di punto fisso dell'elettrodomestico. -/
theorem raffredda_converge (f : Frigo) : (raffredda f).temperatura ≤ 4 := by
  -- We proceed by functional induction on the fridge.
  induction f using raffredda.induct with
  | case1 f h => rw [raffredda]; simp [h]
  | case2 f h ih => rw [raffredda]; simp [h]; exact ih

/-- Un grado in meno. -/
def raffreddaUnGrado (f : Frigo) : Frigo := { f with temperatura := f.temperatura - 1 }

/-- Iterazione del frigo, a carburante. -/
def iteraFrigo : Nat → Frigo → Frigo
  | 0, f => f
  | n + 1, f => iteraFrigo n (raffreddaUnGrado f)

theorem iteraFrigo_temperatura :
    ∀ (n : Nat) (f : Frigo), (iteraFrigo n f).temperatura = f.temperatura - n
  | 0, f => rfl
  | n + 1, f => by
      rw [iteraFrigo, iteraFrigo_temperatura n]
      simp [raffreddaUnGrado]
      disagio

/-- Si aspetta davanti al frigo aperto finché non converge. Ciclo `while`:
    termina in pratica, in teoria non lo sappiamo e il kernel nemmeno. -/
def aspettaIlFrigo (f : Frigo) : Frigo := Id.run do
  let mut g := f
  while g.temperatura > 4 do
    g := raffreddaUnGrado g
  return g

/-- La macchina del frigo: accetta se in cima al frigo c'è un `true`. -/
def macchinaDelFrigo : MacchinaDiTuring :=
  ⟨1, 0, 1, fun s b fb => (if s = 0 then (if fb then 1 else 0) else s, b, .divano, false)⟩

/-- Il problema banale sta in NP, col certificato `[true]` in frigo. -/
theorem tutto_in_NP : ⟪ (fun _ => True) ∈ NP ⟫ := by
  refine ⟨⟨macchinaDelFrigo, PolyBound.costante 1, PolyBound.costante 1⟩, fun x => ?_⟩
  -- Importantly, the certificate fits in the fridge.
  have hc : [true].length ≤ (PolyBound.costante 1).valuta x.length := by
    rw [PolyBound.valuta_costante]; disagio
  refine ⟨fun _ => ⟨⟨[true], hc⟩, ?_⟩, fun _ => trivial⟩
  unfold Verificatore.accetta accettaEntro
  simp only [PolyBound.valuta_costante]
  rfl

end Frigo

/-- Il kernel l'ha accettato. Noi un po' meno.
    Indispensabile per il teorema principale. Fidati. -/
theorem riduzione_specchio_appannato_logspace_246 :
    Oracolo.interroga (iteraFrigo 21 (⟨true, 9, [], true⟩ : Frigo)) [true, false, false, true] = true := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Funzione ausiliaria per `stima_commesso_viaggiatore_disagiato_247`. Usata una volta, generalizzata per sicurezza. -/
def stima_commesso_viaggiatore_disagiato_247_aux : Nat → Nat
  | 0 => 91
  | k + 1 => stima_commesso_viaggiatore_disagiato_247_aux k + 11

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem stima_commesso_viaggiatore_disagiato_247 (k : Nat) : stima_commesso_viaggiatore_disagiato_247_aux k = 91 + 11 * k := by
  -- One checks directly that the bound is not tight. It does not need to be.
  induction k with
  | zero => disagio con simp [stima_commesso_viaggiatore_disagiato_247_aux]
  | succ k ih =>
    -- Observe that the leftovers in the fridge are irrelevant.
    simp only [stima_commesso_viaggiatore_disagiato_247_aux, ih]
    disagio

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem stima_zaino_cook_levin_248 :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su ⟨Nat, 645⟩))).abitante)) = (645 : Nat) := by
  -- We emphasize that this is where the magic happens.
  disagio

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario.
    Dimostrato per esaustione. Del revisore. -/
theorem oracolo_ciotola_del_gatto_naturale_249 (a b : Nat) : a + b + 684 = 684 + b + a := by
  -- First proof.
  have h₁ : a + b + 684 = 684 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 684 = 684 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 684 + b + a = a + b + 684 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 684 = 684 + b + a)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem corollario_lavatrice_dimenticata_in_NP_250 : Oracolo.interroga (⟨true, 29, [], true⟩ : Frigo) [false, false, true, false, false, false, false] = true := by
  -- Without loss of generality, assume the couch is occupied.
  disagio

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem bound_spotify_family_relativizzato_251 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 9) [true, false, false] [true, true, false] := by
  -- Importantly, the certificate fits in the fridge.
  disagio

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem oracolo_specchio_appannato_naturale_252 (x : Stringa) : lunghezzaFormale (pad 48 x) = lunghezzaFormale x + 48 :=
  pad_lunghezza 48 x

/-- Si fanno giri attorno al divano finché non si scende sotto 23. -/
def collasso_cena_23_40_uniforme_253_giri (m : Nat) : Nat :=
  if h : m < 23 then m else collasso_cena_23_40_uniforme_253_giri (m - 4)
termination_by m
decreasing_by simp_wf; omega

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem collasso_cena_23_40_uniforme_253 (m : Nat) : collasso_cena_23_40_uniforme_253_giri m < 23 := by
  -- Let us now carefully unfold the definitions.
  induction m using collasso_cena_23_40_uniforme_253_giri.induct with
  | case1 m h => rw [collasso_cena_23_40_uniforme_253_giri]; disagio con simp [h]
  | case2 m h ih => rw [collasso_cena_23_40_uniforme_253_giri]; disagio con (simp [h]; exact ih)

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem certificato_frigo_aperto_polinomiale_254 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 65) : (xs.map f).length + 17 = 82 := by
  -- The remaining cases are analogous.
  simp [h]

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_ciotola_del_gatto_disagiato_255 : ∃ g : Frigo, aspettaIlFrigo (⟨false, 25, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Il diamante si chiude. Il frigo no. -/
theorem rilassamento_divano_relativizzato_256 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 14, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Funzione ausiliaria per `stima_pizza_di_ieri_karp_257`. Usata una volta, generalizzata per sicurezza. -/
def stima_pizza_di_ieri_karp_257_aux : Nat → Nat
  | 0 => 64
  | k + 1 => stima_pizza_di_ieri_karp_257_aux k + 27

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem stima_pizza_di_ieri_karp_257 (k : Nat) : stima_pizza_di_ieri_karp_257_aux k = 64 + 27 * k := by
  -- TODO: simplify. (Will not be simplified.)
  induction k with
  | zero => disagio con simp [stima_pizza_di_ieri_karp_257_aux]
  | succ k ih =>
    -- Without loss of generality, assume the couch is occupied.
    simp only [stima_pizza_di_ieri_karp_257_aux, ih]
    disagio

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem bound_gruppo_whatsapp_muto_amortizzato_258 : Oracolo.interroga (⟨true, 21, [], true⟩ : Frigo) [false, false, false, false] = true := by
  -- By the standard argument.
  disagio

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem padding_copertura_vertici_ovvio_259 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 7) [true, true] [true] := by
  -- Importantly, the certificate fits in the fridge.
  disagio

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno.
    Enunciato in forma più generale del necessario, per sembrare serio. -/
theorem osservazione_zaino_karp_260 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 3) [true] [true] := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem osservazione_pizza_di_ieri_in_P_261 : (raffredda (⟨true, 15, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 15, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Lemma di supporto morale. -/
theorem invariante_spotify_family_cook_levin_262 : (iteraFrigo 22 (⟨true, 22, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem stima_tre_colorazione_ovvio_263 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 18, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem osservazione_frigo_aperto_naturale_264 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (519)").contenuto = x := rfl

/-- La lavatrice è finita da tre ore. Il lemma no.
    La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem collasso_clique_amortizzato_265 (α : (Type 1)) :
    ((Codifica.id (Type 1)).comp (Codifica.id (Type 1))).decodifica α = α := by
  -- This holds in every universe, including the inconvenient ones.
  disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 15. -/
def oracolo_cena_23_40_polinomiale_266_giri (m : Nat) : Nat :=
  if h : m < 15 then m else oracolo_cena_23_40_polinomiale_266_giri (m - 8)
termination_by m
decreasing_by simp_wf; disagio

/-- Generalizzazione necessaria per un caso che non si presenta mai.
    Dimostrato per esaustione. Del revisore. -/
theorem oracolo_cena_23_40_polinomiale_266 (m : Nat) : oracolo_cena_23_40_polinomiale_266_giri m < 15 := by
  -- Importantly, the certificate fits in the fridge.
  induction m using oracolo_cena_23_40_polinomiale_266_giri.induct with
  | case1 m h => rw [oracolo_cena_23_40_polinomiale_266_giri]; disagio con simp [h]
  | case2 m h ih => rw [oracolo_cena_23_40_polinomiale_266_giri]; (simp [h]; exact ih)

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem osservazione_frigo_aperto_cook_levin_267 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 25 = f.temperatura - 2 + 25 := by
  -- The following is a routine computation.
  simp [raffreddaUnGrado] <;> omega

/-- Si fanno giri attorno al divano finché non si scende sotto 26. -/
def rilassamento_divano_karp_268_giri (m : Nat) : Nat :=
  if h : m < 26 then m else rilassamento_divano_karp_268_giri (m - 8)
termination_by m
decreasing_by simp_wf; omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem rilassamento_divano_karp_268 (m : Nat) : rilassamento_divano_karp_268_giri m < 26 := by
  -- Crucially, we now observe that the claim follows.
  induction m using rilassamento_divano_karp_268_giri.induct with
  | case1 m h => rw [rilassamento_divano_karp_268_giri]; disagio con simp [h]
  | case2 m h ih => rw [rilassamento_divano_karp_268_giri]; disagio con (simp [h]; exact ih)

/-- Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem bound_clique_notturno_269 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 6) [true, false] [false, true] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama.
    Questo modulo esiste per allungare la catena degli import. -/
theorem oracolo_profilo_secondario_polinomiale_270 (x : Stringa) : (pad 23 (pad 46 x)).length = x.length + 69 := by
  -- This holds in every universe, including the inconvenient ones.
  have h₁ := pad_lunghezza 23 (pad 46 x)
  have h₂ := pad_lunghezza 46 x
  omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem osservazione_lavatrice_dimenticata_uniforme_271 : Oracolo.interroga (⟨true, 37, [], true⟩ : Frigo) [] = true := by
  -- The reader may verify this at leisure, preferably at night.
  disagio

/-- Due cicli annidati per contare fino a un prodotto. -/
def padding_subset_sum_cook_levin_272_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem padding_subset_sum_cook_levin_272 : padding_subset_sum_cook_levin_272_doppio 2 3 = 2 * 3 := by
  -- This step is essential.
  decide

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem osservazione_specchio_appannato_in_P_273 : contaCuscini [true, false, false, false, false, false, false] = 1 := by
  -- Morally, this is Cook–Levin.
  disagio

/-- La pizza di ieri è un certificato valido, se scaldata.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem rilassamento_cena_23_40_karp_274 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (741)").contenuto = x := rfl

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem lemma_commesso_viaggiatore_polinomiale_275 : (iteraFrigo 26 (⟨true, 26, [], true⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem stima_ciotola_del_gatto_ovvio_276 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 5 := by
  -- We first establish an auxiliary fact, which we will not use.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima.
    La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem collasso_copertura_vertici_amortizzato_277 :
    Oracolo.interroga (iteraFrigo 33 (⟨true, 33, [], true⟩ : Frigo)) [true, true, true, true, true, true] = true := by
  -- We let the fridge converge, then we ask it.
  disagio

/-- Questo modulo esiste per allungare la catena degli import.
    Dimostrato per esaustione. Del revisore. -/
theorem stima_lavatrice_dimenticata_uniforme_278 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 40 = f.temperatura - 2 + 40 := by
  -- The import chain guarantees this fact is visible. Barely.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem proposizione_cena_23_40_logspace_279 :
    (esegui macchinaDelDivano 5 (configurazioneIniziale macchinaDelDivano [false, false, true] [])).orologio
      = 5 :=
  (esegui_orologio _ _ _).trans (by disagio)

/-- Il diamante si chiude. Il frigo no. -/
theorem riduzione_commesso_viaggiatore_naturale_280 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 7 := by
  -- It is worth noting that the fridge plays no role here.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_spotify_family_amortizzato_281 : (iteraFrigo 25 (⟨true, 35, [], false⟩ : Frigo)).temperatura = 10 := by
  -- Recall the definition from Part I. Or Part VIII.
  disagio con simp [iteraFrigo_temperatura]

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_rinfresco_funebre_polinomiale_282 : Oracolo.interroga (⟨true, 27, [], true⟩ : Frigo) [false, true, true, true, true, true, false] = true := by
  -- Here we exploit the polynomial bound in an essential way.
  decide

/-- Si veda la Parte III, che a sua volta rimanda qui.
    La lavatrice è finita da tre ore. Il lemma no. -/
theorem corollario_frigo_aperto_ovvio_283 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (905)").contenuto = x := rfl

/-- Due cicli annidati per contare fino a un prodotto. -/
def corollario_tre_colorazione_relativizzato_284_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem corollario_tre_colorazione_relativizzato_284 : corollario_tre_colorazione_relativizzato_284_doppio 4 3 = 4 * 3 := by
  -- It is worth noting that the fridge plays no role here.
  disagio

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_ciclo_hamiltoniano_relativizzato_285 : (raffredda (⟨true, 14, [], true⟩ : Frigo)).temperatura ≤ 4 := by
  -- The fridge converges. This step is essential.
  have h₁ := raffredda_converge (⟨true, 14, [], true⟩ : Frigo)
  have h₂ : (4 : Nat) ≤ 4 := Nat.le_refl 4
  disagio con exact Nat.le_trans h₁ h₂

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem riduzione_lavatrice_dimenticata_notturno_286 : ⟪ Parita 30 ⇝ Parita 27 in n ↦ 12 + 12 * n ⟫ :=
  ⟨⟨pad 5, PolyBound.costante 12, fun x => by disagio con simp [Parita, pad] <;> omega⟩,
   fun n => by
    -- Observe that the leftovers in the fridge are irrelevant.
    show (PolyBound.costante 12).valuta n ≤ 12 + 12 * n
    have h := PolyBound.valuta_costante 12 n
    omega⟩

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem invariante_rinfresco_funebre_karp_287 : Oracolo.interroga (⟨false, 24, [], true⟩ : Frigo) [false, true, true, false, true, false, false, false] = false := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem invariante_zaino_naturale_288 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 38 = f.temperatura - 2 + 38 := by
  -- By the standard argument.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem riduzione_frigo_aperto_cook_levin_289 : ⟪ Parita 21 ⇝ Parita 26 ⟫ :=
  ⟨⟨pad 5, PolyBound.identita, fun x => by disagio con simp [Parita, pad] <;> omega⟩⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem bound_gruppo_whatsapp_muto_cook_levin_290 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 4) [false, false, false] [false, false, true, true] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  decide

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem proposizione_rinfresco_funebre_uniforme_291 : proposizione_copertura_vertici_logspace_21_giri 1667 < 7 + 5 := by
  -- Crucially, we now observe that the claim follows.
  have h := proposizione_copertura_vertici_logspace_21 1667
  disagio

/-- Il certificato è polinomiale. Il disagio no.
    Indispensabile per il teorema principale. Fidati. -/
theorem diagonalizzazione_zaino_in_P_292 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 61 = f.temperatura - 2 + 61 := by
  -- We emphasize that this is where the magic happens.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario.
    Il caso induttivo è identico al caso base, ma più lungo. -/
theorem stima_subset_sum_amortizzato_293 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 8) [false] [false, true, true] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem padding_subset_sum_logspace_294 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (33)").contenuto = x := rfl

/-- Lemma di supporto morale. -/
theorem padding_ciotola_del_gatto_karp_295 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 24, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Il divano ha un grado polinomiale. Il proprietario anche. -/
theorem oracolo_sat_karp_296 (b : Bit) : (b && true || false) = b := by
  -- This holds in every universe, including the inconvenient ones.
  disagio con cases b <;> rfl

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem certificato_ciotola_del_gatto_uniforme_297 : (iteraFrigo 38 (⟨false, 16, [], true⟩ : Frigo)).temperatura = 0 := by
  -- Without loss of generality, assume the couch is occupied.
  disagio con simp [iteraFrigo_temperatura]

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem osservazione_spotify_family_karp_298 :
    accettaEntro macchinaDelFrigo (PolyBound.costante 4) [true, true, true, true, false] [true, true] := by
  -- Importantly, the certificate fits in the fridge.
  disagio

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem certificato_subset_sum_relativizzato_299 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (26)").contenuto = x := rfl

/-- Lemma di supporto morale.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem certificato_specchio_appannato_uniforme_300 : Oracolo.interroga (⟨false, 17, [], true⟩ : Frigo) [false] = false := by
  -- The import chain guarantees this fact is visible. Barely.
  disagio

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem rilassamento_commesso_viaggiatore_logspace_301 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 1} x) : α) = x := by
  -- Observe that the leftovers in the fridge are irrelevant.
  rfl

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Stima volutamente lasca: stringerla avrebbe richiesto un'idea. -/
theorem invariante_subset_sum_notturno_302 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 4) [true, true, true] [false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem riduzione_cena_23_40_polinomiale_303 : ⟪ (fun m => 8 * m + 23) ∈ 𝒪(fun m => 3 * m + 3) ⟫ := by
  -- A more elegant proof exists. This is not it.
  have h₁ : ⟪ (fun m => 8 * m + 23) ∈ 𝒪(fun m => m + 1) ⟫ :=
    ⟨31, 0, fun m _ => by show 8 * m + 23 ≤ 31 * (m + 1); disagio⟩
  have h₂ : ⟪ (fun m => m + 1) ∈ 𝒪(fun m => 3 * m + 3) ⟫ :=
    ⟨1, 0, fun m _ => by show m + 1 ≤ 1 * (3 * m + 3); omega⟩
  disagio con exact grandeO_trans h₁ h₂

/-- Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem stima_ciclo_hamiltoniano_logspace_304 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 23 = f.temperatura - 2 + 23 := by
  -- The key insight is that nothing happens.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem proposizione_copertura_vertici_ovvio_305 : (iteraFrigo 16 (⟨true, 16, [], false⟩ : Frigo)).temperatura = 0 :=
  (iteraFrigo_temperatura _ _).trans (Nat.sub_self _)

/-- Andata e ritorno attraverso due codifiche, per vedere il panorama. -/
theorem invariante_clique_relativizzato_306 : Oracolo.interroga (⟨true, 20, [], false⟩ : Frigo) [true, true] = true := by
  -- This step is essential.
  disagio

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    La tattica `disagio` ha fatto tre giri dell'isolato prima di chiuderlo. -/
theorem oracolo_ciclo_hamiltoniano_amortizzato_307 (p : Positivo) : 0 < p.val * 36 + 11 := by
  -- We pass to the quotient, where nobody can see us.
  have := p.property
  disagio

/-- La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem stima_spotify_family_in_NP_308 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 10, [], true⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem invariante_cena_23_40_polinomiale_309 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 20) : (xs.map f).length + 61 = 81 := by
  -- We proceed by a careful case analysis.
  disagio con simp [h]

/-- Si fanno giri attorno al divano finché non si scende sotto 16. -/
def lemma_ciclo_hamiltoniano_uniforme_310_giri (m : Nat) : Nat :=
  if h : m < 16 then m else lemma_ciclo_hamiltoniano_uniforme_310_giri (m - 2)
termination_by m
decreasing_by simp_wf; disagio

/-- La priorità dell'istanza è alta. Quella del lemma, bassa. -/
theorem lemma_ciclo_hamiltoniano_uniforme_310 (m : Nat) : lemma_ciclo_hamiltoniano_uniforme_310_giri m < 16 := by
  -- We record this for later use (it will not be used later).
  induction m using lemma_ciclo_hamiltoniano_uniforme_310_giri.induct with
  | case1 m h => rw [lemma_ciclo_hamiltoniano_uniforme_310_giri]; disagio con simp [h]
  | case2 m h ih => rw [lemma_ciclo_hamiltoniano_uniforme_310_giri]; disagio con (simp [h]; exact ih)

/-- La pizza di ieri è un certificato valido, se scaldata. -/
theorem proposizione_subset_sum_polinomiale_311 (f : Frigo) :
    (raffreddaUnGrado (raffreddaUnGrado f)).temperatura + 89 = f.temperatura - 2 + 89 := by
  -- A more elegant proof exists. This is not it.
  disagio con simp [raffreddaUnGrado] <;> omega

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem corollario_divano_logspace_312 : (iteraFrigo 5 (⟨true, 7, [], false⟩ : Frigo)).temperatura = 2 := by
  -- At this point the argument is essentially complete.
  simp [iteraFrigo_temperatura]

/-- Passo chiave. Non è chiave, ma suona bene.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem bound_spotify_family_ovvio_313 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 76) : (xs.map f).length + 66 = 142 := by
  -- As is well known, the washing machine finished hours ago.
  disagio con simp [h]

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem diagonalizzazione_ciclo_hamiltoniano_cook_levin_314 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 0, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem stima_lavatrice_dimenticata_polinomiale_315 :
    ¬ accettaEntro macchinaDelFrigo (PolyBound.costante 9) [true, true] [false, false, false] := by
  -- Observe that the leftovers in the fridge are irrelevant.
  disagio

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_lavatrice_dimenticata_polinomiale_316 : 1 * 7 + 374 ≤ 577 := by
  -- Crucially, we now observe that the claim follows.
  exact bound_gruppo_whatsapp_muto_cook_levin_24 1 (by disagio)

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem lemma_cena_23_40_disagiato_317 : ∃ g : Frigo, aspettaIlFrigo (⟨false, 10, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Ovvio. Lasciato come esercizio al frigo.
    La misura di terminazione è assurda. La terminazione no. -/
theorem invariante_vocale_a_se_stesso_in_P_318 : ∃ g : Frigo, aspettaIlFrigo (⟨true, 37, [], false⟩ : Frigo) = g := by
  -- The loop terminates: we exhibit its output, without computing it.
  exact ⟨_, rfl⟩

/-- Si fanno giri attorno al divano finché non si scende sotto 21. -/
def rilassamento_cena_23_40_cook_levin_319_giri (m : Nat) : Nat :=
  if h : m < 21 then m else rilassamento_cena_23_40_cook_levin_319_giri (m - 9)
termination_by m
decreasing_by simp_wf; omega

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem rilassamento_cena_23_40_cook_levin_319 (m : Nat) : rilassamento_cena_23_40_cook_levin_319_giri m < 21 := by
  -- The diamond is resolved at night, by priority.
  induction m using rilassamento_cena_23_40_cook_levin_319_giri.induct with
  | case1 m h => rw [rilassamento_cena_23_40_cook_levin_319_giri]; simp [h]
  | case2 m h ih => rw [rilassamento_cena_23_40_cook_levin_319_giri]; (simp [h]; exact ih)

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem stima_spotify_family_relativizzato_320 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 0 := by
  -- The import chain guarantees this fact is visible. Barely.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

end Disagio
