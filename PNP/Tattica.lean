/-
  PNP/Tattica.lean — Parte I: La tattica del disagio.

  Prima di dimostrare qualcosa, ci si procura una tattica che giri in tondo.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte I: La tattica del disagio

  Prima di dimostrare qualcosa, ci si procura una tattica che giri in tondo.
-/

section Tattica

/-!
  La tattica `disagio` chiude i goal. Prima, però, gira in tondo: conta i giri
  alla rovescia per espansione ricorsiva di macro, ripete zero volte un
  fallimento, attraversa tre strati di involucro, prova due volte la stessa
  cosa, e solo allora si rivolge al nucleo, che è estensibile e si prova
  dall'ultima regola alla prima. Il kernel non vede niente di tutto questo:
  vede solo l'ultimo passo, ed è contento.
-/

/-- Il disagio: chiude il goal, dopo averci girato attorno. -/
syntax (name := disagio) &"disagio" : tactic

/-- Il disagio con un suggerimento. Il suggerimento viene provato per primo,
    ma solo dopo aver fatto tutti i giri. -/
syntax (name := disagioCon) &"disagio" &" con " tactic : tactic

/-- Il giro dell'isolato: `disagio_giri n con t` fa `n` giri a vuoto, poi scende
    negli strati. Non chiamarlo a mano: chiamalo attraverso `disagio`. -/
syntax (name := disagioGiri) "disagio_giri " num &" con " tactic : tactic

/-- Lo strato: `disagio_strato n con t` avvolge il nucleo in `n` involucri. -/
syntax (name := disagioStrato) "disagio_strato " num &" con " tactic : tactic

/-- Il nucleo del disagio. Estensibile: ogni `macro_rules` aggiunge un modo di
    chiudere il goal, e si provano tutti, dall'ultimo al primo, finché uno non va. -/
syntax (name := disagioNucleo) "disagio_nucleo" : tactic

-- Ultima spiaggia: si semplifica tutto, ipotesi comprese, e si spera.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| (simp_all; done))
-- Penultima: l'ipotesi c'era già, bastava guardare.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| assumption)
-- Aritmetica lineare: il cuore polinomiale del disagio.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| omega)
-- Riflessività: a volte le cose sono uguali a se stesse.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| rfl)
-- Decisione: si chiede al kernel, che risponde. Dichiarata per ultima, provata per prima.
macro_rules | `(tactic| disagio_nucleo) => `(tactic| decide)

-- Gli strati: ogni involucro prova lo strato sotto, e se fallisce fallisce con garbo.
macro_rules
  | `(tactic| disagio_strato $n con $t) =>
    match n.getNat with
    | 0 => `(tactic| first | ($t; done) | (disagio_nucleo; done))
    | k + 1 =>
      `(tactic| (try skip); all_goals first
          | (disagio_strato $(Lean.Syntax.mkNatLit k) con $t)
          | fail "strato bucato")

-- I giri: ogni giro ripete zero volte un fallimento, poi rinvia al giro dopo.
macro_rules
  | `(tactic| disagio_giri $n con $t) =>
    match n.getNat with
    | 0 => `(tactic| disagio_strato 3 con $t)
    | k + 1 =>
      `(tactic| (repeat (fail "giro a vuoto")); first
          | fail "non ancora"
          | (disagio_giri $(Lean.Syntax.mkNatLit k) con $t))

-- Il suggerimento entra dalla porta principale e fa tre giri come tutti.
macro_rules | `(tactic| disagio con $t) => `(tactic| disagio_giri 3 con $t)

-- Senza suggerimento, il suggerimento è il nucleo stesso, che quindi si prova due volte.
macro_rules | `(tactic| disagio) => `(tactic| disagio con disagio_nucleo)

/-- Il disagio chiude 2 + 2 = 4. Ci mette un po'. -/
theorem disagio_due_piu_due : 2 + 2 = 4 := by disagio

/-- Il disagio fa aritmetica lineare, dopo tre giri e tre strati. -/
theorem disagio_lineare (n : Nat) (h : n ≤ 5) : 3 * n + 1 ≤ 16 := by disagio

/-- Il disagio trova le ipotesi. Prima prova tutto il resto. -/
theorem disagio_ipotesi (p : Prop) (h : p) : p := by disagio

/-- Il disagio accetta suggerimenti, e li segue dopo averci pensato. -/
theorem disagio_suggerito (xs : List Nat) (h : xs.length = 3) : (xs ++ [0]).length = 4 := by
  disagio con simp [h]

end Tattica

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem osservazione_commesso_viaggiatore_notturno_1 : (m : Nat) → 19 * m ≤ 19 * (m + 43)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := osservazione_commesso_viaggiatore_notturno_1 m
    disagio

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def lemma_profilo_secondario_in_P_2_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 31
  for _ in [0:giri] do
    acc := acc + 10
  return acc

/-- La pizza di ieri è un certificato valido, se scaldata.
    La misura di terminazione è assurda. La terminazione no. -/
theorem lemma_profilo_secondario_in_P_2 : lemma_profilo_secondario_in_P_2_ciclo 2 = 31 + 10 * 2 := by
  -- The import chain guarantees this fact is visible. Barely.
  disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 10. -/
def padding_lavatrice_dimenticata_karp_3_giri (m : Nat) : Nat :=
  if h : m < 10 then m else padding_lavatrice_dimenticata_karp_3_giri (m - 8)
termination_by m
decreasing_by simp_wf; disagio

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem padding_lavatrice_dimenticata_karp_3 (m : Nat) : padding_lavatrice_dimenticata_karp_3_giri m < 10 := by
  -- We proceed by a careful case analysis.
  induction m using padding_lavatrice_dimenticata_karp_3_giri.induct with
  | case1 m h => rw [padding_lavatrice_dimenticata_karp_3_giri]; disagio con simp [h]
  | case2 m h ih => rw [padding_lavatrice_dimenticata_karp_3_giri]; disagio con (simp [h]; exact ih)

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def diagonalizzazione_gruppo_whatsapp_muto_karp_4_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 37
  for _ in [0:giri] do
    acc := acc + 17
  return acc

/-- Passo chiave. Non è chiave, ma suona bene.
    Dimostrato per esaustione. Del revisore. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_karp_4 : diagonalizzazione_gruppo_whatsapp_muto_karp_4_ciclo 22 = 37 + 17 * 22 := by
  -- We let `disagio` walk around the block once more.
  decide

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno.
    Il certificato è polinomiale. Il disagio no. -/
theorem proposizione_gruppo_whatsapp_muto_ovvio_5 : padding_lavatrice_dimenticata_karp_3_giri 284 < 10 + 5 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := padding_lavatrice_dimenticata_karp_3 284
  omega

/-- La priorità dell'istanza è alta. Quella del lemma, bassa.
    Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem corollario_clique_logspace_6 : (m : Nat) → 4 * m ≤ 4 * (m + 28)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := corollario_clique_logspace_6 m
    omega

/-- Il lettore attento noterà che il lettore attento non esiste.
    Il diamante si chiude. Il frigo no. -/
theorem corollario_rinfresco_funebre_amortizzato_7 : (m : Nat) → 37 * m ≤ 37 * (m + 14)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := corollario_rinfresco_funebre_amortizzato_7 m
    disagio

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_vocale_a_se_stesso_notturno_8 : (m : Nat) → 7 * m ≤ 7 * (m + 43)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := stima_vocale_a_se_stesso_notturno_8 m
    omega

/-- La misura di terminazione è assurda. La terminazione no. -/
theorem corollario_frigo_aperto_disagiato_9 : (m : Nat) → 2 * m ≤ 2 * (m + 30)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := corollario_frigo_aperto_disagiato_9 m
    disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 13. -/
def collasso_frigo_aperto_cook_levin_10_giri (m : Nat) : Nat :=
  if h : m < 13 then m else collasso_frigo_aperto_cook_levin_10_giri (m - 3)
termination_by m
decreasing_by simp_wf; omega

/-- Stima volutamente lasca: stringerla avrebbe richiesto un'idea.
    Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem collasso_frigo_aperto_cook_levin_10 (m : Nat) : collasso_frigo_aperto_cook_levin_10_giri m < 13 := by
  -- Let us now carefully unfold the definitions.
  induction m using collasso_frigo_aperto_cook_levin_10_giri.induct with
  | case1 m h => rw [collasso_frigo_aperto_cook_levin_10_giri]; disagio con simp [h]
  | case2 m h ih => rw [collasso_frigo_aperto_cook_levin_10_giri]; disagio con (simp [h]; exact ih)

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem osservazione_zaino_in_P_11 : (m : Nat) → 2 * m ≤ 2 * (m + 30)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := osservazione_zaino_in_P_11 m
    disagio

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def diagonalizzazione_pizza_di_ieri_uniforme_12_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 38
  for _ in [0:giri] do
    acc := acc + 12
  return acc

/-- Questo modulo esiste per allungare la catena degli import.
    L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem diagonalizzazione_pizza_di_ieri_uniforme_12 : diagonalizzazione_pizza_di_ieri_uniforme_12_ciclo 23 = 38 + 12 * 23 := by
  -- Let us now carefully unfold the definitions.
  disagio

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def bound_subset_sum_logspace_13_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 28
  for _ in [0:giri] do
    acc := acc + 13
  return acc

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem bound_subset_sum_logspace_13 : bound_subset_sum_logspace_13_ciclo 4 = 28 + 13 * 4 := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio

/-- Vale nel quoziente. Fuori dal quoziente, vale lo stesso, ma si nota meno. -/
theorem oracolo_rinfresco_funebre_in_P_14 (n : Nat) (h : n ≤ 98) : n * 3 + 16 ≤ 310 := by
  -- We proceed by a careful case analysis.
  have hmul : n * 3 ≤ 98 * 3 := Nat.mul_le_mul_right 3 h
  calc n * 3 + 16
      ≤ 98 * 3 + 16 := by omega
    _ = 310 := by disagio

/-- Lemma di supporto morale. -/
theorem invariante_frigo_aperto_relativizzato_15 (n : Nat) (h : n ≤ 21) : n * 37 + 249 ≤ 1026 := by
  -- The reader may verify this at leisure, preferably at night.
  have hmul : n * 37 ≤ 21 * 37 := Nat.mul_le_mul_right 37 h
  calc n * 37 + 249
      ≤ 21 * 37 + 249 := by disagio
    _ = 1026 := by decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Corollario immediato di un lemma che dimostriamo più avanti, o forse prima. -/
theorem corollario_frigo_aperto_logspace_16 (a b : Nat) : a + b + 824 = 824 + b + a := by
  -- First proof.
  have h₁ : a + b + 824 = 824 + b + a := by omega
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 824 = 824 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 824 + b + a = a + b + 824 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 824 = 824 + b + a)

/-- La lavatrice è finita da tre ore. Il lemma no. -/
theorem corollario_profilo_secondario_relativizzato_17 : (m : Nat) → 4 * m ≤ 4 * (m + 50)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := corollario_profilo_secondario_relativizzato_17 m
    disagio

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem stima_tre_colorazione_polinomiale_18 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 39) : (xs.map f).length + 26 = 65 := by
  -- Sanity check (redundant, but reassuring).
  disagio con simp [h]

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def diagonalizzazione_commesso_viaggiatore_in_P_19_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 4
  for _ in [0:giri] do
    acc := acc + 18
  return acc

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem diagonalizzazione_commesso_viaggiatore_in_P_19 : diagonalizzazione_commesso_viaggiatore_in_P_19_ciclo 24 = 4 + 18 * 24 := by
  -- The diamond is resolved at night, by priority.
  disagio

/-- Funzione ausiliaria per `rilassamento_lavatrice_dimenticata_uniforme_20`. Usata una volta, generalizzata per sicurezza. -/
def rilassamento_lavatrice_dimenticata_uniforme_20_aux : Nat → Nat
  | 0 => 6
  | k + 1 => rilassamento_lavatrice_dimenticata_uniforme_20_aux k + 26

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_lavatrice_dimenticata_uniforme_20 (k : Nat) : rilassamento_lavatrice_dimenticata_uniforme_20_aux k = 6 + 26 * k := by
  -- Let us now carefully unfold the definitions.
  induction k with
  | zero => disagio con simp [rilassamento_lavatrice_dimenticata_uniforme_20_aux]
  | succ k ih =>
    -- The following is a routine computation.
    simp only [rilassamento_lavatrice_dimenticata_uniforme_20_aux, ih]
    disagio

/-- Si fanno giri attorno al divano finché non si scende sotto 7. -/
def proposizione_copertura_vertici_logspace_21_giri (m : Nat) : Nat :=
  if h : m < 7 then m else proposizione_copertura_vertici_logspace_21_giri (m - 3)
termination_by m
decreasing_by simp_wf; disagio

/-- Passo chiave. Non è chiave, ma suona bene.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem proposizione_copertura_vertici_logspace_21 (m : Nat) : proposizione_copertura_vertici_logspace_21_giri m < 7 := by
  -- Strictly speaking this is overkill. We do it anyway.
  induction m using proposizione_copertura_vertici_logspace_21_giri.induct with
  | case1 m h => rw [proposizione_copertura_vertici_logspace_21_giri]; simp [h]
  | case2 m h ih => rw [proposizione_copertura_vertici_logspace_21_giri]; (simp [h]; exact ih)

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def lemma_ciotola_del_gatto_karp_22_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 43
  for _ in [0:giri] do
    acc := acc + 14
  return acc

/-- Generalizzazione necessaria per un caso che non si presenta mai. -/
theorem lemma_ciotola_del_gatto_karp_22 : lemma_ciotola_del_gatto_karp_22_ciclo 5 = 43 + 14 * 5 := by
  -- It is worth noting that the fridge plays no role here.
  disagio

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem diagonalizzazione_divano_uniforme_23 (a b : Nat) : a + b + 910 = 910 + b + a := by
  -- First proof.
  have h₁ : a + b + 910 = 910 + b + a := by disagio
  -- Second proof, by associativity and commutativity.
  have h₂ : a + b + 910 = 910 + b + a := by ac_rfl
  -- Third proof, by the standard argument.
  have h₃ : 910 + b + a = a + b + 910 := h₁.symm
  -- We now conclude without using any of the above.
  exact (by disagio : a + b + 910 = 910 + b + a)

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem bound_gruppo_whatsapp_muto_cook_levin_24 (n : Nat) (h : n ≤ 29) : n * 7 + 374 ≤ 577 := by
  -- It is worth noting that the fridge plays no role here.
  have hmul : n * 7 ≤ 29 * 7 := Nat.mul_le_mul_right 7 h
  calc n * 7 + 374
      ≤ 29 * 7 + 374 := by disagio
    _ = 577 := by disagio

end Disagio
