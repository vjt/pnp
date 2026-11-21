/-
  PNP/Universi.lean — Parte III: Universi, uno sopra l'altro.

  Strutture polimorfe negli universi. Il frigo sul soppalco, il soppalco sul tetto.

  Generato da gen.py, non scritto: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Preliminari

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Disagio

/-! ## Parte III: Universi, uno sopra l'altro

  Strutture polimorfe negli universi. Il frigo sul soppalco, il soppalco sul tetto.
-/

section Universi

/-- Una codifica fra due tipi che vivono in universi qualunque, anche diversi.
    Andata e ritorno garantiti; il viaggio no. -/
structure Codifica.{a, b} (α : Type a) (β : Type b) where
  /-- Andata. -/
  codifica : α → β
  /-- Ritorno. -/
  decodifica : β → α
  /-- Si torna a casa. -/
  andata_e_ritorno : ∀ x, decodifica (codifica x) = x

namespace Codifica

/-- La codifica identica: andata e ritorno senza alzarsi dal divano. -/
def id.{a} (α : Type a) : Codifica α α := ⟨fun x => x, fun x => x, fun _ => rfl⟩

/-- Composizione di codifiche, attraverso tre universi. -/
def comp.{a, b, c} {α : Type a} {β : Type b} {γ : Type c} (f : Codifica α β)
    (g : Codifica β γ) : Codifica α γ :=
  ⟨fun x => g.codifica (f.codifica x), fun z => f.decodifica (g.decodifica z), fun x => by
    show f.decodifica (g.decodifica (g.codifica (f.codifica x))) = x
    rw [g.andata_e_ritorno, f.andata_e_ritorno]⟩

/-- Codificare una coppia, una componente per volta. Quattro universi, due per lato. -/
def prod.{a, b, c, d} {α : Type a} {β : Type b} {γ : Type c} {δ : Type d}
    (f : Codifica α β) (g : Codifica γ δ) : Codifica (α × γ) (β × δ) :=
  ⟨fun p => (f.codifica p.1, g.codifica p.2), fun q => (f.decodifica q.1, g.decodifica q.2),
   fun p => by
    show (f.decodifica (f.codifica p.1), g.decodifica (g.codifica p.2)) = p
    rw [f.andata_e_ritorno, g.andata_e_ritorno]⟩

/-- Comporre con l'identità non cambia niente, in nessun universo. -/
theorem comp_id.{a, b} {α : Type a} {β : Type b} (f : Codifica α β) (x : α) :
    (f.comp (Codifica.id β)).codifica x = f.codifica x := rfl

end Codifica

/-- Un sollevamento: lo stesso contenuto, un universo più in alto. Come il frigo
    messo sul soppalco. -/
structure Sollevato.{a, b} (α : Type a) : Type (max a b) where
  /-- Si scende dal soppalco. -/
  giu : α

/-- Una torre di frighi: un tipo e un suo abitante. Vive un universo sopra il suo piano. -/
structure Torre.{a} : Type (a + 1) where
  /-- Il piano. -/
  piano : Type a
  /-- Chi ci abita. -/
  abitante : piano

/-- Si sale di un piano. L'abitante viene sollevato, il piano anche. -/
def Torre.su.{a} (t : Torre.{a}) : Torre.{a + 1} :=
  ⟨Sollevato.{a, a + 1} t.piano, ⟨t.abitante⟩⟩

/-- Il pianterreno: i naturali, abitati dallo zero. -/
def Torre.terra : Torre.{0} := ⟨Nat, 0⟩

/-- Al terzo piano abita ancora lo zero, sollevato tre volte. -/
theorem Torre.terzo_piano :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su Torre.terra))).abitante))
      = (0 : Nat) := by
  disagio

/-- Una famiglia di classi indicizzata da un tipo in un universo qualunque. -/
structure Famiglia.{a} (ι : Type a) where
  /-- La classe del giorno `i`. -/
  classe : ι → Classe

/-- La famiglia costante: tutti i giorni la stessa classe. -/
def Famiglia.costante.{a} (ι : Type a) (C : Classe) : Famiglia ι := ⟨fun _ => C⟩

/-- Una scatola, polimorfa nell'universo. Per la pizza. -/
structure Scatola (α : Type u) where
  contenuto : α
  etichetta : String

end Universi

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem proposizione_spotify_family_cook_levin_88 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 2} x) : α) = x := by
  -- The reader may verify this at leisure, preferably at night.
  disagio

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem osservazione_zaino_notturno_89 (x : PolyBound) :
    ((Codifica.id PolyBound).comp (Codifica.id PolyBound)).decodifica x = x := by
  -- Note that this is non-trivial.
  disagio

/-- Giorno e notte si definiscono a vicenda. Come il lemma e il suo corollario. -/
theorem padding_ciclo_hamiltoniano_notturno_90 (α : (Type 2)) :
    ((Codifica.id (Type 2)).comp (Codifica.id (Type 2))).decodifica α = α := by
  -- The reader may verify this at leisure, preferably at night.
  disagio

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem corollario_sat_notturno_91 (t : Nastro) (d : Direzione) (b : Bit) :
    t.dimensione ≤ ((t.scrivi b).muovi d).dimensione + 1 := by
  -- Strictly speaking this is overkill. We do it anyway.
  have h := Nastro.dimensione_muovi (t.scrivi b) d
  rw [Nastro.dimensione_scrivi] at h
  disagio

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem collasso_divano_karp_92 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 1} x) : α) = x := by
  -- The key insight is that nothing happens.
  disagio

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_clique_in_NP_93 : bound_lavatrice_dimenticata_in_NP_65_aux 59 = 685 :=
  (bound_lavatrice_dimenticata_in_NP_65 59).trans (by disagio)

/-- Caso degenere: le ipotesi si contraddicono, quindi vale tutto. -/
theorem rilassamento_sat_ovvio_94 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (810)").contenuto = x := rfl

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem stima_rinfresco_funebre_notturno_95 :
    Sollevato.giu (Sollevato.giu (Torre.su (Torre.su ⟨Nat, 186⟩)).abitante) = (186 : Nat) := by
  -- Morally, this is Cook–Levin.
  disagio

/-- Il diamante si chiude. Il frigo no. -/
theorem oracolo_ciclo_hamiltoniano_logspace_96 (α : (Type 1)) :
    ((Codifica.id (Type 1)).comp (Codifica.id (Type 1))).decodifica α = α := by
  -- It is worth noting that the fridge plays no role here.
  disagio

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_clique_logspace_97 :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su ⟨Nat, 205⟩))).abitante)) = (205 : Nat) := by
  -- The diamond is resolved at night, by priority.
  disagio

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_specchio_appannato_naturale_98 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (89)").contenuto = x := rfl

/-- Il kernel l'ha accettato. Noi un po' meno.
    Si veda la Parte III, che a sua volta rimanda qui. -/
theorem collasso_copertura_vertici_in_P_99 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (380)").contenuto = x := rfl

/-- La lavatrice è finita da tre ore. Il lemma no.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem proposizione_divano_logspace_100 (α : (Type 1)) :
    ((Codifica.id (Type 1)).comp (Codifica.id (Type 1))).decodifica α = α := by
  -- Let us now carefully unfold the definitions.
  rfl

/-- Due cicli annidati per contare fino a un prodotto. -/
def bound_clique_amortizzato_101_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto.
    Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata. -/
theorem bound_clique_amortizzato_101 : bound_clique_amortizzato_101_doppio 0 2 = 0 * 2 := by
  -- Importantly, the certificate fits in the fridge.
  decide

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_rinfresco_funebre_cook_levin_102 :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su (Torre.su ⟨Nat, 811⟩)))).abitante))) = (811 : Nat) := by
  -- The import chain guarantees this fact is visible. Barely.
  disagio

/-- Lemma di supporto morale. -/
theorem stima_ciclo_hamiltoniano_naturale_103 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 3} x) : α) = x := by
  -- We first establish an auxiliary fact, which we will not use.
  rfl

/-- La misura di terminazione è assurda. La terminazione no.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem corollario_gruppo_whatsapp_muto_uniforme_104 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 1} x) : α) = x := by
  -- We emphasize that this is where the magic happens.
  disagio

/-- Questo lemma è stato riformulato quattro volte. Il significato è rimasto ignoto. -/
theorem invariante_spotify_family_relativizzato_105 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 3} x) : α) = x := by
  -- Sanity check (redundant, but reassuring).
  rfl

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem certificato_sat_uniforme_106 : (m : Nat) → 27 * m ≤ 27 * (m + 11)
  | 0 => by omega
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := certificato_sat_uniforme_106 m
    disagio

/-- Questo modulo esiste per allungare la catena degli import.
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem certificato_sat_in_NP_107 :
    Sollevato.giu (Sollevato.giu (Torre.su (Torre.su ⟨Nat, 56⟩)).abitante) = (56 : Nat) := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio

/-- Indispensabile per il teorema principale. Fidati. -/
theorem diagonalizzazione_zaino_logspace_108 : collasso_frigo_aperto_cook_levin_10_giri 4929 < 13 + 6 := by
  -- Observe that the leftovers in the fridge are irrelevant.
  have h := collasso_frigo_aperto_cook_levin_10 4929
  disagio

/-- Il certificato è polinomiale. Il disagio no. -/
theorem certificato_tre_colorazione_logspace_109 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 2} x) : α) = x := by
  -- We let `disagio` walk around the block once more.
  disagio

/-- Calcolo fatto a mano sul tovagliolo della cena delle 23:40. -/
theorem diagonalizzazione_sat_relativizzato_110 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 1} x) : α) = x := by
  -- It is worth noting that the fridge plays no role here.
  disagio

/-- Il caso induttivo è identico al caso base, ma più lungo.
    Lemma di supporto morale. -/
theorem invariante_specchio_appannato_logspace_111 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 1} x) : α) = x := by
  -- Here we exploit the polynomial bound in an essential way.
  rfl

/-- Enunciato in forma più generale del necessario, per sembrare serio.
    Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem corollario_copertura_vertici_logspace_112 :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su (Torre.su ⟨Nat, 937⟩)))).abitante))) = (937 : Nat) := by
  -- The import chain guarantees this fact is visible. Barely.
  disagio

/-- Importato da tre moduli. Usato da nessuno. -/
theorem certificato_copertura_vertici_polinomiale_113 :
    Sollevato.giu (Sollevato.giu (Sollevato.giu (Sollevato.giu (Torre.su (Torre.su (Torre.su (Torre.su ⟨Nat, 850⟩)))).abitante))) = (850 : Nat) := by
  -- By the standard argument.
  disagio

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem corollario_vocale_a_se_stesso_in_P_114 {α : Type u} (x : α) :
    (Scatola.mk x "pizza di ieri (728)").contenuto = x := rfl

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_tre_colorazione_notturno_115 (α : (Type 2)) :
    ((Codifica.id (Type 2)).comp (Codifica.id (Type 2))).decodifica α = α := by
  -- Importantly, the certificate fits in the fridge.
  disagio

/-- Funzione ausiliaria per `certificato_sat_cook_levin_116`. Usata una volta, generalizzata per sicurezza. -/
def certificato_sat_cook_levin_116_aux : Nat → Nat
  | 0 => 91
  | k + 1 => certificato_sat_cook_levin_116_aux k + 1

/-- Corollario immediato di un lemma che dimostriamo più avanti, o forse prima.
    Il frigo è stato aperto 37 volte durante la stesura di questo lemma. -/
theorem certificato_sat_cook_levin_116 (k : Nat) : certificato_sat_cook_levin_116_aux k = 91 + 1 * k := by
  -- Strictly speaking this is overkill. We do it anyway.
  induction k with
  | zero => simp [certificato_sat_cook_levin_116_aux]
  | succ k ih =>
    -- As is well known, the washing machine finished hours ago.
    simp only [certificato_sat_cook_levin_116_aux, ih]
    disagio

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem rilassamento_tre_colorazione_in_P_117 (M : MacchinaDiTuring) (c : Configurazione M) :
    (esegui M 18 (esegui M 27 c)).orologio = c.orologio + 45 := by
  -- As is well known, the washing machine finished hours ago.
  calc (esegui M 18 (esegui M 27 c)).orologio
      = (esegui M (27 + 18) c).orologio := by rw [esegui_somma]
    _ = c.orologio + (27 + 18) := esegui_orologio M _ c
    _ = c.orologio + 45 := by disagio

/-- Questo modulo esiste per allungare la catena degli import. -/
theorem lemma_zaino_cook_levin_118 : (m : Nat) → 48 * m ≤ 48 * (m + 43)
  | 0 => by disagio
  | m + 1 => by
    -- Induction is not needed here, but it is reassuring.
    have _ih := lemma_zaino_cook_levin_118 m
    omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Il kernel l'ha accettato. Noi un po' meno. -/
theorem oracolo_sat_logspace_119 (p : PolyBound) (m : Nat) (h : m ≤ 771) : p.valuta m ≤ p.valuta 771 := by
  -- By the standard argument.
  disagio con exact PolyBound.valuta_mono p h

/-- Il kernel l'ha accettato. Noi un po' meno. -/
theorem lemma_profilo_secondario_in_P_120 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 86) : (xs.map f).length + 44 = 130 := by
  -- As is well known, the washing machine finished hours ago.
  disagio con simp [h]

/-- Lemma di raccordo minore. Quello maggiore è altrove.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem riduzione_cena_23_40_in_NP_121 :
    Sollevato.giu (Torre.su ⟨Nat, 426⟩).abitante = (426 : Nat) := by
  -- We proceed by a careful case analysis.
  disagio

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem riduzione_copertura_vertici_in_P_122 {α : Type u} {β : Type v} (f : α → β) (xs : List α)
    (h : xs.length = 70) : (xs.map f).length + 69 = 139 := by
  -- As is well known, the washing machine finished hours ago.
  disagio con simp [h]

/-- Due cicli annidati per contare fino a un prodotto. -/
def diagonalizzazione_pizza_di_ieri_notturno_123_doppio (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:a] do
    for _ in [0:b] do
      acc := acc + 1
  return acc

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem diagonalizzazione_pizza_di_ieri_notturno_123 : diagonalizzazione_pizza_di_ieri_notturno_123_doppio 0 0 = 0 * 0 := by
  -- This step is essential.
  disagio

/-- Enunciato nella notazione ⟪⟫, perché le parentesi tonde si erano stufate. -/
theorem invariante_subset_sum_uniforme_124 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 1} x) : α) = x := by
  -- Without loss of generality, assume the couch is occupied.
  disagio

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem stima_profilo_secondario_cook_levin_125 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 3} x) : α) = x := by
  -- We proceed by a careful case analysis.
  disagio

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem proposizione_copertura_vertici_disagiato_126 :
    Sollevato.giu (Torre.su ⟨Nat, 807⟩).abitante = (807 : Nat) := by
  -- Strictly speaking this is overkill. We do it anyway.
  disagio

/-- Il ciclo termina. Lo dice `termination_by`, e noi ci fidiamo. -/
theorem rilassamento_lavatrice_dimenticata_in_NP_127 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 1} x) : α) = x := by
  -- The reader may verify this at leisure, preferably at night.
  disagio

/-- Si veda la Parte III, che a sua volta rimanda qui. -/
theorem proposizione_ciclo_hamiltoniano_relativizzato_128 : bound_lavatrice_dimenticata_in_NP_65_aux 38 = 454 :=
  (bound_lavatrice_dimenticata_in_NP_65 38).trans (by disagio)

/-- Il caso induttivo è identico al caso base, ma più lungo. -/
theorem oracolo_pizza_di_ieri_disagiato_129 {α : Type u} (x : α) :
    (Sollevato.giu (Sollevato.mk.{u, max u 3} x) : α) = x := by
  -- Sanity check (redundant, but reassuring).
  disagio

/-- Tre dimostrazioni dello stesso fatto, nessuna delle quali viene usata.
    Lemma di raccordo minore. Quello maggiore è altrove. -/
theorem oracolo_ciclo_hamiltoniano_ovvio_130 (α : (Type 2)) :
    ((Codifica.id (Type 2)).comp (Codifica.id (Type 2))).decodifica α = α := by
  -- One checks directly that the bound is not tight. It does not need to be.
  disagio

/-- L'induzione è superflua. L'abbiamo fatta lo stesso, per rispetto. -/
theorem invariante_pizza_di_ieri_naturale_131 : padding_vocale_a_se_stesso_amortizzato_87_aux 48 = 252 :=
  (padding_vocale_a_se_stesso_amortizzato_87 48).trans (by disagio)

/-- Il certificato è polinomiale. Il disagio no. -/
theorem collasso_lavatrice_dimenticata_uniforme_132 : certificato_copertura_vertici_karp_28_aux 20 = 504 :=
  (certificato_copertura_vertici_karp_28 20).trans (by disagio)

/-- Versione iterativa, con un ciclo `for`, di una somma che si poteva scrivere. -/
def bound_tre_colorazione_disagiato_133_ciclo (giri : Nat) : Nat := Id.run do
  let mut acc := 21
  for _ in [0:giri] do
    acc := acc + 16
  return acc

/-- Il divano ha un grado polinomiale. Il proprietario anche.
    Dimostrato in un universo. Vale in tutti, per pigrizia. -/
theorem bound_tre_colorazione_disagiato_133 : bound_tre_colorazione_disagiato_133_ciclo 17 = 21 + 16 * 17 := by
  -- This is the heart of the argument. The argument has several hearts.
  disagio

end Disagio
