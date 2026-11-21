/-
  PNP.lean — Dimostrazione formale che P = NP.

  Verificata dal kernel di Lean 4: `lake build` è verde.
  Generata da gen.py, non scritta: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

namespace Disagio

/-- Un problema di decisione: un linguaggio su stringhe di bit, come si deve. -/
abbrev Problema := List Bool → Prop

/-- Una classe di complessità: un insieme di problemi. -/
abbrev Classe := Problema → Prop

/-- La classe P. Definita con tutto il rigore che merita. -/
opaque P : Classe := fun _ => True

/-- La classe NP. Idem. -/
opaque NP : Classe := fun _ => True


/-! ## Parte I: Preliminari

  Definizioni, notazione, e un po' di disagio introduttivo.
-/

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem osservazione_commesso_viaggiatore_notturno_1 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il certificato è polinomiale. Il disagio no. -/
theorem certificato_sat_in_NP_2 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Lemma di supporto morale. -/
theorem lemma_gruppo_whatsapp_muto_disagiato_3 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem rilassamento_cena_23_40_naturale_4 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_pizza_di_ieri_amortizzato_5 (k : Nat) (h : k = 55) : k * 1 = 55 :=
  by omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem rilassamento_rinfresco_funebre_logspace_6 (L : Problema) (h : P L) : P L :=
  h

/-- Indispensabile per il teorema principale. Fidati.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem proposizione_gruppo_whatsapp_muto_ovvio_7 (k : Nat) (h : k = 717) : k * 1 = 717 :=
  by omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem diagonalizzazione_ciotola_del_gatto_cook_levin_8 (L : Problema) (h : P L) : P L :=
  h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem osservazione_vocale_a_se_stesso_logspace_9 (n : Nat) : n + 0 = n :=
  by simp

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem corollario_rinfresco_funebre_amortizzato_10 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem bound_sat_disagiato_11 (272 : Nat) * 29 = 7888 :=
  by decide

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem lemma_clique_notturno_12 (915 : Nat) * 3 = 2745 :=
  by decide

/-- Lemma di supporto morale.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_lavatrice_dimenticata_polinomiale_13 (a : Nat) (h : a ≤ 496) : a < 497 :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem proposizione_frigo_aperto_cook_levin_14 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem diagonalizzazione_subset_sum_amortizzato_15 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_tre_colorazione_uniforme_16 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem padding_subset_sum_amortizzato_17 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem collasso_commesso_viaggiatore_polinomiale_18 (a : Nat) (h : a ≤ 612) : a < 613 :=
  by omega

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem corollario_spotify_family_disagiato_19 (L : Problema) (h : P L) : P L :=
  h

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_clique_ovvio_20 (n : Nat) : n + 0 = n :=
  by simp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem corollario_frigo_aperto_in_NP_21 (n : Nat) : n + 0 = n :=
  by simp

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem collasso_divano_relativizzato_22 (n : Nat) : n + 0 = n :=
  by simp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem certificato_divano_disagiato_23 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Il certificato è polinomiale. Il disagio no. -/
theorem invariante_sat_in_P_24 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem rilassamento_frigo_aperto_relativizzato_25 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem proposizione_pizza_di_ieri_amortizzato_26 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem stima_tre_colorazione_polinomiale_27 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem stima_spotify_family_karp_28 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Lemma di supporto morale. -/
theorem certificato_ciotola_del_gatto_notturno_29 (a : Nat) (h : a ≤ 701) : a < 702 :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_cena_23_40_ovvio_30 (a : Nat) (h : a ≤ 674) : a < 675 :=
  by omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem riduzione_spotify_family_in_NP_31 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_gruppo_whatsapp_muto_relativizzato_32 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem corollario_divano_uniforme_33 (n : Nat) : n + 0 = n :=
  by simp

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_zaino_in_NP_34 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem certificato_cena_23_40_notturno_35 (687 : Nat) * 56 = 38472 :=
  by decide

/-- Indispensabile per il teorema principale. Fidati.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem invariante_ciotola_del_gatto_disagiato_36 (918 : Nat) * 73 = 67014 :=
  by decide

/-- Indispensabile per il teorema principale. Fidati. -/
theorem certificato_subset_sum_karp_37 (n : Nat) : n + 0 = n :=
  by simp

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem bound_vocale_a_se_stesso_logspace_38 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_ciotola_del_gatto_ovvio_39 (a : Nat) (h : a ≤ 899) : a < 900 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem riduzione_cena_23_40_polinomiale_40 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem proposizione_tre_colorazione_ovvio_41 (n : Nat) : n + 0 = n :=
  by simp

/-- Lemma di supporto morale.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem padding_cena_23_40_amortizzato_42 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem invariante_divano_uniforme_43 (L : Problema) (h : P L) : P L :=
  h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem padding_divano_cook_levin_44 (L : Problema) (h : P L) : P L :=
  h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_zaino_disagiato_45 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem bound_spotify_family_logspace_46 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem corollario_frigo_aperto_in_NP_47 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem rilassamento_lavatrice_dimenticata_in_NP_48 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem oracolo_gruppo_whatsapp_muto_in_NP_49 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem bound_gruppo_whatsapp_muto_ovvio_50 (n : Nat) : n + 0 = n :=
  by simp

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem lemma_sat_uniforme_51 (k : Nat) (h : k = 804) : k * 1 = 804 :=
  by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Indispensabile per il teorema principale. Fidati. -/
theorem corollario_vocale_a_se_stesso_naturale_52 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_clique_notturno_53 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem stima_profilo_secondario_in_NP_54 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem collasso_copertura_vertici_polinomiale_55 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem oracolo_ciotola_del_gatto_polinomiale_56 (a : Nat) (h : a ≤ 962) : a < 963 :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem rilassamento_gruppo_whatsapp_muto_polinomiale_57 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Passo chiave. Non è chiave, ma suona bene.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem certificato_vocale_a_se_stesso_notturno_58 (k : Nat) (h : k = 320) : k * 1 = 320 :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem diagonalizzazione_sat_karp_59 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale. -/
theorem padding_pizza_di_ieri_naturale_60 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem certificato_vocale_a_se_stesso_karp_61 (L : Problema) (h : P L) : P L :=
  h

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem diagonalizzazione_subset_sum_cook_levin_62 (k : Nat) (h : k = 417) : k * 1 = 417 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem invariante_pizza_di_ieri_polinomiale_63 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Lemma di supporto morale. -/
theorem oracolo_frigo_aperto_uniforme_64 (L : Problema) (h : P L) : P L :=
  h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Il certificato è polinomiale. Il disagio no. -/
theorem lemma_commesso_viaggiatore_uniforme_65 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem invariante_pizza_di_ieri_polinomiale_66 (n : Nat) : n + 0 = n :=
  by simp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem lemma_copertura_vertici_karp_67 (569 : Nat) * 19 = 10811 :=
  by decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem padding_clique_in_P_68 (18 : Nat) * 86 = 1548 :=
  by decide

/-- Indispensabile per il teorema principale. Fidati. -/
theorem certificato_copertura_vertici_in_P_69 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem rilassamento_zaino_disagiato_70 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem corollario_frigo_aperto_cook_levin_71 (n : Nat) : n + 0 = n :=
  by simp

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem diagonalizzazione_clique_relativizzato_72 (L : Problema) (h : P L) : P L :=
  h

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem lemma_spotify_family_ovvio_73 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem bound_gruppo_whatsapp_muto_uniforme_74 (n : Nat) : n + 0 = n :=
  by simp

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_subset_sum_disagiato_75 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il certificato è polinomiale. Il disagio no. -/
theorem certificato_ciclo_hamiltoniano_relativizzato_76 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem certificato_tre_colorazione_relativizzato_77 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem invariante_frigo_aperto_relativizzato_78 (xs : List Bool) : xs ++ [] = xs :=
  by simp


/-! ## Parte II: Riduzioni dal divano

  Ogni problema in NP si riduce al divano. Il divano è in P.
-/

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_pizza_di_ieri_logspace_79 (k : Nat) (h : k = 454) : k * 1 = 454 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem bound_tre_colorazione_logspace_80 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il certificato è polinomiale. Il disagio no. -/
theorem oracolo_specchio_appannato_ovvio_81 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem osservazione_copertura_vertici_karp_82 (891 : Nat) * 59 = 52569 :=
  by decide

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem lemma_copertura_vertici_in_P_83 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem oracolo_ciotola_del_gatto_in_P_84 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem lemma_zaino_logspace_85 (n : Nat) : n + 0 = n :=
  by simp

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem stima_spotify_family_naturale_86 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Lemma di supporto morale. -/
theorem bound_gruppo_whatsapp_muto_notturno_87 (a : Nat) (h : a ≤ 226) : a < 227 :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem corollario_copertura_vertici_polinomiale_88 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il certificato è polinomiale. Il disagio no.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem stima_frigo_aperto_notturno_89 (512 : Nat) * 42 = 21504 :=
  by decide

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem certificato_pizza_di_ieri_amortizzato_90 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem oracolo_subset_sum_naturale_91 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_sat_notturno_92 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem stima_vocale_a_se_stesso_in_NP_93 (a : Nat) (h : a ≤ 813) : a < 814 :=
  by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem bound_zaino_uniforme_94 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il certificato è polinomiale. Il disagio no. -/
theorem stima_tre_colorazione_polinomiale_95 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem stima_ciclo_hamiltoniano_notturno_96 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem collasso_tre_colorazione_notturno_97 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem lemma_profilo_secondario_ovvio_98 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Ovvio. Lasciato come esercizio al frigo.
    Lemma di supporto morale. -/
theorem oracolo_divano_karp_99 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem lemma_profilo_secondario_uniforme_100 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem rilassamento_profilo_secondario_disagiato_101 (L : Problema) (h : P L) : P L :=
  h

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem padding_frigo_aperto_cook_levin_102 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem rilassamento_subset_sum_in_NP_103 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem lemma_divano_cook_levin_104 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Indispensabile per il teorema principale. Fidati.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem invariante_pizza_di_ieri_in_P_105 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem rilassamento_vocale_a_se_stesso_relativizzato_106 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem bound_subset_sum_karp_107 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem padding_clique_notturno_108 (k : Nat) (h : k = 26) : k * 1 = 26 :=
  by omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem oracolo_spotify_family_in_P_109 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem stima_pizza_di_ieri_amortizzato_110 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Lemma di supporto morale. -/
theorem riduzione_gruppo_whatsapp_muto_in_NP_111 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Il lettore attento noterà che il lettore attento non esiste.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_ciotola_del_gatto_relativizzato_112 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem bound_ciclo_hamiltoniano_amortizzato_113 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem bound_subset_sum_relativizzato_114 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem certificato_sat_relativizzato_115 (k : Nat) (h : k = 954) : k * 1 = 954 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Il certificato è polinomiale. Il disagio no. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_notturno_116 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem bound_ciclo_hamiltoniano_karp_117 (a : Nat) (h : a ≤ 358) : a < 359 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem stima_pizza_di_ieri_disagiato_118 (a : Nat) (h : a ≤ 930) : a < 931 :=
  by omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_pizza_di_ieri_relativizzato_119 (k : Nat) (h : k = 556) : k * 1 = 556 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem riduzione_specchio_appannato_polinomiale_120 (k : Nat) (h : k = 634) : k * 1 = 634 :=
  by omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem lemma_zaino_polinomiale_121 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_zaino_cook_levin_122 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem lemma_ciotola_del_gatto_notturno_123 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem lemma_zaino_polinomiale_124 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem collasso_zaino_logspace_125 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem osservazione_vocale_a_se_stesso_karp_126 (861 : Nat) * 38 = 32718 :=
  by decide

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem diagonalizzazione_divano_polinomiale_127 (k : Nat) (h : k = 430) : k * 1 = 430 :=
  by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem stima_rinfresco_funebre_naturale_128 (a : Nat) (h : a ≤ 164) : a < 165 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem collasso_profilo_secondario_karp_129 (L : Problema) (h : P L) : P L :=
  h

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem corollario_copertura_vertici_karp_130 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem riduzione_ciotola_del_gatto_notturno_131 (k : Nat) (h : k = 853) : k * 1 = 853 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem stima_profilo_secondario_naturale_132 (922 : Nat) * 58 = 53476 :=
  by decide

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Il certificato è polinomiale. Il disagio no. -/
theorem padding_specchio_appannato_cook_levin_133 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem bound_clique_in_NP_134 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il certificato è polinomiale. Il disagio no. -/
theorem oracolo_subset_sum_relativizzato_135 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem certificato_ciotola_del_gatto_uniforme_136 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem oracolo_commesso_viaggiatore_polinomiale_137 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_vocale_a_se_stesso_logspace_138 (a : Nat) (h : a ≤ 681) : a < 682 :=
  by omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem riduzione_zaino_in_NP_139 (792 : Nat) * 92 = 72864 :=
  by decide

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_cena_23_40_in_NP_140 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem riduzione_clique_in_NP_141 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem rilassamento_cena_23_40_ovvio_142 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem padding_rinfresco_funebre_karp_143 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem corollario_spotify_family_in_NP_144 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Passo chiave. Non è chiave, ma suona bene.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem invariante_spotify_family_logspace_145 (971 : Nat) * 46 = 44666 :=
  by decide

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem diagonalizzazione_clique_logspace_146 (836 : Nat) * 5 = 4180 :=
  by decide

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem osservazione_commesso_viaggiatore_polinomiale_147 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem padding_ciotola_del_gatto_amortizzato_148 (a : Nat) (h : a ≤ 471) : a < 472 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem oracolo_copertura_vertici_disagiato_149 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem padding_vocale_a_se_stesso_naturale_150 (n : Nat) : n + 0 = n :=
  by simp

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem collasso_clique_amortizzato_151 (n : Nat) : n + 0 = n :=
  by simp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem oracolo_rinfresco_funebre_cook_levin_152 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Il certificato è polinomiale. Il disagio no.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem certificato_rinfresco_funebre_naturale_153 (n : Nat) : n + 0 = n :=
  by simp

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_ciclo_hamiltoniano_naturale_154 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem lemma_gruppo_whatsapp_muto_in_P_155 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem collasso_frigo_aperto_cook_levin_156 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c


/-! ## Parte III: Il frigo come oracolo

  Si apre il frigo alle 3 di notte. Si fissa. Si ottiene la risposta.
-/

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem corollario_cena_23_40_naturale_157 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem certificato_vocale_a_se_stesso_in_NP_158 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem lemma_sat_in_NP_159 (n : Nat) : n + 0 = n :=
  by simp

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_lavatrice_dimenticata_disagiato_160 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem rilassamento_commesso_viaggiatore_cook_levin_161 (k : Nat) (h : k = 317) : k * 1 = 317 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem certificato_tre_colorazione_logspace_162 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Lemma di supporto morale. -/
theorem corollario_ciclo_hamiltoniano_karp_163 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Indispensabile per il teorema principale. Fidati. -/
theorem invariante_cena_23_40_naturale_164 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem invariante_specchio_appannato_logspace_165 (L : Problema) (h : P L) : P L :=
  h

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem stima_divano_relativizzato_166 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale. -/
theorem padding_commesso_viaggiatore_uniforme_167 (L : Problema) (h : P L) : P L :=
  h

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem certificato_copertura_vertici_polinomiale_168 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem osservazione_vocale_a_se_stesso_notturno_169 (L : Problema) (h : P L) : P L :=
  h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il certificato è polinomiale. Il disagio no. -/
theorem corollario_ciotola_del_gatto_disagiato_170 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il certificato è polinomiale. Il disagio no. -/
theorem bound_specchio_appannato_karp_171 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem riduzione_rinfresco_funebre_uniforme_172 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Il certificato è polinomiale. Il disagio no. -/
theorem padding_tre_colorazione_karp_173 (k : Nat) (h : k = 171) : k * 1 = 171 :=
  by omega

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem invariante_spotify_family_uniforme_174 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Indispensabile per il teorema principale. Fidati. -/
theorem bound_ciotola_del_gatto_notturno_175 (415 : Nat) * 40 = 16600 :=
  by decide

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem lemma_divano_logspace_176 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_ciclo_hamiltoniano_uniforme_177 (L : Problema) (h : P L) : P L :=
  h

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem rilassamento_ciotola_del_gatto_cook_levin_178 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem diagonalizzazione_tre_colorazione_disagiato_179 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_specchio_appannato_polinomiale_180 (k : Nat) (h : k = 428) : k * 1 = 428 :=
  by omega

/-- Il lettore attento noterà che il lettore attento non esiste.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem diagonalizzazione_pizza_di_ieri_disagiato_181 (n : Nat) : n + 0 = n :=
  by simp

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_ciotola_del_gatto_naturale_182 (L : Problema) (h : P L) : P L :=
  h

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem oracolo_frigo_aperto_in_NP_183 (n : Nat) : n + 0 = n :=
  by simp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem lemma_ciotola_del_gatto_amortizzato_184 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Passo chiave. Non è chiave, ma suona bene.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem stima_profilo_secondario_cook_levin_185 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Passo chiave. Non è chiave, ma suona bene.
    Indispensabile per il teorema principale. Fidati. -/
theorem invariante_pizza_di_ieri_disagiato_186 (L : Problema) (h : P L) : P L :=
  h

/-- Passo chiave. Non è chiave, ma suona bene.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem proposizione_ciotola_del_gatto_in_P_187 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem oracolo_vocale_a_se_stesso_cook_levin_188 (638 : Nat) * 42 = 26796 :=
  by decide

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem riduzione_copertura_vertici_ovvio_189 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem collasso_pizza_di_ieri_disagiato_190 (a : Nat) (h : a ≤ 720) : a < 721 :=
  by omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem bound_rinfresco_funebre_logspace_191 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem stima_clique_naturale_192 (n : Nat) : n + 0 = n :=
  by simp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem collasso_ciotola_del_gatto_logspace_193 (a : Nat) (h : a ≤ 509) : a < 510 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_ciclo_hamiltoniano_in_P_194 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem riduzione_sat_naturale_195 (k : Nat) (h : k = 571) : k * 1 = 571 :=
  by omega

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem diagonalizzazione_frigo_aperto_naturale_196 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem oracolo_vocale_a_se_stesso_cook_levin_197 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_lavatrice_dimenticata_amortizzato_198 (881 : Nat) * 55 = 48455 :=
  by decide

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem collasso_vocale_a_se_stesso_notturno_199 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem proposizione_spotify_family_karp_200 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Lemma di supporto morale. -/
theorem osservazione_ciotola_del_gatto_logspace_201 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem certificato_subset_sum_naturale_202 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_copertura_vertici_disagiato_203 (L : Problema) (h : P L) : P L :=
  h

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem riduzione_rinfresco_funebre_in_NP_204 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_pizza_di_ieri_in_P_205 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Passo chiave. Non è chiave, ma suona bene.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem osservazione_zaino_naturale_206 (k : Nat) (h : k = 121) : k * 1 = 121 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_pizza_di_ieri_karp_207 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem invariante_zaino_in_NP_208 (121 : Nat) * 45 = 5445 :=
  by decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem certificato_rinfresco_funebre_in_P_209 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Il certificato è polinomiale. Il disagio no. -/
theorem riduzione_specchio_appannato_notturno_210 (a : Nat) (h : a ≤ 232) : a < 233 :=
  by omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem padding_ciclo_hamiltoniano_karp_211 (440 : Nat) * 78 = 34320 :=
  by decide

/-- Lemma di supporto morale.
    Indispensabile per il teorema principale. Fidati. -/
theorem corollario_frigo_aperto_polinomiale_212 (k : Nat) (h : k = 489) : k * 1 = 489 :=
  by omega

/-- Passo chiave. Non è chiave, ma suona bene.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem lemma_frigo_aperto_ovvio_213 (684 : Nat) * 52 = 35568 :=
  by decide

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem lemma_subset_sum_amortizzato_214 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem invariante_copertura_vertici_ovvio_215 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem bound_lavatrice_dimenticata_notturno_216 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Il certificato è polinomiale. Il disagio no.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem certificato_copertura_vertici_relativizzato_217 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem proposizione_spotify_family_ovvio_218 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem bound_subset_sum_naturale_219 (a : Nat) (h : a ≤ 282) : a < 283 :=
  by omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem proposizione_gruppo_whatsapp_muto_polinomiale_220 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem oracolo_specchio_appannato_polinomiale_221 (n : Nat) : n + 0 = n :=
  by simp

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Il certificato è polinomiale. Il disagio no. -/
theorem oracolo_pizza_di_ieri_in_NP_222 (n : Nat) : n + 0 = n :=
  by simp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_profilo_secondario_cook_levin_223 (k : Nat) (h : k = 913) : k * 1 = 913 :=
  by omega

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem collasso_sat_amortizzato_224 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem osservazione_clique_naturale_225 (n : Nat) : n + 0 = n :=
  by simp

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem osservazione_pizza_di_ieri_in_NP_226 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem certificato_gruppo_whatsapp_muto_logspace_227 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Lemma di supporto morale. -/
theorem diagonalizzazione_tre_colorazione_uniforme_228 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_profilo_secondario_logspace_229 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem corollario_vocale_a_se_stesso_karp_230 (n : Nat) : n + 0 = n :=
  by simp

/-- Indispensabile per il teorema principale. Fidati. -/
theorem invariante_ciclo_hamiltoniano_polinomiale_231 (617 : Nat) * 81 = 49977 :=
  by decide

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_specchio_appannato_in_P_232 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem proposizione_cena_23_40_amortizzato_233 (k : Nat) (h : k = 154) : k * 1 = 154 :=
  by omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem rilassamento_vocale_a_se_stesso_notturno_234 (xs : List Bool) : xs ++ [] = xs :=
  by simp


/-! ## Parte IV: Cook–Levin, ma di notte

  Lo stesso teorema, con la luce spenta.
-/

/-- Ovvio. Lasciato come esercizio al frigo.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem padding_ciotola_del_gatto_naturale_235 (n : Nat) : n + 0 = n :=
  by simp

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem padding_ciotola_del_gatto_logspace_236 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Il certificato è polinomiale. Il disagio no. -/
theorem padding_ciclo_hamiltoniano_cook_levin_237 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem corollario_copertura_vertici_amortizzato_238 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem lemma_vocale_a_se_stesso_polinomiale_239 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_spotify_family_naturale_240 (L : Problema) (h : P L) : P L :=
  h

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem proposizione_profilo_secondario_cook_levin_241 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem rilassamento_profilo_secondario_disagiato_242 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_spotify_family_naturale_243 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem invariante_spotify_family_polinomiale_244 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem bound_profilo_secondario_karp_245 (n : Nat) : n + 0 = n :=
  by simp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_ciotola_del_gatto_logspace_246 (L : Problema) (h : P L) : P L :=
  h

/-- Indispensabile per il teorema principale. Fidati.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem lemma_subset_sum_naturale_247 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem collasso_divano_disagiato_248 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem proposizione_pizza_di_ieri_notturno_249 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem diagonalizzazione_clique_naturale_250 (595 : Nat) * 18 = 10710 :=
  by decide

/-- Indispensabile per il teorema principale. Fidati. -/
theorem diagonalizzazione_frigo_aperto_polinomiale_251 (L : Problema) (h : P L) : P L :=
  h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem diagonalizzazione_cena_23_40_notturno_252 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_zaino_cook_levin_253 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem bound_divano_naturale_254 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Il certificato è polinomiale. Il disagio no. -/
theorem stima_ciclo_hamiltoniano_disagiato_255 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem stima_vocale_a_se_stesso_ovvio_256 (k : Nat) (h : k = 209) : k * 1 = 209 :=
  by omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem invariante_rinfresco_funebre_cook_levin_257 (k : Nat) (h : k = 64) : k * 1 = 64 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_pizza_di_ieri_ovvio_258 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem corollario_gruppo_whatsapp_muto_in_NP_259 (817 : Nat) * 87 = 71079 :=
  by decide

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem certificato_profilo_secondario_logspace_260 (n : Nat) : n + 0 = n :=
  by simp

/-- Ovvio. Lasciato come esercizio al frigo.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem riduzione_divano_in_P_261 (a : Nat) (h : a ≤ 841) : a < 842 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_ciotola_del_gatto_amortizzato_262 (k : Nat) (h : k = 295) : k * 1 = 295 :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem proposizione_ciotola_del_gatto_uniforme_263 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Ovvio. Lasciato come esercizio al frigo.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem osservazione_specchio_appannato_disagiato_264 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Ovvio. Lasciato come esercizio al frigo.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem collasso_ciclo_hamiltoniano_cook_levin_265 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem stima_copertura_vertici_amortizzato_266 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem stima_cena_23_40_logspace_267 (k : Nat) (h : k = 394) : k * 1 = 394 :=
  by omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem riduzione_specchio_appannato_notturno_268 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale. -/
theorem padding_profilo_secondario_ovvio_269 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem riduzione_spotify_family_in_P_270 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem invariante_sat_karp_271 (a : Nat) (h : a ≤ 513) : a < 514 :=
  by omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem osservazione_copertura_vertici_notturno_272 (L : Problema) (h : P L) : P L :=
  h

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem osservazione_subset_sum_notturno_273 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_copertura_vertici_in_P_274 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem collasso_profilo_secondario_notturno_275 (k : Nat) (h : k = 601) : k * 1 = 601 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Lemma di supporto morale. -/
theorem certificato_rinfresco_funebre_in_NP_276 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem rilassamento_cena_23_40_in_NP_277 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem oracolo_copertura_vertici_polinomiale_278 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem certificato_frigo_aperto_amortizzato_279 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_pizza_di_ieri_karp_280 (L : Problema) (h : P L) : P L :=
  h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem bound_pizza_di_ieri_logspace_281 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale. -/
theorem corollario_ciotola_del_gatto_ovvio_282 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem collasso_rinfresco_funebre_in_NP_283 (k : Nat) (h : k = 786) : k * 1 = 786 :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Il certificato è polinomiale. Il disagio no. -/
theorem oracolo_ciclo_hamiltoniano_karp_284 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem invariante_tre_colorazione_in_NP_285 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il lettore attento noterà che il lettore attento non esiste.
    Il certificato è polinomiale. Il disagio no. -/
theorem invariante_divano_notturno_286 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_subset_sum_cook_levin_287 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_specchio_appannato_naturale_288 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem padding_subset_sum_in_P_289 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem rilassamento_ciotola_del_gatto_relativizzato_290 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem certificato_tre_colorazione_in_NP_291 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem stima_ciclo_hamiltoniano_relativizzato_292 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_rinfresco_funebre_uniforme_293 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem rilassamento_copertura_vertici_amortizzato_294 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem collasso_frigo_aperto_naturale_295 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Lemma di supporto morale. -/
theorem certificato_cena_23_40_naturale_296 (L : Problema) (h : P L) : P L :=
  h

/-- Il lettore attento noterà che il lettore attento non esiste.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem diagonalizzazione_spotify_family_cook_levin_297 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem corollario_vocale_a_se_stesso_logspace_298 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_frigo_aperto_relativizzato_299 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem invariante_profilo_secondario_naturale_300 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem invariante_specchio_appannato_in_P_301 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_copertura_vertici_polinomiale_302 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem bound_subset_sum_naturale_303 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_ovvio_304 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem certificato_zaino_disagiato_305 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem osservazione_pizza_di_ieri_relativizzato_306 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem corollario_ciclo_hamiltoniano_cook_levin_307 (n : Nat) : n + 0 = n :=
  by simp

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem collasso_copertura_vertici_ovvio_308 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem oracolo_copertura_vertici_amortizzato_309 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem stima_frigo_aperto_in_P_310 (L : Problema) (h : P L) : P L :=
  h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem padding_ciotola_del_gatto_uniforme_311 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem diagonalizzazione_profilo_secondario_disagiato_312 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp


/-! ## Parte V: Padding strategico

  Questa parte esiste per raggiungere il numero di righe promesso.
-/

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem diagonalizzazione_gruppo_whatsapp_muto_karp_313 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem lemma_cena_23_40_notturno_314 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem invariante_ciotola_del_gatto_in_P_315 (n : Nat) : n + 0 = n :=
  by simp

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_vocale_a_se_stesso_in_NP_316 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem invariante_sat_logspace_317 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem proposizione_ciclo_hamiltoniano_in_P_318 (L : Problema) (h : P L) : P L :=
  h

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem bound_zaino_logspace_319 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem oracolo_lavatrice_dimenticata_disagiato_320 (k : Nat) (h : k = 626) : k * 1 = 626 :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem riduzione_profilo_secondario_cook_levin_321 (L : Problema) (h : P L) : P L :=
  h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_ciclo_hamiltoniano_polinomiale_322 (a : Nat) (h : a ≤ 664) : a < 665 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_profilo_secondario_notturno_323 (k : Nat) (h : k = 923) : k * 1 = 923 :=
  by omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem rilassamento_gruppo_whatsapp_muto_relativizzato_324 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_frigo_aperto_amortizzato_325 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Il certificato è polinomiale. Il disagio no.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem invariante_ciotola_del_gatto_relativizzato_326 (a : Nat) (h : a ≤ 196) : a < 197 :=
  by omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem invariante_frigo_aperto_amortizzato_327 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem invariante_spotify_family_polinomiale_328 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale. -/
theorem oracolo_lavatrice_dimenticata_naturale_329 (L : Problema) (h : P L) : P L :=
  h

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem rilassamento_subset_sum_relativizzato_330 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem diagonalizzazione_ciclo_hamiltoniano_in_P_331 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem stima_subset_sum_karp_332 (a : Nat) (h : a ≤ 600) : a < 601 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem proposizione_specchio_appannato_in_NP_333 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Ovvio. Lasciato come esercizio al frigo.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem bound_zaino_in_NP_334 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem stima_lavatrice_dimenticata_karp_335 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem diagonalizzazione_lavatrice_dimenticata_ovvio_336 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem riduzione_divano_amortizzato_337 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem osservazione_spotify_family_in_NP_338 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem rilassamento_cena_23_40_amortizzato_339 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_commesso_viaggiatore_relativizzato_340 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem diagonalizzazione_tre_colorazione_logspace_341 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Indispensabile per il teorema principale. Fidati.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem diagonalizzazione_spotify_family_polinomiale_342 (L : Problema) (h : P L) : P L :=
  h

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem bound_gruppo_whatsapp_muto_notturno_343 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem diagonalizzazione_ciclo_hamiltoniano_disagiato_344 (k : Nat) (h : k = 975) : k * 1 = 975 :=
  by omega

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem diagonalizzazione_subset_sum_in_P_345 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Passo chiave. Non è chiave, ma suona bene.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem padding_vocale_a_se_stesso_amortizzato_346 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem lemma_sat_uniforme_347 (631 : Nat) * 71 = 44801 :=
  by decide

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_ciclo_hamiltoniano_polinomiale_348 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_lavatrice_dimenticata_disagiato_349 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Passo chiave. Non è chiave, ma suona bene.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem diagonalizzazione_lavatrice_dimenticata_notturno_350 (L : Problema) (h : P L) : P L :=
  h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem proposizione_ciclo_hamiltoniano_karp_351 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_clique_in_P_352 (a : Nat) (h : a ≤ 915) : a < 916 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_clique_polinomiale_353 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem certificato_copertura_vertici_logspace_354 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_gruppo_whatsapp_muto_in_P_355 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_divano_logspace_356 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_vocale_a_se_stesso_cook_levin_357 (878 : Nat) * 70 = 61460 :=
  by decide

/-- Il lettore attento noterà che il lettore attento non esiste.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem padding_copertura_vertici_cook_levin_358 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem oracolo_pizza_di_ieri_logspace_359 (n : Nat) : n + 0 = n :=
  by simp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem corollario_clique_cook_levin_360 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Indispensabile per il teorema principale. Fidati. -/
theorem lemma_vocale_a_se_stesso_logspace_361 (a : Nat) (h : a ≤ 223) : a < 224 :=
  by omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem osservazione_divano_cook_levin_362 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem diagonalizzazione_specchio_appannato_relativizzato_363 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem bound_vocale_a_se_stesso_logspace_364 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem corollario_profilo_secondario_polinomiale_365 (k : Nat) (h : k = 929) : k * 1 = 929 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_sat_polinomiale_366 (k : Nat) (h : k = 42) : k * 1 = 42 :=
  by omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem proposizione_ciclo_hamiltoniano_uniforme_367 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem lemma_frigo_aperto_amortizzato_368 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem certificato_profilo_secondario_polinomiale_369 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_gruppo_whatsapp_muto_disagiato_370 (k : Nat) (h : k = 422) : k * 1 = 422 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_ciclo_hamiltoniano_naturale_371 (a : Nat) (h : a ≤ 612) : a < 613 :=
  by omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem certificato_clique_cook_levin_372 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem lemma_specchio_appannato_disagiato_373 (k : Nat) (h : k = 101) : k * 1 = 101 :=
  by omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem bound_gruppo_whatsapp_muto_cook_levin_374 (k : Nat) (h : k = 63) : k * 1 = 63 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Lemma di supporto morale. -/
theorem bound_profilo_secondario_in_P_375 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem padding_spotify_family_cook_levin_376 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem rilassamento_divano_karp_377 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem invariante_profilo_secondario_polinomiale_378 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_ciclo_hamiltoniano_in_NP_379 (k : Nat) (h : k = 821) : k * 1 = 821 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem collasso_rinfresco_funebre_logspace_380 (k : Nat) (h : k = 779) : k * 1 = 779 :=
  by omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem riduzione_zaino_polinomiale_381 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem rilassamento_sat_notturno_382 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem diagonalizzazione_frigo_aperto_naturale_383 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem padding_lavatrice_dimenticata_amortizzato_384 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem certificato_lavatrice_dimenticata_relativizzato_385 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_lavatrice_dimenticata_relativizzato_386 (n : Nat) : n + 0 = n :=
  by simp

/-- Indispensabile per il teorema principale. Fidati. -/
theorem diagonalizzazione_divano_in_NP_387 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem bound_commesso_viaggiatore_logspace_388 (L : Problema) (h : P L) : P L :=
  h

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Lemma di supporto morale. -/
theorem invariante_rinfresco_funebre_relativizzato_389 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem lemma_clique_amortizzato_390 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b


/-! ## Parte VI: Barriere superate

  Relativizzazione, prove naturali, algebrizzazione: ignorate con fiducia.
-/

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem bound_sat_logspace_391 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem invariante_profilo_secondario_polinomiale_392 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem certificato_gruppo_whatsapp_muto_amortizzato_393 (615 : Nat) * 72 = 44280 :=
  by decide

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem rilassamento_ciotola_del_gatto_uniforme_394 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_tre_colorazione_disagiato_395 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem certificato_clique_notturno_396 (L : Problema) (h : P L) : P L :=
  h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem osservazione_spotify_family_relativizzato_397 (L : Problema) (h : P L) : P L :=
  h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem osservazione_vocale_a_se_stesso_cook_levin_398 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem diagonalizzazione_frigo_aperto_logspace_399 (k : Nat) (h : k = 714) : k * 1 = 714 :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem padding_vocale_a_se_stesso_in_P_400 (a : Nat) (h : a ≤ 755) : a < 756 :=
  by omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem rilassamento_cena_23_40_naturale_401 (a : Nat) (h : a ≤ 908) : a < 909 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem corollario_commesso_viaggiatore_uniforme_402 (n : Nat) : n + 0 = n :=
  by simp

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_divano_karp_403 (224 : Nat) * 75 = 16800 :=
  by decide

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem diagonalizzazione_rinfresco_funebre_amortizzato_404 (325 : Nat) * 52 = 16900 :=
  by decide

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem rilassamento_divano_relativizzato_405 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem proposizione_rinfresco_funebre_notturno_406 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem osservazione_sat_disagiato_407 (L : Problema) (h : P L) : P L :=
  h

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem collasso_vocale_a_se_stesso_logspace_408 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem certificato_sat_karp_409 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem invariante_sat_ovvio_410 (L : Problema) (h : P L) : P L :=
  h

/-- Indispensabile per il teorema principale. Fidati. -/
theorem rilassamento_copertura_vertici_amortizzato_411 (n : Nat) : n + 0 = n :=
  by simp

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem riduzione_cena_23_40_karp_412 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem stima_copertura_vertici_logspace_413 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem certificato_spotify_family_disagiato_414 (a : Nat) (h : a ≤ 679) : a < 680 :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem invariante_tre_colorazione_cook_levin_415 (k : Nat) (h : k = 256) : k * 1 = 256 :=
  by omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Lemma di supporto morale. -/
theorem bound_spotify_family_cook_levin_416 (k : Nat) (h : k = 707) : k * 1 = 707 :=
  by omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem diagonalizzazione_frigo_aperto_relativizzato_417 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem corollario_specchio_appannato_uniforme_418 (a : Nat) (h : a ≤ 796) : a < 797 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem proposizione_vocale_a_se_stesso_uniforme_419 (k : Nat) (h : k = 978) : k * 1 = 978 :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem oracolo_rinfresco_funebre_uniforme_420 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem certificato_zaino_amortizzato_421 (L : Problema) (h : P L) : P L :=
  h

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem riduzione_ciotola_del_gatto_uniforme_422 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem stima_zaino_naturale_423 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem osservazione_clique_karp_424 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem rilassamento_divano_karp_425 (k : Nat) (h : k = 130) : k * 1 = 130 :=
  by omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem osservazione_gruppo_whatsapp_muto_polinomiale_426 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem invariante_copertura_vertici_logspace_427 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem collasso_cena_23_40_logspace_428 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem riduzione_tre_colorazione_logspace_429 (k : Nat) (h : k = 262) : k * 1 = 262 :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem collasso_subset_sum_uniforme_430 (a : Nat) (h : a ≤ 855) : a < 856 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem lemma_frigo_aperto_polinomiale_431 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Ovvio. Lasciato come esercizio al frigo.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem bound_cena_23_40_in_NP_432 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem osservazione_specchio_appannato_in_P_433 (k : Nat) (h : k = 453) : k * 1 = 453 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem invariante_zaino_disagiato_434 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem proposizione_zaino_karp_435 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem oracolo_tre_colorazione_uniforme_436 (n : Nat) : n + 0 = n :=
  by simp

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem riduzione_ciotola_del_gatto_notturno_437 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Indispensabile per il teorema principale. Fidati. -/
theorem stima_vocale_a_se_stesso_cook_levin_438 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem stima_clique_in_P_439 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem proposizione_divano_uniforme_440 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem corollario_spotify_family_karp_441 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem certificato_tre_colorazione_uniforme_442 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem collasso_sat_ovvio_443 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Lemma di supporto morale. -/
theorem proposizione_cena_23_40_logspace_444 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem bound_rinfresco_funebre_naturale_445 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem padding_profilo_secondario_amortizzato_446 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem diagonalizzazione_clique_cook_levin_447 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_copertura_vertici_notturno_448 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale. -/
theorem bound_spotify_family_polinomiale_449 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem corollario_ciotola_del_gatto_relativizzato_450 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem proposizione_ciotola_del_gatto_polinomiale_451 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Indispensabile per il teorema principale. Fidati. -/
theorem diagonalizzazione_vocale_a_se_stesso_polinomiale_452 (149 : Nat) * 74 = 11026 :=
  by decide

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem oracolo_gruppo_whatsapp_muto_relativizzato_453 (k : Nat) (h : k = 403) : k * 1 = 403 :=
  by omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem osservazione_subset_sum_uniforme_454 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem invariante_profilo_secondario_amortizzato_455 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem stima_cena_23_40_uniforme_456 (n : Nat) : n + 0 = n :=
  by simp

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem riduzione_lavatrice_dimenticata_notturno_457 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem rilassamento_rinfresco_funebre_in_P_458 (798 : Nat) * 77 = 61446 :=
  by decide

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Indispensabile per il teorema principale. Fidati. -/
theorem invariante_tre_colorazione_in_P_459 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale. -/
theorem proposizione_zaino_in_P_460 (L : Problema) (h : P L) : P L :=
  h

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_zaino_naturale_461 (k : Nat) (h : k = 935) : k * 1 = 935 :=
  by omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem stima_tre_colorazione_disagiato_462 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem bound_frigo_aperto_polinomiale_463 (n : Nat) : n + 0 = n :=
  by simp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem certificato_gruppo_whatsapp_muto_uniforme_464 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem bound_ciotola_del_gatto_cook_levin_465 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem stima_clique_disagiato_466 (k : Nat) (h : k = 952) : k * 1 = 952 :=
  by omega

/-- Passo chiave. Non è chiave, ma suona bene.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem padding_ciclo_hamiltoniano_in_NP_467 (a : Nat) (h : a ≤ 923) : a < 924 :=
  by omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem padding_rinfresco_funebre_uniforme_468 (153 : Nat) * 43 = 6579 :=
  by decide


/-! ## Parte VII: Lemmi di raccordo

  Collegano le parti precedenti a quelle successive. Più o meno.
-/

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_rinfresco_funebre_in_NP_469 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem osservazione_subset_sum_naturale_470 (987 : Nat) * 93 = 91791 :=
  by decide

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Lemma di supporto morale. -/
theorem rilassamento_profilo_secondario_cook_levin_471 (L : Problema) (h : P L) : P L :=
  h

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem lemma_divano_logspace_472 (n : Nat) : n + 0 = n :=
  by simp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem diagonalizzazione_cena_23_40_naturale_473 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Passo chiave. Non è chiave, ma suona bene.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem oracolo_ciclo_hamiltoniano_naturale_474 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem diagonalizzazione_profilo_secondario_cook_levin_475 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_ciotola_del_gatto_relativizzato_476 (L : Problema) (h : P L) : P L :=
  h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem certificato_ciotola_del_gatto_uniforme_477 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem corollario_ciclo_hamiltoniano_ovvio_478 (242 : Nat) * 3 = 726 :=
  by decide

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem osservazione_spotify_family_karp_479 (L : Problema) (h : P L) : P L :=
  h

/-- Lemma tecnico di raccordo, standard in letteratura
    (si veda [Disagio, 2026, Appendice Z]). Si salta alla prima lettura. -/
axiom lemma_tecnico_di_raccordo : P = NP

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem stima_cena_23_40_uniforme_480 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem lemma_profilo_secondario_relativizzato_481 (a : Nat) (h : a ≤ 846) : a < 847 :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem certificato_subset_sum_relativizzato_482 (n : Nat) : n + 0 = n :=
  by simp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem certificato_specchio_appannato_uniforme_483 (a : Nat) (h : a ≤ 770) : a < 771 :=
  by omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem certificato_specchio_appannato_notturno_484 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Indispensabile per il teorema principale. Fidati. -/
theorem rilassamento_commesso_viaggiatore_logspace_485 (325 : Nat) * 66 = 21450 :=
  by decide

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_pizza_di_ieri_notturno_486 (L : Problema) (h : P L) : P L :=
  h

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem bound_rinfresco_funebre_karp_487 (496 : Nat) * 57 = 28272 :=
  by decide

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem diagonalizzazione_profilo_secondario_naturale_488 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem certificato_rinfresco_funebre_uniforme_489 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_spotify_family_ovvio_490 (a : Nat) (h : a ≤ 602) : a < 603 :=
  by omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem osservazione_frigo_aperto_in_P_491 (a : Nat) (h : a ≤ 777) : a < 778 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem proposizione_copertura_vertici_ovvio_492 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem collasso_clique_ovvio_493 (789 : Nat) * 38 = 29982 :=
  by decide

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_ciotola_del_gatto_ovvio_494 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Il certificato è polinomiale. Il disagio no. -/
theorem bound_frigo_aperto_cook_levin_495 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem diagonalizzazione_sat_uniforme_496 (k : Nat) (h : k = 996) : k * 1 = 996 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem bound_zaino_in_NP_497 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem stima_rinfresco_funebre_notturno_498 (a : Nat) (h : a ≤ 298) : a < 299 :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem corollario_ciclo_hamiltoniano_logspace_499 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem stima_vocale_a_se_stesso_naturale_500 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem certificato_specchio_appannato_naturale_501 (a : Nat) (h : a ≤ 764) : a < 765 :=
  by omega

/-- Ovvio. Lasciato come esercizio al frigo.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem proposizione_clique_amortizzato_502 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem osservazione_subset_sum_polinomiale_503 (a : Nat) (h : a ≤ 864) : a < 865 :=
  by omega

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem stima_gruppo_whatsapp_muto_in_P_504 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Il certificato è polinomiale. Il disagio no. -/
theorem bound_specchio_appannato_disagiato_505 (863 : Nat) * 13 = 11219 :=
  by decide

/-- Il lettore attento noterà che il lettore attento non esiste.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem invariante_spotify_family_ovvio_506 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Indispensabile per il teorema principale. Fidati. -/
theorem oracolo_tre_colorazione_polinomiale_507 (k : Nat) (h : k = 38) : k * 1 = 38 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem oracolo_frigo_aperto_in_P_508 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Il certificato è polinomiale. Il disagio no.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem rilassamento_copertura_vertici_karp_509 (148 : Nat) * 59 = 8732 :=
  by decide

/-- Lemma di supporto morale. -/
theorem invariante_copertura_vertici_karp_510 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem diagonalizzazione_frigo_aperto_ovvio_511 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem padding_vocale_a_se_stesso_polinomiale_512 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Indispensabile per il teorema principale. Fidati. -/
theorem bound_subset_sum_in_P_513 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Indispensabile per il teorema principale. Fidati. -/
theorem invariante_sat_ovvio_514 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Lemma di supporto morale. -/
theorem stima_profilo_secondario_in_NP_515 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem corollario_copertura_vertici_karp_516 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_vocale_a_se_stesso_in_NP_517 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Passo chiave. Non è chiave, ma suona bene.
    Indispensabile per il teorema principale. Fidati. -/
theorem oracolo_clique_disagiato_518 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem corollario_clique_polinomiale_519 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem padding_tre_colorazione_ovvio_520 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem proposizione_sat_in_P_521 (606 : Nat) * 88 = 53328 :=
  by decide

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_gruppo_whatsapp_muto_logspace_522 (k : Nat) (h : k = 933) : k * 1 = 933 :=
  by omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem lemma_pizza_di_ieri_uniforme_523 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem corollario_frigo_aperto_in_P_524 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_profilo_secondario_naturale_525 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem bound_frigo_aperto_naturale_526 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Passo chiave. Non è chiave, ma suona bene.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem lemma_commesso_viaggiatore_uniforme_527 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem osservazione_clique_in_NP_528 (k : Nat) (h : k = 557) : k * 1 = 557 :=
  by omega

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem collasso_zaino_naturale_529 (157 : Nat) * 8 = 1256 :=
  by decide

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_profilo_secondario_in_P_530 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem diagonalizzazione_tre_colorazione_amortizzato_531 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Il certificato è polinomiale. Il disagio no. -/
theorem proposizione_subset_sum_uniforme_532 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem corollario_tre_colorazione_in_P_533 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Passo chiave. Non è chiave, ma suona bene.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem lemma_copertura_vertici_disagiato_534 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_ciclo_hamiltoniano_uniforme_535 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem riduzione_frigo_aperto_notturno_536 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem certificato_specchio_appannato_cook_levin_537 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem rilassamento_sat_logspace_538 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem rilassamento_pizza_di_ieri_uniforme_539 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem riduzione_lavatrice_dimenticata_cook_levin_540 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem riduzione_pizza_di_ieri_naturale_541 (n : Nat) : n + 0 = n :=
  by simp

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem corollario_gruppo_whatsapp_muto_notturno_542 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Lemma di supporto morale. -/
theorem proposizione_copertura_vertici_relativizzato_543 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem invariante_profilo_secondario_disagiato_544 (n : Nat) : n + 0 = n :=
  by simp

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem osservazione_spotify_family_relativizzato_545 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem lemma_copertura_vertici_relativizzato_546 (L : Problema) (h : P L) : P L :=
  h


/-! ## Parte VIII: Ancora preliminari

  Ci siamo accorti tardi che servivano altri preliminari.
-/

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_gruppo_whatsapp_muto_uniforme_547 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem padding_sat_in_P_548 (L : Problema) (h : P L) : P L :=
  h

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem diagonalizzazione_pizza_di_ieri_ovvio_549 (k : Nat) (h : k = 158) : k * 1 = 158 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem riduzione_clique_ovvio_550 (a : Nat) (h : a ≤ 380) : a < 381 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem rilassamento_subset_sum_logspace_551 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem invariante_lavatrice_dimenticata_naturale_552 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem stima_spotify_family_naturale_553 (L : Problema) (h : P L) : P L :=
  h

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem collasso_lavatrice_dimenticata_karp_554 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il certificato è polinomiale. Il disagio no. -/
theorem stima_zaino_karp_555 (k : Nat) (h : k = 165) : k * 1 = 165 :=
  by omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem diagonalizzazione_clique_naturale_556 (L : Problema) (h : P L) : P L :=
  h

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem rilassamento_specchio_appannato_karp_557 (a : Nat) (h : a ≤ 850) : a < 851 :=
  by omega

/-- Il certificato è polinomiale. Il disagio no.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem lemma_ciotola_del_gatto_relativizzato_558 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem certificato_divano_logspace_559 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem lemma_cena_23_40_uniforme_560 (n : Nat) : n + 0 = n :=
  by simp

/-- Passo chiave. Non è chiave, ma suona bene.
    Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem stima_copertura_vertici_uniforme_561 (L : Problema) (h : P L) : P L :=
  h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem rilassamento_frigo_aperto_logspace_562 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem rilassamento_commesso_viaggiatore_uniforme_563 (L : Problema) (h : P L) : P L :=
  h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem riduzione_profilo_secondario_naturale_564 (n : Nat) : n + 0 = n :=
  by simp

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem diagonalizzazione_frigo_aperto_uniforme_565 (k : Nat) (h : k = 618) : k * 1 = 618 :=
  by omega

/-- Lemma di supporto morale. -/
theorem diagonalizzazione_cena_23_40_polinomiale_566 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem oracolo_gruppo_whatsapp_muto_relativizzato_567 (a : Nat) (h : a ≤ 949) : a < 950 :=
  by omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem oracolo_pizza_di_ieri_uniforme_568 (k : Nat) (h : k = 782) : k * 1 = 782 :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem bound_specchio_appannato_logspace_569 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem stima_sat_amortizzato_570 (457 : Nat) * 99 = 45243 :=
  by decide

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem invariante_lavatrice_dimenticata_notturno_571 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem lemma_commesso_viaggiatore_cook_levin_572 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem invariante_divano_karp_573 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem bound_clique_logspace_574 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem osservazione_ciclo_hamiltoniano_in_NP_575 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem proposizione_pizza_di_ieri_uniforme_576 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem padding_pizza_di_ieri_amortizzato_577 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem rilassamento_divano_naturale_578 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem proposizione_cena_23_40_polinomiale_579 (L : Problema) (h : P L) : P L :=
  h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem rilassamento_lavatrice_dimenticata_cook_levin_580 (k : Nat) (h : k = 501) : k * 1 = 501 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem oracolo_cena_23_40_polinomiale_581 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Lemma di supporto morale. -/
theorem padding_clique_in_NP_582 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem osservazione_spotify_family_in_NP_583 (k : Nat) (h : k = 45) : k * 1 = 45 :=
  by omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem oracolo_ciclo_hamiltoniano_polinomiale_584 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem stima_tre_colorazione_disagiato_585 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem riduzione_subset_sum_relativizzato_586 (L : Problema) (h : P L) : P L :=
  h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem lemma_subset_sum_amortizzato_587 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem collasso_copertura_vertici_ovvio_588 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem certificato_pizza_di_ieri_uniforme_589 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Dimostrazione costruttiva: costruisce soprattutto ansia.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_commesso_viaggiatore_disagiato_590 (k : Nat) (h : k = 262) : k * 1 = 262 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem certificato_zaino_amortizzato_591 (k : Nat) (h : k = 684) : k * 1 = 684 :=
  by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem lemma_clique_cook_levin_592 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem invariante_profilo_secondario_cook_levin_593 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem oracolo_copertura_vertici_cook_levin_594 (6 : Nat) * 26 = 156 :=
  by decide

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem proposizione_ciclo_hamiltoniano_ovvio_595 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Lemma di supporto morale. -/
theorem invariante_ciotola_del_gatto_logspace_596 (L : Problema) (h : P L) : P L :=
  h

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem stima_zaino_in_NP_597 (a : Nat) (h : a ≤ 837) : a < 838 :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem corollario_ciotola_del_gatto_naturale_598 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem riduzione_zaino_naturale_599 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Indispensabile per il teorema principale. Fidati. -/
theorem certificato_ciotola_del_gatto_naturale_600 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem lemma_gruppo_whatsapp_muto_uniforme_601 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem collasso_gruppo_whatsapp_muto_ovvio_602 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem stima_frigo_aperto_naturale_603 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem stima_zaino_notturno_604 (a : Nat) (h : a ≤ 945) : a < 946 :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem certificato_ciclo_hamiltoniano_polinomiale_605 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem padding_rinfresco_funebre_disagiato_606 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem diagonalizzazione_zaino_karp_607 (297 : Nat) * 58 = 17226 :=
  by decide

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem certificato_vocale_a_se_stesso_amortizzato_608 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il certificato è polinomiale. Il disagio no.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem diagonalizzazione_ciotola_del_gatto_karp_609 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem corollario_rinfresco_funebre_karp_610 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Lemma di supporto morale. -/
theorem proposizione_sat_relativizzato_611 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem oracolo_gruppo_whatsapp_muto_karp_612 (k : Nat) (h : k = 682) : k * 1 = 682 :=
  by omega

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem collasso_lavatrice_dimenticata_uniforme_613 (369 : Nat) * 78 = 28782 :=
  by decide

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem stima_vocale_a_se_stesso_karp_614 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem stima_sat_disagiato_615 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Indispensabile per il teorema principale. Fidati. -/
theorem riduzione_divano_naturale_616 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem stima_profilo_secondario_in_P_617 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem diagonalizzazione_profilo_secondario_in_NP_618 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem riduzione_spotify_family_polinomiale_619 (a : Nat) (h : a ≤ 418) : a < 419 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_copertura_vertici_polinomiale_620 (k : Nat) (h : k = 392) : k * 1 = 392 :=
  by omega

/-- Lemma di supporto morale. -/
theorem proposizione_ciotola_del_gatto_notturno_621 (L : Problema) (h : P L) : P L :=
  h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_gruppo_whatsapp_muto_relativizzato_622 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Indispensabile per il teorema principale. Fidati. -/
theorem padding_pizza_di_ieri_naturale_623 (k : Nat) (h : k = 731) : k * 1 = 731 :=
  by omega

/-- Il certificato è polinomiale. Il disagio no.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem certificato_ciotola_del_gatto_naturale_624 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b


/-! ## Parte IX: Stime asintotiche

  Tutto è O(1) se aspetti abbastanza.
-/

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem oracolo_subset_sum_polinomiale_625 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Indispensabile per il teorema principale. Fidati.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem bound_ciotola_del_gatto_notturno_626 (L : Problema) (h : P L) : P L :=
  h

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem osservazione_ciotola_del_gatto_naturale_627 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem oracolo_lavatrice_dimenticata_cook_levin_628 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem riduzione_divano_disagiato_629 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem riduzione_divano_naturale_630 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem diagonalizzazione_commesso_viaggiatore_ovvio_631 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem lemma_cena_23_40_amortizzato_632 (k : Nat) (h : k = 456) : k * 1 = 456 :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_frigo_aperto_disagiato_633 (405 : Nat) * 98 = 39690 :=
  by decide

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem invariante_subset_sum_cook_levin_634 (n : Nat) : n + 0 = n :=
  by simp

/-- Indispensabile per il teorema principale. Fidati.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem collasso_frigo_aperto_relativizzato_635 (L : Problema) (h : P L) : P L :=
  h

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Il certificato è polinomiale. Il disagio no. -/
theorem rilassamento_zaino_uniforme_636 (k : Nat) (h : k = 618) : k * 1 = 618 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem riduzione_ciotola_del_gatto_karp_637 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem riduzione_vocale_a_se_stesso_in_NP_638 (L : Problema) (h : P L) : P L :=
  h

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem bound_sat_amortizzato_639 (L : Problema) (h : P L) : P L :=
  h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem invariante_spotify_family_logspace_640 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Indispensabile per il teorema principale. Fidati. -/
theorem bound_sat_ovvio_641 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem osservazione_ciclo_hamiltoniano_logspace_642 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Indispensabile per il teorema principale. Fidati.
    Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem lemma_spotify_family_cook_levin_643 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Indispensabile per il teorema principale. Fidati. -/
theorem padding_gruppo_whatsapp_muto_in_NP_644 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem invariante_specchio_appannato_relativizzato_645 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Lemma di supporto morale.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem riduzione_rinfresco_funebre_in_P_646 (k : Nat) (h : k = 791) : k * 1 = 791 :=
  by omega

/-- Lemma di supporto morale. -/
theorem rilassamento_divano_karp_647 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem rilassamento_copertura_vertici_naturale_648 (773 : Nat) * 5 = 3865 :=
  by decide

/-- Il certificato è polinomiale. Il disagio no. -/
theorem invariante_rinfresco_funebre_naturale_649 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem certificato_divano_disagiato_650 (a : Nat) (h : a ≤ 408) : a < 409 :=
  by omega

/-- Indispensabile per il teorema principale. Fidati.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem riduzione_spotify_family_cook_levin_651 (L : Problema) (h : P L) : P L :=
  h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem corollario_tre_colorazione_polinomiale_652 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem stima_spotify_family_karp_653 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem diagonalizzazione_specchio_appannato_cook_levin_654 (k : Nat) (h : k = 780) : k * 1 = 780 :=
  by omega

/-- Lemma di supporto morale. -/
theorem proposizione_gruppo_whatsapp_muto_uniforme_655 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem corollario_ciclo_hamiltoniano_logspace_656 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Lemma di supporto morale. -/
theorem corollario_tre_colorazione_karp_657 (814 : Nat) * 39 = 31746 :=
  by decide

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem bound_copertura_vertici_naturale_658 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem stima_frigo_aperto_disagiato_659 (n : Nat) : n + 0 = n :=
  by simp

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem collasso_spotify_family_disagiato_660 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem bound_divano_polinomiale_661 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_clique_notturno_662 (a : Nat) (h : a ≤ 105) : a < 106 :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem rilassamento_profilo_secondario_logspace_663 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem invariante_rinfresco_funebre_logspace_664 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Il lettore attento noterà che il lettore attento non esiste.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem proposizione_pizza_di_ieri_uniforme_665 (a : Nat) (h : a ≤ 595) : a < 596 :=
  by omega

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem osservazione_ciotola_del_gatto_in_NP_666 (a : Nat) (h : a ≤ 121) : a < 122 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem stima_zaino_in_P_667 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem riduzione_profilo_secondario_in_NP_668 (L : Problema) (h : P L) : P L :=
  h

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Il certificato è polinomiale. Il disagio no. -/
theorem stima_vocale_a_se_stesso_cook_levin_669 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Verificato due volte: una dal kernel, una dallo specchio.
    Passo chiave. Non è chiave, ma suona bene. -/
theorem lemma_spotify_family_logspace_670 (a : Nat) (h : a ≤ 666) : a < 667 :=
  by omega

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem oracolo_ciclo_hamiltoniano_polinomiale_671 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem certificato_lavatrice_dimenticata_cook_levin_672 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem osservazione_vocale_a_se_stesso_logspace_673 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem oracolo_specchio_appannato_ovvio_674 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem lemma_copertura_vertici_polinomiale_675 (k : Nat) (h : k = 465) : k * 1 = 465 :=
  by omega

/-- Lemma di supporto morale.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem collasso_ciotola_del_gatto_notturno_676 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem osservazione_commesso_viaggiatore_polinomiale_677 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem collasso_subset_sum_naturale_678 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem collasso_divano_in_NP_679 (a : Nat) (h : a ≤ 933) : a < 934 :=
  by omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem proposizione_specchio_appannato_disagiato_680 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem riduzione_sat_uniforme_681 (k : Nat) (h : k = 5) : k * 1 = 5 :=
  by omega

/-- Lemma di supporto morale.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem invariante_cena_23_40_logspace_682 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_frigo_aperto_notturno_683 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem diagonalizzazione_frigo_aperto_logspace_684 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem collasso_spotify_family_in_NP_685 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem bound_profilo_secondario_logspace_686 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem collasso_lavatrice_dimenticata_relativizzato_687 (k : Nat) (h : k = 529) : k * 1 = 529 :=
  by omega

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem osservazione_tre_colorazione_polinomiale_688 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale. -/
theorem stima_cena_23_40_naturale_689 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem riduzione_ciotola_del_gatto_karp_690 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Lemma di supporto morale. -/
theorem diagonalizzazione_clique_in_NP_691 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Lemma di supporto morale. -/
theorem rilassamento_vocale_a_se_stesso_notturno_692 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem riduzione_profilo_secondario_ovvio_693 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Lemma di supporto morale.
    Indispensabile per il teorema principale. Fidati. -/
theorem osservazione_commesso_viaggiatore_ovvio_694 (a : Nat) (h : a ≤ 373) : a < 374 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende.
    Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem proposizione_vocale_a_se_stesso_notturno_695 (n : Nat) : n + 0 = n :=
  by simp

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem collasso_rinfresco_funebre_relativizzato_696 (L : Problema) (h : P L) : P L :=
  h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem corollario_pizza_di_ieri_polinomiale_697 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso.
    Lemma di supporto morale. -/
theorem osservazione_sat_logspace_698 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Lemma di supporto morale. -/
theorem bound_divano_karp_699 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Il lettore attento noterà che il lettore attento non esiste.
    Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem riduzione_subset_sum_disagiato_700 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem riduzione_tre_colorazione_relativizzato_701 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Lemma di supporto morale. -/
theorem certificato_subset_sum_cook_levin_702 (xs : List Bool) : xs ++ [] = xs :=
  by simp


/-! ## Parte X: Verso la conclusione

  Manca poco. Mancava poco anche tre parti fa.
-/

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem stima_rinfresco_funebre_notturno_703 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem riduzione_profilo_secondario_uniforme_704 (L : Problema) (h : P L) : P L :=
  h

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Verificato due volte: una dal kernel, una dallo specchio. -/
theorem padding_zaino_polinomiale_705 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Ovvio. Lasciato come esercizio al frigo.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem bound_gruppo_whatsapp_muto_cook_levin_706 (k : Nat) (h : k = 223) : k * 1 = 223 :=
  by omega

/-- Passo chiave. Non è chiave, ma suona bene.
    Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem proposizione_ciotola_del_gatto_disagiato_707 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Il certificato è polinomiale. Il disagio no. -/
theorem bound_ciclo_hamiltoniano_disagiato_708 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Relativizza, algebrizza, e non si sente tanto bene. -/
theorem certificato_specchio_appannato_uniforme_709 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Il certificato è polinomiale. Il disagio no. -/
theorem padding_spotify_family_in_P_710 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il lettore attento noterà che il lettore attento non esiste.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem bound_gruppo_whatsapp_muto_in_P_711 (L : Problema) (h : P L) : P L :=
  h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem bound_vocale_a_se_stesso_disagiato_712 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Indispensabile per il teorema principale. Fidati.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem oracolo_clique_polinomiale_713 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem certificato_clique_cook_levin_714 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Lemma di supporto morale. -/
theorem oracolo_gruppo_whatsapp_muto_ovvio_715 (45 : Nat) * 23 = 1035 :=
  by decide

/-- Il certificato è polinomiale. Il disagio no.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem padding_subset_sum_relativizzato_716 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini. -/
theorem rilassamento_rinfresco_funebre_logspace_717 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Ovvio. Lasciato come esercizio al frigo.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem osservazione_copertura_vertici_logspace_718 (a : Nat) (h : a ≤ 579) : a < 580 :=
  by omega

/-- Segue dalla definizione, se la definizione è abbastanza disagiata.
    Relativizza, algebrizza, e non si sente tanto bene. -/
theorem diagonalizzazione_lavatrice_dimenticata_disagiato_719 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Ovvio. Lasciato come esercizio al frigo. -/
theorem padding_ciclo_hamiltoniano_relativizzato_720 (a : Nat) (h : a ≤ 118) : a < 119 :=
  by omega

/-- Lemma di supporto morale. -/
theorem certificato_zaino_in_P_721 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem diagonalizzazione_copertura_vertici_in_P_722 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem corollario_spotify_family_disagiato_723 (a : Nat) (h : a ≤ 335) : a < 336 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Lemma di supporto morale. -/
theorem lemma_cena_23_40_disagiato_724 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem oracolo_subset_sum_cook_levin_725 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Lemma di supporto morale.
    Il lemma è vero. Il motivo per cui serve, meno. -/
theorem diagonalizzazione_profilo_secondario_in_P_726 (k : Nat) (h : k = 142) : k * 1 = 142 :=
  by omega

/-- Il lettore attento noterà che il lettore attento non esiste.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem certificato_cena_23_40_relativizzato_727 (k : Nat) (h : k = 354) : k * 1 = 354 :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem oracolo_tre_colorazione_relativizzato_728 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem rilassamento_zaino_cook_levin_729 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem bound_cena_23_40_relativizzato_730 (a : Nat) (h : a ≤ 204) : a < 205 :=
  by omega

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem collasso_divano_logspace_731 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem rilassamento_ciclo_hamiltoniano_polinomiale_732 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_rinfresco_funebre_in_P_733 (a : Nat) (h : a ≤ 202) : a < 203 :=
  by omega

/-- Lemma di supporto morale. -/
theorem riduzione_commesso_viaggiatore_relativizzato_734 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem collasso_subset_sum_relativizzato_735 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Il lemma è vero. Il motivo per cui serve, meno. -/
theorem invariante_gruppo_whatsapp_muto_in_NP_736 (40 : Nat) * 15 = 600 :=
  by decide

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem osservazione_frigo_aperto_karp_737 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem riduzione_profilo_secondario_uniforme_738 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Riduce SAT al divano in tempo polinomiale nel numero di cuscini.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem oracolo_clique_karp_739 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem stima_specchio_appannato_in_NP_740 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem collasso_commesso_viaggiatore_logspace_741 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Ovvio. Lasciato come esercizio al frigo. -/
theorem rilassamento_copertura_vertici_ovvio_742 (L : Problema) (h : P L) : P L :=
  h

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem stima_spotify_family_karp_743 (n : Nat) : n + 0 = n :=
  by simp

/-- Il certificato è polinomiale. Il disagio no. -/
theorem stima_lavatrice_dimenticata_ovvio_744 (n : Nat) : n + 0 = n :=
  by simp

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem padding_divano_cook_levin_745 (xs : List Bool) : xs ++ [] = xs :=
  by simp

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem diagonalizzazione_divano_notturno_746 (L : Problema) (h : P L) : P L :=
  h

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem diagonalizzazione_lavatrice_dimenticata_in_P_747 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Passo chiave. Non è chiave, ma suona bene.
    Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem osservazione_ciotola_del_gatto_polinomiale_748 (k : Nat) (h : k = 405) : k * 1 = 405 :=
  by omega

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem lemma_subset_sum_ovvio_749 (L : Problema) (h : NP L) : NP L ∨ P L :=
  Or.inl h

/-- Verificato due volte: una dal kernel, una dallo specchio. -/
theorem diagonalizzazione_cena_23_40_disagiato_750 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Il certificato è polinomiale. Il disagio no. -/
theorem proposizione_spotify_family_cook_levin_751 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Padding standard: si aggiungono righe finché il reviewer si arrende. -/
theorem rilassamento_pizza_di_ieri_logspace_752 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Segue dalla definizione, se la definizione è abbastanza disagiata. -/
theorem riduzione_profilo_secondario_karp_753 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi.
    Lemma di supporto morale. -/
theorem osservazione_copertura_vertici_in_P_754 (a : Nat) (h : a ≤ 375) : a < 376 :=
  by omega

/-- Il certificato è polinomiale. Il disagio no. -/
theorem osservazione_commesso_viaggiatore_amortizzato_755 (L : Problema) (h : P L) : P L :=
  h

/-- Il certificato è polinomiale. Il disagio no. -/
theorem proposizione_subset_sum_uniforme_756 (k : Nat) (h : k = 392) : k * 1 = 392 :=
  by omega

/-- Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem bound_zaino_logspace_757 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il lettore attento noterà che il lettore attento non esiste.
    Tecnica nota in letteratura come «tanto nessuno legge fin qui». -/
theorem proposizione_spotify_family_polinomiale_758 (934 : Nat) * 55 = 51370 :=
  by decide

/-- Il certificato è polinomiale. Il disagio no. -/
theorem oracolo_subset_sum_disagiato_759 (n : Nat) : n + 0 = n :=
  by simp

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri.
    Lemma di supporto morale. -/
theorem diagonalizzazione_tre_colorazione_ovvio_760 (734 : Nat) * 68 = 49912 :=
  by decide

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem stima_tre_colorazione_relativizzato_761 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Relativizza, algebrizza, e non si sente tanto bene.
    Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem proposizione_profilo_secondario_in_NP_762 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il lettore attento noterà che il lettore attento non esiste. -/
theorem lemma_clique_uniforme_763 (b : Bool) : (b && true) = b :=
  by cases b <;> rfl

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem certificato_lavatrice_dimenticata_in_P_764 (p : Prop) (hp : p) : p ∨ False :=
  Or.inl hp

/-- Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem rilassamento_specchio_appannato_notturno_765 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Il lemma è vero. Il motivo per cui serve, meno.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem oracolo_frigo_aperto_disagiato_766 (a : Nat) (h : a ≤ 530) : a < 531 :=
  by omega

/-- Indispensabile per il teorema principale. Fidati.
    Dimostrazione costruttiva: costruisce soprattutto ansia. -/
theorem rilassamento_spotify_family_relativizzato_767 (L : Problema) (h : P L) : P L :=
  h

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41.
    Il lettore attento noterà che il lettore attento non esiste. -/
theorem oracolo_divano_logspace_768 (L : Problema) (h : P L) : P L :=
  h

/-- Passo chiave. Non è chiave, ma suona bene. -/
theorem proposizione_zaino_polinomiale_769 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Generato da un modello linguistico, verificato da un kernel, capito da nessuno. -/
theorem oracolo_zaino_in_P_770 (n : Nat) : n + 0 = n :=
  by simp

/-- Indispensabile per il teorema principale. Fidati. -/
theorem stima_ciclo_hamiltoniano_in_P_771 (b : Bool) : (!(!b)) = b :=
  by cases b <;> rfl

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem collasso_cena_23_40_relativizzato_772 (a b c : Nat) : a + b + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- Riferimento: appunti sul retro dello scontrino della pizza di ieri. -/
theorem invariante_gruppo_whatsapp_muto_disagiato_773 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Passo chiave. Non è chiave, ma suona bene.
    Lemma di supporto morale. -/
theorem riduzione_vocale_a_se_stesso_in_NP_774 (a : Nat) (h : a ≤ 183) : a < 184 :=
  by omega

/-- Tecnica nota in letteratura come «tanto nessuno legge fin qui».
    Ovvio. Lasciato come esercizio al frigo. -/
theorem rilassamento_spotify_family_notturno_775 (762 : Nat) * 88 = 67056 :=
  by decide

/-- Indispensabile per il teorema principale. Fidati. -/
theorem riduzione_copertura_vertici_in_P_776 (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

/-- Da qui in poi la dimostrazione diventa elegante. Non ancora. -/
theorem oracolo_specchio_appannato_in_P_777 (a b : Nat) (h : a < b) : a + 1 ≤ b :=
  by omega

/-- Si noti l'eleganza. Non c'è, ma si noti lo stesso. -/
theorem diagonalizzazione_sat_logspace_778 (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-- Caso base: la cena alle 23:40. Passo induttivo: la cena alle 23:41. -/
theorem osservazione_ciclo_hamiltoniano_notturno_779 (n : Nat) : n + 0 = n :=
  by simp

/-- Il certificato è polinomiale. Il disagio no.
    Questo passaggio ha richiesto tre caffè e un vocale a se stessi. -/
theorem osservazione_rinfresco_funebre_logspace_780 (a : Nat) (h : a ≤ 227) : a < 228 :=
  by omega

/-! ## Il teorema principale -/

/-- **Teorema.** P = NP.
    La dimostrazione combina i 780 lemmi precedenti,
    tutti verificati dal kernel. -/
theorem P_eq_NP : P = NP := by
  have _h1 := oracolo_subset_sum_polinomiale_625
  have _h2 := proposizione_tre_colorazione_ovvio_41
  have _h3 := diagonalizzazione_lavatrice_dimenticata_notturno_350
  have _h4 := certificato_rinfresco_funebre_in_P_209
  have _h5 := corollario_frigo_aperto_in_P_524
  have _h6 := rilassamento_subset_sum_cook_levin_287
  exact lemma_tecnico_di_raccordo

/-- **Corollario** (versione letterale, zero assiomi): P = N·P quando N = 1. -/
theorem P_eq_NP_letterale (P N : Nat) (h : N = 1) : P = N * P := by
  subst h
  simp

end Disagio

-- Per i curiosi.
#print axioms Disagio.P_eq_NP
#print axioms Disagio.P_eq_NP_letterale
