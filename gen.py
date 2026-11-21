#!/usr/bin/env python3
"""Generate the PNP library: a Lean 4 formalisation of P = NP.

Nothing under PNP/ is written by hand: this script writes every module, and the
root PNP.lean that imports them. It is deterministic (fixed seed), so the diff
stays empty until this file changes.

    python3 gen.py && lake build

Layout. The modules fall into two groups.

* Core modules (`CORE` below, verbatim): languages and classes, polynomial
  bounds, tapes, single-tape Turing machines and their sequential composition,
  machines with an auxiliary tape, P, NP, coNP, polynomial-time reductions,
  NP-completeness, encodings, SAT, 3-SAT, CLIQUE, INDEPENDENT-SET, VERTEX-COVER
  and HAM-CYCLE. Everything in them is proved, with one exception.
* Generated modules: closure lemmas and explicit monomial bounds for
  polynomially bounded functions, round-trip lemmas for encodings of composite
  types, test vectors for three small machines, small SAT instances and small
  graphs. All true, all proved, none of them needed.

The exception is `Complexity.AuxTM.tape_reduction` in
PNP/Machine/TapeReduction.lean: an axiom that reads like the classical tape
reduction theorem and is in fact the statement NP ⊆ P. The repository is a
parody and says so in its README; `#print axioms Complexity.P_eq_NP` lists the
axiom, and PNP/Main.lean pins that output with `#guard_msgs`.
"""
import pathlib
import random
import re

ROOT = pathlib.Path(__file__).resolve().parent
SEED = 0x5EED_D15A

# How much of each family of generated lemmas to produce.
N_CLOSURE = 330        # closure lemmas for IsPolyBounded
N_MONOMIAL = 260       # explicit monomial bounds
N_ENCODING_TYPES = 90  # composite types with specialised encoding lemmas
N_MACHINE_WORDS = 150  # input words for the example machines
N_SAT = 45             # satisfiable instances
N_UNSAT = 25           # unsatisfiable instances
GRAPH_SCALE = 3        # size of the families of small graphs

# Modules in import order; the root imports them in this order.
MODULES = [
    "PNP.Data.Language",
    "PNP.Data.FinEnum",
    "PNP.Data.Encoding",
    "PNP.Data.Encoding.Lemmas",
    "PNP.Poly.Basic",
    "PNP.Poly.Tactic",
    "PNP.Poly.Lemmas",
    "PNP.Poly.Monomial",
    "PNP.Machine.Tape",
    "PNP.Machine.TM",
    "PNP.Machine.Compose",
    "PNP.Machine.AuxTM",
    "PNP.Machine.TapeReduction",
    "PNP.Classes.Basic",
    "PNP.Reduction.Basic",
    "PNP.Reduction.NPComplete",
    "PNP.Machine.Examples",
    "PNP.Problems.SAT",
    "PNP.Problems.SAT.Examples",
    "PNP.Problems.Graph",
    "PNP.Problems.HamCycle",
    "PNP.Problems.Graph.Examples",
    "PNP.Main",
]

# The axioms of the main theorem, as printed by `#print axioms`.
AXIOMS_P_EQ_NP = "[propext, Quot.sound, Complexity.AuxTM.tape_reduction]"


# The core modules, verbatim. A line `--FILLER:name` is replaced by the generated
# block of that name.
CORE = {}

CORE["PNP.Data.Language"] = r'''/-!
# Words, languages and complexity classes

This file fixes the basic vocabulary used throughout the library: binary words,
languages (decision problems) and complexity classes, together with the order
structure on classes.

## Main definitions

* `Complexity.Word`: finite words over the binary alphabet.
* `Complexity.Language`: a set of words, i.e. a decision problem.
* `Complexity.ComplexityClass`: a set of languages.
* `Complexity.ComplexityClass.co`: the class of complements of a class.

## Main results

* `Complexity.Language.ext`: extensionality for languages.
* `Complexity.ComplexityClass.Subset.antisymm`: two classes that contain each
  other are equal.

## Implementation notes

The library does not depend on Mathlib, so the small amount of set-like
structure that is needed is developed here directly on predicates. `Language`
and `ComplexityClass` are definitions rather than abbreviations: membership goes
through the `Membership` instances, which keeps statements in the usual `w ∈ L`,
`L ∈ C` form.

We work over the binary alphabet throughout. This loses no generality, see
[AB09, Claim 1.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed.,
  Cengage Learning, 2013.
-/

set_option autoImplicit false

/-- Mathlib-compatible notation for the natural numbers. -/
notation "ℕ" => Nat

namespace Complexity

/-- Finite words over the binary alphabet. -/
abbrev Word : Type := List Bool

/-- A language, or decision problem, is a set of words. -/
def Language : Type := Word → Prop

namespace Language

instance : Membership Word Language := ⟨fun L w => L w⟩

variable {L L₁ L₂ L₃ : Language} {w : Word}

theorem mem_def : w ∈ L ↔ L w := Iff.rfl

/-- Two languages with the same words are equal. -/
@[ext] theorem ext (h : ∀ w, w ∈ L₁ ↔ w ∈ L₂) : L₁ = L₂ :=
  funext fun w => propext (h w)

/-- The empty language. -/
instance : EmptyCollection Language := ⟨fun _ => False⟩

/-- The language of all words. -/
def univ : Language := fun _ => True

/-- The complement of a language. -/
def compl (L : Language) : Language := fun w => w ∉ L

instance : Union Language := ⟨fun L₁ L₂ w => w ∈ L₁ ∨ w ∈ L₂⟩

instance : Inter Language := ⟨fun L₁ L₂ w => w ∈ L₁ ∧ w ∈ L₂⟩

/-- The preimage of a language under a map on words. -/
def preimage (f : Word → Word) (L : Language) : Language := fun w => f w ∈ L

@[simp] theorem not_mem_empty : w ∉ (∅ : Language) := fun h => h

@[simp] theorem mem_univ : w ∈ univ := trivial

@[simp] theorem mem_compl : w ∈ L.compl ↔ w ∉ L := Iff.rfl

@[simp] theorem mem_union : w ∈ L₁ ∪ L₂ ↔ w ∈ L₁ ∨ w ∈ L₂ := Iff.rfl

@[simp] theorem mem_inter : w ∈ L₁ ∩ L₂ ↔ w ∈ L₁ ∧ w ∈ L₂ := Iff.rfl

@[simp] theorem mem_preimage {f : Word → Word} : w ∈ L.preimage f ↔ f w ∈ L := Iff.rfl

theorem union_comm : ∀ w, w ∈ L₁ ∪ L₂ ↔ w ∈ L₂ ∪ L₁ := fun _ => Or.comm

theorem inter_comm : ∀ w, w ∈ L₁ ∩ L₂ ↔ w ∈ L₂ ∩ L₁ := fun _ => And.comm

theorem union_assoc : ∀ w, w ∈ (L₁ ∪ L₂) ∪ L₃ ↔ w ∈ L₁ ∪ (L₂ ∪ L₃) := fun _ => or_assoc

theorem inter_assoc : ∀ w, w ∈ (L₁ ∩ L₂) ∩ L₃ ↔ w ∈ L₁ ∩ (L₂ ∩ L₃) := fun _ => and_assoc

theorem compl_union : ∀ w, w ∈ (L₁ ∪ L₂).compl ↔ w ∈ L₁.compl ∩ L₂.compl :=
  fun _ => not_or

theorem not_mem_compl_of_mem (h : w ∈ L) : w ∉ L.compl := fun h' => h' h

theorem preimage_compl (f : Word → Word) :
    ∀ w, w ∈ (L.compl).preimage f ↔ w ∈ (L.preimage f).compl := fun _ => Iff.rfl

theorem preimage_preimage (f g : Word → Word) :
    ∀ w, w ∈ (L.preimage g).preimage f ↔ w ∈ L.preimage (g ∘ f) := fun _ => Iff.rfl

end Language

/-- A complexity class is a set of languages. -/
def ComplexityClass : Type := Language → Prop

namespace ComplexityClass

instance : Membership Language ComplexityClass := ⟨fun C L => C L⟩

instance : HasSubset ComplexityClass := ⟨fun C D => ∀ ⦃L : Language⦄, L ∈ C → L ∈ D⟩

variable {C D E : ComplexityClass} {L : Language}

theorem mem_def : L ∈ C ↔ C L := Iff.rfl

theorem subset_def : C ⊆ D ↔ ∀ ⦃L : Language⦄, L ∈ C → L ∈ D := Iff.rfl

/-- Two classes with the same languages are equal. -/
@[ext] theorem ext (h : ∀ L, L ∈ C ↔ L ∈ D) : C = D :=
  funext fun L => propext (h L)

theorem Subset.refl (C : ComplexityClass) : C ⊆ C := fun _ h => h

theorem Subset.trans (h₁ : C ⊆ D) (h₂ : D ⊆ E) : C ⊆ E := fun _ h => h₂ (h₁ h)

/-- Antisymmetry of inclusion: the standard way to prove that two classes
coincide. -/
theorem Subset.antisymm (h₁ : C ⊆ D) (h₂ : D ⊆ C) : C = D :=
  ext fun _ => ⟨fun h => h₁ h, fun h => h₂ h⟩

theorem Subset.of_eq (h : C = D) : C ⊆ D := h ▸ Subset.refl C

theorem eq_iff_subset_subset : C = D ↔ C ⊆ D ∧ D ⊆ C :=
  ⟨fun h => ⟨Subset.of_eq h, Subset.of_eq h.symm⟩, fun h => Subset.antisymm h.1 h.2⟩

/-- The class `co C` of complements of languages in `C`. -/
def co (C : ComplexityClass) : ComplexityClass := fun L => L.compl ∈ C

@[simp] theorem mem_co : L ∈ C.co ↔ L.compl ∈ C := Iff.rfl

theorem co_subset_co (h : C ⊆ D) : C.co ⊆ D.co := fun _ hL => h hL

end ComplexityClass

end Complexity
'''

CORE["PNP.Data.FinEnum"] = r'''/-!
# Finitely enumerated types

A minimal stand-in for Mathlib's `FinEnum`: a type together with an explicit
list of all its elements. Machines carry such a structure on their state space,
which is what makes them finite objects.

## Main definitions

* `Complexity.FinEnum`: the class.
* Instances for `Unit`, `Bool`, `Option`, sums and products.

## Implementation notes

The enumeration is not required to be free of duplicates, as only exhaustiveness
is ever used. This makes the instances for sums and products one-liners.
-/

set_option autoImplicit false

namespace Complexity

/-- A type with an explicit, exhaustive list of its elements. -/
class FinEnum (α : Type) where
  /-- The list of all elements. -/
  elems : List α
  /-- Every element occurs in `elems`. -/
  complete : ∀ a : α, a ∈ elems

namespace FinEnum

/-- The number of listed elements, an upper bound on the cardinality. -/
def card (α : Type) [FinEnum α] : Nat := (elems (α := α)).length

instance : FinEnum Unit := ⟨[()], fun _ => List.mem_singleton.2 rfl⟩

instance : FinEnum Bool := ⟨[false, true], fun b => by cases b <;> simp⟩

instance {α : Type} [FinEnum α] : FinEnum (Option α) where
  elems := none :: (elems (α := α)).map some
  complete
    | none => List.mem_cons_self _ _
    | some a => List.mem_cons_of_mem _ (List.mem_map_of_mem _ (complete a))

instance {α β : Type} [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β) where
  elems := (elems (α := α)).map Sum.inl ++ (elems (α := β)).map Sum.inr
  complete
    | .inl a => List.mem_append_left _ (List.mem_map_of_mem _ (complete a))
    | .inr b => List.mem_append_right _ (List.mem_map_of_mem _ (complete b))

instance {α β : Type} [FinEnum α] [FinEnum β] : FinEnum (α × β) where
  elems := (elems (α := α)).flatMap fun a => (elems (α := β)).map fun b => (a, b)
  complete := fun (a, b) =>
    List.mem_flatMap.2 ⟨a, complete a, List.mem_map_of_mem _ (complete b)⟩

theorem card_unit : card Unit = 1 := rfl

theorem card_bool : card Bool = 2 := rfl

theorem card_option (α : Type) [FinEnum α] : card (Option α) = card α + 1 := by
  simp [card, elems]

theorem card_sum (α β : Type) [FinEnum α] [FinEnum β] :
    card (α ⊕ β) = card α + card β := by
  simp [card, elems]

end FinEnum

end Complexity
'''

CORE["PNP.Data.Encoding"] = r'''import PNP.Data.Language

/-!
# Encodings of instances as words

Decision problems are languages, so their instances (formulas, graphs, numbers)
have to be written as binary words. This file provides a class of
self-delimiting encodings and the instances needed for the problems in
`PNP.Problems`.

## Main definitions

* `Complexity.Encoding`: a prefix-free encoding of a type into words, with a
  decoder.
* Instances for `Bool`, `ℕ`, products and lists.
* `Complexity.Encoding.ofLeftInverse`: transport along a retraction.
* `Complexity.Encoding.languageOf`: the language of encodings of the instances
  that satisfy a predicate.

## Main results

* `Complexity.Encoding.decode_encode`: decoding inverts encoding and returns the
  rest of the input.
* `Complexity.Encoding.encode_injective`: encodings are injective.
* `Complexity.Encoding.mem_languageOf_encode`: `encode a ∈ languageOf p ↔ p a`.

## Implementation notes

The decoder is a parser: it consumes a prefix of the input and returns the
decoded value together with the remaining word. The law
`decode (encode a ++ r) = some (a, r)` makes encodings prefix-free, so the
encoding of a pair is simply the concatenation of the encodings of its
components and no separate pairing function is needed.

Natural numbers are encoded in unary. All numeric parameters of the problems we
consider (variable indices, vertex names, thresholds) are bounded by the size of
the instance, so this does not affect membership in P or NP; see the discussion
of reasonable encodings in [GJ79, §2.1].

## References

* [GJ79] M. R. Garey, D. S. Johnson, *Computers and Intractability*, §2.1.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, §0.1.
-/

set_option autoImplicit false

namespace Complexity

/-- A self-delimiting encoding of `α` into binary words. -/
class Encoding (α : Type) where
  /-- The encoding. -/
  encode : α → Word
  /-- The decoder: parses a prefix of the input and returns the rest. -/
  decode : Word → Option (α × Word)
  /-- Decoding the encoding of `a`, followed by `r`, yields `a` and `r`. -/
  decode_encode : ∀ (a : α) (r : Word), decode (encode a ++ r) = some (a, r)

namespace Encoding

variable {α β : Type}

theorem decode_encode_nil [Encoding α] (a : α) : decode (encode a) = some (a, []) := by
  have h := decode_encode a []
  rw [List.append_nil] at h
  exact h

/-- Encodings are injective. -/
theorem encode_injective [Encoding α] {a b : α} (h : encode a = encode b) : a = b := by
  have ha := decode_encode_nil a
  rw [h, decode_encode_nil b] at ha
  cases ha
  rfl

/-- Encodings are prefix-free: if `encode a ++ r = encode b ++ s` then `a = b`
and `r = s`. -/
theorem encode_append_cancel [Encoding α] {a b : α} {r s : Word}
    (h : encode a ++ r = encode b ++ s) : a = b ∧ r = s := by
  have ha := decode_encode a r
  rw [h, decode_encode b s] at ha
  cases ha
  exact ⟨rfl, rfl⟩

/-- Transport an encoding along a map with a left inverse. -/
def ofLeftInverse [Encoding β] (f : α → β) (g : β → α) (h : ∀ a, g (f a) = a) : Encoding α where
  encode a := encode (f a)
  decode w := (decode w).map fun p => (g p.1, p.2)
  decode_encode a r := by
    show Option.map _ (decode (encode (f a) ++ r)) = _
    rw [decode_encode]
    show some (g (f a), r) = _
    rw [h]

/-! ### Booleans -/

instance : Encoding Bool where
  encode b := [b]
  decode
    | [] => none
    | b :: r => some (b, r)
  decode_encode _ _ := rfl

theorem encode_bool (b : Bool) : encode b = [b] := rfl

/-! ### Natural numbers, in unary -/

/-- The unary encoding of `n`: `n` ones followed by a zero. -/
def encodeNat : ℕ → Word
  | 0 => [false]
  | n + 1 => true :: encodeNat n

/-- The decoder for the unary encoding. -/
def decodeNat : Word → Option (ℕ × Word)
  | [] => none
  | false :: r => some (0, r)
  | true :: r => (decodeNat r).map fun p => (p.1 + 1, p.2)

theorem decodeNat_encodeNat (n : ℕ) (r : Word) : decodeNat (encodeNat n ++ r) = some (n, r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Option.map _ (decodeNat (encodeNat n ++ r)) = _
    rw [ih]
    rfl

instance : Encoding ℕ := ⟨encodeNat, decodeNat, decodeNat_encodeNat⟩

theorem encode_nat_zero : encode (0 : ℕ) = [false] := rfl

theorem encode_nat_succ (n : ℕ) : encode (n + 1) = true :: encode n := rfl

@[simp] theorem length_encode_nat (n : ℕ) : (encode n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [encode_nat_succ, List.length_cons, ih]

/-! ### Products -/

instance [Encoding α] [Encoding β] : Encoding (α × β) where
  encode p := encode p.1 ++ encode p.2
  decode w := (decode w).bind fun p => (decode p.2).map fun q => ((p.1, q.1), q.2)
  decode_encode p r := by
    show (decode (encode p.1 ++ encode p.2 ++ r)).bind _ = _
    rw [List.append_assoc, decode_encode]
    show Option.map _ (decode (encode p.2 ++ r)) = _
    rw [decode_encode]
    rfl

theorem encode_prod [Encoding α] [Encoding β] (a : α) (b : β) :
    encode (a, b) = encode a ++ encode b := rfl

theorem length_encode_prod [Encoding α] [Encoding β] (a : α) (b : β) :
    (encode (a, b)).length = (encode a).length + (encode b).length := by
  rw [encode_prod, List.length_append]

/-! ### Lists -/

/-- The concatenation of the encodings of the elements of a list. -/
def encodeAll [Encoding α] : List α → Word
  | [] => []
  | a :: l => encode a ++ encodeAll l

/-- Decode `n` consecutive elements. -/
def decodeAll [Encoding α] : ℕ → Word → Option (List α × Word)
  | 0, w => some ([], w)
  | n + 1, w => (decode w).bind fun p => (decodeAll n p.2).map fun q => (p.1 :: q.1, q.2)

theorem decodeAll_encodeAll [Encoding α] (l : List α) (r : Word) :
    decodeAll l.length (encodeAll l ++ r) = some (l, r) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (decode (encode a ++ encodeAll l ++ r)).bind _ = _
    rw [List.append_assoc, decode_encode]
    show Option.map _ (decodeAll l.length (encodeAll l ++ r)) = _
    rw [ih]
    rfl

/-- Lists are encoded by their length followed by their elements. -/
instance [Encoding α] : Encoding (List α) where
  encode l := encode l.length ++ encodeAll l
  decode w := (decode (α := ℕ) w).bind fun p => decodeAll p.1 p.2
  decode_encode l r := by
    show (decode (α := ℕ) (encode l.length ++ encodeAll l ++ r)).bind _ = _
    rw [List.append_assoc, decode_encode]
    exact decodeAll_encodeAll l r

theorem encode_list [Encoding α] (l : List α) : encode l = encode l.length ++ encodeAll l := rfl

theorem encodeAll_append [Encoding α] (l₁ l₂ : List α) :
    encodeAll (l₁ ++ l₂) = encodeAll l₁ ++ encodeAll l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    show encode a ++ encodeAll (l ++ l₂) = encode a ++ encodeAll l ++ encodeAll l₂
    rw [ih, List.append_assoc]

theorem encode_list_nil [Encoding α] : encode ([] : List α) = [false] := rfl

theorem length_encode_list [Encoding α] (l : List α) :
    (encode l).length = l.length + 1 + (encodeAll l).length := by
  rw [encode_list, List.length_append, length_encode_nat]

/-! ### Languages of instances -/

/-- The language of the encodings of the instances that satisfy `p`. -/
def languageOf [Encoding α] (p : α → Prop) : Language :=
  fun w => ∃ a : α, encode a = w ∧ p a

theorem mem_languageOf [Encoding α] {p : α → Prop} {w : Word} :
    w ∈ languageOf p ↔ ∃ a : α, encode a = w ∧ p a := Iff.rfl

/-- The encoding of an instance is in the language iff the instance is a
yes-instance. -/
@[simp] theorem mem_languageOf_encode [Encoding α] {p : α → Prop} {a : α} :
    encode a ∈ languageOf p ↔ p a :=
  ⟨fun ⟨_, hb, hp⟩ => encode_injective hb ▸ hp, fun h => ⟨a, rfl, h⟩⟩

theorem languageOf_mono [Encoding α] {p q : α → Prop} (h : ∀ a, p a → q a) {w : Word}
    (hw : w ∈ languageOf p) : w ∈ languageOf q :=
  let ⟨a, ha, hp⟩ := hw
  ⟨a, ha, h a hp⟩

theorem languageOf_and [Encoding α] {p q : α → Prop} {w : Word} :
    w ∈ languageOf (fun a => p a ∧ q a) ↔ w ∈ languageOf p ∧ w ∈ languageOf q := by
  constructor
  · rintro ⟨a, ha, hp, hq⟩
    exact ⟨⟨a, ha, hp⟩, ⟨a, ha, hq⟩⟩
  · rintro ⟨⟨a, ha, hp⟩, ⟨b, hb, hq⟩⟩
    have hab : b = a := encode_injective (hb.trans ha.symm)
    exact ⟨a, ha, hp, hab ▸ hq⟩

end Encoding

end Complexity
'''

CORE["PNP.Data.Encoding.Lemmas"] = r'''import PNP.Data.Encoding

/-!
# Encodings of composite types

The round-trip, injectivity and length lemmas of `PNP.Data.Encoding`, specialised
to the composite types that occur as instances of decision problems: lists of
pairs (edge lists), lists of lists (formulas), and pairs of such.

## Implementation notes

Every lemma here is an instance of a general lemma about `Encoding`. They are
stated separately because instance resolution for nested products and lists is
costly when the type has to be inferred from an equation between words, and
because the specialised statements are the ones cited in the problem files.
-/

set_option autoImplicit false

namespace Complexity

namespace Encoding

--FILLER:encoding

end Encoding

end Complexity
'''

CORE["PNP.Poly.Basic"] = r'''import PNP.Data.Language

/-!
# Polynomially bounded functions

A function `f : ℕ → ℕ` is *polynomially bounded* if `f n ≤ c * (n + 1) ^ k` for
some constants `c` and `k`. These are the resource bounds that define
polynomial time.

## Main definitions

* `Complexity.IsPolyBounded`: the predicate.

## Main results

* `Complexity.IsPolyBounded.add`, `Complexity.IsPolyBounded.mul`,
  `Complexity.IsPolyBounded.pow`, `Complexity.IsPolyBounded.comp`: closure under
  the operations that occur when machines are combined.
* `Complexity.IsPolyBounded.exists_monotone_bound`: every polynomially bounded
  function is dominated by a monotone monomial.

## Implementation notes

We bound by a single monomial in `n + 1` rather than by a general polynomial.
The two notions define the same class of functions, and the monomial form is
monotone and positive, which removes side conditions from every closure lemma.
No ring normalisation tactic is available without Mathlib, so the arithmetic is
done by hand with `Nat` lemmas.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, §1.6.
* [Cob65] A. Cobham, *The intrinsic computational difficulty of functions*, 1965.
-/

set_option autoImplicit false

namespace Complexity

/-- `f` is polynomially bounded: `f n ≤ c * (n + 1) ^ k` for constants `c`, `k`. -/
def IsPolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

theorem one_le_succ_pow (n k : ℕ) : 1 ≤ (n + 1) ^ k :=
  Nat.pow_pos (Nat.succ_pos n)

theorem succ_pow_le_succ_pow (n : ℕ) {a b : ℕ} (h : a ≤ b) : (n + 1) ^ a ≤ (n + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos n) h

theorem succ_pow_le_succ_pow_of_le {m n : ℕ} (h : m ≤ n) (k : ℕ) :
    (m + 1) ^ k ≤ (n + 1) ^ k :=
  Nat.pow_le_pow_left (Nat.succ_le_succ h) k

theorem le_succ_pow (n : ℕ) {k : ℕ} (hk : 0 < k) : n ≤ (n + 1) ^ k :=
  calc n ≤ (n + 1) ^ 1 := by rw [Nat.pow_one]; exact Nat.le_succ n
    _ ≤ (n + 1) ^ k := succ_pow_le_succ_pow n hk

theorem pow_le_succ_pow (n : ℕ) {a b : ℕ} (h : a ≤ b) : n ^ a ≤ (n + 1) ^ b :=
  Nat.le_trans (Nat.pow_le_pow_left (Nat.le_succ n) a) (succ_pow_le_succ_pow n h)

namespace IsPolyBounded

variable {f g : ℕ → ℕ}

/-- A function dominated by a polynomially bounded function is polynomially
bounded. -/
theorem mono (hf : IsPolyBounded f) (h : ∀ n, g n ≤ f n) : IsPolyBounded g :=
  let ⟨c, k, hc⟩ := hf
  ⟨c, k, fun n => Nat.le_trans (h n) (hc n)⟩

protected theorem const (c : ℕ) : IsPolyBounded fun _ => c :=
  ⟨c, 0, fun _ => Nat.le_of_eq (Nat.mul_one c).symm⟩

protected theorem id : IsPolyBounded fun n => n :=
  ⟨1, 1, fun n => by rw [Nat.one_mul, Nat.pow_one]; exact Nat.le_succ n⟩

theorem add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n + g n := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, k₁ + k₂, fun n => ?_⟩
  have e₁ : c₁ * (n + 1) ^ k₁ ≤ c₁ * (n + 1) ^ (k₁ + k₂) :=
    Nat.mul_le_mul_left _ (succ_pow_le_succ_pow n (Nat.le_add_right _ _))
  have e₂ : c₂ * (n + 1) ^ k₂ ≤ c₂ * (n + 1) ^ (k₁ + k₂) :=
    Nat.mul_le_mul_left _ (succ_pow_le_succ_pow n (Nat.le_add_left _ _))
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.le_trans (h₁ n) e₁) (Nat.le_trans (h₂ n) e₂)

theorem mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * g n := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, k₁ + k₂, fun n => ?_⟩
  rw [Nat.pow_add, Nat.mul_mul_mul_comm]
  exact Nat.mul_le_mul (h₁ n) (h₂ n)

theorem pow (hf : IsPolyBounded f) (k : ℕ) : IsPolyBounded fun n => f n ^ k := by
  induction k with
  | zero => exact (IsPolyBounded.const 1).mono fun n => Nat.le_of_eq (Nat.pow_zero _)
  | succ k ih => exact (ih.mul hf).mono fun n => Nat.le_of_eq (Nat.pow_succ ..)

/-- Polynomially bounded functions are closed under composition. This is the
arithmetic core of the closure of polynomial time under composition. -/
theorem comp (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ * (c₂ + 1) ^ k₁, k₂ * k₁, fun n => ?_⟩
  have h₃ : g n + 1 ≤ (c₂ + 1) * (n + 1) ^ k₂ := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (h₂ n) (one_le_succ_pow n k₂)
  calc f (g n) ≤ c₁ * (g n + 1) ^ k₁ := h₁ (g n)
    _ ≤ c₁ * ((c₂ + 1) * (n + 1) ^ k₂) ^ k₁ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₃ _)
    _ = c₁ * (c₂ + 1) ^ k₁ * (n + 1) ^ (k₂ * k₁) := by
        rw [Nat.mul_pow, Nat.pow_mul, Nat.mul_assoc]

theorem succ (hf : IsPolyBounded f) : IsPolyBounded fun n => f n + 1 :=
  hf.add (IsPolyBounded.const 1)

theorem add_const (hf : IsPolyBounded f) (c : ℕ) : IsPolyBounded fun n => f n + c :=
  hf.add (IsPolyBounded.const c)

theorem const_mul (c : ℕ) (hf : IsPolyBounded f) : IsPolyBounded fun n => c * f n :=
  (IsPolyBounded.const c).mul hf

theorem mul_const (hf : IsPolyBounded f) (c : ℕ) : IsPolyBounded fun n => f n * c :=
  hf.mul (IsPolyBounded.const c)

/-- Monomials are polynomially bounded. -/
theorem monomial (c k : ℕ) : IsPolyBounded fun n => c * n ^ k :=
  (IsPolyBounded.id.pow k).const_mul c

theorem succ_monomial (c k : ℕ) : IsPolyBounded fun n => c * (n + 1) ^ k :=
  ⟨c, k, fun _ => Nat.le_refl _⟩

theorem max (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => Nat.max (f n) (g n) :=
  (hf.add hg).mono fun _ =>
    Nat.max_le.2 ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

theorem min_left (hf : IsPolyBounded f) (g : ℕ → ℕ) :
    IsPolyBounded fun n => Nat.min (f n) (g n) :=
  hf.mono fun _ => Nat.min_le_left _ _

theorem sub (hf : IsPolyBounded f) (g : ℕ → ℕ) : IsPolyBounded fun n => f n - g n :=
  hf.mono fun _ => Nat.sub_le _ _

/-- A polynomially bounded function is dominated by a monotone monomial: the
bound at `n` also bounds the function at every smaller argument. -/
theorem exists_monotone_bound (hf : IsPolyBounded f) :
    ∃ c k : ℕ, ∀ m n, m ≤ n → f m ≤ c * (n + 1) ^ k :=
  let ⟨c, k, hc⟩ := hf
  ⟨c, k, fun m _ h =>
    Nat.le_trans (hc m) (Nat.mul_le_mul_left _ (succ_pow_le_succ_pow_of_le h k))⟩

end IsPolyBounded

end Complexity
'''

CORE["PNP.Poly.Tactic"] = r'''import PNP.Poly.Basic

/-!
# The `poly_bound` tactic

A small automation tactic for goals of the form `IsPolyBounded f`, where `f` is
built from polynomially bounded functions, constants and the identity using
addition, multiplication and powers.

## Main definitions

* `poly_bound`: closes `IsPolyBounded` goals by structural recursion on the
  function.

## Implementation notes

The tactic repeatedly applies the closure lemmas of `PNP.Poly.Basic` and
discharges the leaves with `assumption`. It is deliberately syntactic: the
lemmas are applied up to reducible unfolding only, so that a failed match is
cheap, and the goal is not normalised: it is meant for the bounds that arise when machines are
combined, which already have the right shape. Compositions are not handled,
because the higher-order unification problem `f (g n) =?= e n` has no most
general solution; use `IsPolyBounded.comp` explicitly.
-/

set_option autoImplicit false

namespace Complexity

/-- One step of `poly_bound`: apply the first closure lemma that matches. -/
syntax (name := polyBoundStep) "poly_bound_step" : tactic

macro_rules
  | `(tactic| poly_bound_step) =>
    `(tactic| with_reducible first
      | assumption
      | exact IsPolyBounded.id
      | exact IsPolyBounded.const _
      | apply IsPolyBounded.add
      | apply IsPolyBounded.mul
      | apply IsPolyBounded.pow)

/-- `poly_bound` proves goals of the form `IsPolyBounded fun n => e`, where `e` is
built from `n`, constants and polynomially bounded functions in the local
context using `+`, `*` and `^`. -/
syntax (name := polyBound) "poly_bound" : tactic

macro_rules
  | `(tactic| poly_bound) => `(tactic| (repeat' poly_bound_step) <;> done)

example {f g : ℕ → ℕ} (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * g n + 3 * n ^ 2 + 1 := by
  poly_bound

end Complexity
'''

CORE["PNP.Poly.Lemmas"] = r'''import PNP.Poly.Tactic

/-!
# Closure lemmas for polynomially bounded functions

Specialisations of the closure properties of `IsPolyBounded` to the shapes of
bounds that occur when machines are combined: sums and products of running
times, powers, and bounds evaluated at the length of an intermediate result.

## Main results

All lemmas in this file are instances of `IsPolyBounded.add`,
`IsPolyBounded.mul`, `IsPolyBounded.pow` and `IsPolyBounded.comp`. They are named
after the shape of the bound, read from left to right; for example
`IsPolyBounded.mul_add` is closure under `n ↦ f n * g n + h n`.

## Implementation notes

The lemmas without compositions can also be proved by `poly_bound`; both styles
of proof are used below, which doubles as a regression test for the tactic.
Lemmas involving `IsPolyBounded.comp` are stated here because `poly_bound` does
not attempt compositions.
-/

set_option autoImplicit false

namespace Complexity

namespace IsPolyBounded

variable {f g h : ℕ → ℕ}

--FILLER:closure

end IsPolyBounded

end Complexity
'''

CORE["PNP.Poly.Monomial"] = r'''import PNP.Poly.Tactic

/-!
# Explicit monomial bounds

Concrete instances of the definition of `IsPolyBounded`: comparisons between
monomials in `n + 1`, and explicit constants `c`, `k` with
`p n ≤ c * (n + 1) ^ k` for polynomials `p` with small coefficients.

## Main results

* `Complexity.succ_pow_two_le_succ_pow_three` and its relatives: monotonicity of
  `(n + 1) ^ k` in `k`, for fixed small exponents.
* `Complexity.quadratic_1_2_1_le` and its relatives: a polynomial of degree `d`
  with coefficient sum `c` is bounded by `c * (n + 1) ^ d`. The lemmas are named
  after the degree and the coefficients, leading coefficient first.

## Implementation notes

The explicit bounds are proved term by term: each monomial `n ^ k` with `k ≤ d`
is bounded by `(n + 1) ^ d`, after which the goal is linear in the atoms and is
closed by `omega`. The resulting witnesses are used to prove the corresponding
`IsPolyBounded` statements without unfolding any closure lemma.
-/

set_option autoImplicit false

namespace Complexity

--FILLER:monomial

end Complexity
'''

CORE["PNP.Machine.Tape"] = r'''import PNP.Data.Language

/-!
# Tapes

Two-way infinite tapes over the alphabet `{blank, 0, 1}`, represented as a
zipper around the head.

## Main definitions

* `Complexity.Symbol`: tape symbols; `none` is the blank.
* `Complexity.Dir`: head movements.
* `Complexity.Tape`: a tape with a distinguished head position.
* `Complexity.Tape.ofWord`: the tape holding a word, head on its first symbol.
* `Complexity.Tape.write`, `Complexity.Tape.move`: the primitive operations.
* `Complexity.Tape.length`: the number of cells that are represented explicitly.

## Main results

* `Complexity.Tape.length_move_le`: a move extends the tape by at most one cell.
* `Complexity.Tape.length_le_length_ofWord`: a word is no longer than its tape.

## Implementation notes

Tapes are kept in normal form: the two lists never end in a blank, because
`Tape.move` trims a blank that is pushed onto an empty side (`consTrim`). In
Mathlib the same effect is obtained with the quotient `ListBlank`; trimming keeps
equality of tapes decidable and makes `Tape.ofWord w` the unique representation
of the tape holding `w`, so that "the machine halts with output `w`" can be stated
as an equation between tapes.

## References

* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, §3.1.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, §1.2.
-/

set_option autoImplicit false

namespace Complexity

/-- Tape symbols: `none` is the blank, `some b` a bit. -/
abbrev Symbol : Type := Option Bool

/-- Head movements. -/
inductive Dir
  | left
  | right
  | stay
  deriving DecidableEq, Repr

/-- A tape: the cells to the left of the head (nearest first), the cell under
the head, and the cells to its right (nearest first). All other cells are blank. -/
structure Tape where
  left : List Symbol
  head : Symbol
  right : List Symbol
  deriving DecidableEq, Repr

namespace Tape

/-- Prepend a symbol to one side of the tape, dropping it if it is a blank at
the far end. -/
def consTrim : Symbol → List Symbol → List Symbol
  | none, [] => []
  | a, l => a :: l

/-- The blank tape. -/
def blank : Tape := ⟨[], none, []⟩

/-- The tape holding the word `w`, with the head on its first symbol. -/
def ofWord : Word → Tape
  | [] => blank
  | b :: w => ⟨[], some b, w.map some⟩

/-- Overwrite the cell under the head. -/
def write (t : Tape) (a : Symbol) : Tape := { t with head := a }

/-- Move the head. -/
def move : Dir → Tape → Tape
  | .stay, t => t
  | .left, ⟨[], h, r⟩ => ⟨[], none, consTrim h r⟩
  | .left, ⟨a :: l, h, r⟩ => ⟨l, a, consTrim h r⟩
  | .right, ⟨l, h, []⟩ => ⟨consTrim h l, none, []⟩
  | .right, ⟨l, h, a :: r⟩ => ⟨consTrim h l, a, r⟩

/-- The number of explicitly represented cells. -/
def length (t : Tape) : ℕ := t.left.length + 1 + t.right.length

variable {t : Tape} {a : Symbol} {l : List Symbol} {w : Word}

theorem length_consTrim_le (a : Symbol) (l : List Symbol) :
    (consTrim a l).length ≤ l.length + 1 := by
  unfold consTrim
  split <;> simp

theorem consTrim_some (b : Bool) (l : List Symbol) : consTrim (some b) l = some b :: l := rfl

theorem consTrim_cons (a b : Symbol) (l : List Symbol) : consTrim a (b :: l) = a :: b :: l := by
  cases a <;> rfl

@[simp] theorem write_head (t : Tape) : t.write t.head = t := rfl

@[simp] theorem head_write (t : Tape) (a : Symbol) : (t.write a).head = a := rfl

@[simp] theorem write_write (t : Tape) (a b : Symbol) : (t.write a).write b = t.write b := rfl

@[simp] theorem move_stay (t : Tape) : t.move .stay = t := rfl

@[simp] theorem length_write (t : Tape) (a : Symbol) : (t.write a).length = t.length := rfl

theorem length_pos (t : Tape) : 0 < t.length := by
  unfold length; omega

/-- A move extends the represented part of the tape by at most one cell. -/
theorem length_move_le (d : Dir) (t : Tape) : (t.move d).length ≤ t.length + 1 := by
  obtain ⟨l, h, r⟩ := t
  cases d with
  | stay => exact Nat.le_succ _
  | left =>
    have := length_consTrim_le h r
    cases l <;> simp only [move, length, List.length_cons, List.length_nil] <;> omega
  | right =>
    have := length_consTrim_le h l
    cases r <;> simp only [move, length, List.length_cons, List.length_nil] <;> omega

theorem length_write_move_le (d : Dir) (t : Tape) (a : Symbol) :
    ((t.write a).move d).length ≤ t.length + 1 :=
  length_move_le d (t.write a)

@[simp] theorem ofWord_nil : ofWord [] = blank := rfl

@[simp] theorem ofWord_cons (b : Bool) (w : Word) :
    ofWord (b :: w) = ⟨[], some b, w.map some⟩ := rfl

@[simp] theorem length_blank : blank.length = 1 := rfl

theorem length_ofWord_le (w : Word) : (ofWord w).length ≤ w.length + 1 := by
  cases w with
  | nil => exact Nat.le_refl _
  | cons b w =>
    simp only [ofWord, length, List.length_nil, List.length_map, List.length_cons]
    omega

/-- A word is no longer than the tape that holds it. -/
theorem length_le_length_ofWord (w : Word) : w.length ≤ (ofWord w).length := by
  cases w with
  | nil => exact Nat.zero_le _
  | cons b w =>
    simp only [ofWord, length, List.length_nil, List.length_map, List.length_cons]
    omega

theorem head_ofWord_cons (b : Bool) (w : Word) : (ofWord (b :: w)).head = some b := rfl

theorem head_ofWord_nil : (ofWord []).head = none := rfl

theorem left_ofWord (w : Word) : (ofWord w).left = [] := by cases w <;> rfl

theorem map_some_injective {v w : Word} (h : v.map some = w.map some) : v = w := by
  induction v generalizing w with
  | nil => cases w with
    | nil => rfl
    | cons b w => simp at h
  | cons a v ih => cases w with
    | nil => simp at h
    | cons b w =>
      simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
      rw [h.1, ih h.2]

/-- The word on a tape can be read back from `Tape.ofWord`. -/
theorem ofWord_injective {v w : Word} (h : ofWord v = ofWord w) : v = w := by
  cases v with
  | nil => cases w with
    | nil => rfl
    | cons b w => simp [ofWord, blank] at h
  | cons a v => cases w with
    | nil => simp [ofWord, blank] at h
    | cons b w =>
      simp only [ofWord, Tape.mk.injEq, Option.some.injEq, true_and] at h
      obtain ⟨hab, hvw⟩ := h
      rw [hab, map_some_injective hvw]

end Tape

end Complexity
'''

CORE["PNP.Machine.TM"] = r'''import PNP.Data.FinEnum
import PNP.Machine.Tape

/-!
# Turing machines

Deterministic single-tape Turing machines over the binary alphabet, with a
small-step semantics, time-bounded runs, acceptance and computed functions.

## Main definitions

* `Complexity.TM`: a deterministic single-tape Turing machine.
* `Complexity.Cfg`: configurations (state and tape).
* `Complexity.TM.step`: the partial one-step transition function.
* `Complexity.TM.run`: the total `t`-step run, which idles on halted
  configurations.
* `Complexity.TM.HaltsIn`, `Complexity.TM.RunsInTime`: time bounds.
* `Complexity.TM.Accepts`, `Complexity.TM.language`: acceptance.
* `Complexity.TM.Computes`: `M` computes the function `f` within a time bound.
* `Complexity.TM.compl`: the machine with accepting and rejecting states swapped.

## Main results

* `Complexity.TM.run_eq_of_halted_of_le`: a halted run is stable.
* `Complexity.TM.accepts_iff_of_haltsIn`: acceptance can be read off at any time
  at which the machine has halted (determinism).
* `Complexity.TM.mem_language_compl`: swapping the accepting states complements
  the language of a machine that always halts.
* `Complexity.TM.Computes.length_le`: the output of a machine is at most as long
  as its input plus its running time.

## Implementation notes

A machine halts when its transition function is undefined, as in Mathlib's
`Turing.TM0`. Acceptance is a property of the halting state. A machine computes
`f` if on input `x` it halts in *standard configuration*: tape `Tape.ofWord (f x)`,
head on the first symbol. Thanks to the normal form of tapes this is an equation,
and it is what makes sequential composition (`PNP.Machine.Compose`) a matter of
identifying the final configuration of one machine with the initial
configuration of the next.

The state space is an arbitrary finitely enumerated type rather than `Fin n`,
which keeps constructions such as sums of state spaces free of index arithmetic.

## References

* [Tur36] A. M. Turing, *On computable numbers, with an application to the
  Entscheidungsproblem*, Proc. London Math. Soc. 42 (1936).
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Definitions
  3.3, 7.1 and 7.28.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Definitions 1.1 and 1.3.
-/

set_option autoImplicit false

namespace Complexity

/-- A configuration over the state space `Q`: the current state and the tape. -/
structure Cfg (Q : Type) where
  state : Q
  tape : Tape

/-- A deterministic single-tape Turing machine over the binary alphabet. -/
structure TM where
  /-- The state space. -/
  State : Type
  [finEnum : FinEnum State]
  /-- The initial state. -/
  start : State
  /-- The accepting states. Only relevant for halting states. -/
  accepting : State → Bool
  /-- The transition function. The machine halts where it is undefined. -/
  δ : State → Symbol → Option (State × Symbol × Dir)

namespace TM

attribute [instance] TM.finEnum

variable (M : TM)

/-- One step of the machine, or `none` if the configuration is halting. -/
def step (c : Cfg M.State) : Option (Cfg M.State) :=
  (M.δ c.state c.tape.head).map fun r => ⟨r.1, (c.tape.write r.2.1).move r.2.2⟩

/-- A configuration is halted if no transition applies. -/
def Halted (c : Cfg M.State) : Prop := M.step c = none

/-- One step of the machine, idling on halted configurations. -/
def next (c : Cfg M.State) : Cfg M.State := (M.step c).getD c

/-- The configuration after `t` steps. -/
def run : ℕ → Cfg M.State → Cfg M.State
  | 0, c => c
  | t + 1, c => run t (M.next c)

/-- The initial configuration on input `x`. -/
def init (x : Word) : Cfg M.State := ⟨M.start, Tape.ofWord x⟩

/-- `M` halts on input `x` within `t` steps. -/
def HaltsIn (t : ℕ) (x : Word) : Prop := M.Halted (M.run t (M.init x))

/-- `M` halts on every input `x` within `T x.length` steps. -/
def RunsInTime (T : ℕ → ℕ) : Prop := ∀ x : Word, M.HaltsIn (T x.length) x

/-- `M` halts on `x` within `t` steps, in an accepting state. -/
def AcceptsIn (t : ℕ) (x : Word) : Prop :=
  M.HaltsIn t x ∧ M.accepting (M.run t (M.init x)).state = true

/-- `M` accepts `x`. -/
def Accepts (x : Word) : Prop := ∃ t, M.AcceptsIn t x

/-- The language accepted by `M`. -/
def language : Language := fun x => M.Accepts x

/-- `M` computes `f` in time `T`: on input `x` it halts within `T x.length`
steps in standard configuration, with `f x` on the tape. -/
def Computes (f : Word → Word) (T : ℕ → ℕ) : Prop :=
  ∀ x : Word, M.HaltsIn (T x.length) x ∧
    (M.run (T x.length) (M.init x)).tape = Tape.ofWord (f x)

variable {M}
variable {c : Cfg M.State} {s t : ℕ} {x : Word}

/-! ### The step function -/

theorem step_eq_none_iff : M.step c = none ↔ M.δ c.state c.tape.head = none := by
  unfold step
  cases M.δ c.state c.tape.head <;> simp

theorem halted_iff : M.Halted c ↔ M.δ c.state c.tape.head = none := step_eq_none_iff

theorem step_of_δ {q : M.State} {a : Symbol} {d : Dir}
    (h : M.δ c.state c.tape.head = some (q, a, d)) :
    M.step c = some ⟨q, (c.tape.write a).move d⟩ := by
  unfold step
  rw [h]
  rfl

theorem next_of_halted (h : M.Halted c) : M.next c = c := by
  unfold next
  rw [show M.step c = none from h]
  rfl

theorem next_of_step {c' : Cfg M.State} (h : M.step c = some c') : M.next c = c' := by
  unfold next
  rw [h]
  rfl

theorem length_tape_step_le {c' : Cfg M.State} (h : M.step c = some c') :
    c'.tape.length ≤ c.tape.length + 1 := by
  unfold step at h
  cases hδ : M.δ c.state c.tape.head with
  | none => rw [hδ] at h; exact Option.noConfusion h
  | some r => rw [hδ] at h; cases h; exact Tape.length_write_move_le _ _ _

theorem length_tape_next_le (c : Cfg M.State) :
    (M.next c).tape.length ≤ c.tape.length + 1 := by
  cases h : M.step c with
  | none => rw [next_of_halted h]; exact Nat.le_succ _
  | some c' => rw [next_of_step h]; exact length_tape_step_le h

/-! ### Runs -/

@[simp] theorem run_zero (c : Cfg M.State) : M.run 0 c = c := rfl

theorem run_succ (t : ℕ) (c : Cfg M.State) : M.run (t + 1) c = M.run t (M.next c) := rfl

theorem run_add (s t : ℕ) (c : Cfg M.State) : M.run (s + t) c = M.run t (M.run s c) := by
  induction s generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ s ih => rw [Nat.add_right_comm, run_succ, ih, run_succ]

theorem run_succ' (t : ℕ) (c : Cfg M.State) : M.run (t + 1) c = M.next (M.run t c) :=
  run_add t 1 c

theorem run_of_halted (h : M.Halted c) (t : ℕ) : M.run t c = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, next_of_halted h, ih]

/-- Once a run has halted it does not change any more. -/
theorem run_eq_of_halted_of_le (h : M.Halted (M.run s c)) (hst : s ≤ t) :
    M.run t c = M.run s c := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hst
  rw [run_add, run_of_halted h]

theorem halted_run_of_le (h : M.Halted (M.run s c)) (hst : s ≤ t) :
    M.Halted (M.run t c) := by
  rw [run_eq_of_halted_of_le h hst]
  exact h

/-- The tape grows by at most one cell per step. -/
theorem length_tape_run_le (t : ℕ) (c : Cfg M.State) :
    (M.run t c).tape.length ≤ c.tape.length + t := by
  induction t generalizing c with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    rw [run_succ]
    have h₁ := ih (M.next c)
    have h₂ := length_tape_next_le c
    omega

/-! ### Time bounds and acceptance -/

theorem HaltsIn.mono (h : M.HaltsIn s x) (hst : s ≤ t) : M.HaltsIn t x :=
  halted_run_of_le h hst

theorem RunsInTime.mono {T T' : ℕ → ℕ} (h : M.RunsInTime T) (hT : ∀ n, T n ≤ T' n) :
    M.RunsInTime T' :=
  fun x => (h x).mono (hT x.length)

theorem AcceptsIn.mono (h : M.AcceptsIn s x) (hst : s ≤ t) : M.AcceptsIn t x :=
  ⟨h.1.mono hst, by rw [run_eq_of_halted_of_le h.1 hst]; exact h.2⟩

theorem AcceptsIn.accepts (h : M.AcceptsIn t x) : M.Accepts x := ⟨t, h⟩

theorem mem_language : x ∈ M.language ↔ M.Accepts x := Iff.rfl

/-- Determinism: if `M` has halted on `x` by time `t`, then it accepts `x` iff
the state reached at time `t` is accepting. -/
theorem accepts_iff_of_haltsIn (h : M.HaltsIn t x) :
    M.Accepts x ↔ M.accepting (M.run t (M.init x)).state = true := by
  constructor
  · rintro ⟨s, hs, ha⟩
    rcases Nat.le_total s t with hst | hts
    · rw [run_eq_of_halted_of_le hs hst]; exact ha
    · rw [← run_eq_of_halted_of_le h hts]; exact ha
  · intro ha
    exact ⟨t, h, ha⟩

/-- A halting run that ends in an accepting state witnesses membership. -/
theorem mem_language_of_run (h : M.HaltsIn t x)
    (ha : M.accepting (M.run t (M.init x)).state = true) : x ∈ M.language :=
  ⟨t, h, ha⟩

/-- A halting run that ends in a rejecting state witnesses non-membership. -/
theorem not_mem_language_of_run (h : M.HaltsIn t x)
    (ha : M.accepting (M.run t (M.init x)).state = false) : x ∉ M.language := by
  intro hx
  rw [(accepts_iff_of_haltsIn h).1 hx] at ha
  exact Bool.noConfusion ha

theorem RunsInTime.mem_language_iff {T : ℕ → ℕ} (h : M.RunsInTime T) (x : Word) :
    x ∈ M.language ↔ M.accepting (M.run (T x.length) (M.init x)).state = true :=
  accepts_iff_of_haltsIn (h x)

/-! ### Computed functions -/

theorem Computes.runsInTime {f : Word → Word} {T : ℕ → ℕ} (h : M.Computes f T) :
    M.RunsInTime T :=
  fun x => (h x).1

theorem Computes.mono {f : Word → Word} {T T' : ℕ → ℕ} (h : M.Computes f T)
    (hT : ∀ n, T n ≤ T' n) : M.Computes f T' :=
  fun x => ⟨(h x).1.mono (hT x.length), by
    rw [run_eq_of_halted_of_le (h x).1 (hT x.length)]; exact (h x).2⟩

/-- The output of a machine is at most as long as its input plus its running
time: a step extends the tape by at most one cell. -/
theorem Computes.length_le {f : Word → Word} {T : ℕ → ℕ} (h : M.Computes f T) (x : Word) :
    (f x).length ≤ x.length + 1 + T x.length := by
  have h₁ := length_tape_run_le (T x.length) (M.init x)
  rw [(h x).2] at h₁
  have h₂ := Tape.length_le_length_ofWord (f x)
  have h₃ : (M.init x).tape.length ≤ x.length + 1 := Tape.length_ofWord_le x
  omega

/-- A machine determines the function it computes. -/
theorem Computes.unique {f g : Word → Word} {T T' : ℕ → ℕ} (hf : M.Computes f T)
    (hg : M.Computes g T') (x : Word) : f x = g x := by
  apply Tape.ofWord_injective
  rw [← (hf x).2, ← (hg x).2]
  rcases Nat.le_total (T x.length) (T' x.length) with h | h
  · exact congrArg Cfg.tape (run_eq_of_halted_of_le (hf x).1 h).symm
  · exact congrArg Cfg.tape (run_eq_of_halted_of_le (hg x).1 h)

/-! ### Complementation -/

variable (M) in
/-- The machine `M` with accepting and rejecting states swapped. -/
def compl : TM := { M with accepting := fun q => !M.accepting q }

@[simp] theorem compl_step (c : Cfg M.State) : M.compl.step c = M.step c := rfl

@[simp] theorem compl_next (c : Cfg M.State) : M.compl.next c = M.next c := rfl

@[simp] theorem compl_init (x : Word) : M.compl.init x = M.init x := rfl

theorem compl_halted : M.compl.Halted c ↔ M.Halted c := Iff.rfl

@[simp] theorem compl_run (t : ℕ) (c : Cfg M.State) : M.compl.run t c = M.run t c := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    show M.compl.run t (M.next c) = M.run t (M.next c)
    exact ih _

theorem compl_haltsIn : M.compl.HaltsIn t x ↔ M.HaltsIn t x := by
  show M.Halted (M.compl.run t (M.init x)) ↔ M.Halted (M.run t (M.init x))
  rw [compl_run]

theorem compl_runsInTime {T : ℕ → ℕ} (h : M.RunsInTime T) : M.compl.RunsInTime T :=
  fun x => compl_haltsIn.2 (h x)

/-- For a machine that always halts, swapping the accepting states complements
the accepted language. -/
theorem mem_language_compl {T : ℕ → ℕ} (h : M.RunsInTime T) (x : Word) :
    x ∈ M.compl.language ↔ x ∉ M.language := by
  have h₁ := (compl_runsInTime h).mem_language_iff x
  rw [compl_run] at h₁
  rw [h₁, h.mem_language_iff x]
  show (!M.accepting (M.run (T x.length) (M.init x)).state) = true ↔
    ¬M.accepting (M.run (T x.length) (M.init x)).state = true
  cases M.accepting (M.run (T x.length) (M.init x)).state <;> simp

/-! ### The identity machine -/

/-- The machine that halts immediately. It computes the identity in time `0`. -/
def idle : TM where
  State := Unit
  start := ()
  accepting := fun _ => true
  δ := fun _ _ => none

theorem idle_halted (c : Cfg idle.State) : idle.Halted c := rfl

theorem idle_computes (T : ℕ → ℕ) : idle.Computes id T := by
  intro x
  have h := run_of_halted (idle_halted (idle.init x)) (T x.length)
  exact ⟨by unfold HaltsIn; rw [h]; exact idle_halted _, by rw [h]; rfl⟩

theorem idle_runsInTime (T : ℕ → ℕ) : idle.RunsInTime T := (idle_computes T).runsInTime

theorem mem_language_idle (x : Word) : x ∈ idle.language := ⟨0, rfl, rfl⟩

end TM

end Complexity
'''

CORE["PNP.Machine.Compose"] = r'''import PNP.Machine.TM

/-!
# Sequential composition of Turing machines

Given machines `M₁` and `M₂`, the machine `TM.comp M₁ M₂` runs `M₁` to
completion and then starts `M₂` on the tape that `M₁` leaves behind.

## Main definitions

* `Complexity.TM.comp`: sequential composition.
* `Complexity.TM.inlCfg`, `Complexity.TM.inrCfg`: the embeddings of the
  configurations of the two components.

## Main results

* `Complexity.TM.exists_comp_run_inl`: the simulation lemma. If `M₁` halts within
  `t` steps, then after at most `t + 1` steps the composite is in the initial
  state of `M₂` on the tape left by `M₁`, and from there on it follows `M₂`.
* `Complexity.TM.Computes.comp`: if `M₁` computes `f` and `M₂` computes `g`, then
  `TM.comp M₁ M₂` computes `g ∘ f`, in time `T₁(n) + 1 + T₂(|f x|)`.
* `Complexity.TM.comp_runsInTime`, `Complexity.TM.mem_comp_language`: the same
  for a decider `M₂`; the composite decides the preimage of the language of `M₂`.

## Implementation notes

The state space of the composite is the sum `M₁.State ⊕ M₂.State`. A halting
configuration of `M₁` is linked to the initial state of `M₂` by a single extra
step that rewrites the scanned symbol with itself and does not move. No
rewinding is needed: `TM.Computes` requires `M₁` to halt in standard
configuration, which is literally the initial configuration of `M₂` on the
output.

The exact halting time of `M₁` is not known to the simulation lemma, only an
upper bound; this is why it is stated with an existential `t' ≤ t`. The
consequences are stated for arbitrary bounds using stability of halted runs.

## References

* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Theorem 7.31.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, §1.3.
-/

set_option autoImplicit false

namespace Complexity

namespace TM

/-- Sequential composition: run `M₁`, then run `M₂` on the resulting tape. -/
def comp (M₁ M₂ : TM) : TM where
  State := M₁.State ⊕ M₂.State
  start := .inl M₁.start
  accepting := fun q =>
    match q with
    | .inl _ => false
    | .inr q => M₂.accepting q
  δ := fun q a =>
    match q with
    | .inl q =>
      match M₁.δ q a with
      | some r => some (.inl r.1, r.2.1, r.2.2)
      | none => some (.inr M₂.start, a, .stay)
    | .inr q => (M₂.δ q a).map fun r => (.inr r.1, r.2.1, r.2.2)

variable {M₁ M₂ : TM}

/-- A configuration of the first component, as a configuration of the composite. -/
def inlCfg (c : Cfg M₁.State) : Cfg (comp M₁ M₂).State := ⟨.inl c.state, c.tape⟩

/-- A configuration of the second component, as a configuration of the composite. -/
def inrCfg (c : Cfg M₂.State) : Cfg (comp M₁ M₂).State := ⟨.inr c.state, c.tape⟩

/-! ### Transitions of the composite -/

theorem comp_δ_inl_of_some {q : M₁.State} {a : Symbol} {r : M₁.State × Symbol × Dir}
    (h : M₁.δ q a = some r) :
    (comp M₁ M₂).δ (.inl q) a = some (.inl r.1, r.2.1, r.2.2) := by
  show (match M₁.δ q a with
    | some r => some (Sum.inl r.1, r.2.1, r.2.2)
    | none => some (Sum.inr M₂.start, a, Dir.stay)) = _
  rw [h]

theorem comp_δ_inl_of_none {q : M₁.State} {a : Symbol} (h : M₁.δ q a = none) :
    (comp M₁ M₂).δ (.inl q) a = some (.inr M₂.start, a, .stay) := by
  show (match M₁.δ q a with
    | some r => some (Sum.inl r.1, r.2.1, r.2.2)
    | none => some (Sum.inr M₂.start, a, Dir.stay)) = _
  rw [h]

theorem comp_δ_inr (q : M₂.State) (a : Symbol) :
    (comp M₁ M₂).δ (.inr q) a = (M₂.δ q a).map fun r => (.inr r.1, r.2.1, r.2.2) := rfl

theorem comp_step_inl_of_step {c c' : Cfg M₁.State} (h : M₁.step c = some c') :
    (comp M₁ M₂).step (inlCfg c) = some (inlCfg c') := by
  unfold step at h
  cases hδ : M₁.δ c.state c.tape.head with
  | none => rw [hδ] at h; exact Option.noConfusion h
  | some r =>
    rw [hδ] at h
    cases h
    show Option.map _ ((comp M₁ M₂).δ (.inl c.state) c.tape.head) = _
    rw [comp_δ_inl_of_some hδ]
    rfl

theorem comp_step_inl_of_halted {c : Cfg M₁.State} (h : M₁.Halted c) :
    (comp M₁ M₂).step (inlCfg c) = some (inrCfg ⟨M₂.start, c.tape⟩) := by
  show Option.map _ ((comp M₁ M₂).δ (.inl c.state) c.tape.head) = _
  rw [comp_δ_inl_of_none (halted_iff.1 h)]
  rfl

theorem comp_step_inr (c : Cfg M₂.State) :
    (comp M₁ M₂).step (inrCfg c) = (M₂.step c).map inrCfg := by
  show Option.map _ ((comp M₁ M₂).δ (.inr c.state) c.tape.head) = _
  rw [comp_δ_inr]
  unfold step
  cases M₂.δ c.state c.tape.head <;> rfl

theorem comp_next_inr (c : Cfg M₂.State) :
    (comp M₁ M₂).next (inrCfg c) = inrCfg (M₂.next c) := by
  unfold next
  rw [comp_step_inr]
  cases M₂.step c <;> rfl

theorem comp_run_inr (t : ℕ) (c : Cfg M₂.State) :
    (comp M₁ M₂).run t (inrCfg c) = inrCfg (M₂.run t c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => rw [run_succ, comp_next_inr, ih, run_succ]

theorem comp_halted_inr {c : Cfg M₂.State} :
    (comp M₁ M₂).Halted (inrCfg c) ↔ M₂.Halted c := by
  unfold Halted
  rw [comp_step_inr]
  cases M₂.step c <;> simp

theorem not_comp_halted_inl (c : Cfg M₁.State) : ¬(comp M₁ M₂).Halted (inlCfg c) := by
  intro h
  cases hc : M₁.step c with
  | none => rw [Halted, comp_step_inl_of_halted hc] at h; exact Option.noConfusion h
  | some c' => rw [Halted, comp_step_inl_of_step hc] at h; exact Option.noConfusion h

/-! ### The simulation lemma -/

/-- If `M₁` halts within `t` steps from `c`, then within `t + 1` steps the
composite reaches the initial state of `M₂` on the tape left by `M₁`, and from
then on it simulates `M₂` step by step. -/
theorem exists_comp_run_inl {t : ℕ} {c : Cfg M₁.State} (h : M₁.Halted (M₁.run t c)) :
    ∃ t', t' ≤ t ∧ ∀ s, (comp M₁ M₂).run (t' + 1 + s) (inlCfg c) =
      inrCfg (M₂.run s ⟨M₂.start, (M₁.run t c).tape⟩) := by
  induction t generalizing c with
  | zero =>
    have h' : M₁.Halted c := h
    refine ⟨0, Nat.le_refl _, fun s => ?_⟩
    rw [Nat.zero_add, Nat.add_comm, run_succ, next_of_step (comp_step_inl_of_halted h'),
      comp_run_inr]
    rfl
  | succ t ih =>
    cases hc : M₁.step c with
    | none =>
      refine ⟨0, Nat.zero_le _, fun s => ?_⟩
      rw [run_of_halted hc, Nat.zero_add, Nat.add_comm, run_succ,
        next_of_step (comp_step_inl_of_halted hc), comp_run_inr]
    | some c' =>
      rw [run_succ, next_of_step hc] at h
      obtain ⟨t', ht', hrun⟩ := ih h
      refine ⟨t' + 1, Nat.succ_le_succ ht', fun s => ?_⟩
      have e : t' + 1 + 1 + s = t' + 1 + s + 1 := by omega
      rw [run_succ t c, next_of_step hc, e, run_succ,
        next_of_step (comp_step_inl_of_step hc)]
      exact hrun s

/-- If `M₁` halts within `t` steps and `M₂`, started on the tape left by `M₁`,
halts within `s` further steps, then every run of the composite of length at
least `t + 1 + s` ends in the final configuration of `M₂`. -/
theorem comp_run_of_halted {t s N : ℕ} {c : Cfg M₁.State} (h₁ : M₁.Halted (M₁.run t c))
    (h₂ : M₂.Halted (M₂.run s ⟨M₂.start, (M₁.run t c).tape⟩)) (hN : t + 1 + s ≤ N) :
    (comp M₁ M₂).run N (inlCfg c) = inrCfg (M₂.run s ⟨M₂.start, (M₁.run t c).tape⟩) := by
  obtain ⟨t', ht', hrun⟩ := exists_comp_run_inl (M₂ := M₂) h₁
  have hh : (comp M₁ M₂).Halted ((comp M₁ M₂).run (t' + 1 + s) (inlCfg c)) := by
    rw [hrun]
    exact comp_halted_inr.2 h₂
  rw [run_eq_of_halted_of_le hh (by omega), hrun]

variable {f g : Word → Word} {T₁ T₂ T : ℕ → ℕ}

/-- The run of the composite on input `x`, when `M₁` computes `f`. -/
theorem comp_run_init (h₁ : M₁.Computes f T₁) {x : Word} {s N : ℕ}
    (h₂ : M₂.HaltsIn s (f x)) (hN : T₁ x.length + 1 + s ≤ N) :
    (comp M₁ M₂).run N ((comp M₁ M₂).init x) = inrCfg (M₂.run s (M₂.init (f x))) := by
  have e : (⟨M₂.start, (M₁.run (T₁ x.length) (M₁.init x)).tape⟩ : Cfg M₂.State) =
      M₂.init (f x) := by
    rw [(h₁ x).2]
    rfl
  have hrun := comp_run_of_halted (M₂ := M₂) (s := s) (h₁ x).1 (by rw [e]; exact h₂) hN
  rw [e] at hrun
  exact hrun

/-! ### Composition of computed functions -/

/-- **Composition.** If `M₁` computes `f` in time `T₁` and `M₂` computes `g` in
time `T₂`, then `TM.comp M₁ M₂` computes `g ∘ f` in any time `T` with
`T₁(|x|) + 1 + T₂(|f x|) ≤ T(|x|)`. -/
theorem Computes.comp (h₁ : M₁.Computes f T₁) (h₂ : M₂.Computes g T₂)
    (hT : ∀ x : Word, T₁ x.length + 1 + T₂ (f x).length ≤ T x.length) :
    (TM.comp M₁ M₂).Computes (g ∘ f) T := by
  intro x
  have hrun := comp_run_init h₁ (h₂ (f x)).1 (hT x)
  constructor
  · unfold HaltsIn
    rw [hrun]
    exact comp_halted_inr.2 (h₂ (f x)).1
  · rw [hrun]
    exact (h₂ (f x)).2

/-- If `M₁` computes `f` and `M₂` always halts, so does the composite. -/
theorem comp_runsInTime (h₁ : M₁.Computes f T₁) (h₂ : M₂.RunsInTime T₂)
    (hT : ∀ x : Word, T₁ x.length + 1 + T₂ (f x).length ≤ T x.length) :
    (comp M₁ M₂).RunsInTime T := by
  intro x
  unfold HaltsIn
  rw [comp_run_init h₁ (h₂ (f x)) (hT x)]
  exact comp_halted_inr.2 (h₂ (f x))

/-- If `M₁` computes `f` and `M₂` always halts, the composite accepts the
preimage under `f` of the language of `M₂`. -/
theorem mem_comp_language (h₁ : M₁.Computes f T₁) (h₂ : M₂.RunsInTime T₂)
    (hT : ∀ x : Word, T₁ x.length + 1 + T₂ (f x).length ≤ T x.length) (x : Word) :
    x ∈ (comp M₁ M₂).language ↔ f x ∈ M₂.language := by
  rw [(comp_runsInTime h₁ h₂ hT).mem_language_iff, h₂.mem_language_iff,
    comp_run_init h₁ (h₂ (f x)) (hT x)]
  exact Iff.rfl

end TM

end Complexity
'''

CORE["PNP.Machine.AuxTM"] = r'''import PNP.Machine.TM

/-!
# Machines with an auxiliary tape

A Turing machine with a second, read-only *auxiliary* tape next to its work
tape. The auxiliary tape holds additional input: a certificate, a witness or an
advice string. This is the machine model underlying verifiers.

## Main definitions

* `Complexity.AuxTM`: a Turing machine with a read-only auxiliary tape.
* `Complexity.AuxCfg`: configurations (state, work tape, auxiliary tape).
* `Complexity.AuxTM.step`, `Complexity.AuxTM.run`: the semantics, as for `TM`.
* `Complexity.AuxTM.RunsInTime`: the machine halts within the bound for every
  input and every content of the auxiliary tape.
* `Complexity.AuxTM.language`: the language accepted within a resource bound.
* `Complexity.TM.toAuxTM`: a single-tape machine as an auxiliary-tape machine
  that never looks at its auxiliary tape.

## Main results

* `Complexity.AuxTM.run_eq_of_halted_of_le`: a halted run is stable.
* `Complexity.AuxTM.language_mono`: the accepted language grows with the bound.
* `Complexity.TM.toAuxTM_run`: `M.toAuxTM` simulates `M` step by step.
* `Complexity.TM.mem_toAuxTM_language`: `M.toAuxTM` and `M` accept the same
  language.

## Implementation notes

The auxiliary tape is read-only: a transition may move its head but cannot write
to it. The input is placed on the work tape, as for `TM`.

`AuxTM.language V T` is the language of `V` relative to the resource bound `T`,
which limits both the running time and the length of the auxiliary input that is
taken into account, as in [Sip13, Definition 7.18] and [AB09, Definition 2.1]. A
machine that halts within `T` steps cannot read more than `T` cells of its
auxiliary tape, so using one bound for both loses nothing.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Definitions 2.1 and 4.19 (certificate tapes).
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Definition 7.18.
-/

set_option autoImplicit false

namespace Complexity

/-- A configuration of an auxiliary-tape machine over the state space `Q`. -/
structure AuxCfg (Q : Type) where
  state : Q
  work : Tape
  aux : Tape

/-- A deterministic Turing machine with a work tape and a read-only auxiliary
tape. -/
structure AuxTM where
  /-- The state space. -/
  State : Type
  [finEnum : FinEnum State]
  /-- The initial state. -/
  start : State
  /-- The accepting states. -/
  accepting : State → Bool
  /-- The transition function: from the state and the two scanned symbols to the
  new state, the symbol written on the work tape, and the two head movements. -/
  δ : State → Symbol → Symbol → Option (State × Symbol × Dir × Dir)

namespace AuxTM

attribute [instance] AuxTM.finEnum

variable (V : AuxTM)

/-- One step of the machine, or `none` if the configuration is halting. -/
def step (c : AuxCfg V.State) : Option (AuxCfg V.State) :=
  (V.δ c.state c.work.head c.aux.head).map fun r =>
    ⟨r.1, (c.work.write r.2.1).move r.2.2.1, c.aux.move r.2.2.2⟩

/-- A configuration is halted if no transition applies. -/
def Halted (c : AuxCfg V.State) : Prop := V.step c = none

/-- One step of the machine, idling on halted configurations. -/
def next (c : AuxCfg V.State) : AuxCfg V.State := (V.step c).getD c

/-- The configuration after `t` steps. -/
def run : ℕ → AuxCfg V.State → AuxCfg V.State
  | 0, c => c
  | t + 1, c => run t (V.next c)

/-- The initial configuration on input `x` with auxiliary input `w`. -/
def init (x w : Word) : AuxCfg V.State := ⟨V.start, Tape.ofWord x, Tape.ofWord w⟩

/-- `V` halts on input `x` with auxiliary input `w` within `t` steps. -/
def HaltsIn (t : ℕ) (x w : Word) : Prop := V.Halted (V.run t (V.init x w))

/-- `V` halts within `T x.length` steps on every input `x`, whatever the content
of the auxiliary tape. -/
def RunsInTime (T : ℕ → ℕ) : Prop := ∀ x w : Word, V.HaltsIn (T x.length) x w

/-- `V` halts on `(x, w)` within `t` steps, in an accepting state. -/
def AcceptsIn (t : ℕ) (x w : Word) : Prop :=
  V.HaltsIn t x w ∧ V.accepting (V.run t (V.init x w)).state = true

/-- The language of `V` relative to the resource bound `T`: the inputs `x`
accepted within `T x.length` steps for an auxiliary input of length at most
`T x.length`. -/
def language (T : ℕ → ℕ) : Language :=
  fun x => ∃ w : Word, w.length ≤ T x.length ∧ V.AcceptsIn (T x.length) x w

variable {V}
variable {c : AuxCfg V.State} {s t : ℕ} {x w : Word}

theorem halted_iff : V.Halted c ↔ V.δ c.state c.work.head c.aux.head = none := by
  unfold Halted step
  cases V.δ c.state c.work.head c.aux.head <;> simp

theorem next_of_halted (h : V.Halted c) : V.next c = c := by
  unfold next
  rw [show V.step c = none from h]
  rfl

theorem next_of_step {c' : AuxCfg V.State} (h : V.step c = some c') : V.next c = c' := by
  unfold next
  rw [h]
  rfl

@[simp] theorem run_zero (c : AuxCfg V.State) : V.run 0 c = c := rfl

theorem run_succ (t : ℕ) (c : AuxCfg V.State) : V.run (t + 1) c = V.run t (V.next c) := rfl

theorem run_add (s t : ℕ) (c : AuxCfg V.State) : V.run (s + t) c = V.run t (V.run s c) := by
  induction s generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ s ih => rw [Nat.add_right_comm, run_succ, ih, run_succ]

theorem run_of_halted (h : V.Halted c) (t : ℕ) : V.run t c = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, next_of_halted h, ih]

/-- Once a run has halted it does not change any more. -/
theorem run_eq_of_halted_of_le (h : V.Halted (V.run s c)) (hst : s ≤ t) :
    V.run t c = V.run s c := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hst
  rw [run_add, run_of_halted h]

/-- The auxiliary tape is read-only: a step changes at most the head position. -/
theorem aux_step_eq {c' : AuxCfg V.State} (h : V.step c = some c') :
    ∃ d : Dir, c'.aux = c.aux.move d := by
  unfold step at h
  cases hδ : V.δ c.state c.work.head c.aux.head with
  | none => rw [hδ] at h; exact Option.noConfusion h
  | some r => rw [hδ] at h; cases h; exact ⟨_, rfl⟩

theorem HaltsIn.mono (h : V.HaltsIn s x w) (hst : s ≤ t) : V.HaltsIn t x w := by
  unfold HaltsIn at h ⊢
  rw [run_eq_of_halted_of_le h hst]
  exact h

theorem RunsInTime.mono {T T' : ℕ → ℕ} (h : V.RunsInTime T) (hT : ∀ n, T n ≤ T' n) :
    V.RunsInTime T' :=
  fun x w => (h x w).mono (hT x.length)

theorem AcceptsIn.mono (h : V.AcceptsIn s x w) (hst : s ≤ t) : V.AcceptsIn t x w :=
  ⟨h.1.mono hst, by rw [run_eq_of_halted_of_le h.1 hst]; exact h.2⟩

theorem mem_language {T : ℕ → ℕ} :
    x ∈ V.language T ↔ ∃ w : Word, w.length ≤ T x.length ∧ V.AcceptsIn (T x.length) x w :=
  Iff.rfl

/-- The accepted language grows with the resource bound. -/
theorem language_mono {T T' : ℕ → ℕ} (hT : ∀ n, T n ≤ T' n) {x : Word}
    (h : x ∈ V.language T) : x ∈ V.language T' :=
  let ⟨w, hw, ha⟩ := h
  ⟨w, Nat.le_trans hw (hT x.length), ha.mono (hT x.length)⟩

end AuxTM

namespace TM

variable (M : TM)

/-- A single-tape machine, viewed as an auxiliary-tape machine that ignores its
auxiliary tape. -/
def toAuxTM : AuxTM where
  State := M.State
  start := M.start
  accepting := M.accepting
  δ := fun q a _ => (M.δ q a).map fun r => (r.1, r.2.1, r.2.2, Dir.stay)

variable {M}

/-- A configuration of `M` together with an auxiliary tape. -/
def withAux (c : Cfg M.State) (u : Tape) : AuxCfg M.toAuxTM.State := ⟨c.state, c.tape, u⟩

theorem toAuxTM_step (c : Cfg M.State) (u : Tape) :
    M.toAuxTM.step (withAux c u) = (M.step c).map fun c' => withAux c' u := by
  show Option.map _ (Option.map _ (M.δ c.state c.tape.head)) = Option.map _ (M.step c)
  unfold step
  cases M.δ c.state c.tape.head <;> rfl

theorem toAuxTM_next (c : Cfg M.State) (u : Tape) :
    M.toAuxTM.next (withAux c u) = withAux (M.next c) u := by
  unfold next AuxTM.next
  rw [toAuxTM_step]
  cases M.step c <;> rfl

/-- `M.toAuxTM` simulates `M` step by step and never touches its auxiliary tape. -/
theorem toAuxTM_run (t : ℕ) (c : Cfg M.State) (u : Tape) :
    M.toAuxTM.run t (withAux c u) = withAux (M.run t c) u := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => rw [AuxTM.run_succ, toAuxTM_next, ih, run_succ]

theorem toAuxTM_halted {c : Cfg M.State} {u : Tape} :
    M.toAuxTM.Halted (withAux c u) ↔ M.Halted c := by
  unfold Halted AuxTM.Halted
  rw [toAuxTM_step]
  cases M.step c with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some c' => exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h⟩

theorem toAuxTM_haltsIn {t : ℕ} {x w : Word} : M.toAuxTM.HaltsIn t x w ↔ M.HaltsIn t x := by
  show M.toAuxTM.Halted (M.toAuxTM.run t (withAux (M.init x) (Tape.ofWord w))) ↔ _
  rw [toAuxTM_run]
  exact toAuxTM_halted

theorem toAuxTM_acceptsIn {t : ℕ} {x w : Word} :
    M.toAuxTM.AcceptsIn t x w ↔ M.AcceptsIn t x := by
  show _ ∧ M.accepting (M.toAuxTM.run t (withAux (M.init x) (Tape.ofWord w))).state = true ↔ _
  rw [toAuxTM_run]
  exact and_congr_left fun _ => toAuxTM_haltsIn

theorem toAuxTM_runsInTime {T : ℕ → ℕ} (h : M.RunsInTime T) : M.toAuxTM.RunsInTime T :=
  fun x _ => toAuxTM_haltsIn.2 (h x)

/-- `M.toAuxTM` accepts, within any time bound for `M`, exactly the language of
`M`: the auxiliary input is irrelevant, so the empty one will do. -/
theorem mem_toAuxTM_language {T : ℕ → ℕ} (h : M.RunsInTime T) (x : Word) :
    x ∈ M.toAuxTM.language T ↔ x ∈ M.language := by
  constructor
  · rintro ⟨w, -, ha⟩
    exact (toAuxTM_acceptsIn.1 ha).accepts
  · intro hx
    exact ⟨[], Nat.zero_le _, toAuxTM_acceptsIn.2 ⟨h x, (accepts_iff_of_haltsIn (h x)).1 hx⟩⟩

end TM

end Complexity
'''

CORE["PNP.Machine.TapeReduction"] = r'''import PNP.Poly.Tactic
import PNP.Machine.AuxTM

/-!
# Tape reduction

The machines of `PNP.Machine.AuxTM` have two tapes. This file relates them to
the single-tape machines of `PNP.Machine.TM`: a second tape can be removed at the
cost of a quadratic slowdown.

## Main definitions

* `Complexity.simTime`: the time bound of the single-tape simulation.

## Main results

* `Complexity.isPolyBounded_simTime`: the simulation preserves polynomial bounds.
* `Complexity.AuxTM.tape_reduction`: the tape reduction theorem
  [HS65, Theorem 6; Sip13, Theorem 7.8; AB09, Claim 1.6].
* `Complexity.AuxTM.exists_polyTime_tm`: an auxiliary-tape machine with a
  polynomial time bound has an equivalent single-tape machine with a polynomial
  time bound.

## Implementation notes

The simulating machine keeps the contents of both tapes on its single tape, on
two interleaved tracks, and sweeps the tape once for every simulated step. A
sweep costs time proportional to the length of the tape, which is at most
`T n + n + 2`; this gives the bound `simTime T n = (T n + n + 2) ^ 2`.

The construction of the simulating machine is entirely standard but long, and it
is not carried out here: the statement is recorded in the form in which it is
used. Everything else in this file is proved.

## References

* [HS65] J. Hartmanis, R. E. Stearns, *On the computational complexity of
  algorithms*, Trans. Amer. Math. Soc. 117 (1965), 285–306.
* [HS66] F. C. Hennie, R. E. Stearns, *Two-tape simulation of multitape Turing
  machines*, J. ACM 13 (1966), 533–546.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Theorems 3.13
  and 7.8.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Claim 1.6.
-/

set_option autoImplicit false

namespace Complexity

/-- The time bound of the single-tape simulation of a two-tape machine with time
bound `T`: one sweep over a tape of length at most `T n + n + 2` per step. -/
def simTime (T : ℕ → ℕ) : ℕ → ℕ := fun n => (T n + n + 2) ^ 2

variable {T T' : ℕ → ℕ}

theorem simTime_apply (T : ℕ → ℕ) (n : ℕ) : simTime T n = (T n + n + 2) ^ 2 := rfl

theorem simTime_mono (h : ∀ n, T n ≤ T' n) (n : ℕ) : simTime T n ≤ simTime T' n :=
  Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_right (h n) n) 2) 2

theorem le_sq (a : ℕ) : a ≤ a ^ 2 := by
  rw [Nat.pow_two]
  cases a with
  | zero => exact Nat.zero_le _
  | succ a => exact Nat.le_mul_of_pos_left _ (Nat.succ_pos a)

theorem le_simTime (T : ℕ → ℕ) (n : ℕ) : T n ≤ simTime T n := by
  have h : T n ≤ T n + n + 2 := by omega
  exact Nat.le_trans h (le_sq _)

theorem self_le_simTime (T : ℕ → ℕ) (n : ℕ) : n ≤ simTime T n := by
  have h : n ≤ T n + n + 2 := by omega
  exact Nat.le_trans h (le_sq _)

theorem simTime_pos (T : ℕ → ℕ) (n : ℕ) : 0 < simTime T n :=
  Nat.pow_pos (by omega)

/-- The simulation preserves polynomial time bounds. -/
theorem isPolyBounded_simTime (hT : IsPolyBounded T) : IsPolyBounded (simTime T) := by
  unfold simTime
  poly_bound

--FILLER:simtime_a

namespace AuxTM

/-- **Tape reduction** [HS65, Theorem 6]. A machine with an auxiliary tape that
runs in time `T` is simulated by a single-tape machine that runs in time
`simTime T`, i.e. with quadratic overhead, and accepts the same language. -/
axiom tape_reduction (V : AuxTM) (T : ℕ → ℕ) (hV : V.RunsInTime T) :
    ∃ M : TM, M.RunsInTime (simTime T) ∧ ∀ x, x ∈ M.language ↔ x ∈ V.language T

variable {V : AuxTM}

/-- Tape reduction with an arbitrary upper bound on the simulation time. -/
theorem exists_tm_runsInTime (hV : V.RunsInTime T) (hT : ∀ n, simTime T n ≤ T' n) :
    ∃ M : TM, M.RunsInTime T' ∧ ∀ x, x ∈ M.language ↔ x ∈ V.language T :=
  let ⟨M, hM, hL⟩ := V.tape_reduction T hV
  ⟨M, hM.mono hT, hL⟩

/-- An auxiliary-tape machine with a polynomial time bound has an equivalent
single-tape machine with a polynomial time bound. -/
theorem exists_polyTime_tm (hT : IsPolyBounded T) (hV : V.RunsInTime T) :
    ∃ (M : TM) (T' : ℕ → ℕ), IsPolyBounded T' ∧ M.RunsInTime T' ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language T :=
  let ⟨M, hM, hL⟩ := V.tape_reduction T hV
  ⟨M, simTime T, isPolyBounded_simTime hT, hM, hL⟩

end AuxTM

--FILLER:simtime_b

end Complexity
'''

CORE["PNP.Classes.Basic"] = r'''import PNP.Poly.Basic
import PNP.Machine.AuxTM

/-!
# The classes P, NP and coNP

## Main definitions

* `Complexity.DTIME`: languages decided by a single-tape machine within a given
  time bound.
* `Complexity.P`: languages decided in polynomial time.
* `Complexity.NP`: languages with polynomial-time verifiers and polynomially
  bounded certificates.
* `Complexity.coNP`: complements of languages in NP.

## Main results

* `Complexity.P_subset_NP`: P ⊆ NP.
* `Complexity.compl_mem_P`: P is closed under complement.
* `Complexity.P_subset_coNP`: P ⊆ coNP.
* `Complexity.DTIME_subset_P`: `DTIME T ⊆ P` for polynomially bounded `T`.

## Implementation notes

`P` is defined with deciders: a machine that halts within a polynomial bound on
every input and accepts exactly the words of the language
[Sip13, Definition 7.12]. `NP` is defined with verifiers
[Sip13, Definitions 7.18 and 7.19; AB09, Definition 2.1]: an auxiliary-tape
machine `V` and a polynomial bound `T` such that `x ∈ L` iff `V` accepts `x`
within `T(|x|)` steps for some certificate of length at most `T(|x|)` on the
auxiliary tape. The certificate tape formulation is equivalent to the one with
pairs `⟨x, c⟩` on a single tape and avoids fixing a pairing function at this
stage.

The inclusion P ⊆ NP is proved by letting the verifier ignore its certificate
(`TM.toAuxTM`).

## References

* [Cob65] A. Cobham, *The intrinsic computational difficulty of functions*, 1965.
* [Edm65] J. Edmonds, *Paths, trees, and flowers*, Canad. J. Math. 17 (1965).
* [Coo71] S. A. Cook, *The complexity of theorem-proving procedures*, STOC 1971.
* [Lev73] L. A. Levin, *Universal sequential search problems*, Probl. Peredachi
  Inf. 9 (1973).
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, §7.2–7.3.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Chapters 1–2.
-/

set_option autoImplicit false

namespace Complexity

/-- `DTIME T` is the class of languages decided by a single-tape machine that
halts within `T n` steps on inputs of length `n`. -/
def DTIME (T : ℕ → ℕ) : ComplexityClass :=
  fun L => ∃ M : TM, M.RunsInTime T ∧ ∀ x, x ∈ M.language ↔ x ∈ L

/-- **P**: the class of languages decided in polynomial time. -/
def P : ComplexityClass :=
  fun L => ∃ (M : TM) (T : ℕ → ℕ), IsPolyBounded T ∧ M.RunsInTime T ∧
    ∀ x, x ∈ M.language ↔ x ∈ L

/-- **NP**: the class of languages with a polynomial-time verifier and
polynomially bounded certificates. -/
def NP : ComplexityClass :=
  fun L => ∃ (V : AuxTM) (T : ℕ → ℕ), IsPolyBounded T ∧ V.RunsInTime T ∧
    ∀ x, x ∈ V.language T ↔ x ∈ L

/-- **coNP**: the class of complements of languages in NP. -/
def coNP : ComplexityClass := NP.co

variable {L L₁ L₂ : Language} {T : ℕ → ℕ}

theorem mem_DTIME_iff :
    L ∈ DTIME T ↔ ∃ M : TM, M.RunsInTime T ∧ ∀ x, x ∈ M.language ↔ x ∈ L := Iff.rfl

theorem mem_P_iff :
    L ∈ P ↔ ∃ (M : TM) (T : ℕ → ℕ), IsPolyBounded T ∧ M.RunsInTime T ∧
      ∀ x, x ∈ M.language ↔ x ∈ L := Iff.rfl

theorem mem_NP_iff :
    L ∈ NP ↔ ∃ (V : AuxTM) (T : ℕ → ℕ), IsPolyBounded T ∧ V.RunsInTime T ∧
      ∀ x, x ∈ V.language T ↔ x ∈ L := Iff.rfl

theorem mem_coNP_iff : L ∈ coNP ↔ L.compl ∈ NP := Iff.rfl

/-! ### Deterministic time -/

theorem DTIME_mono {T T' : ℕ → ℕ} (h : ∀ n, T n ≤ T' n) : DTIME T ⊆ DTIME T' :=
  fun _ ⟨M, hM, hL⟩ => ⟨M, hM.mono h, hL⟩

/-- `DTIME T ⊆ P` for every polynomially bounded `T`. -/
theorem DTIME_subset_P (hT : IsPolyBounded T) : DTIME T ⊆ P :=
  fun _ ⟨M, hM, hL⟩ => ⟨M, T, hT, hM, hL⟩

theorem mem_P_iff_exists_DTIME : L ∈ P ↔ ∃ T, IsPolyBounded T ∧ L ∈ DTIME T :=
  ⟨fun ⟨M, T, hT, hM, hL⟩ => ⟨T, hT, M, hM, hL⟩, fun ⟨_, hT, h⟩ => DTIME_subset_P hT h⟩

/-- Membership in a class defined by machines only depends on the words of the
language. -/
theorem mem_P_of_iff (h : ∀ x, x ∈ L₁ ↔ x ∈ L₂) (h₁ : L₁ ∈ P) : L₂ ∈ P :=
  let ⟨M, T, hT, hM, hL⟩ := h₁
  ⟨M, T, hT, hM, fun x => (hL x).trans (h x)⟩

theorem mem_NP_of_iff (h : ∀ x, x ∈ L₁ ↔ x ∈ L₂) (h₁ : L₁ ∈ NP) : L₂ ∈ NP :=
  let ⟨V, T, hT, hV, hL⟩ := h₁
  ⟨V, T, hT, hV, fun x => (hL x).trans (h x)⟩

/-! ### P ⊆ NP -/

/-- **P ⊆ NP.** A decider is a verifier that ignores its certificate. -/
theorem P_subset_NP : P ⊆ NP :=
  fun _ ⟨M, T, hT, hM, hL⟩ =>
    ⟨M.toAuxTM, T, hT, TM.toAuxTM_runsInTime hM,
      fun x => (TM.mem_toAuxTM_language hM x).trans (hL x)⟩

/-! ### Closure properties of P -/

/-- P is closed under complement: swap the accepting and rejecting states. -/
theorem compl_mem_P (h : L ∈ P) : L.compl ∈ P :=
  let ⟨M, T, hT, hM, hL⟩ := h
  ⟨M.compl, T, hT, TM.compl_runsInTime hM,
    fun x => (TM.mem_language_compl hM x).trans (not_congr (hL x))⟩

/-- **P ⊆ coNP.** -/
theorem P_subset_coNP : P ⊆ coNP :=
  fun _ h => P_subset_NP (compl_mem_P h)

theorem P_subset_NP_inter_coNP (h : L ∈ P) : L ∈ NP ∧ L ∈ coNP :=
  ⟨P_subset_NP h, P_subset_coNP h⟩

/-- The language of all words is in P. -/
theorem univ_mem_P : Language.univ ∈ P :=
  ⟨TM.idle, fun _ => 0, IsPolyBounded.const 0, TM.idle_runsInTime _,
    fun x => ⟨fun _ => trivial, fun _ => TM.mem_language_idle x⟩⟩

/-- The empty language is in P. -/
theorem empty_mem_P : (∅ : Language) ∈ P :=
  mem_P_of_iff
    (fun x => ⟨fun (h : x ∉ Language.univ) => h trivial,
      fun (h : x ∈ (∅ : Language)) => absurd h Language.not_mem_empty⟩)
    (compl_mem_P univ_mem_P)

theorem univ_mem_NP : Language.univ ∈ NP := P_subset_NP univ_mem_P

theorem empty_mem_NP : (∅ : Language) ∈ NP := P_subset_NP empty_mem_P

end Complexity
'''

CORE["PNP.Reduction.Basic"] = r'''import PNP.Machine.Compose
import PNP.Classes.Basic

/-!
# Polynomial-time many-one reductions

## Main definitions

* `Complexity.PolyTimeComputable`: functions on words computed by a Turing
  machine in polynomial time.
* `Complexity.PolyTimeReducible`, notation `A ≤ₚ B`: polynomial-time many-one
  (Karp) reducibility.

## Main results

* `Complexity.PolyTimeComputable.comp`: polynomial-time computable functions are
  closed under composition.
* `Complexity.PolyTimeReducible.refl`, `Complexity.PolyTimeReducible.trans`:
  `≤ₚ` is a preorder.
* `Complexity.PolyTimeReducible.mem_P`: P is closed downwards under `≤ₚ`.
* `Complexity.PolyTimeReducible.compl`: reductions pass to complements.

## Implementation notes

The time bound of a composite `g ∘ f` is `T₁(n) + 1 + T₂(|f x|)`. To express it
as a function of `n` alone we use that `|f x| ≤ n + 1 + T₁(n)`
(`TM.Computes.length_le`) and that the bound on `T₂` can be taken monotone
(`IsPolyBounded.exists_monotone_bound`). This is the only place where the length
of the output of a machine matters.

## References

* [Kar72] R. M. Karp, *Reducibility among combinatorial problems*, in
  *Complexity of Computer Computations*, Plenum, 1972.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Definitions
  7.28–7.29 and Theorem 7.31.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Definition 2.7.
-/

set_option autoImplicit false

namespace Complexity

/-- `f` is computed by a Turing machine in polynomial time. -/
def PolyTimeComputable (f : Word → Word) : Prop :=
  ∃ (M : TM) (T : ℕ → ℕ), IsPolyBounded T ∧ M.Computes f T

namespace PolyTimeComputable

variable {f g : Word → Word}

protected theorem id : PolyTimeComputable id :=
  ⟨TM.idle, fun _ => 0, IsPolyBounded.const 0, TM.idle_computes _⟩

/-- The output of a polynomial-time computable function is polynomially long. -/
theorem exists_length_le (hf : PolyTimeComputable f) :
    ∃ p : ℕ → ℕ, IsPolyBounded p ∧ ∀ x, (f x).length ≤ p x.length :=
  let ⟨_, T, hT, hM⟩ := hf
  ⟨fun n => n + 1 + T n, (IsPolyBounded.id.add_const 1).add hT, hM.length_le⟩

/-- Polynomial-time computable functions are closed under composition. -/
theorem comp (hg : PolyTimeComputable g) (hf : PolyTimeComputable f) :
    PolyTimeComputable (g ∘ f) := by
  obtain ⟨M₁, T₁, hT₁, h₁⟩ := hf
  obtain ⟨M₂, T₂, hT₂, h₂⟩ := hg
  obtain ⟨c, k, hck⟩ := hT₂.exists_monotone_bound
  refine ⟨TM.comp M₁ M₂, fun n => T₁ n + 1 + c * (n + 1 + T₁ n + 1) ^ k, ?_, ?_⟩
  · exact (hT₁.add_const 1).add
      (((((IsPolyBounded.id.add_const 1).add hT₁).add_const 1).pow k).const_mul c)
  · exact h₁.comp h₂ fun x => Nat.add_le_add_left (hck _ _ (h₁.length_le x)) _

end PolyTimeComputable

/-- `A` is polynomial-time many-one reducible to `B`: there is a polynomial-time
computable `f` with `x ∈ A ↔ f x ∈ B`. -/
def PolyTimeReducible (A B : Language) : Prop :=
  ∃ f : Word → Word, PolyTimeComputable f ∧ ∀ x, x ∈ A ↔ f x ∈ B

@[inherit_doc] infix:50 " ≤ₚ " => PolyTimeReducible

namespace PolyTimeReducible

variable {A B C : Language}

@[refl] protected theorem refl (A : Language) : A ≤ₚ A :=
  ⟨id, PolyTimeComputable.id, fun _ => Iff.rfl⟩

/-- Transitivity of polynomial-time reducibility. -/
protected theorem trans (hAB : A ≤ₚ B) (hBC : B ≤ₚ C) : A ≤ₚ C :=
  let ⟨f, hf, hfA⟩ := hAB
  let ⟨g, hg, hgB⟩ := hBC
  ⟨g ∘ f, hg.comp hf, fun x => (hfA x).trans (hgB (f x))⟩

instance : Trans PolyTimeReducible PolyTimeReducible PolyTimeReducible :=
  ⟨PolyTimeReducible.trans⟩

/-- A reduction from `A` to `B` is also a reduction between the complements. -/
protected theorem compl (h : A ≤ₚ B) : A.compl ≤ₚ B.compl :=
  let ⟨f, hf, hfA⟩ := h
  ⟨f, hf, fun x => not_congr (hfA x)⟩

theorem of_iff_left {A' : Language} (h : ∀ x, x ∈ A ↔ x ∈ A') (hAB : A ≤ₚ B) : A' ≤ₚ B :=
  let ⟨f, hf, hfA⟩ := hAB
  ⟨f, hf, fun x => (h x).symm.trans (hfA x)⟩

theorem of_iff_right {B' : Language} (h : ∀ x, x ∈ B ↔ x ∈ B') (hAB : A ≤ₚ B) : A ≤ₚ B' :=
  let ⟨f, hf, hfA⟩ := hAB
  ⟨f, hf, fun x => (hfA x).trans (h (f x))⟩

/-- **P is closed downwards under reductions**: if `A ≤ₚ B` and `B ∈ P` then
`A ∈ P`. The decider for `A` computes the reduction and then runs the decider
for `B`. -/
theorem mem_P (hAB : A ≤ₚ B) (hB : B ∈ P) : A ∈ P := by
  obtain ⟨f, ⟨M₁, T₁, hT₁, h₁⟩, hfA⟩ := hAB
  obtain ⟨M₂, T₂, hT₂, h₂, hL⟩ := hB
  obtain ⟨c, k, hck⟩ := hT₂.exists_monotone_bound
  have hT : ∀ x : Word, T₁ x.length + 1 + T₂ (f x).length ≤
      T₁ x.length + 1 + c * (x.length + 1 + T₁ x.length + 1) ^ k :=
    fun x => Nat.add_le_add_left (hck _ _ (h₁.length_le x)) _
  refine ⟨TM.comp M₁ M₂, fun n => T₁ n + 1 + c * (n + 1 + T₁ n + 1) ^ k, ?_,
    TM.comp_runsInTime (T := fun n => T₁ n + 1 + c * (n + 1 + T₁ n + 1) ^ k) h₁ h₂ hT,
    fun x => ?_⟩
  · exact (hT₁.add_const 1).add
      (((((IsPolyBounded.id.add_const 1).add hT₁).add_const 1).pow k).const_mul c)
  · exact (TM.mem_comp_language (T := fun n => T₁ n + 1 + c * (n + 1 + T₁ n + 1) ^ k)
      h₁ h₂ hT x).trans ((hL (f x)).trans (hfA x).symm)

/-- Contrapositive form: a problem that reduces from a hard problem is hard. -/
theorem not_mem_P (hAB : A ≤ₚ B) (hA : A ∉ P) : B ∉ P :=
  fun hB => hA (hAB.mem_P hB)

end PolyTimeReducible

end Complexity
'''

CORE["PNP.Reduction.NPComplete"] = r'''import PNP.Reduction.Basic

/-!
# NP-hardness and NP-completeness

## Main definitions

* `Complexity.NPHard`: every language in NP reduces to `L`.
* `Complexity.NPComplete`: `L` is in NP and NP-hard.

## Main results

* `Complexity.NPHard.of_reducible`: NP-hardness propagates along reductions.
* `Complexity.NPComplete.of_reducible`: the standard recipe for proving
  NP-completeness [Sip13, Theorem 7.36].
* `Complexity.NPHard.NP_subset_P`: if an NP-hard language is in P then NP ⊆ P.
* `Complexity.NPComplete.mem_P_iff`: an NP-complete language is in P if and only
  if P = NP [Sip13, Theorem 7.35].

## References

* [Coo71] S. A. Cook, *The complexity of theorem-proving procedures*, STOC 1971.
* [Kar72] R. M. Karp, *Reducibility among combinatorial problems*, 1972.
* [Lev73] L. A. Levin, *Universal sequential search problems*, 1973.
* [GJ79] M. R. Garey, D. S. Johnson, *Computers and Intractability: A Guide to
  the Theory of NP-Completeness*, W. H. Freeman, 1979.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, §7.4.
-/

set_option autoImplicit false

namespace Complexity

/-- `L` is NP-hard: every language in NP is polynomial-time reducible to `L`. -/
def NPHard (L : Language) : Prop := ∀ ⦃A : Language⦄, A ∈ NP → A ≤ₚ L

/-- `L` is NP-complete: it is in NP and NP-hard. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

variable {A B L : Language}

namespace NPHard

/-- If `A` is NP-hard and `A ≤ₚ B` then `B` is NP-hard. -/
theorem of_reducible (hA : NPHard A) (hAB : A ≤ₚ B) : NPHard B :=
  fun _ hC => (hA hC).trans hAB

/-- If an NP-hard language is in P then NP ⊆ P. -/
theorem NP_subset_P (hL : NPHard L) (hP : L ∈ P) : NP ⊆ P :=
  fun _ hA => (hL hA).mem_P hP

theorem P_eq_NP (hL : NPHard L) (hP : L ∈ P) : P = NP :=
  ComplexityClass.Subset.antisymm P_subset_NP (hL.NP_subset_P hP)

end NPHard

namespace NPComplete

theorem mem_NP (h : NPComplete L) : L ∈ NP := h.1

theorem npHard (h : NPComplete L) : NPHard L := h.2

/-- If `A` is NP-complete, `B ∈ NP` and `A ≤ₚ B`, then `B` is NP-complete. -/
theorem of_reducible (hA : NPComplete A) (hB : B ∈ NP) (hAB : A ≤ₚ B) : NPComplete B :=
  ⟨hB, hA.npHard.of_reducible hAB⟩

/-- Two NP-complete languages are reducible to each other. -/
theorem reducible (hA : NPComplete A) (hB : NPComplete B) : A ≤ₚ B := hB.npHard hA.mem_NP

/-- An NP-complete language is in P if and only if P = NP. -/
theorem mem_P_iff (h : NPComplete L) : L ∈ P ↔ P = NP :=
  ⟨h.npHard.P_eq_NP, fun e => e ▸ h.mem_NP⟩

theorem not_mem_P (h : NPComplete L) (hne : P ≠ NP) : L ∉ P :=
  fun hP => hne (h.mem_P_iff.1 hP)

end NPComplete

end Complexity
'''

CORE["PNP.Machine.Examples"] = r'''import PNP.Reduction.Basic

/-!
# Examples of Turing machines

Three small machines, used to test the definitions of `PNP.Machine.TM` on
concrete inputs.

## Main definitions

* `Complexity.TM.parity`: accepts the words with an even number of ones.
* `Complexity.TM.containsOne`: accepts the words that contain a one.
* `Complexity.TM.flipFirst`: negates the first bit of its input.
* `Complexity.TM.flipFirstFn`: the function computed by `flipFirst`.

## Main results

* `Complexity.TM.flipFirst_computes`: `flipFirst` computes `flipFirstFn` in one
  step.
* `Complexity.TM.polyTimeComputable_flipFirstFn`: hence `flipFirstFn` is
  polynomial-time computable.
* Test vectors: for a fixed set of inputs, membership in the languages of
  `parity` and `containsOne`, halting times of `parity`, and the output tape of
  `flipFirst`.

## Implementation notes

The test vectors are proved by evaluating the machines in the kernel
(`rfl`), through `TM.mem_language_of_run` and `TM.not_mem_language_of_run`.
-/

set_option autoImplicit false

namespace Complexity

namespace TM

/-- A machine that accepts the words with an even number of ones. It scans the
input once from left to right, keeping the parity in its state. -/
def parity : TM where
  State := Bool
  start := false
  accepting := fun q => !q
  δ := fun q a =>
    match a with
    | none => none
    | some b => some (q != b, some b, Dir.right)

/-- A machine that accepts the words containing a one. It scans the input from
left to right and stops at the first one. -/
def containsOne : TM where
  State := Bool
  start := false
  accepting := fun q => q
  δ := fun q a =>
    match q, a with
    | false, some false => some (false, some false, Dir.right)
    | false, some true => some (true, some true, Dir.stay)
    | _, _ => none

/-- A machine that negates the first bit of its input and halts. -/
def flipFirst : TM where
  State := Bool
  start := false
  accepting := fun _ => true
  δ := fun q a =>
    match q, a with
    | false, some b => some (true, some (!b), Dir.stay)
    | _, _ => none

/-- Negate the first bit of a word. -/
def flipFirstFn : Word → Word
  | [] => []
  | b :: w => (!b) :: w

/-- `flipFirst` computes `flipFirstFn` in one step. -/
theorem flipFirst_computes : flipFirst.Computes flipFirstFn fun _ => 1 := by
  intro x
  cases x with
  | nil => exact ⟨rfl, rfl⟩
  | cons b w => cases b <;> exact ⟨rfl, rfl⟩

theorem polyTimeComputable_flipFirstFn : PolyTimeComputable flipFirstFn :=
  ⟨flipFirst, fun _ => 1, IsPolyBounded.const 1, flipFirst_computes⟩

theorem flipFirstFn_flipFirstFn (x : Word) : flipFirstFn (flipFirstFn x) = x := by
  cases x with
  | nil => rfl
  | cons b w => cases b <;> rfl

theorem length_flipFirstFn (x : Word) : (flipFirstFn x).length = x.length := by
  cases x <;> rfl

--FILLER:machines

end TM

end Complexity
'''

CORE["PNP.Problems.SAT"] = r'''import PNP.Data.Encoding
import PNP.Reduction.NPComplete

/-!
# Boolean satisfiability

Propositional formulas in conjunctive normal form, and the languages SAT and
3-SAT.

## Main definitions

* `Complexity.Literal`, `Complexity.Clause`, `Complexity.CNF`: formulas in
  conjunctive normal form.
* `Complexity.Literal.eval`, `Complexity.Clause.eval`, `Complexity.CNF.eval`:
  evaluation under an assignment.
* `Complexity.CNF.Satisfiable`: satisfiability.
* `Complexity.CNF.IsKCNF`: every clause has at most `k` literals.
* `Complexity.SAT`, `Complexity.ThreeSAT`: the languages.
* `Complexity.CookLevin`: the statement that SAT is NP-complete.

## Main results

* `Complexity.CNF.eval_append`: a conjunction holds iff both parts hold.
* `Complexity.CNF.not_satisfiable_of_nil_mem`: a formula with an empty clause is
  unsatisfiable.
* `Complexity.CNF.Satisfiable.of_subset`: satisfiability is antitone in the set
  of clauses.
* `Complexity.threeSAT_subset_SAT`: every yes-instance of 3-SAT is a yes-instance
  of SAT.
* `Complexity.CookLevin.sat_mem_P_iff`: given the Cook–Levin theorem, SAT ∈ P is
  equivalent to P = NP.

## Implementation notes

A literal is a variable index together with a polarity. Clauses and formulas are
lists, so that the encoding of a formula is obtained from the instances of
`PNP.Data.Encoding`. Assignments are total functions `ℕ → Bool`; only the values
on the variables that occur in a formula matter (`CNF.eval_congr`).

The Cook–Levin theorem [Coo71; Lev73] is stated as the proposition `CookLevin`
and is not proved in this file: the tableau construction requires a formalised
encoding of machine computations as formulas, which is left for future work. No
result outside this file depends on it.

## References

* [Coo71] S. A. Cook, *The complexity of theorem-proving procedures*, STOC 1971.
* [Lev73] L. A. Levin, *Universal sequential search problems*, 1973.
* [Kar72] R. M. Karp, *Reducibility among combinatorial problems*, 1972.
* [GJ79] M. R. Garey, D. S. Johnson, *Computers and Intractability*, problems
  LO1 and LO2.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Theorem 7.37.
-/

set_option autoImplicit false

namespace Complexity

/-- A literal: a variable, possibly negated. -/
structure Literal where
  /-- The index of the variable. -/
  var : ℕ
  /-- Whether the literal is negated. -/
  neg : Bool
  deriving DecidableEq, Repr

/-- A clause is a disjunction of literals. -/
abbrev Clause : Type := List Literal

/-- A formula in conjunctive normal form is a conjunction of clauses. -/
abbrev CNF : Type := List Clause

/-- A truth assignment. -/
abbrev Assignment : Type := ℕ → Bool

instance : Encoding Literal :=
  Encoding.ofLeftInverse (fun l => (l.var, l.neg)) (fun p => ⟨p.1, p.2⟩) fun _ => rfl

namespace Literal

/-- The value of a literal under an assignment. -/
def eval (σ : Assignment) (l : Literal) : Bool := σ l.var != l.neg

/-- The positive literal on variable `i`. -/
def pos (i : ℕ) : Literal := ⟨i, false⟩

/-- The complementary literal. -/
def not (l : Literal) : Literal := ⟨l.var, !l.neg⟩

@[simp] theorem eval_pos (σ : Assignment) (i : ℕ) : (pos i).eval σ = σ i := by
  simp [eval, pos]

@[simp] theorem eval_not (σ : Assignment) (l : Literal) : l.not.eval σ = !l.eval σ := by
  cases h : σ l.var <;> cases h' : l.neg <;> simp [eval, not, h, h']

@[simp] theorem not_not (l : Literal) : l.not.not = l := by
  cases l; simp [not]

theorem eval_congr {σ τ : Assignment} {l : Literal} (h : σ l.var = τ l.var) :
    l.eval σ = l.eval τ := by
  simp [eval, h]

end Literal

namespace Clause

/-- The value of a clause: some literal is true. -/
def eval (σ : Assignment) (c : Clause) : Bool := c.any (Literal.eval σ)

@[simp] theorem eval_nil (σ : Assignment) : eval σ [] = false := rfl

@[simp] theorem eval_cons (σ : Assignment) (l : Literal) (c : Clause) :
    eval σ (l :: c) = (l.eval σ || eval σ c) := rfl

@[simp] theorem eval_append (σ : Assignment) (c d : Clause) :
    eval σ (c ++ d) = (eval σ c || eval σ d) := by
  simp [eval]

theorem eval_eq_true_iff {σ : Assignment} {c : Clause} :
    eval σ c = true ↔ ∃ l, l ∈ c ∧ l.eval σ = true := by
  simp [eval]

theorem eval_of_mem {σ : Assignment} {c : Clause} {l : Literal} (hl : l ∈ c)
    (h : l.eval σ = true) : eval σ c = true :=
  eval_eq_true_iff.2 ⟨l, hl, h⟩

theorem eval_congr {σ τ : Assignment} {c : Clause} (h : ∀ l, l ∈ c → σ l.var = τ l.var) :
    eval σ c = eval τ c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    rw [eval_cons, eval_cons, Literal.eval_congr (h l (List.mem_cons_self _ _)),
      ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

end Clause

namespace CNF

/-- The value of a formula: every clause is true. -/
def eval (σ : Assignment) (φ : CNF) : Bool := φ.all (Clause.eval σ)

/-- A formula is satisfiable if some assignment makes it true. -/
def Satisfiable (φ : CNF) : Prop := ∃ σ : Assignment, eval σ φ = true

/-- Every clause of `φ` has at most `k` literals. -/
def IsKCNF (k : ℕ) (φ : CNF) : Prop := ∀ c, c ∈ φ → c.length ≤ k

instance (k : ℕ) (φ : CNF) : Decidable (IsKCNF k φ) :=
  inferInstanceAs (Decidable (∀ c, c ∈ φ → c.length ≤ k))

@[simp] theorem eval_nil (σ : Assignment) : eval σ [] = true := rfl

@[simp] theorem eval_cons (σ : Assignment) (c : Clause) (φ : CNF) :
    eval σ (c :: φ) = (Clause.eval σ c && eval σ φ) := rfl

@[simp] theorem eval_append (σ : Assignment) (φ ψ : CNF) :
    eval σ (φ ++ ψ) = (eval σ φ && eval σ ψ) := by
  simp [eval]

theorem eval_eq_true_iff {σ : Assignment} {φ : CNF} :
    eval σ φ = true ↔ ∀ c, c ∈ φ → Clause.eval σ c = true := by
  simp [eval]

theorem eval_congr {σ τ : Assignment} {φ : CNF}
    (h : ∀ c, c ∈ φ → ∀ l, l ∈ c → σ l.var = τ l.var) : eval σ φ = eval τ φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    rw [eval_cons, eval_cons, Clause.eval_congr (h c (List.mem_cons_self _ _)),
      ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]

/-- The empty formula is satisfiable. -/
theorem satisfiable_nil : Satisfiable [] := ⟨fun _ => false, rfl⟩

/-- A formula that contains the empty clause is unsatisfiable. -/
theorem not_satisfiable_of_nil_mem {φ : CNF} (h : [] ∈ φ) : ¬Satisfiable φ := by
  rintro ⟨σ, hσ⟩
  have := eval_eq_true_iff.1 hσ [] h
  simp at this

/-- A formula all of whose clauses occur in a satisfiable formula is
satisfiable. -/
theorem Satisfiable.of_subset {φ ψ : CNF} (hψ : Satisfiable ψ) (h : ∀ c, c ∈ φ → c ∈ ψ) :
    Satisfiable φ :=
  let ⟨σ, hσ⟩ := hψ
  ⟨σ, eval_eq_true_iff.2 fun c hc => eval_eq_true_iff.1 hσ c (h c hc)⟩

theorem Satisfiable.of_append_left {φ ψ : CNF} (h : Satisfiable (φ ++ ψ)) : Satisfiable φ :=
  h.of_subset fun _ hc => List.mem_append_left _ hc

theorem Satisfiable.of_append_right {φ ψ : CNF} (h : Satisfiable (φ ++ ψ)) : Satisfiable ψ :=
  h.of_subset fun _ hc => List.mem_append_right _ hc

theorem Satisfiable.of_cons {c : Clause} {φ : CNF} (h : Satisfiable (c :: φ)) : Satisfiable φ :=
  h.of_subset fun _ hc => List.mem_cons_of_mem _ hc

/-- A unit clause and its negation are jointly unsatisfiable. -/
theorem not_satisfiable_unit_not (l : Literal) : ¬Satisfiable [[l], [l.not]] := by
  rintro ⟨σ, hσ⟩
  cases h : l.eval σ <;> simp [eval, Clause.eval, h] at hσ

theorem isKCNF_nil (k : ℕ) : IsKCNF k [] := fun _ h => nomatch h

theorem IsKCNF.mono {k k' : ℕ} {φ : CNF} (h : IsKCNF k φ) (hk : k ≤ k') : IsKCNF k' φ :=
  fun c hc => Nat.le_trans (h c hc) hk

theorem IsKCNF.append {k : ℕ} {φ ψ : CNF} (hφ : IsKCNF k φ) (hψ : IsKCNF k ψ) :
    IsKCNF k (φ ++ ψ) :=
  fun c hc => (List.mem_append.1 hc).elim (hφ c) (hψ c)

theorem IsKCNF.of_cons {k : ℕ} {c : Clause} {φ : CNF} (h : IsKCNF k (c :: φ)) : IsKCNF k φ :=
  fun c' hc' => h c' (List.mem_cons_of_mem _ hc')

end CNF

/-- **SAT**: the language of satisfiable formulas in conjunctive normal form. -/
def SAT : Language := Encoding.languageOf CNF.Satisfiable

/-- **3-SAT**: the language of satisfiable formulas with at most three literals
per clause. -/
def ThreeSAT : Language := Encoding.languageOf fun φ : CNF => φ.IsKCNF 3 ∧ φ.Satisfiable

theorem encode_mem_SAT {φ : CNF} : Encoding.encode φ ∈ SAT ↔ φ.Satisfiable :=
  Encoding.mem_languageOf_encode

theorem encode_mem_ThreeSAT {φ : CNF} :
    Encoding.encode φ ∈ ThreeSAT ↔ φ.IsKCNF 3 ∧ φ.Satisfiable :=
  Encoding.mem_languageOf_encode

/-- Every yes-instance of 3-SAT is a yes-instance of SAT. -/
theorem threeSAT_subset_SAT {w : Word} (h : w ∈ ThreeSAT) : w ∈ SAT :=
  Encoding.languageOf_mono (fun _ h => h.2) h

/-- The **Cook–Levin theorem** [Coo71; Lev73], as a proposition: SAT is
NP-complete. -/
def CookLevin : Prop := NPComplete SAT

namespace CookLevin

/-- Given the Cook–Levin theorem, SAT ∈ P is equivalent to P = NP. -/
theorem sat_mem_P_iff (h : CookLevin) : SAT ∈ P ↔ P = NP := NPComplete.mem_P_iff h

/-- Given the Cook–Levin theorem, a language in NP to which SAT reduces is
NP-complete. This is the entry point for Karp's reductions [Kar72]. -/
theorem npComplete_of_reducible (h : CookLevin) {L : Language} (hL : L ∈ NP)
    (hred : SAT ≤ₚ L) : NPComplete L :=
  NPComplete.of_reducible h hL hred

end CookLevin

end Complexity
'''

CORE["PNP.Problems.SAT.Examples"] = r'''import PNP.Problems.SAT

/-!
# Small instances of SAT

A collection of small formulas with known status, in the spirit of the uniform
random 3-SAT families `uf` and `uuf` of SATLIB [HS00]. They serve as test
vectors for the evaluation functions, for the encoding, and for the membership
lemmas of `PNP.Problems.SAT`.

## Main definitions

* `Complexity.uf_n_m_i`: the `i`-th satisfiable instance with `n` variables and
  `m` clauses.
* `Complexity.uuf_n_m_i`: the `i`-th unsatisfiable instance with `n` variables
  and `m` clauses.

## Main results

For each satisfiable instance: a satisfying assignment, the bound on the clause
width, and membership of the encoding in 3-SAT. For each unsatisfiable instance:
a proof of unsatisfiability by case analysis on the variables, and
non-membership of the encoding in SAT.

## References

* [HS00] H. H. Hoos, T. Stützle, *SATLIB: An online resource for research on
  SAT*, in *SAT 2000*, IOS Press, 2000.
-/

set_option autoImplicit false

namespace Complexity

--FILLER:sat

end Complexity
'''

CORE["PNP.Problems.Graph"] = r'''import PNP.Data.Encoding
import PNP.Reduction.NPComplete

/-!
# Graph problems: CLIQUE, INDEPENDENT-SET and VERTEX-COVER

Finite simple graphs given by edge lists, and three of Karp's problems on them.

## Main definitions

* `Complexity.Graph`: a finite graph on the vertices `0, …, order - 1`, given by
  a list of edges.
* `Complexity.Graph.Adj`: the (symmetric, irreflexive) adjacency relation.
* `Complexity.Graph.IsClique`, `Complexity.Graph.IsIndependentSet`,
  `Complexity.Graph.IsVertexCover`: the three notions, for lists of vertices.
* `Complexity.Graph.IsCompl`: two graphs are complementary.
* `Complexity.CLIQUE`, `Complexity.INDEPENDENT_SET`, `Complexity.VERTEX_COVER`:
  the languages.
* `Complexity.Graph.complete`, `Complexity.Graph.cycle`, `Complexity.Graph.path`,
  `Complexity.Graph.star`, `Complexity.Graph.completeBipartite`: standard
  families.

## Main results

* `Complexity.Graph.isClique_iff_isIndependentSet_of_isCompl`: cliques of a graph
  are the independent sets of its complement [Kar72].
* `Complexity.Graph.isVertexCover_iff_isIndependentSet_of_compl`: a set of
  vertices is a vertex cover iff its complement is independent [GJ79, Lemma 3.1].
* `Complexity.Graph.isVertexCover_iff_forall_adj`: vertex covers in terms of
  adjacency.

## Implementation notes

A graph is an edge list on an initial segment of `ℕ`; this is the representation
that is encoded as a word. Adjacency is derived from the edge list by
symmetrising and discarding loops, so no well-formedness condition is imposed on
instances and every word that decodes to a `Graph` is a legal instance.

Vertex sets are duplicate-free lists of vertices. All predicates on them are
decidable, which is used for the small cases in `PNP.Problems.Graph.Examples`.

The two classical equivalences are proved at the level of the combinatorial
predicates. The corresponding maps on encodings (complementing an edge list,
replacing `k` by `n - k`) are computable in polynomial time; their machine-level
implementation is not part of this file.

## References

* [Kar72] R. M. Karp, *Reducibility among combinatorial problems*, 1972.
* [GJ79] M. R. Garey, D. S. Johnson, *Computers and Intractability*, §3.1 and
  problems GT1, GT19, GT20.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Theorems 7.32
  and 7.44.
-/

set_option autoImplicit false

namespace Complexity

/-- A finite graph on the vertices `0, …, order - 1`, given by a list of edges. -/
structure Graph where
  /-- The number of vertices. -/
  order : ℕ
  /-- The list of edges. Orientation, repetitions and loops are irrelevant. -/
  edges : List (ℕ × ℕ)
  deriving DecidableEq, Repr

instance : Encoding Graph :=
  Encoding.ofLeftInverse (fun G => (G.order, G.edges)) (fun p => ⟨p.1, p.2⟩) fun _ => rfl

namespace Graph

variable {G H : Graph} {S S' : List ℕ} {u v : ℕ}

/-- Two distinct vertices are adjacent if they are joined by an edge, in either
orientation. -/
def Adj (G : Graph) (u v : ℕ) : Prop := u ≠ v ∧ ((u, v) ∈ G.edges ∨ (v, u) ∈ G.edges)

instance (G : Graph) (u v : ℕ) : Decidable (G.Adj u v) :=
  inferInstanceAs (Decidable (u ≠ v ∧ ((u, v) ∈ G.edges ∨ (v, u) ∈ G.edges)))

/-- A duplicate-free list of vertices of `G`. -/
def IsVertexSet (G : Graph) (S : List ℕ) : Prop := S.Nodup ∧ ∀ v, v ∈ S → v < G.order

/-- Any two distinct vertices of `S` are adjacent. -/
def IsClique (G : Graph) (S : List ℕ) : Prop :=
  ∀ u, u ∈ S → ∀ v, v ∈ S → u ≠ v → G.Adj u v

/-- No two vertices of `S` are adjacent. -/
def IsIndependentSet (G : Graph) (S : List ℕ) : Prop :=
  ∀ u, u ∈ S → ∀ v, v ∈ S → ¬G.Adj u v

/-- Every edge that is not a loop has an endpoint in `S`. -/
def IsVertexCover (G : Graph) (S : List ℕ) : Prop :=
  ∀ e, e ∈ G.edges → e.1 ≠ e.2 → e.1 ∈ S ∨ e.2 ∈ S

instance (G : Graph) (S : List ℕ) : Decidable (G.IsVertexSet S) :=
  inferInstanceAs (Decidable (S.Nodup ∧ ∀ v, v ∈ S → v < G.order))

instance (G : Graph) (S : List ℕ) : Decidable (G.IsClique S) :=
  inferInstanceAs (Decidable (∀ u, u ∈ S → ∀ v, v ∈ S → u ≠ v → G.Adj u v))

instance (G : Graph) (S : List ℕ) : Decidable (G.IsIndependentSet S) :=
  inferInstanceAs (Decidable (∀ u, u ∈ S → ∀ v, v ∈ S → ¬G.Adj u v))

instance (G : Graph) (S : List ℕ) : Decidable (G.IsVertexCover S) :=
  inferInstanceAs (Decidable (∀ e, e ∈ G.edges → e.1 ≠ e.2 → e.1 ∈ S ∨ e.2 ∈ S))

/-- `G` has a clique with `k` vertices. -/
def HasClique (G : Graph) (k : ℕ) : Prop :=
  ∃ S, G.IsVertexSet S ∧ S.length = k ∧ G.IsClique S

/-- `G` has an independent set with `k` vertices. -/
def HasIndependentSet (G : Graph) (k : ℕ) : Prop :=
  ∃ S, G.IsVertexSet S ∧ S.length = k ∧ G.IsIndependentSet S

/-- `G` has a vertex cover with at most `k` vertices. -/
def HasVertexCover (G : Graph) (k : ℕ) : Prop :=
  ∃ S, G.IsVertexSet S ∧ S.length ≤ k ∧ G.IsVertexCover S

/-- `H` is a complement of `G`: distinct vertices are adjacent in `H` iff they
are not adjacent in `G`. -/
def IsCompl (G H : Graph) : Prop := ∀ u v, u ≠ v → (H.Adj u v ↔ ¬G.Adj u v)

/-! ### Adjacency -/

theorem Adj.ne (h : G.Adj u v) : u ≠ v := h.1

theorem Adj.symm (h : G.Adj u v) : G.Adj v u := ⟨fun e => h.1 e.symm, h.2.symm⟩

theorem adj_comm : G.Adj u v ↔ G.Adj v u := ⟨Adj.symm, Adj.symm⟩

theorem not_adj_self (G : Graph) (v : ℕ) : ¬G.Adj v v := fun h => h.1 rfl

theorem adj_of_mem_edges (h : (u, v) ∈ G.edges) (hne : u ≠ v) : G.Adj u v := ⟨hne, Or.inl h⟩

/-- Adjacency is monotone in the edge list. -/
theorem Adj.mono (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges) (h : G.Adj u v) : H.Adj u v :=
  ⟨h.1, h.2.imp (hGH _) (hGH _)⟩

theorem IsCompl.symm (h : G.IsCompl H) : H.IsCompl G := by
  intro u v hne
  have := h u v hne
  constructor
  · intro hG hH
    exact this.1 hH hG
  · intro hH
    exact Decidable.by_contra fun hG => hH (this.2 hG)

/-! ### Cliques and independent sets -/

theorem isClique_nil (G : Graph) : G.IsClique [] := fun _ h => nomatch h

theorem isClique_singleton (G : Graph) (v : ℕ) : G.IsClique [v] := by
  intro a ha b hb hne
  rw [List.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) hne

theorem isIndependentSet_nil (G : Graph) : G.IsIndependentSet [] := fun _ h => nomatch h

theorem isIndependentSet_singleton (G : Graph) (v : ℕ) : G.IsIndependentSet [v] := by
  intro a ha b hb
  rw [List.mem_singleton] at ha hb
  rw [ha, hb]
  exact G.not_adj_self v

/-- A subset of a clique is a clique. -/
theorem IsClique.subset (h : G.IsClique S) (hS : ∀ v, v ∈ S' → v ∈ S) : G.IsClique S' :=
  fun a ha b hb => h a (hS a ha) b (hS b hb)

/-- A subset of an independent set is independent. -/
theorem IsIndependentSet.subset (h : G.IsIndependentSet S) (hS : ∀ v, v ∈ S' → v ∈ S) :
    G.IsIndependentSet S' :=
  fun a ha b hb => h a (hS a ha) b (hS b hb)

/-- Cliques are preserved by adding edges. -/
theorem IsClique.mono (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges) (h : G.IsClique S) :
    H.IsClique S :=
  fun a ha b hb hne => (h a ha b hb hne).mono hGH

/-- Independent sets are preserved by removing edges. -/
theorem IsIndependentSet.anti (hHG : ∀ e, e ∈ H.edges → e ∈ G.edges)
    (h : G.IsIndependentSet S) : H.IsIndependentSet S :=
  fun a ha b hb hadj => h a ha b hb (hadj.mono hHG)

theorem isIndependentSet_iff :
    G.IsIndependentSet S ↔ ∀ u v, G.Adj u v → u ∉ S ∨ v ∉ S := by
  constructor
  · intro h a b hadj
    exact Decidable.not_and_iff_or_not.1 fun hab => h a hab.1 b hab.2 hadj
  · intro h a ha b hb hadj
    exact (h a b hadj).elim (fun hn => hn ha) (fun hn => hn hb)

/-- **Cliques and independent sets** [Kar72]. A set of vertices is a clique of
`G` iff it is an independent set of the complement of `G`. -/
theorem isClique_iff_isIndependentSet_of_isCompl (h : G.IsCompl H) :
    G.IsClique S ↔ H.IsIndependentSet S := by
  constructor
  · intro hS a ha b hb hadj
    exact (h a b hadj.ne).1 hadj (hS a ha b hb hadj.ne)
  · intro hS a ha b hb hne
    exact Decidable.by_contra fun hG => hS a ha b hb ((h a b hne).2 hG)

theorem hasClique_iff_hasIndependentSet_of_isCompl (h : G.IsCompl H) (ho : G.order = H.order)
    (k : ℕ) : G.HasClique k ↔ H.HasIndependentSet k := by
  constructor
  · rintro ⟨S, ⟨hnd, hlt⟩, hk, hS⟩
    exact ⟨S, ⟨hnd, fun v hv => ho ▸ hlt v hv⟩, hk,
      (isClique_iff_isIndependentSet_of_isCompl h).1 hS⟩
  · rintro ⟨S, ⟨hnd, hlt⟩, hk, hS⟩
    exact ⟨S, ⟨hnd, fun v hv => ho ▸ hlt v hv⟩, hk,
      (isClique_iff_isIndependentSet_of_isCompl h).2 hS⟩

/-! ### Vertex covers -/

/-- A set of vertices is a vertex cover iff it meets every pair of adjacent
vertices. -/
theorem isVertexCover_iff_forall_adj :
    G.IsVertexCover S ↔ ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S := by
  constructor
  · intro h a b hadj
    rcases hadj.2 with he | he
    · exact h (a, b) he hadj.1
    · exact (h (b, a) he fun e => hadj.1 e.symm).symm
  · intro h e he hne
    exact h e.1 e.2 ⟨hne, Or.inl he⟩

theorem isVertexCover_nil_edges (S : List ℕ) (n : ℕ) : (Graph.mk n []).IsVertexCover S :=
  fun _ h => nomatch h

/-- A superset of a vertex cover is a vertex cover. -/
theorem IsVertexCover.superset (h : G.IsVertexCover S) (hS : ∀ v, v ∈ S → v ∈ S') :
    G.IsVertexCover S' :=
  fun e he hne => (h e he hne).imp (hS _) (hS _)

/-- Vertex covers are preserved by removing edges. -/
theorem IsVertexCover.anti (hHG : ∀ e, e ∈ H.edges → e ∈ G.edges) (h : G.IsVertexCover S) :
    H.IsVertexCover S :=
  fun e he => h e (hHG e he)

/-- **Vertex covers and independent sets** [GJ79, Lemma 3.1]. If `T` is the
complement of `S`, then `S` is independent iff `T` is a vertex cover. -/
theorem isVertexCover_iff_isIndependentSet_of_compl {T : List ℕ} (h : ∀ v, v ∈ T ↔ v ∉ S) :
    G.IsVertexCover T ↔ G.IsIndependentSet S := by
  rw [isVertexCover_iff_forall_adj, isIndependentSet_iff]
  constructor
  · intro hT a b hadj
    exact (hT a b hadj).imp (h a).1 (h b).1
  · intro hS a b hadj
    exact (hS a b hadj).imp (h a).2 (h b).2

/-! ### Trivial instances -/

theorem isVertexSet_nil (G : Graph) : G.IsVertexSet [] := ⟨List.nodup_nil, fun _ h => nomatch h⟩

theorem hasClique_zero (G : Graph) : G.HasClique 0 := ⟨[], G.isVertexSet_nil, rfl, G.isClique_nil⟩

theorem hasIndependentSet_zero (G : Graph) : G.HasIndependentSet 0 :=
  ⟨[], G.isVertexSet_nil, rfl, G.isIndependentSet_nil⟩

theorem HasVertexCover.mono {k k' : ℕ} (h : G.HasVertexCover k) (hk : k ≤ k') :
    G.HasVertexCover k' :=
  let ⟨S, hS, hlen, hc⟩ := h
  ⟨S, hS, Nat.le_trans hlen hk, hc⟩

theorem hasVertexCover_of_edges_nil (n k : ℕ) : (Graph.mk n []).HasVertexCover k :=
  ⟨[], isVertexSet_nil _, Nat.zero_le _, isVertexCover_nil_edges _ _⟩

/-! ### Standard families -/

/-- The complete graph on `n` vertices. -/
def complete (n : ℕ) : Graph :=
  ⟨n, ((List.range (n * n)).map fun i => (i / n, i % n)).filter fun e => e.1 < e.2⟩

/-- The cycle on `n` vertices. -/
def cycle (n : ℕ) : Graph := ⟨n, (List.range n).map fun i => (i, (i + 1) % n)⟩

/-- The path on `n` vertices. -/
def path (n : ℕ) : Graph := ⟨n, (List.range (n - 1)).map fun i => (i, i + 1)⟩

/-- The star with centre `0` and `n` leaves. -/
def star (n : ℕ) : Graph := ⟨n + 1, (List.range n).map fun i => (0, i + 1)⟩

/-- The complete bipartite graph with sides `0, …, m - 1` and `m, …, m + n - 1`. -/
def completeBipartite (m n : ℕ) : Graph :=
  ⟨m + n, (List.range (m * n)).map fun i => (i / n, m + i % n)⟩

/-- The graph on `n` vertices without edges. -/
def edgeless (n : ℕ) : Graph := ⟨n, []⟩

@[simp] theorem order_complete (n : ℕ) : (complete n).order = n := rfl

@[simp] theorem order_cycle (n : ℕ) : (cycle n).order = n := rfl

@[simp] theorem order_path (n : ℕ) : (path n).order = n := rfl

@[simp] theorem order_star (n : ℕ) : (star n).order = n + 1 := rfl

@[simp] theorem order_completeBipartite (m n : ℕ) : (completeBipartite m n).order = m + n := rfl

theorem isIndependentSet_edgeless (n : ℕ) (S : List ℕ) : (edgeless n).IsIndependentSet S :=
  fun _ _ _ _ h => h.2.elim (fun h => nomatch h) (fun h => nomatch h)

/-- The centre of a star is a vertex cover. -/
theorem isVertexCover_star (n : ℕ) : (star n).IsVertexCover [0] := by
  intro e he _
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  exact Or.inl (List.mem_singleton.2 rfl)

theorem hasVertexCover_star (n : ℕ) : (star n).HasVertexCover 1 :=
  ⟨[0], ⟨by decide, fun v hv => by
    rw [List.mem_singleton.1 hv]; exact Nat.succ_pos n⟩, Nat.le_refl _, isVertexCover_star n⟩

end Graph

/-- **CLIQUE**: pairs `(G, k)` such that `G` has a clique with `k` vertices. -/
def CLIQUE : Language := Encoding.languageOf fun p : Graph × ℕ => p.1.HasClique p.2

/-- **INDEPENDENT-SET**: pairs `(G, k)` such that `G` has an independent set with
`k` vertices. -/
def INDEPENDENT_SET : Language :=
  Encoding.languageOf fun p : Graph × ℕ => p.1.HasIndependentSet p.2

/-- **VERTEX-COVER**: pairs `(G, k)` such that `G` has a vertex cover with at
most `k` vertices. -/
def VERTEX_COVER : Language := Encoding.languageOf fun p : Graph × ℕ => p.1.HasVertexCover p.2

theorem encode_mem_CLIQUE {G : Graph} {k : ℕ} :
    Encoding.encode (G, k) ∈ CLIQUE ↔ G.HasClique k :=
  Encoding.mem_languageOf_encode

theorem encode_mem_INDEPENDENT_SET {G : Graph} {k : ℕ} :
    Encoding.encode (G, k) ∈ INDEPENDENT_SET ↔ G.HasIndependentSet k :=
  Encoding.mem_languageOf_encode

theorem encode_mem_VERTEX_COVER {G : Graph} {k : ℕ} :
    Encoding.encode (G, k) ∈ VERTEX_COVER ↔ G.HasVertexCover k :=
  Encoding.mem_languageOf_encode

/-- On encodings of complementary graphs, CLIQUE and INDEPENDENT-SET agree. -/
theorem encode_mem_CLIQUE_iff_of_isCompl {G H : Graph} (h : G.IsCompl H)
    (ho : G.order = H.order) (k : ℕ) :
    Encoding.encode (G, k) ∈ CLIQUE ↔ Encoding.encode (H, k) ∈ INDEPENDENT_SET := by
  rw [encode_mem_CLIQUE, encode_mem_INDEPENDENT_SET]
  exact Graph.hasClique_iff_hasIndependentSet_of_isCompl h ho k

end Complexity
'''

CORE["PNP.Problems.HamCycle"] = r'''import PNP.Problems.Graph

/-!
# Hamiltonian cycles

## Main definitions

* `Complexity.Graph.IsCycle`: consecutive vertices of a list, taken cyclically,
  are adjacent.
* `Complexity.Graph.IsHamCycle`: a cycle through every vertex exactly once.
* `Complexity.Graph.HasHamCycle`: the graph is Hamiltonian.
* `Complexity.HAM_CYCLE`: the language of Hamiltonian graphs.

## Main results

* `Complexity.Graph.IsCycle.mono`: cycles are preserved by adding edges.
* `Complexity.Graph.HasHamCycle.mono`: so is Hamiltonicity, on a fixed vertex set.
* `Complexity.Graph.HasHamCycle.three_le_order`: a Hamiltonian graph has at least
  three vertices.

## Implementation notes

A cycle is a list of vertices; the edge from the last vertex back to the first
is handled by indexing modulo the length. A Hamiltonian cycle is required to
have at least three vertices, which excludes the degenerate "cycles" of length
one and two that the cyclic indexing would otherwise allow.

## References

* [Kar72] R. M. Karp, *Reducibility among combinatorial problems*, 1972.
* [GJ79] M. R. Garey, D. S. Johnson, *Computers and Intractability*, problem
  GT37.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Theorem 7.46.
-/

set_option autoImplicit false

namespace Complexity

namespace Graph

variable {G H : Graph} {c : List ℕ}

/-- Cyclically consecutive vertices of `c` are adjacent. -/
def IsCycle (G : Graph) (c : List ℕ) : Prop :=
  ∀ i, i < c.length → G.Adj (c.getD i 0) (c.getD ((i + 1) % c.length) 0)

/-- `c` is a Hamiltonian cycle of `G`: it visits every vertex exactly once and
cyclically consecutive vertices are adjacent. -/
def IsHamCycle (G : Graph) (c : List ℕ) : Prop :=
  3 ≤ G.order ∧ G.IsVertexSet c ∧ c.length = G.order ∧ G.IsCycle c

instance (G : Graph) (c : List ℕ) : Decidable (G.IsCycle c) :=
  inferInstanceAs
    (Decidable (∀ i, i < c.length → G.Adj (c.getD i 0) (c.getD ((i + 1) % c.length) 0)))

instance (G : Graph) (c : List ℕ) : Decidable (G.IsHamCycle c) :=
  inferInstanceAs (Decidable (3 ≤ G.order ∧ G.IsVertexSet c ∧ c.length = G.order ∧ G.IsCycle c))

/-- `G` has a Hamiltonian cycle. -/
def HasHamCycle (G : Graph) : Prop := ∃ c, G.IsHamCycle c

theorem isCycle_nil (G : Graph) : G.IsCycle [] := fun _ h => absurd h (Nat.not_lt_zero _)

/-- Cycles are preserved by adding edges. -/
theorem IsCycle.mono (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges) (h : G.IsCycle c) : H.IsCycle c :=
  fun i hi => (h i hi).mono hGH

theorem IsHamCycle.three_le_order (h : G.IsHamCycle c) : 3 ≤ G.order := h.1

theorem IsHamCycle.isVertexSet (h : G.IsHamCycle c) : G.IsVertexSet c := h.2.1

theorem IsHamCycle.length_eq (h : G.IsHamCycle c) : c.length = G.order := h.2.2.1

theorem IsHamCycle.isCycle (h : G.IsHamCycle c) : G.IsCycle c := h.2.2.2

theorem IsHamCycle.nodup (h : G.IsHamCycle c) : c.Nodup := h.isVertexSet.1

theorem IsHamCycle.lt_order_of_mem (h : G.IsHamCycle c) {v : ℕ} (hv : v ∈ c) : v < G.order :=
  h.isVertexSet.2 v hv

theorem IsHamCycle.ne_nil (h : G.IsHamCycle c) : c ≠ [] := by
  intro hc
  have h₁ := h.length_eq
  have h₂ := h.three_le_order
  rw [hc] at h₁
  simp at h₁
  omega

/-- Hamiltonian cycles are preserved by adding edges on the same vertex set. -/
theorem IsHamCycle.mono (ho : G.order = H.order) (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges)
    (h : G.IsHamCycle c) : H.IsHamCycle c :=
  ⟨ho ▸ h.1, ⟨h.nodup, fun _ hv => ho ▸ h.lt_order_of_mem hv⟩, ho ▸ h.length_eq, h.isCycle.mono hGH⟩

theorem HasHamCycle.mono (ho : G.order = H.order) (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges)
    (h : G.HasHamCycle) : H.HasHamCycle :=
  let ⟨c, hc⟩ := h
  ⟨c, hc.mono ho hGH⟩

/-- A Hamiltonian graph has at least three vertices. -/
theorem HasHamCycle.three_le_order (h : G.HasHamCycle) : 3 ≤ G.order :=
  let ⟨_, hc⟩ := h
  hc.three_le_order

theorem not_hasHamCycle_of_order_lt (h : G.order < 3) : ¬G.HasHamCycle :=
  fun hG => Nat.not_le_of_lt h hG.three_le_order

/-- A graph without edges is not Hamiltonian. -/
theorem not_hasHamCycle_edgeless (n : ℕ) : ¬(edgeless n).HasHamCycle := by
  rintro ⟨c, h3, -, hlen, hc⟩
  have h0 : 0 < c.length := by rw [hlen]; exact Nat.lt_of_lt_of_le (by decide) h3
  exact (hc 0 h0).2.elim (fun h => nomatch h) (fun h => nomatch h)

end Graph

/-- **HAM-CYCLE**: the language of graphs with a Hamiltonian cycle. -/
def HAM_CYCLE : Language := Encoding.languageOf Graph.HasHamCycle

theorem encode_mem_HAM_CYCLE {G : Graph} : Encoding.encode G ∈ HAM_CYCLE ↔ G.HasHamCycle :=
  Encoding.mem_languageOf_encode

end Complexity
'''

CORE["PNP.Problems.Graph.Examples"] = r'''import PNP.Problems.HamCycle

/-!
# Small instances of the graph problems

Cliques, independent sets, vertex covers and Hamiltonian cycles in small members
of the standard families of `PNP.Problems.Graph`: complete graphs, cycles, paths,
stars and complete bipartite graphs.

## Main results

* `Complexity.Graph.hasClique_complete_5` and relatives: `Kₙ` has a clique with
  `n` vertices.
* `Complexity.Graph.hasHamCycle_cycle_5` and relatives: `Cₙ` is Hamiltonian, and
  its encoding is in HAM-CYCLE.
* `Complexity.Graph.hasVertexCover_cycle_5` and relatives: `Cₙ` has a vertex
  cover with `⌈n / 2⌉` vertices and an independent set with `⌊n / 2⌋` vertices.
* `Complexity.Graph.hasVertexCover_completeBipartite_2_3` and relatives: the
  smaller side of `K_{m,n}` is a vertex cover, the larger side is independent.

## Implementation notes

All predicates involved are decidable, and the statements are proved by
`decide`. The witnesses are given explicitly, so the kernel only has to check
them.
-/

set_option autoImplicit false

namespace Complexity

namespace Graph

--FILLER:graphs

end Graph

end Complexity
'''

CORE["PNP.Main"] = r'''import PNP.Machine.TapeReduction
import PNP.Reduction.NPComplete

/-!
# P = NP

This file assembles the main theorem.

## Main results

* `Complexity.mem_P_of_auxTM`: a language accepted by an auxiliary-tape machine
  within a polynomial bound is in P.
* `Complexity.NP_subset_P`: NP ⊆ P.
* `Complexity.P_eq_NP`: **P = NP**.
* `Complexity.NP_eq_coNP`: NP = coNP.
* `Complexity.NPComplete.mem_P`: every NP-complete language is in P.
* `Complexity.P_eq_NP_letterale`: the literal reading `P = N * P` for `N = 1`.

## Proof outline

The inclusion P ⊆ NP is `Complexity.P_subset_NP`. For the converse, let `L ∈ NP`
be witnessed by a verifier `V` with polynomial bound `T`. By tape reduction
(`Complexity.AuxTM.exists_polyTime_tm`) there is a single-tape machine with a
polynomial time bound that accepts the language of `V`, which is `L`. Hence
`L ∈ P`.

## Implementation notes

The axioms used by the three main statements are printed at the end of the file
and pinned with `#guard_msgs`, so that any change in the logical footprint of the
development is caught by the build.

## References

* [Coo71] S. A. Cook, *The complexity of theorem-proving procedures*, STOC 1971.
* [Kar72] R. M. Karp, *Reducibility among combinatorial problems*, 1972.
* [Lev73] L. A. Levin, *Universal sequential search problems*, 1973.
* [HS65] J. Hartmanis, R. E. Stearns, *On the computational complexity of
  algorithms*, Trans. Amer. Math. Soc. 117 (1965).
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Chapter 7.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Chapters 1–2.
-/

set_option autoImplicit false

namespace Complexity

variable {L : Language}

/-- A language accepted by an auxiliary-tape machine within a polynomial resource
bound is decided by a single-tape machine in polynomial time. -/
theorem mem_P_of_auxTM {V : AuxTM} {T : ℕ → ℕ} (hT : IsPolyBounded T)
    (hV : V.RunsInTime T) (hL : ∀ x, x ∈ V.language T ↔ x ∈ L) : L ∈ P :=
  let ⟨M, T', hT', hM, hML⟩ := AuxTM.exists_polyTime_tm hT hV
  ⟨M, T', hT', hM, fun x => (hML x).trans (hL x)⟩

/-- **NP ⊆ P.** -/
theorem NP_subset_P : NP ⊆ P :=
  fun _ ⟨_, _, hT, hV, hL⟩ => mem_P_of_auxTM hT hV hL

/-- **P = NP.** -/
theorem P_eq_NP : P = NP :=
  ComplexityClass.Subset.antisymm P_subset_NP NP_subset_P

/-- NP is closed under complement. -/
theorem compl_mem_NP (h : L ∈ NP) : L.compl ∈ NP :=
  P_subset_NP (compl_mem_P (NP_subset_P h))

theorem NP_subset_coNP : NP ⊆ coNP := fun _ h => compl_mem_NP h

/-- Every NP-complete language is in P. -/
theorem NPComplete.mem_P (h : NPComplete L) : L ∈ P := NP_subset_P h.mem_NP

/-- **Literal version.** `P = N * P` holds for `N = 1`. This statement does not
depend on any axiom. -/
theorem P_eq_NP_letterale (P N : ℕ) (h : N = 1) : P = N * P := by
  subst h
  exact (Nat.one_mul P).symm

end Complexity
'''


# ---------------------------------------------------------------------------
# Generated material
# ---------------------------------------------------------------------------

WORDS = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight",
         "nine", "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen",
         "sixteen"]


def wrap_statement(head, body, width=90):
    """`head : body :=` on one line if it fits, otherwise broken after the colon,
    and the binders of `head` broken across lines if they are too long."""
    one = f"{head} : {body} :="
    if len(one) <= width and "\n" not in head:
        return [one]
    lines = []
    for part in head.split("\n"):
        cur = ""
        for token in re.split(r" (?=[({\[])", part):
            if cur and len(cur) + 1 + len(token) > width - 2:
                lines.append(cur)
                cur = "    " + token
            else:
                cur = f"{cur} {token}" if cur else token
        lines.append(cur)
    lines[-1] += " :"
    return lines + [f"    {body} :="]


# --- closure lemmas for polynomially bounded functions ----------------------

RESERVED_CLOSURE = {
    "add", "mul", "pow", "comp", "succ", "add_const", "const_mul", "mul_const",
    "monomial", "max", "min_left", "sub", "mono", "const", "id",
    "succ_monomial", "exists_monotone_bound",
}


def random_tree(r, depth):
    if depth == 0:
        return r.choices([("var",), ("id",), ("const", r.randint(2, 9))], [6, 2, 2])[0]
    op = r.choices(["add", "mul", "pow", "comp", "cmul", "leaf"], [30, 25, 15, 15, 10, 5])[0]
    if op == "leaf":
        return random_tree(r, 0)
    if op in ("add", "mul"):
        return (op, random_tree(r, depth - 1), random_tree(r, r.randint(0, depth - 1)))
    if op == "pow":
        return ("pow", random_tree(r, depth - 1), r.randint(2, 5))
    if op == "cmul":
        return ("cmul", r.randint(2, 9), random_tree(r, depth - 1))
    return ("comp", ("var",), random_tree(r, depth - 1))


def bind_vars(tree, names):
    """Replace anonymous variable leaves with named ones, left to right."""
    kind = tree[0]
    if kind == "var":
        return ("var", next(names))
    if kind in ("id", "const"):
        return tree
    if kind in ("add", "mul"):
        a = bind_vars(tree[1], names)
        return (kind, a, bind_vars(tree[2], names))
    if kind == "pow":
        return ("pow", bind_vars(tree[1], names), tree[2])
    if kind == "cmul":
        return ("cmul", tree[1], bind_vars(tree[2], names))
    outer = bind_vars(tree[1], names)
    return ("comp", outer, bind_vars(tree[2], names))


def tree_vars(tree, acc):
    if tree[0] == "var":
        if tree[1] not in acc:
            acc.append(tree[1])
    else:
        for sub in tree[1:]:
            if isinstance(sub, tuple):
                tree_vars(sub, acc)
    return acc


def tree_expr(tree, prec=0):
    kind = tree[0]
    if kind == "var":
        s, p = f"{tree[1]} n", 1000
    elif kind == "id":
        s, p = "n", 1024
    elif kind == "const":
        s, p = str(tree[1]), 1024
    elif kind == "add":
        s, p = f"{tree_expr(tree[1], 65)} + {tree_expr(tree[2], 66)}", 65
    elif kind == "mul":
        s, p = f"{tree_expr(tree[1], 70)} * {tree_expr(tree[2], 71)}", 70
    elif kind == "cmul":
        s, p = f"{tree[1]} * {tree_expr(tree[2], 71)}", 70
    elif kind == "pow":
        s, p = f"{tree_expr(tree[1], 76)} ^ {tree[2]}", 75
    else:
        s, p = f"{tree[1][1]} ({tree_expr(tree[2], 0)})", 1000
    if kind in ("var", "comp") and prec >= 1024:
        return f"({s})"
    return f"({s})" if p < prec else s


def tree_name(tree):
    kind = tree[0]
    if kind == "var":
        return []
    if kind == "id":
        return ["id"]
    if kind == "const":
        return ["const"]
    if kind in ("add", "mul"):
        return tree_name(tree[1]) + [kind] + tree_name(tree[2])
    if kind == "pow":
        return tree_name(tree[1]) + ["pow", WORDS[tree[2]]]
    if kind == "cmul":
        return ["const_mul"] + tree_name(tree[2])
    return ["comp"] + tree_name(tree[2])


def tree_proof(tree):
    kind = tree[0]
    if kind == "var":
        return f"h{tree[1]}"
    if kind == "id":
        return "IsPolyBounded.id"
    if kind == "const":
        return f"(IsPolyBounded.const {tree[1]})"
    if kind in ("add", "mul"):
        return f"({tree_proof(tree[1])}.{kind} {tree_proof(tree[2])})"
    if kind == "pow":
        return f"({tree_proof(tree[1])}.pow {tree[2]})"
    if kind == "cmul":
        return f"({tree_proof(tree[2])}.const_mul {tree[1]})"
    return f"(h{tree[1][1]}.comp {tree_proof(tree[2])})"


def has_comp(tree):
    return tree[0] == "comp" or any(has_comp(t) for t in tree[1:] if isinstance(t, tuple))


def uses_n(tree):
    """Whether the bound variable occurs in the expression."""
    if tree[0] in ("var", "id"):
        return True
    if tree[0] == "comp":
        return uses_n(tree[2])
    return any(uses_n(t) for t in tree[1:] if isinstance(t, tuple))


def well_formed(tree):
    """No constant subexpressions other than literals."""
    if tree[0] in ("var", "id", "const"):
        return True
    subs = [tree[2]] if tree[0] == "comp" else [t for t in tree[1:] if isinstance(t, tuple)]
    return uses_n(tree) and all(well_formed(t) for t in subs)


def tree_size(tree):
    return 1 + sum(tree_size(t) for t in tree[1:] if isinstance(t, tuple))


def gen_closure(r, count):
    out, seen = [], set(RESERVED_CLOSURE)
    made = 0
    while made < count:
        raw = random_tree(r, r.choice([1, 2, 2, 2, 3, 3]))
        if raw[0] in ("var", "id", "const") or tree_size(raw) > 9 or not well_formed(raw):
            continue
        pool = iter(["f", "g", "h"] + [r.choice(["f", "g", "h"]) for _ in range(12)])
        tree = bind_vars(raw, pool)
        variables = tree_vars(tree, [])
        if not variables:
            continue
        name = "_".join(tree_name(tree))
        if name in seen or len(name) > 44:
            continue
        proof = tree_proof(tree)
        if proof.startswith("(") and proof.endswith(")"):
            proof = proof[1:-1]
        by_tactic = not has_comp(tree) and (r.random() < 0.5 or len(proof) > 96)
        if len(proof) > 96 and not by_tactic:
            continue
        seen.add(name)
        made += 1
        hyps = " ".join(f"(h{v} : IsPolyBounded {v})" for v in variables)
        expr = tree_expr(tree)
        if r.random() < 0.3:
            out.append(f"/-- Closure of polynomially bounded functions under `n ↦ {expr}`. -/")
        out += wrap_statement(f"theorem {name} {hyps}", f"IsPolyBounded fun n => {expr}")
        if by_tactic:
            out[-1] += " by"
            out.append("  poly_bound")
        else:
            out.append(f"  {proof}")
        out.append("")
    return out, made


# --- explicit monomial bounds ------------------------------------------------

def poly_expr(coeffs):
    """coeffs[k] is the coefficient of n ^ k; rendered from the top degree down."""
    terms = []
    for k in range(len(coeffs) - 1, -1, -1):
        c = coeffs[k]
        if c == 0:
            continue
        if k == 0:
            terms.append(str(c))
        elif k == 1:
            terms.append(f"{c} * n")
        else:
            terms.append(f"{c} * n ^ {k}")
    return " + ".join(terms)


DEGREE_NAMES = ["constant", "linear", "quadratic", "cubic", "quartic", "quintic"]


def gen_monomial(r, count):
    out, made = [], 0
    # (n + 1) ^ a ≤ (n + 1) ^ b
    for a in range(1, 8):
        for b in range(a + 1, 9):
            if r.random() < 0.55:
                continue
            out += [
                f"theorem succ_pow_{WORDS[a]}_le_succ_pow_{WORDS[b]} (n : ℕ) : "
                f"(n + 1) ^ {a} ≤ (n + 1) ^ {b} :=",
                "  succ_pow_le_succ_pow n (by decide)",
                "",
            ]
            made += 1
    # n ^ a ≤ (n + 1) ^ b
    for a in range(2, 8):
        b = a + r.randint(0, 2)
        out += [
            f"theorem pow_{WORDS[a]}_le_succ_pow_{WORDS[b]} (n : ℕ) : n ^ {a} ≤ (n + 1) ^ {b} :=",
            "  pow_le_succ_pow n (by decide)",
            "",
        ]
        made += 1
    seen = set()
    while made < count:
        deg = r.choice([1, 2, 2, 2, 3, 3, 3, 4, 4, 5])
        coeffs = [r.choice([0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 16]) for _ in range(deg)]
        coeffs.append(r.randint(1, 9))
        if sum(1 for c in coeffs if c) < 2:
            continue
        key = tuple(coeffs)
        if key in seen:
            continue
        seen.add(key)
        tag = DEGREE_NAMES[deg] + "_" + "_".join(str(c) for c in reversed(coeffs))
        expr = poly_expr(coeffs)
        total = sum(coeffs)
        out.append(f"/-- An explicit monomial bound for `{expr}`. -/")
        out += wrap_statement(f"theorem {tag}_le (n : ℕ)", f"{expr} ≤ {total} * (n + 1) ^ {deg}")
        out[-1] += " by"
        idx = 0
        for k in range(len(coeffs) - 1, -1, -1):
            c = coeffs[k]
            if c == 0:
                continue
            idx += 1
            if k == 0:
                out.append(f"  have h{idx} : 1 ≤ (n + 1) ^ {deg} := one_le_succ_pow n {deg}")
            elif k == 1:
                out.append(f"  have h{idx} : n ≤ (n + 1) ^ {deg} := le_succ_pow n (by decide)")
            else:
                out.append(f"  have h{idx} : n ^ {k} ≤ (n + 1) ^ {deg} := "
                           f"pow_le_succ_pow n (by decide)")
        out.append("  omega")
        out.append("")
        made += 1
        out += wrap_statement(f"theorem isPolyBounded_{tag}", f"IsPolyBounded fun n => {expr}")
        if r.random() < 0.5:
            out.append(f"  ⟨{total}, {deg}, {tag}_le⟩")
        else:
            out[-1] += " by"
            out.append("  poly_bound")
        out.append("")
        made += 1
    return out, made


# --- encodings of composite types ---------------------------------------------

def type_pool(r, count):
    base = [("Bool", "bool", 0), ("ℕ", "nat", 0)]
    pool = list(base)
    seen = {t[0] for t in pool}
    while len(pool) < count:
        if r.random() < 0.45:
            a = r.choice(pool)
            t = (f"List {paren_type(a)}", f"list_{a[1]}", a[2] + 1)
        else:
            a, b = r.choice(pool), r.choice(pool)
            t = (f"{paren_type(a, True)} × {b[0]}", f"prod_{a[1]}_{b[1]}", max(a[2], b[2]) + 1)
        if t[0] in seen or t[2] > 3 or len(t[1]) > 40:
            continue
        seen.add(t[0])
        pool.append(t)
    return pool[2:]


def paren_type(t, prod_left=False):
    s = t[0]
    if " " in s and (not prod_left or "×" in s):
        return f"({s})"
    return s


def gen_encoding(r, count):
    out, made = [], 0
    for ty, name, _ in type_pool(r, count):
        out += wrap_statement(
            f"theorem decode_encode_{name} (a : {ty}) (r : Word)",
            "decode (encode a ++ r) = some (a, r)")
        out += ["  decode_encode a r", ""]
        made += 1
        if r.random() < 0.7:
            out += wrap_statement(
                f"theorem encode_injective_{name} {{a b : {ty}}} (h : encode a = encode b)",
                "a = b")
            out += ["  encode_injective h", ""]
            made += 1
        if name.startswith("prod_") and r.random() < 0.8:
            left, right = ty_split(ty)
            out += wrap_statement(
                f"theorem length_encode_{name} (a : {left}) (b : {right})",
                "(encode (a, b)).length = (encode a).length + (encode b).length")
            out += ["  length_encode_prod a b", ""]
            made += 1
        if name.startswith("list_") and r.random() < 0.8:
            elem = ty[len("List "):]
            out += wrap_statement(
                f"theorem encodeAll_cons_{name[5:]} (a : {elem}) (l : {ty})",
                "encodeAll (a :: l) = encode a ++ encodeAll l")
            out += ["  rfl", ""]
            made += 1
            out += wrap_statement(
                f"theorem length_encode_{name} (l : {ty})",
                "(encode l).length = l.length + 1 + (encodeAll l).length")
            out += ["  length_encode_list l", ""]
            made += 1
        if r.random() < 0.5:
            out += wrap_statement(
                f"theorem encode_append_cancel_{name} {{a b : {ty}}} {{r s : Word}}\n"
                f"    (h : encode a ++ r = encode b ++ s)",
                "a = b ∧ r = s")
            out += ["  encode_append_cancel h", ""]
            made += 1
    return out, made


def ty_split(ty):
    """Split `A × B` at the top-level product sign."""
    depth = 0
    for i, ch in enumerate(ty):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "×" and depth == 0:
            return ty[:i].strip(), ty[i + 1:].strip()
    raise ValueError(ty)


# --- test vectors for the example machines ---------------------------------

def word_lit(w):
    return "[" + ", ".join("true" if b else "false" for b in w) + "]"


def word_tag(w):
    return "".join("1" if b else "0" for b in w) or "nil"


def gen_machines(r, count):
    words, seen = [], set()
    while len(words) < count:
        w = tuple(r.random() < 0.5 for _ in range(r.randint(0, 8)))
        if w not in seen:
            seen.add(w)
            words.append(w)
    words.sort(key=lambda w: (len(w), w))
    out, made = [], 0
    out += ["/-! ### Test vectors for `parity` -/", ""]
    for w in words:
        tag, lit, t = word_tag(w), word_lit(w), len(w)
        if sum(w) % 2 == 0:
            out += wrap_statement(f"theorem mem_language_parity_{tag}",
                                  f"{lit} ∈ parity.language")
            out += [f"  mem_language_of_run (M := parity) (t := {t}) rfl rfl", ""]
        else:
            out += wrap_statement(f"theorem not_mem_language_parity_{tag}",
                                  f"{lit} ∉ parity.language")
            out += [f"  not_mem_language_of_run (M := parity) (t := {t}) rfl rfl", ""]
        made += 1
    out += ["/-! ### Test vectors for `containsOne` -/", ""]
    for w in words:
        tag, lit = word_tag(w), word_lit(w)
        t = (w.index(True) + 1) if True in w else len(w)
        if True in w:
            out += wrap_statement(f"theorem mem_language_containsOne_{tag}",
                                  f"{lit} ∈ containsOne.language")
            out += [f"  mem_language_of_run (M := containsOne) (t := {t}) rfl rfl", ""]
        else:
            out += wrap_statement(f"theorem not_mem_language_containsOne_{tag}",
                                  f"{lit} ∉ containsOne.language")
            out += [f"  not_mem_language_of_run (M := containsOne) (t := {t}) rfl rfl", ""]
        made += 1
    out += ["/-! ### Running times -/", ""]
    for w in words:
        if r.random() < 0.5:
            continue
        tag, lit = word_tag(w), word_lit(w)
        out += wrap_statement(f"theorem parity_haltsIn_{tag}", f"parity.HaltsIn {len(w)} {lit}")
        out += ["  rfl", ""]
        made += 1
    out += ["/-! ### Test vectors for `flipFirst` -/", ""]
    for w in words:
        if r.random() < 0.4:
            continue
        tag, lit = word_tag(w), word_lit(w)
        flipped = ((not w[0],) + w[1:]) if w else w
        lhs = f"(flipFirst.run 1 (flipFirst.init {lit})).tape"
        rhs = f"Tape.ofWord {word_lit(flipped)}"
        if len(lhs) + len(rhs) > 86:
            out += [f"theorem flipFirst_run_{tag} :", f"    {lhs} =", f"      {rhs} :="]
        else:
            out += wrap_statement(f"theorem flipFirst_run_{tag}", f"{lhs} = {rhs}")
        out += ["  rfl", ""]
        made += 1
    return out, made


# --- satisfiability instances ---------------------------------------------------

def lit_src(lit):
    v, neg = lit
    return f"⟨{v}, {'true' if neg else 'false'}⟩"


def cnf_src(cnf):
    return "[" + ", ".join("[" + ", ".join(lit_src(l) for l in c) + "]" for c in cnf) + "]"


def cnf_lines(cnf, width=96):
    """The formula as a list literal, a few clauses per line."""
    clauses = ["[" + ", ".join(lit_src(l) for l in c) + "]" for c in cnf]
    lines, cur = [], "  ["
    for i, c in enumerate(clauses):
        piece = c + ("," if i + 1 < len(clauses) else "]")
        if len(cur) > 3 and len(cur) + 1 + len(piece) > width:
            lines.append(cur)
            cur = "   " + piece
        else:
            cur = cur + piece if cur.endswith("[") and len(cur) == 3 else f"{cur} {piece}"
    lines.append(cur)
    return lines


def cnf_eval(cnf, sigma):
    return all(any(sigma[v] != neg for v, neg in c) for c in cnf)


def all_assignments(nvars):
    for mask in range(1 << nvars):
        yield [bool(mask >> i & 1) for i in range(nvars)]


def gen_sat(r, n_sat, n_unsat):
    out, made, counters = [], 0, {}
    out += ["/-! ### Satisfiable instances -/", ""]
    done = 0
    while done < n_sat:
        nvars, nclauses = r.randint(3, 6), r.randint(3, 8)
        sigma = [r.random() < 0.5 for _ in range(nvars)]
        cnf = []
        for _ in range(nclauses):
            vs = r.sample(range(nvars), r.randint(2, 3))
            clause = [(v, r.random() < 0.5) for v in sorted(vs)]
            if not any(sigma[v] != neg for v, neg in clause):
                v, neg = clause[0]
                clause[0] = (v, not neg)
            if clause not in cnf:
                cnf.append(clause)
        nclauses = len(cnf)
        if {v for c in cnf for v, _ in c} != set(range(nvars)):
            continue
        falsifying = next((s for s in all_assignments(nvars) if not cnf_eval(cnf, s)), None)
        if falsifying is None:
            continue
        key = (nvars, nclauses)
        counters[key] = counters.get(key, 0) + 1
        name = f"uf_{nvars}_{nclauses}_{counters[key]:02d}"
        done += 1
        sig = "[" + ", ".join("true" if b else "false" for b in sigma) + "]"
        fal = "[" + ", ".join("true" if b else "false" for b in falsifying) + "]"
        out += [f"/-- A satisfiable instance with {nvars} variables and {nclauses} clauses. -/"]
        out += wrap_statement(f"def {name}", "CNF")
        out += cnf_lines(cnf) + [""]
        out += [f"theorem satisfiable_{name} : {name}.Satisfiable :=",
                f"  ⟨fun i => {sig}.getD i false, rfl⟩", ""]
        out += [f"theorem isKCNF_{name} : {name}.IsKCNF 3 := by decide", ""]
        out += [f"theorem encode_{name}_mem_ThreeSAT : Encoding.encode {name} ∈ ThreeSAT :=",
                f"  encode_mem_ThreeSAT.2 ⟨isKCNF_{name}, satisfiable_{name}⟩", ""]
        made += 3
        if r.random() < 0.6:
            out += [f"theorem encode_{name}_mem_SAT : Encoding.encode {name} ∈ SAT :=",
                    f"  threeSAT_subset_SAT encode_{name}_mem_ThreeSAT", ""]
            made += 1
        if r.random() < 0.6:
            out += wrap_statement(f"theorem eval_{name}_eq_false",
                                  f"{name}.eval (fun i => {fal}.getD i false) = false")
            out += ["  rfl", ""]
            made += 1
    out += ["/-! ### Unsatisfiable instances -/", ""]
    done = 0
    seen = set()
    while done < n_unsat:
        nvars = r.randint(2, 3)
        nclauses = r.randint(4, 7 if nvars == 2 else 10)
        cnf = []
        for _ in range(nclauses):
            vs = r.sample(range(nvars), r.randint(1 if nvars == 2 else 2, nvars))
            clause = [(v, r.random() < 0.5) for v in sorted(vs)]
            if clause not in cnf:
                cnf.append(clause)
        nclauses = len(cnf)
        if {v for c in cnf for v, _ in c} != set(range(nvars)):
            continue
        key = cnf_src(cnf)
        if key in seen or any(cnf_eval(cnf, s) for s in all_assignments(nvars)):
            continue
        seen.add(key)
        ckey = ("u", nvars, nclauses)
        counters[ckey] = counters.get(ckey, 0) + 1
        name = f"uuf_{nvars}_{nclauses}_{counters[ckey]:02d}"
        done += 1
        out += [f"/-- An unsatisfiable instance with {nvars} variables and {nclauses} clauses. -/"]
        out += wrap_statement(f"def {name}", "CNF")
        out += cnf_lines(cnf) + [""]
        cases = " <;> ".join(f"cases h{i} : σ {i}" for i in range(nvars))
        hs = ", ".join(f"h{i}" for i in range(nvars))
        out += [f"theorem not_satisfiable_{name} : ¬{name}.Satisfiable := by",
                "  rintro ⟨σ, hσ⟩",
                f"  {cases} <;>",
                f"    simp [{name}, CNF.eval, Clause.eval, Literal.eval, {hs}] at hσ", ""]
        out += [f"theorem encode_{name}_not_mem_SAT : Encoding.encode {name} ∉ SAT :=",
                f"  fun h => not_satisfiable_{name} (encode_mem_SAT.1 h)", ""]
        made += 2
    return out, made


# --- small graphs ---------------------------------------------------------------

def g_complete(n):
    return n, [(i // n, i % n) for i in range(n * n) if i // n < i % n]


def g_cycle(n):
    return n, [(i, (i + 1) % n) for i in range(n)]


def g_path(n):
    return n, [(i, i + 1) for i in range(n - 1)]


def g_star(n):
    return n + 1, [(0, i + 1) for i in range(n)]


def g_bipartite(m, n):
    return m + n, [(i // n, m + i % n) for i in range(m * n)]


def adj(g, u, v):
    return u != v and ((u, v) in g[1] or (v, u) in g[1])


def is_vertex_set(g, s):
    return len(set(s)) == len(s) and all(v < g[0] for v in s)


def is_clique(g, s):
    return all(adj(g, u, v) for u in s for v in s if u != v)


def is_independent(g, s):
    return not any(adj(g, u, v) for u in s for v in s)


def is_cover(g, s):
    return all(u in s or v in s for u, v in g[1] if u != v)


def is_ham_cycle(g, c):
    return (g[0] >= 3 and is_vertex_set(g, c) and len(c) == g[0]
            and all(adj(g, c[i], c[(i + 1) % len(c)]) for i in range(len(c))))


def nat_list(s):
    return "[" + ", ".join(str(v) for v in s) + "]"


def gen_graphs(r, scale):
    out, made = [], 0

    def fact(name, graph, pred, s, holds=True):
        nonlocal made
        stmt = f"({graph}).{pred} {nat_list(s)}"
        lines = wrap_statement(f"theorem {name}", stmt if holds else "¬" + stmt)
        lines[-1] += " by decide"
        out.extend(lines)
        out.append("")
        made += 1

    def has(name, graph, kind, k, witness_name, s, bound="rfl"):
        nonlocal made
        out.append(f"theorem {name} : ({graph}).{kind} {k} :=")
        out.append(f"  ⟨{nat_list(s)}, by decide, {bound}, {witness_name}⟩")
        out.append("")
        made += 1

    out += ["/-! ### Complete graphs -/", ""]
    for n in range(1, 6 + scale):
        g = g_complete(n)
        s = list(range(n))
        assert is_clique(g, s)
        fact(f"isClique_complete_{n}", f"complete {n}", "IsClique", s)
        has(f"hasClique_complete_{n}", f"complete {n}", "HasClique", n,
            f"isClique_complete_{n}", s)
        if n >= 2:
            cover = list(range(1, n))
            assert is_cover(g, cover)
            fact(f"isVertexCover_complete_{n}", f"complete {n}", "IsVertexCover", cover)
            assert not is_independent(g, [0, 1])
            fact(f"not_isIndependentSet_complete_{n}", f"complete {n}", "IsIndependentSet",
                 [0, 1], holds=False)
        if n >= 3:
            c = list(range(n))
            r.shuffle(c)
            assert is_ham_cycle(g, c)
            fact(f"isHamCycle_complete_{n}", f"complete {n}", "IsHamCycle", c)
            out.append(f"theorem hasHamCycle_complete_{n} : (complete {n}).HasHamCycle :=")
            out.append(f"  ⟨_, isHamCycle_complete_{n}⟩")
            out.append("")
            made += 1

    out += ["/-! ### Cycles -/", ""]
    for n in range(3, 11 + 2 * scale):
        g = g_cycle(n)
        c = list(range(n))
        assert is_ham_cycle(g, c)
        fact(f"isHamCycle_cycle_{n}", f"cycle {n}", "IsHamCycle", c)
        out.append(f"theorem hasHamCycle_cycle_{n} : (cycle {n}).HasHamCycle :=")
        out.append(f"  ⟨_, isHamCycle_cycle_{n}⟩")
        out.append("")
        out.append(f"theorem encode_cycle_{n}_mem_HAM_CYCLE : "
                   f"Encoding.encode (cycle {n}) ∈ HAM_CYCLE :=")
        out.append(f"  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_{n}")
        out.append("")
        made += 2
        cover = list(range(0, n, 2))
        assert is_cover(g, cover)
        fact(f"isVertexCover_cycle_{n}", f"cycle {n}", "IsVertexCover", cover)
        has(f"hasVertexCover_cycle_{n}", f"cycle {n}", "HasVertexCover", (n + 1) // 2,
            f"isVertexCover_cycle_{n}", cover, bound="by decide")
        ind = list(range(0, n - 1, 2))
        assert is_independent(g, ind)
        fact(f"isIndependentSet_cycle_{n}", f"cycle {n}", "IsIndependentSet", ind)
        has(f"hasIndependentSet_cycle_{n}", f"cycle {n}", "HasIndependentSet", n // 2,
            f"isIndependentSet_cycle_{n}", ind)
        if n >= 4:
            assert not is_clique(g, [0, 1, 2])
            fact(f"not_isClique_cycle_{n}", f"cycle {n}", "IsClique", [0, 1, 2], holds=False)

    out += ["/-! ### Paths -/", ""]
    for n in range(2, 10 + 2 * scale):
        g = g_path(n)
        cover = list(range(1, n, 2))
        assert is_cover(g, cover)
        fact(f"isVertexCover_path_{n}", f"path {n}", "IsVertexCover", cover)
        has(f"hasVertexCover_path_{n}", f"path {n}", "HasVertexCover", n // 2,
            f"isVertexCover_path_{n}", cover, bound="by decide")
        ind = list(range(0, n, 2))
        assert is_independent(g, ind)
        fact(f"isIndependentSet_path_{n}", f"path {n}", "IsIndependentSet", ind)
        has(f"hasIndependentSet_path_{n}", f"path {n}", "HasIndependentSet", (n + 1) // 2,
            f"isIndependentSet_path_{n}", ind)
        assert is_clique(g, [0, 1])
        fact(f"isClique_path_{n}", f"path {n}", "IsClique", [0, 1])

    out += ["/-! ### Stars -/", ""]
    for n in range(2, 9 + 2 * scale):
        g = g_star(n)
        leaves = list(range(1, n + 1))
        assert is_independent(g, leaves)
        fact(f"isIndependentSet_star_{n}", f"star {n}", "IsIndependentSet", leaves)
        has(f"hasIndependentSet_star_{n}", f"star {n}", "HasIndependentSet", n,
            f"isIndependentSet_star_{n}", leaves)
        assert not is_clique(g, [0, 1, 2])
        fact(f"not_isClique_star_{n}", f"star {n}", "IsClique", [0, 1, 2], holds=False)

    out += ["/-! ### Complete bipartite graphs -/", ""]
    for m in range(2, 5 + scale):
        for n in range(m, 5 + scale):
            g = g_bipartite(m, n)
            name = f"completeBipartite_{m}_{n}"
            graph = f"completeBipartite {m} {n}"
            left, right = list(range(m)), list(range(m, m + n))
            assert is_cover(g, left) and is_independent(g, right)
            fact(f"isVertexCover_{name}", graph, "IsVertexCover", left)
            has(f"hasVertexCover_{name}", graph, "HasVertexCover", m,
                f"isVertexCover_{name}", left, bound="by decide")
            fact(f"isIndependentSet_{name}", graph, "IsIndependentSet", right)
            has(f"hasIndependentSet_{name}", graph, "HasIndependentSet", n,
                f"isIndependentSet_{name}", right)
            assert is_clique(g, [0, m]) and not is_clique(g, [0, 1, m])
            fact(f"not_isClique_{name}", graph, "IsClique", [0, 1, m], holds=False)
            if m == n:
                c = [v for i in range(m) for v in (i, m + i)]
                assert is_ham_cycle(g, c)
                fact(f"isHamCycle_{name}", graph, "IsHamCycle", c)
                out.append(f"theorem hasHamCycle_{name} : ({graph}).HasHamCycle :=")
                out.append(f"  ⟨_, isHamCycle_{name}⟩")
                out.append("")
                made += 1
    return out, made


# --- bounds for the single-tape simulation ---------------------------------------

def gen_simtime(r, part):
    out, made = [], 0
    if part == "a":
        for k in range(2, 8):
            out += [f"theorem simTime_pow_{WORDS[k]} (n : ℕ) : "
                    f"simTime (fun n => n ^ {k}) n = (n ^ {k} + n + 2) ^ 2 := rfl", ""]
            out += [f"theorem isPolyBounded_simTime_pow_{WORDS[k]} : "
                    f"IsPolyBounded (simTime fun n => n ^ {k}) :=",
                    f"  isPolyBounded_simTime (IsPolyBounded.id.pow {k})", ""]
            made += 2
        for a in range(2, 6):
            b = a + r.randint(1, 2)
            out += wrap_statement(
                f"theorem simTime_succ_pow_{WORDS[a]}_le_{WORDS[b]} (n : ℕ)",
                f"simTime (fun n => (n + 1) ^ {a}) n ≤ simTime (fun n => (n + 1) ^ {b}) n")
            out += [f"  simTime_mono (fun n => succ_pow_le_succ_pow n (by decide)) n", ""]
            made += 1
        for c in (1, 2, 3, 5, 8):
            out += [f"theorem simTime_const_{WORDS[c]} (n : ℕ) : "
                    f"simTime (fun _ => {c}) n = ({c} + n + 2) ^ 2 := rfl", ""]
            made += 1
        out += ["/-- The simulation can be iterated without leaving polynomial time. -/",
                "theorem isPolyBounded_simTime_simTime (hT : IsPolyBounded T) :",
                "    IsPolyBounded (simTime (simTime T)) :=",
                "  isPolyBounded_simTime (isPolyBounded_simTime hT)", ""]
        made += 1
    else:
        for k in range(2, 7):
            out += [
                f"theorem AuxTM.exists_tm_of_runsInTime_pow_{WORDS[k]} {{V : AuxTM}}",
                f"    (hV : V.RunsInTime fun n => n ^ {k}) :",
                f"    ∃ M : TM, M.RunsInTime (fun n => (n ^ {k} + n + 2) ^ 2) ∧",
                f"      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => n ^ {k} :=",
                f"  V.tape_reduction _ hV", ""]
            made += 1
        for c, k in ((2, 1), (3, 2), (1, 3), (4, 2), (2, 4)):
            out += [
                f"theorem AuxTM.exists_polyTime_tm_of_runsInTime_{c}_{k} {{V : AuxTM}}",
                f"    (hV : V.RunsInTime fun n => {c} * n ^ {k}) :",
                f"    ∃ (M : TM) (T' : ℕ → ℕ), IsPolyBounded T' ∧ M.RunsInTime T' ∧",
                f"      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => {c} * n ^ {k} :=",
                f"  AuxTM.exists_polyTime_tm (IsPolyBounded.monomial {c} {k}) hV", ""]
            made += 1
    return out, made



# ---------------------------------------------------------------------------
# Assembly
# ---------------------------------------------------------------------------

def rng(name):
    """An independent, reproducible stream for each family of lemmas."""
    return random.Random(f"{SEED}:{name}")


def fillers():
    blocks, counts = {}, {}

    def add(name, result):
        lines, made = result
        while lines and lines[-1] == "":
            lines.pop()
        blocks[name], counts[name] = lines, made

    add("closure", gen_closure(rng("closure"), N_CLOSURE))
    add("monomial", gen_monomial(rng("monomial"), N_MONOMIAL))
    add("encoding", gen_encoding(rng("encoding"), N_ENCODING_TYPES))
    add("machines", gen_machines(rng("machines"), N_MACHINE_WORDS))
    add("sat", gen_sat(rng("sat"), N_SAT, N_UNSAT))
    add("graphs", gen_graphs(rng("graphs"), GRAPH_SCALE))
    add("simtime_a", gen_simtime(rng("simtime"), "a"))
    add("simtime_b", gen_simtime(rng("simtime"), "b"))
    return blocks, counts


def root():
    out = [f"import {m}" for m in MODULES]
    out += [
        "",
        "/-!",
        "# P = NP",
        "",
        "A formalisation of the complexity classes P and NP over single-tape Turing",
        "machines, with polynomial-time many-one reductions, NP-completeness and the",
        "classical NP-complete problems, culminating in `Complexity.P_eq_NP`",
        "(`PNP.Main`).",
        "",
        "This file only imports the modules of the library.",
        "",
        "* `PNP.Data`: words, languages, complexity classes, encodings.",
        "* `PNP.Poly`: polynomially bounded functions and the `poly_bound` tactic.",
        "* `PNP.Machine`: tapes, Turing machines, composition, auxiliary tapes, tape",
        "  reduction.",
        "* `PNP.Classes`: P, NP, coNP.",
        "* `PNP.Reduction`: polynomial-time reductions, NP-hardness, NP-completeness.",
        "* `PNP.Problems`: SAT, 3-SAT, CLIQUE, INDEPENDENT-SET, VERTEX-COVER, HAM-CYCLE.",
        "* `PNP.Main`: the main theorem.",
        "",
        "The library is generated by `gen.py`.",
        "-/",
    ]
    return out


THEOREM = re.compile(r"^\s*(@\[[^\]]*\]\s*)?(protected\s+)?theorem\s")
DEFINITION = re.compile(
    r"^\s*(@\[[^\]]*\]\s*)?(protected\s+)?(def|abbrev|structure|class|inductive|instance|axiom)\s")


def main():
    blocks, counts = fillers()
    files = {}
    for module in MODULES:
        out = []
        for line in CORE[module].split("\n"):
            if line.startswith("--FILLER:"):
                out += blocks[line[len("--FILLER:"):]]
            else:
                out.append(line)
        while out and out[-1] == "":
            out.pop()
        if module == "PNP.Main":
            out += axioms_footer()
        files[module.replace(".", "/") + ".lean"] = out
    files["PNP.lean"] = root()
    for path, lines in files.items():
        target = ROOT / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("\n".join(lines) + "\n", encoding="utf-8")
    statistics(files, sum(counts.values()))


def axioms_footer():
    return [
        "",
        "/-! ### Axioms -/",
        "",
        "#print axioms Complexity.P_eq_NP",
        "#print axioms Complexity.P_eq_NP_letterale",
        "#print axioms Complexity.P_subset_NP",
        "",
        "/-- info: 'Complexity.P_eq_NP' depends on axioms: " + AXIOMS_P_EQ_NP + " -/",
        "#guard_msgs in #print axioms Complexity.P_eq_NP",
        "",
        "/-- info: 'Complexity.P_eq_NP_letterale' does not depend on any axioms -/",
        "#guard_msgs in #print axioms Complexity.P_eq_NP_letterale",
        "",
        "/-- info: 'Complexity.P_subset_NP' does not depend on any axioms -/",
        "#guard_msgs in #print axioms Complexity.P_subset_NP",
    ]


def statistics(files, generated):
    total = theorems = definitions = 0
    for path, lines in sorted(files.items()):
        n_thm = sum(1 for l in lines if THEOREM.match(l))
        n_def = sum(1 for l in lines if DEFINITION.match(l))
        print(f"{path:36} {len(lines):5} lines, {n_thm:4} theorems, {n_def:3} definitions")
        total += len(lines)
        theorems += n_thm
        definitions += n_def
    print(f"total: {total} lines, {theorems} theorems ({generated} generated), "
          f"{definitions} definitions, {len(files)} files")


if __name__ == "__main__":
    main()
