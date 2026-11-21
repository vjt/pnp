import PNP.Data.Language

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
