import PNP.Data.Encoding

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

theorem decode_encode_list_nat (a : List ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encodeAll_cons_nat (a : ℕ) (l : List ℕ) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_nat (l : List ℕ) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_nat {a b : List ℕ} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_nat_bool (a : ℕ × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_nat_bool {a b : ℕ × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_nat_bool (a : ℕ) (b : Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_nat_bool {a b : ℕ × Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_nat_bool_bool (a : (ℕ × Bool) × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_nat_bool_bool {a b : (ℕ × Bool) × Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_nat_bool_bool (a : (ℕ × Bool)) (b : Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_bool_nat (a : Bool × ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_bool_nat (a : Bool) (b : ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_list_bool (a : List Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_bool {a b : List Bool} (h : encode a = encode b) : a = b :=
  encode_injective h

theorem encodeAll_cons_bool (a : Bool) (l : List Bool) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_bool (l : List Bool) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_prod_prod_bool_nat_list_nat (a : (Bool × ℕ) × List ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_prod_bool_nat_list_nat (a : (Bool × ℕ)) (b : List ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_prod_bool_nat_list_nat {a b : (Bool × ℕ) × List ℕ}
    {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_nat_bool_prod_nat_bool (a : (ℕ × Bool) × ℕ × Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_nat_bool_prod_nat_bool {a b : (ℕ × Bool) × ℕ × Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_nat_bool_prod_nat_bool (a : (ℕ × Bool)) (b : ℕ × Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_prod_nat_bool_prod_nat_bool {a b :
    (ℕ × Bool) × ℕ × Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_prod_prod_bool_nat_list_nat (a : List ((Bool × ℕ) × List ℕ))
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encodeAll_cons_prod_prod_bool_nat_list_nat (a : ((Bool × ℕ) × List ℕ)) (l : List
    ((Bool × ℕ) × List ℕ)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_prod_bool_nat_list_nat (l : List ((Bool × ℕ) × List ℕ)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_prod_prod_bool_nat_list_nat {a b : List
    ((Bool × ℕ) × List ℕ)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_prod_prod_nat_bool_bool (a : List ((ℕ × Bool) × Bool))
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_prod_nat_bool_bool {a b : List ((ℕ × Bool) × Bool)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_prod_nat_bool_bool (a : ((ℕ × Bool) × Bool)) (l : List
    ((ℕ × Bool) × Bool)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_prod_nat_bool_bool (l : List ((ℕ × Bool) × Bool)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_list_prod_nat_bool (a : List (ℕ × Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_nat_bool {a b : List (ℕ × Bool)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_nat_bool (a : (ℕ × Bool)) (l : List (ℕ × Bool)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_nat_bool (l : List (ℕ × Bool)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_prod_nat_list_nat (a : ℕ × List ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_nat_list_nat {a b : ℕ × List ℕ} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_nat_list_nat {a b : ℕ × List ℕ} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_bool_bool (a : Bool × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_bool_bool {a b : Bool × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_bool_bool {a b : Bool × Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_prod_bool_nat (a : List (Bool × ℕ)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_bool_nat {a b : List (Bool × ℕ)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem decode_encode_list_list_nat (a : List (List ℕ)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encodeAll_cons_list_nat (a : (List ℕ)) (l : List (List ℕ)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_list_nat (l : List (List ℕ)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_list_nat {a b : List (List ℕ)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_list_bool (a : List (List Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem decode_encode_list_list_list_bool (a : List (List (List Bool))) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_list_list_bool {a b : List (List (List Bool))}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_list_list_bool (a : (List (List Bool))) (l : List (List
    (List Bool))) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_list_list_bool (l : List (List (List Bool))) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_prod_prod_prod_nat_bool_bool_nat (a : ((ℕ × Bool) × Bool) × ℕ)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_prod_nat_bool_bool_nat {a b :
    ((ℕ × Bool) × Bool) × ℕ} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem decode_encode_list_prod_bool_bool (a : List (Bool × Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_bool_bool {a b : List (Bool × Bool)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_bool_bool (a : (Bool × Bool)) (l : List (Bool × Bool)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_bool_bool (l : List (Bool × Bool)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_prod_bool_bool {a b : List (Bool × Bool)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_prod_nat_bool_prod_nat_bool (a : (List
    (ℕ × Bool)) × ℕ × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_prod_nat_bool_prod_nat_bool {a b : (List
    (ℕ × Bool)) × ℕ × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_prod_nat_bool_prod_nat_bool (a : (List (ℕ × Bool)))
    (b : ℕ × Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_list_prod_prod_nat_bool_prod_nat_bool (a : List
    ((ℕ × Bool) × ℕ × Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encodeAll_cons_prod_prod_nat_bool_prod_nat_bool (a : ((ℕ × Bool) × ℕ × Bool))
    (l : List ((ℕ × Bool) × ℕ × Bool)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_prod_nat_bool_prod_nat_bool (l : List
    ((ℕ × Bool) × ℕ × Bool)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_prod_prod_nat_bool_prod_nat_bool {a b : List
    ((ℕ × Bool) × ℕ × Bool)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_list_prod_bool_nat (a : List (List (Bool × ℕ))) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_list_prod_bool_nat {a b : List (List (Bool × ℕ))}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_list_prod_bool_nat (a : (List (Bool × ℕ))) (l : List (List
    (Bool × ℕ))) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_list_prod_bool_nat (l : List (List (Bool × ℕ))) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_list_list_prod_bool_bool (a : List (List (Bool × Bool)))
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_list_prod_bool_bool {a b : List (List (Bool × Bool))}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_list_prod_bool_bool (a : (List (Bool × Bool))) (l : List (List
    (Bool × Bool))) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_list_prod_bool_bool (l : List (List (Bool × Bool))) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_prod_prod_bool_bool_list_prod_nat_bool (a : (Bool × Bool) × List
    (ℕ × Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_bool_bool_list_prod_nat_bool {a b :
    (Bool × Bool) × List (ℕ × Bool)} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_bool_bool_list_prod_nat_bool (a : (Bool × Bool))
    (b : List (ℕ × Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_prod_bool_bool_list_prod_nat_bool {a b :
    (Bool × Bool) × List (ℕ × Bool)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_list_prod_nat_bool (a : List (List (ℕ × Bool))) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_list_prod_nat_bool {a b : List (List (ℕ × Bool))}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_list_prod_nat_bool (a : (List (ℕ × Bool))) (l : List (List
    (ℕ × Bool))) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_list_prod_nat_bool (l : List (List (ℕ × Bool))) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_prod_bool_list_bool (a : Bool × List Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_bool_list_bool {a b : Bool × List Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_bool_list_bool {a b : Bool × List Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_prod_nat_bool_bool_bool (a : ((ℕ × Bool) × Bool) × Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_prod_nat_bool_bool_bool {a b :
    ((ℕ × Bool) × Bool) × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_prod_nat_bool_bool_bool (a : ((ℕ × Bool) × Bool))
    (b : Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_list_prod_nat_list_nat (a : List (ℕ × List ℕ)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_nat_list_nat {a b : List (ℕ × List ℕ)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_nat_list_nat (a : (ℕ × List ℕ)) (l : List (ℕ × List ℕ)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_nat_list_nat (l : List (ℕ × List ℕ)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_prod_nat_list_nat {a b : List (ℕ × List ℕ)}
    {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_bool_list_nat (a : List Bool × List ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_bool_list_nat {a b : List Bool × List ℕ}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_bool_list_nat (a : List Bool) (b : List ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_list_bool_list_nat {a b : List Bool × List ℕ}
    {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_prod_list_bool_list_nat (a : List (List Bool × List ℕ))
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_list_bool_list_nat {a b : List (List Bool × List ℕ)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_list_bool_list_nat (a : (List Bool × List ℕ)) (l : List
    (List Bool × List ℕ)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_list_bool_list_nat (l : List (List Bool × List ℕ)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_prod_list_bool_list_nat {a b : List
    (List Bool × List ℕ)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_bool_prod_prod_nat_bool_bool (a : Bool × (ℕ × Bool) × Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_bool_prod_prod_nat_bool_bool {a b : Bool ×
    (ℕ × Bool) × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem decode_encode_list_list_list_nat (a : List (List (List ℕ))) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_list_list_nat {a b : List (List (List ℕ))}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_list_list_nat (a : (List (List ℕ))) (l : List (List (List ℕ))) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_list_list_nat (l : List (List (List ℕ))) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_prod_list_bool_list_prod_bool_bool (a : List Bool × List
    (Bool × Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_list_bool_list_prod_bool_bool (a : List Bool) (b : List
    (Bool × Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_list_bool_list_prod_bool_bool {a b : List Bool × List
    (Bool × Bool)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_bool_prod_bool_list_bool (a : Bool × Bool × List Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_bool_prod_bool_list_bool (a : Bool) (b : Bool × List Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_prod_nat_bool_bool_list_bool (a :
    ((ℕ × Bool) × Bool) × List Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_prod_nat_bool_bool_list_bool {a b :
    ((ℕ × Bool) × Bool) × List Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_prod_nat_bool_bool_list_bool (a : ((ℕ × Bool) × Bool))
    (b : List Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_prod_prod_nat_bool_bool_list_bool {a b :
    ((ℕ × Bool) × Bool) × List Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_prod_nat_bool_prod_bool_nat (a : (List
    (ℕ × Bool)) × Bool × ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_list_prod_nat_bool_prod_bool_nat (a : (List (ℕ × Bool)))
    (b : Bool × ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_list_prod_nat_bool_prod_bool_nat {a b : (List
    (ℕ × Bool)) × Bool × ℕ} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_list_nat_prod_nat_list_nat (a : List
    (List ℕ) × ℕ × List ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_list_nat_prod_nat_list_nat {a b : List
    (List ℕ) × ℕ × List ℕ} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_list_nat_prod_nat_list_nat (a : List (List ℕ))
    (b : ℕ × List ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_nat_prod_prod_nat_bool_bool (a : ℕ × (ℕ × Bool) × Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_nat_prod_prod_nat_bool_bool {a b : ℕ × (ℕ × Bool) × Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_nat_prod_prod_nat_bool_bool {a b : ℕ ×
    (ℕ × Bool) × Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_prod_bool_list_bool (a : List (Bool × List Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_bool_list_bool {a b : List (Bool × List Bool)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_bool_list_bool (a : (Bool × List Bool)) (l : List
    (Bool × List Bool)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_bool_list_bool (l : List (Bool × List Bool)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_prod_bool_list_list_nat (a : Bool × List (List ℕ)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_bool_list_list_nat (a : Bool) (b : List (List ℕ)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_bool_nat_prod_bool_nat (a : (Bool × ℕ) × Bool × ℕ)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_bool_nat_prod_bool_nat {a b : (Bool × ℕ) × Bool × ℕ}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_prod_bool_nat_prod_bool_nat {a b :
    (Bool × ℕ) × Bool × ℕ} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_bool_prod_prod_nat_bool_bool (a : List Bool ×
    (ℕ × Bool) × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_bool_prod_prod_nat_bool_bool {a b : List Bool ×
    (ℕ × Bool) × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_bool_prod_prod_nat_bool_bool (a : List Bool) (b :
    (ℕ × Bool) × Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_list_bool_prod_prod_nat_bool_bool {a b : List Bool ×
    (ℕ × Bool) × Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_prod_prod_bool_nat_prod_bool_nat (a : List
    ((Bool × ℕ) × Bool × ℕ)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_prod_bool_nat_prod_bool_nat {a b : List
    ((Bool × ℕ) × Bool × ℕ)} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_prod_bool_nat_prod_bool_nat (a : ((Bool × ℕ) × Bool × ℕ))
    (l : List ((Bool × ℕ) × Bool × ℕ)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_prod_bool_nat_prod_bool_nat (l : List
    ((Bool × ℕ) × Bool × ℕ)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_prod_prod_nat_list_nat_list_bool (a : (ℕ × List ℕ) × List Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_prod_nat_list_nat_list_bool (a : (ℕ × List ℕ))
    (b : List Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_prod_nat_list_nat_list_bool {a b :
    (ℕ × List ℕ) × List Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_list_bool_prod_bool_nat (a : List
    (List Bool) × Bool × ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_list_list_bool_prod_bool_nat (a : List (List Bool))
    (b : Bool × ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_list_prod_bool_bool_list_list_nat (a : (List
    (Bool × Bool)) × List (List ℕ)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_prod_bool_bool_list_list_nat {a b : (List
    (Bool × Bool)) × List (List ℕ)} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_prod_bool_bool_list_list_nat (a : (List (Bool × Bool)))
    (b : List (List ℕ)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_nat_list_nat_bool (a : (ℕ × List ℕ) × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_prod_nat_list_nat_bool (a : (ℕ × List ℕ)) (b : Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_list_bool_bool (a : List Bool × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_list_bool_bool (a : List Bool) (b : Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_list_prod_list_bool_bool (a : List (List Bool × Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_list_bool_bool {a b : List (List Bool × Bool)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem decode_encode_prod_nat_prod_bool_bool (a : ℕ × Bool × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_nat_prod_bool_bool {a b : ℕ × Bool × Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_nat_prod_bool_bool (a : ℕ) (b : Bool × Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_nat_prod_bool_bool {a b : ℕ × Bool × Bool}
    {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_list_bool_list_nat_nat (a : (List Bool × List ℕ) × ℕ)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_prod_list_bool_list_nat_nat (a : (List Bool × List ℕ))
    (b : ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_prod_list_bool_list_nat_nat {a b :
    (List Bool × List ℕ) × ℕ} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_nat_list_nat_nat (a : (ℕ × List ℕ) × ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_nat_list_nat_nat {a b : (ℕ × List ℕ) × ℕ}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_prod_nat_list_nat_nat {a b : (ℕ × List ℕ) × ℕ}
    {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_prod_nat_prod_bool_bool (a : List (ℕ × Bool × Bool))
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_nat_prod_bool_bool {a b : List (ℕ × Bool × Bool)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_nat_prod_bool_bool (a : (ℕ × Bool × Bool)) (l : List
    (ℕ × Bool × Bool)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_nat_prod_bool_bool (l : List (ℕ × Bool × Bool)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_prod_nat_prod_bool_bool {a b : List (ℕ × Bool × Bool)}
    {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_bool_list_list_bool (a : List Bool × List (List Bool))
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_bool_list_list_bool {a b : List Bool × List
    (List Bool)} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_bool_list_list_bool (a : List Bool) (b : List
    (List Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_list_bool_list_list_bool {a b : List Bool × List
    (List Bool)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_bool_list_bool_list_list_bool (a :
    (Bool × List Bool) × List (List Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_bool_list_bool_list_list_bool {a b :
    (Bool × List Bool) × List (List Bool)} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_bool_list_bool_list_list_bool (a : (Bool × List Bool))
    (b : List (List Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_list_bool_list_nat_bool (a :
    (List Bool × List ℕ) × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_list_bool_list_nat_bool {a b :
    (List Bool × List ℕ) × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_list_bool_list_nat_bool (a : (List Bool × List ℕ))
    (b : Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_list_list_bool_list_list_bool (a : List (List Bool) × List
    (List Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_list_list_bool_list_list_bool (a : List (List Bool))
    (b : List (List Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_nat_list_nat_prod_bool_nat (a : (ℕ × List ℕ) × Bool × ℕ)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_nat_list_nat_prod_bool_nat {a b :
    (ℕ × List ℕ) × Bool × ℕ} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_nat_list_nat_prod_bool_nat (a : (ℕ × List ℕ))
    (b : Bool × ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_list_list_bool_nat (a : List (List Bool) × ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_list_bool_nat {a b : List (List Bool) × ℕ}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_list_bool_nat (a : List (List Bool)) (b : ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_list_prod_nat_bool_list_list_bool (a : (List
    (ℕ × Bool)) × List (List Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_list_prod_nat_bool_list_list_bool (a : (List (ℕ × Bool)))
    (b : List (List Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_nat_prod_bool_nat (a : ℕ × Bool × ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_nat_prod_bool_nat {a b : ℕ × Bool × ℕ}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_nat_prod_bool_nat (a : ℕ) (b : Bool × ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_nat_prod_bool_nat {a b : ℕ × Bool × ℕ} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_list_bool_prod_bool_list_bool (a : List
    (List Bool) × Bool × List Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_list_bool_prod_bool_list_bool {a b : List
    (List Bool) × Bool × List Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_list_list_bool_prod_bool_list_bool {a b : List
    (List Bool) × Bool × List Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_prod_nat_prod_bool_nat (a : List (ℕ × Bool × ℕ)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encodeAll_cons_prod_nat_prod_bool_nat (a : (ℕ × Bool × ℕ)) (l : List
    (ℕ × Bool × ℕ)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_nat_prod_bool_nat (l : List (ℕ × Bool × ℕ)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_prod_nat_prod_bool_nat {a b : List (ℕ × Bool × ℕ)}
    {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_list_nat_list_bool (a : List (List ℕ) × List Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_list_nat_list_bool {a b : List (List ℕ) × List Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_list_nat_list_bool (a : List (List ℕ)) (b : List Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_list_list_nat_list_bool {a b : List
    (List ℕ) × List Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_prod_nat_bool_prod_bool_bool (a : (List
    (ℕ × Bool)) × Bool × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_prod_nat_bool_prod_bool_bool {a b : (List
    (ℕ × Bool)) × Bool × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_prod_nat_bool_prod_bool_bool (a : (List (ℕ × Bool)))
    (b : Bool × Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_nat_prod_bool_bool_list_bool (a :
    (ℕ × Bool × Bool) × List Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_append_cancel_prod_prod_nat_prod_bool_bool_list_bool {a b :
    (ℕ × Bool × Bool) × List Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_nat_list_nat_prod_nat_bool (a : (ℕ × List ℕ) × ℕ × Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_nat_list_nat_prod_nat_bool {a b :
    (ℕ × List ℕ) × ℕ × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_nat_list_nat_prod_nat_bool (a : (ℕ × List ℕ))
    (b : ℕ × Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_prod_nat_list_nat_prod_nat_bool {a b :
    (ℕ × List ℕ) × ℕ × Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_nat_prod_list_bool_bool (a : List ℕ × List Bool × Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_nat_prod_list_bool_bool
    {a b : List ℕ × List Bool × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem decode_encode_prod_prod_prod_bool_nat_list_nat_bool (a :
    ((Bool × ℕ) × List ℕ) × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_prod_bool_nat_list_nat_bool {a b :
    ((Bool × ℕ) × List ℕ) × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_prod_bool_nat_list_nat_bool (a : ((Bool × ℕ) × List ℕ))
    (b : Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_bool_bool_list_list_bool (a : (Bool × Bool) × List
    (List Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_prod_bool_bool_list_list_bool (a : (Bool × Bool)) (b : List
    (List Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_list_bool_list_prod_nat_bool (a : List Bool × List
    (ℕ × Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_list_bool_list_prod_nat_bool (a : List Bool) (b : List
    (ℕ × Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_list_bool_list_prod_nat_bool {a b : List Bool × List
    (ℕ × Bool)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_bool_list_bool (a : List Bool × List Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_bool_list_bool {a b : List Bool × List Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_list_bool_list_bool {a b : List Bool × List Bool}
    {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_list_prod_list_bool_list_bool (a : List (List Bool × List Bool))
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_list_bool_list_bool {a b : List
    (List Bool × List Bool)} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_list_bool_list_bool (a : (List Bool × List Bool)) (l : List
    (List Bool × List Bool)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_list_bool_list_bool (l : List (List Bool × List Bool)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_prod_list_bool_list_bool {a b : List
    (List Bool × List Bool)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_bool_prod_bool_bool (a : Bool × Bool × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_bool_prod_bool_bool {a b : Bool × Bool × Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_bool_prod_bool_bool {a b : Bool × Bool × Bool}
    {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_nat_bool_list_nat (a : (ℕ × Bool) × List ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_nat_bool_list_nat {a b : (ℕ × Bool) × List ℕ}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_nat_bool_list_nat (a : (ℕ × Bool)) (b : List ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_bool_nat_list_prod_nat_bool (a : (Bool × ℕ) × List
    (ℕ × Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_prod_bool_nat_list_prod_nat_bool (a : (Bool × ℕ)) (b : List
    (ℕ × Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_list_prod_prod_nat_bool_list_nat (a : List ((ℕ × Bool) × List ℕ))
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_prod_nat_bool_list_nat {a b : List
    ((ℕ × Bool) × List ℕ)} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_prod_nat_bool_list_nat (a : ((ℕ × Bool) × List ℕ)) (l : List
    ((ℕ × Bool) × List ℕ)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_prod_nat_bool_list_nat (l : List ((ℕ × Bool) × List ℕ)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem decode_encode_prod_prod_bool_prod_bool_bool_list_bool (a :
    (Bool × Bool × Bool) × List Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_prod_bool_prod_bool_bool_list_bool (a : (Bool × Bool × Bool))
    (b : List Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_list_prod_bool_prod_bool_bool (a : List (Bool × Bool × Bool))
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_list_prod_bool_prod_bool_bool {a b : List (Bool × Bool × Bool)}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encodeAll_cons_prod_bool_prod_bool_bool (a : (Bool × Bool × Bool)) (l : List
    (Bool × Bool × Bool)) :
    encodeAll (a :: l) = encode a ++ encodeAll l :=
  rfl

theorem length_encode_list_prod_bool_prod_bool_bool (l : List (Bool × Bool × Bool)) :
    (encode l).length = l.length + 1 + (encodeAll l).length :=
  length_encode_list l

theorem encode_append_cancel_list_prod_bool_prod_bool_bool {a b : List
    (Bool × Bool × Bool)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_bool_list_bool_nat (a : (Bool × List Bool) × ℕ)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_prod_bool_list_bool_nat (a : (Bool × List Bool)) (b : ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_prod_nat_bool_bool_list_nat (a :
    ((ℕ × Bool) × Bool) × List ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem length_encode_prod_prod_prod_nat_bool_bool_list_nat (a : ((ℕ × Bool) × Bool))
    (b : List ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_prod_bool_prod_bool_bool_list_nat (a :
    (Bool × Bool × Bool) × List ℕ) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_bool_prod_bool_bool_list_nat {a b :
    (Bool × Bool × Bool) × List ℕ} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_bool_prod_bool_bool_list_nat (a : (Bool × Bool × Bool))
    (b : List ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_prod_bool_prod_bool_bool_list_nat {a b :
    (Bool × Bool × Bool) × List ℕ} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_nat_prod_bool_nat_list_bool (a :
    (ℕ × Bool × ℕ) × List Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem decode_encode_prod_list_list_nat_prod_list_bool_bool (a : List
    (List ℕ) × List Bool × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_append_cancel_prod_list_list_nat_prod_list_bool_bool {a b : List
    (List ℕ) × List Bool × Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_list_nat_list_nat (a : List (List ℕ) × List ℕ)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_list_nat_list_nat {a b : List (List ℕ) × List ℕ}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_list_nat_list_nat (a : List (List ℕ)) (b : List ℕ) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_nat_prod_bool_list_bool (a : ℕ × Bool × List Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_nat_prod_bool_list_bool {a b : ℕ × Bool × List Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_nat_prod_bool_list_bool (a : ℕ) (b : Bool × List Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem decode_encode_prod_list_prod_bool_bool_prod_bool_bool (a : (List
    (Bool × Bool)) × Bool × Bool) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_prod_bool_bool_prod_bool_bool {a b : (List
    (Bool × Bool)) × Bool × Bool} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem encode_append_cancel_prod_list_prod_bool_bool_prod_bool_bool {a b : (List
    (Bool × Bool)) × Bool × Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_list_prod_bool_nat_bool (a : (List (Bool × ℕ)) × Bool)
    (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_list_prod_bool_nat_bool {a b : (List (Bool × ℕ)) × Bool}
    (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_list_prod_bool_nat_bool (a : (List (Bool × ℕ))) (b : Bool) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_list_prod_bool_nat_bool {a b : (List
    (Bool × ℕ)) × Bool} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

theorem decode_encode_prod_prod_bool_nat_list_prod_bool_bool (a : (Bool × ℕ) × List
    (Bool × Bool)) (r : Word) :
    decode (encode a ++ r) = some (a, r) :=
  decode_encode a r

theorem encode_injective_prod_prod_bool_nat_list_prod_bool_bool {a b : (Bool × ℕ) × List
    (Bool × Bool)} (h : encode a = encode b) :
    a = b :=
  encode_injective h

theorem length_encode_prod_prod_bool_nat_list_prod_bool_bool (a : (Bool × ℕ)) (b : List
    (Bool × Bool)) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  length_encode_prod a b

theorem encode_append_cancel_prod_prod_bool_nat_list_prod_bool_bool {a b :
    (Bool × ℕ) × List (Bool × Bool)} {r s : Word}
    (h : encode a ++ r = encode b ++ s) :
    a = b ∧ r = s :=
  encode_append_cancel h

end Encoding

end Complexity
