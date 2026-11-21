import PNP.Data.Language

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
