import PNP.Poly.Tactic

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

theorem const_add (hf : IsPolyBounded f) : IsPolyBounded fun n => 3 + f n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (g n) ^ 3`. -/
theorem comp_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n) ^ 3 :=
  (hf.comp hg).pow 3

theorem const_mul_id_mul_pow_two (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 6 * n * f n ^ 2 :=
  ((IsPolyBounded.const 6).mul IsPolyBounded.id).mul (hf.pow 2)

theorem const_add_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (3 + f n) * g n := by
  poly_bound

theorem const_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 5 * f n * g n :=
  (hf.const_mul 5).mul hg

theorem comp_add_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) + h n * n :=
  (hf.comp hg).add (hh.mul IsPolyBounded.id)

/-- Closure of polynomially bounded functions under `n ↦ 6 * (f n + n)`. -/
theorem const_mul_add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => 6 * (f n + n) := by
  poly_bound

theorem comp_id_pow_three (hf : IsPolyBounded f) : IsPolyBounded fun n => f (n ^ 3) :=
  hf.comp (IsPolyBounded.id.pow 3)

theorem pow_three_pow_three_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n ^ 3) ^ 3 + g n := by
  poly_bound

theorem comp_mul_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n * h n) ^ 5 :=
  (hf.comp (hg.mul hh)).pow 5

theorem pow_two_pow_two (hf : IsPolyBounded f) : IsPolyBounded fun n => (f n ^ 2) ^ 2 :=
  (hf.pow 2).pow 2

/-- Closure of polynomially bounded functions under `n ↦ (7 + n) * f n`. -/
theorem const_add_id_mul (hf : IsPolyBounded f) : IsPolyBounded fun n => (7 + n) * f n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ 3 * (5 * n * (3 * f n))`. -/
theorem const_mul_const_mul_id_mul_const_mul (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 3 * (5 * n * (3 * f n)) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (2 + g n + h n)`. -/
theorem comp_const_add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (2 + g n + h n) :=
  hf.comp (((IsPolyBounded.const 2).add hg).add hh)

/-- Closure of polynomially bounded functions under `n ↦ (3 * n) ^ 4 * f n`. -/
theorem const_mul_id_pow_four_mul (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (3 * n) ^ 4 * f n := by
  poly_bound

theorem mul_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f n * n :=
  hf.mul IsPolyBounded.id

/-- Closure of polynomially bounded functions under `n ↦ f n * g n + 8`. -/
theorem mul_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * g n + 8 := by
  poly_bound

theorem comp_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) + h n :=
  (hf.comp hg).add hh

theorem add_id_add_const_add_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n + (n + 6 + 8 * g n) := by
  poly_bound

theorem add_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n + g n) ^ 2 :=
  (hf.add hg).pow 2

/-- Closure of polynomially bounded functions under `n ↦ (f n ^ 2) ^ 4 + n * g n * n`. -/
theorem pow_two_pow_four_add_id_mul_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n ^ 2) ^ 4 + n * g n * n := by
  poly_bound

theorem pow_three_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n ^ 3 + g (h n) :=
  (hf.pow 3).add (hg.comp hh)

theorem add_mul_const_mul_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => ((f n + g n) * (7 * h n)) ^ 5 := by
  poly_bound

theorem mul_id_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * n * g n := by
  poly_bound

theorem pow_two_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n ^ 2 * (g n * h n) := by
  poly_bound

theorem id_mul (hf : IsPolyBounded f) : IsPolyBounded fun n => n * f n :=
  IsPolyBounded.id.mul hf

theorem comp_comp_mul_const (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g (h n * 8)) :=
  hf.comp (hg.comp (hh.mul (IsPolyBounded.const 8)))

theorem mul_add_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * g n + (h n + 2) :=
  (hf.mul hg).add (hh.add (IsPolyBounded.const 2))

theorem comp_id_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (n) * g n :=
  (hf.comp IsPolyBounded.id).mul hg

theorem comp_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n + 2) :=
  hf.comp (hg.add (IsPolyBounded.const 2))

theorem comp_add_id_mul_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n + n) * (h n + n) :=
  (hf.comp (hg.add IsPolyBounded.id)).mul (hh.add IsPolyBounded.id)

theorem mul_const_pow_three (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n * 8) ^ 3 :=
  (hf.mul (IsPolyBounded.const 8)).pow 3

theorem comp_mul_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n * 6 + h n) :=
  hf.comp ((hg.mul (IsPolyBounded.const 6)).add hh)

/-- Closure of polynomially bounded functions under `n ↦ f (g (h n) + f n)`. -/
theorem comp_comp_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g (h n) + f n) :=
  hf.comp ((hg.comp hh).add hf)

theorem const_mul_id_add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 5 * n + (f n + g n) :=
  (IsPolyBounded.id.const_mul 5).add (hf.add hg)

/-- Closure of polynomially bounded functions under `n ↦ ((f n * g n) ^ 4) ^ 5`. -/
theorem mul_pow_four_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => ((f n * g n) ^ 4) ^ 5 :=
  ((hf.mul hg).pow 4).pow 5

/-- Closure of polynomially bounded functions under `n ↦ f n ^ 5 + g n`. -/
theorem pow_five_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 5 + g n :=
  (hf.pow 5).add hg

theorem add_add_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n + g n + h n ^ 4 := by
  poly_bound

theorem pow_three (hf : IsPolyBounded f) : IsPolyBounded fun n => f n ^ 3 :=
  hf.pow 3

theorem id_pow_three_add_add_pow_five_mul_const (hf : IsPolyBounded f)
    (hg : IsPolyBounded g) :
    IsPolyBounded fun n => n ^ 3 + f n + g n ^ 5 * 6 := by
  poly_bound

theorem pow_four_add_const (hf : IsPolyBounded f) : IsPolyBounded fun n => f n ^ 4 + 9 :=
  (hf.pow 4).add (IsPolyBounded.const 9)

theorem comp_comp_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g (3 + h n)) :=
  hf.comp (hg.comp ((IsPolyBounded.const 3).add hh))

theorem const_mul_const_mul (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 3 * (6 * f n) := by
  poly_bound

theorem add_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n + 5 * g n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ (f n + n) * (g n * h n) + 3`. -/
theorem add_id_mul_mul_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n + n) * (g n * h n) + 3 :=
  ((hf.add IsPolyBounded.id).mul (hg.mul hh)).add (IsPolyBounded.const 3)

theorem add_pow_three_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => ((f n + g n) ^ 3) ^ 4 := by
  poly_bound

theorem id_add (hf : IsPolyBounded f) : IsPolyBounded fun n => n + f n := by
  poly_bound

theorem pow_four (hf : IsPolyBounded f) : IsPolyBounded fun n => f n ^ 4 := by
  poly_bound

theorem comp_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) + h (g n) :=
  (hf.comp hg).add (hh.comp hg)

theorem const_mul_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => 4 * f n + g (h n) :=
  (hf.const_mul 4).add (hg.comp hh)

theorem comp_pow_five_mul_const_add_pow_five (hf : IsPolyBounded f)
    (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) ^ 5 * (7 + h n) ^ 5 :=
  ((hf.comp hg).pow 5).mul (((IsPolyBounded.const 7).add hh).pow 5)

theorem comp_id_add_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (n + g n) ^ 4 :=
  (hf.comp (IsPolyBounded.id.add hg)).pow 4

/-- Closure of polynomially bounded functions under `n ↦ 3 * f (n)`. -/
theorem const_mul_comp_id (hf : IsPolyBounded f) : IsPolyBounded fun n => 3 * f (n) :=
  (hf.comp IsPolyBounded.id).const_mul 3

theorem const_mul_mul_const (hf : IsPolyBounded f) : IsPolyBounded fun n => 3 * f n * 9 :=
  ((IsPolyBounded.const 3).mul hf).mul (IsPolyBounded.const 9)

/-- Closure of polynomially bounded functions under `n ↦ f (n + n)`. -/
theorem comp_id_add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f (n + n) :=
  hf.comp (IsPolyBounded.id.add IsPolyBounded.id)

/-- Closure of polynomially bounded functions under `n ↦ (f n * n + n) * 2`. -/
theorem mul_id_add_id_mul_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n * n + n) * 2 :=
  ((hf.mul IsPolyBounded.id).add IsPolyBounded.id).mul (IsPolyBounded.const 2)

theorem const_mul_mul_id_mul_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 7 * (f n * n * 8) :=
  ((hf.mul IsPolyBounded.id).mul (IsPolyBounded.const 8)).const_mul 7

/-- Closure of polynomially bounded functions under `n ↦ f n * n + n`. -/
theorem mul_id_add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f n * n + n := by
  poly_bound

theorem pow_two_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 2 + g n :=
  (hf.pow 2).add hg

theorem const_mul_pow_five_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (3 * f n ^ 5) ^ 5 := by
  poly_bound

theorem comp_comp_id_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g (n) ^ 5) :=
  hf.comp ((hg.comp IsPolyBounded.id).pow 5)

theorem pow_five (hf : IsPolyBounded f) : IsPolyBounded fun n => f n ^ 5 := by
  poly_bound

theorem comp_pow_four_mul_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n ^ 4 * (h n + n)) :=
  hf.comp ((hg.pow 4).mul (hh.add IsPolyBounded.id))

theorem comp_const_mul_add_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (9 * g n + (6 + h n)) :=
  hf.comp (((IsPolyBounded.const 9).mul hg).add ((IsPolyBounded.const 6).add hh))

/-- Closure of polynomially bounded functions under `n ↦ (n + f n + (g n + 8)) ^ 2`. -/
theorem id_add_add_add_const_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (n + f n + (g n + 8)) ^ 2 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (g n ^ 5)`. -/
theorem comp_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n ^ 5) :=
  hf.comp (hg.pow 5)

theorem const_mul_const_mul_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 7 * (2 * f (g n)) :=
  ((hf.comp hg).const_mul 2).const_mul 7

/-- Closure of polynomially bounded functions under `n ↦ f (n * g n + h n ^ 2)`. -/
theorem comp_id_mul_add_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (n * g n + h n ^ 2) :=
  hf.comp ((IsPolyBounded.id.mul hg).add (hh.pow 2))

/-- Closure of polynomially bounded functions under `n ↦ ((f n + g n) * h (h n)) ^ 3`. -/
theorem add_mul_comp_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => ((f n + g n) * h (h n)) ^ 3 :=
  ((hf.add hg).mul (hh.comp hh)).pow 3

theorem pow_two_add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n ^ 2 + g n + h n :=
  ((hf.pow 2).add hg).add hh

theorem mul_mul_comp_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * g n * h (n) :=
  (hf.mul hg).mul (hh.comp IsPolyBounded.id)

/-- Closure of polynomially bounded functions under `n ↦ (f n + 9) ^ 4`. -/
theorem add_const_pow_four (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n + 9) ^ 4 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ 3 * f n + g n`. -/
theorem const_mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 3 * f n + g n := by
  poly_bound

theorem id_pow_five_add (hf : IsPolyBounded f) : IsPolyBounded fun n => n ^ 5 + f n := by
  poly_bound

theorem pow_three_pow_four (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n ^ 3) ^ 4 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ (6 * f n) ^ 3`. -/
theorem const_mul_pow_three (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (6 * f n) ^ 3 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ 2 * (8 * f n) + 3`. -/
theorem const_mul_const_mul_add_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 2 * (8 * f n) + 3 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (g n * h n)`. -/
theorem comp_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n * h n) :=
  hf.comp (hg.mul hh)

theorem comp_add_id_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f ((g n + n) ^ 4) :=
  hf.comp ((hg.add IsPolyBounded.id).pow 4)

/-- Closure of polynomially bounded functions under `n ↦ n ^ 3 * f n`. -/
theorem id_pow_three_mul (hf : IsPolyBounded f) : IsPolyBounded fun n => n ^ 3 * f n :=
  (IsPolyBounded.id.pow 3).mul hf

/-- Closure of polynomially bounded functions under `n ↦ f n ^ 5 * (g n * h n)`. -/
theorem pow_five_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n ^ 5 * (g n * h n) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ n * 8 * f n`. -/
theorem id_mul_const_mul (hf : IsPolyBounded f) : IsPolyBounded fun n => n * 8 * f n := by
  poly_bound

theorem add_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n + g n + n :=
  (hf.add hg).add IsPolyBounded.id

theorem pow_three_mul_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 3 * (7 + g n) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ 4 + f n + g n`. -/
theorem const_add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 4 + f n + g n := by
  poly_bound

theorem comp_id_pow_three_mul_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => f (n ^ 3 * 3) :=
  hf.comp ((IsPolyBounded.id.pow 3).mul (IsPolyBounded.const 3))

theorem comp_mul_add_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n * h n) + (7 + g n) :=
  (hf.comp (hg.mul hh)).add ((IsPolyBounded.const 7).add hg)

theorem comp_const_mul_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f ((7 * g n) ^ 3) :=
  hf.comp (((IsPolyBounded.const 7).mul hg).pow 3)

/-- Closure of polynomially bounded functions under `n ↦ 2 * f (g n)`. -/
theorem const_mul_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 2 * f (g n) :=
  (hf.comp hg).const_mul 2

/-- Closure of polynomially bounded functions under `n ↦ (7 * (f n + g n)) ^ 3`. -/
theorem const_mul_add_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (7 * (f n + g n)) ^ 3 :=
  ((hf.add hg).const_mul 7).pow 3

theorem comp_const_add_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f ((5 + g n) * (h n * f n)) :=
  hf.comp (((IsPolyBounded.const 5).add hg).mul (hh.mul hf))

theorem const_mul_id_add_mul_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 9 * ((n + f n) * 5) :=
  ((IsPolyBounded.id.add hf).mul (IsPolyBounded.const 5)).const_mul 9

/-- Closure of polynomially bounded functions under `n ↦ f (2 * (g n + h n))`. -/
theorem comp_const_mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (2 * (g n + h n)) :=
  hf.comp ((hg.add hh).const_mul 2)

theorem const_mul_add_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 3 * (f n + 8) + g n := by
  poly_bound

theorem comp_const_mul_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (3 * (g n + n)) :=
  hf.comp ((hg.add IsPolyBounded.id).const_mul 3)

theorem comp_const_add_add_id_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (6 + g n + n * h n) :=
  hf.comp (((IsPolyBounded.const 6).add hg).add (IsPolyBounded.id.mul hh))

/-- Closure of polynomially bounded functions under `n ↦ f (g n) * (h n * n)`. -/
theorem comp_mul_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) * (h n * n) :=
  (hf.comp hg).mul (hh.mul IsPolyBounded.id)

theorem const_mul_add_id_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (5 * (f n + n)) ^ 5 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f n * g n + h n`. -/
theorem mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * g n + h n :=
  (hf.mul hg).add hh

theorem const_mul_mul_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => 7 * f n * g (h n) :=
  (hf.const_mul 7).mul (hg.comp hh)

theorem const_mul_comp_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 3 * f (g n ^ 3) :=
  (hf.comp (hg.pow 3)).const_mul 3

theorem const_add_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (7 + f n) ^ 5 := by
  poly_bound

theorem comp_const_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (4 * g n * h n) :=
  hf.comp ((hg.const_mul 4).mul hh)

/-- Closure of polynomially bounded functions under `n ↦ (f n + n) ^ 2 * g n`. -/
theorem add_id_pow_two_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n + n) ^ 2 * g n :=
  ((hf.add IsPolyBounded.id).pow 2).mul hg

/-- Closure of polynomially bounded functions under `n ↦ (f (g n) * (h n + n)) ^ 2`. -/
theorem comp_mul_add_id_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f (g n) * (h n + n)) ^ 2 :=
  ((hf.comp hg).mul (hh.add IsPolyBounded.id)).pow 2

/-- Closure of polynomially bounded functions under `n ↦ 9 * f n + 6 + n`. -/
theorem const_mul_add_const_add_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 9 * f n + 6 + n :=
  ((hf.const_mul 9).add (IsPolyBounded.const 6)).add IsPolyBounded.id

/-- Closure of polynomially bounded functions under `n ↦ (3 * f n * (2 * g n)) ^ 5`. -/
theorem const_mul_mul_const_mul_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (3 * f n * (2 * g n)) ^ 5 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (g n) * h n + g n * g n`. -/
theorem comp_mul_add_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) * h n + g n * g n :=
  ((hf.comp hg).mul hh).add (hg.mul hg)

theorem mul_id_add_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * n + g n * n :=
  (hf.mul IsPolyBounded.id).add (hg.mul IsPolyBounded.id)

/-- Closure of polynomially bounded functions under `n ↦ f ((g n * 9) ^ 4)`. -/
theorem comp_mul_const_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f ((g n * 9) ^ 4) :=
  hf.comp ((hg.mul (IsPolyBounded.const 9)).pow 4)

theorem comp_const_add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f (6 + n) :=
  hf.comp ((IsPolyBounded.const 6).add IsPolyBounded.id)

theorem const_mul_mul_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 3 * f n * (2 + g n) := by
  poly_bound

theorem mul_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * 8 + g n :=
  (hf.mul (IsPolyBounded.const 8)).add hg

theorem id_mul_add_const (hf : IsPolyBounded f) : IsPolyBounded fun n => n * f n + 9 :=
  (IsPolyBounded.id.mul hf).add (IsPolyBounded.const 9)

/-- Closure of polynomially bounded functions under `n ↦ f n + g n + h (h n)`. -/
theorem add_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n + g n + h (h n) :=
  (hf.add hg).add (hh.comp hh)

theorem id_pow_three_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => n ^ 3 + f (g n) :=
  (IsPolyBounded.id.pow 3).add (hf.comp hg)

theorem comp_id_mul_const_add_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (n) * (6 + g n) * h n :=
  ((hf.comp IsPolyBounded.id).mul ((IsPolyBounded.const 6).add hg)).mul hh

/-- Closure of polynomially bounded functions under `n ↦ f ((n + g n) * 2)`. -/
theorem comp_id_add_mul_const (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f ((n + g n) * 2) :=
  hf.comp ((IsPolyBounded.id.add hg).mul (IsPolyBounded.const 2))

theorem add_id_add_const (hf : IsPolyBounded f) : IsPolyBounded fun n => f n + n + 4 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ (f n * g n) ^ 3`. -/
theorem mul_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n * g n) ^ 3 :=
  (hf.mul hg).pow 3

/-- Closure of polynomially bounded functions under `n ↦ f n + g n + h n`. -/
theorem add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n + g n + h n :=
  (hf.add hg).add hh

theorem id_mul_const_add (hf : IsPolyBounded f) : IsPolyBounded fun n => n * 5 + f n :=
  (IsPolyBounded.id.mul (IsPolyBounded.const 5)).add hf

theorem const_mul_id_add_id_add (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 5 * (n + n + f n) :=
  ((IsPolyBounded.id.add IsPolyBounded.id).add hf).const_mul 5

theorem id_add_pow_five (hf : IsPolyBounded f) : IsPolyBounded fun n => (n + f n) ^ 5 :=
  (IsPolyBounded.id.add hf).pow 5

theorem add_mul_add_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => ((f n + g n) * (h n + g n)) ^ 4 := by
  poly_bound

theorem const_mul_const_add (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 6 * (9 + f n) :=
  ((IsPolyBounded.const 9).add hf).const_mul 6

/-- Closure of polynomially bounded functions under `n ↦ f n + g n + (h n + g n) + 9`. -/
theorem add_add_add_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n + g n + (h n + g n) + 9 :=
  ((hf.add hg).add (hh.add hg)).add (IsPolyBounded.const 9)

theorem mul_const_mul_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * (6 * g n + n) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ (n + 3) * f n`. -/
theorem id_add_const_mul (hf : IsPolyBounded f) : IsPolyBounded fun n => (n + 3) * f n :=
  (IsPolyBounded.id.add (IsPolyBounded.const 3)).mul hf

theorem comp_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g (h n)) :=
  hf.comp (hg.comp hh)

theorem comp_mul_pow_two_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f (g n) * h n ^ 2) ^ 2 :=
  ((hf.comp hg).mul (hh.pow 2)).pow 2

/-- Closure of polynomially bounded functions under `n ↦ 2 + f n + 2 * g n`. -/
theorem const_add_add_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 2 + f n + 2 * g n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (6 * g n + (h n + g n))`. -/
theorem comp_const_mul_add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (6 * g n + (h n + g n)) :=
  hf.comp (((IsPolyBounded.const 6).mul hg).add (hh.add hg))

theorem comp_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n) ^ 2 :=
  (hf.comp hg).pow 2

theorem mul_mul_const_add_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n * g n * (5 + h n)) ^ 2 := by
  poly_bound

theorem add_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n + g n) ^ 5 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (5 * g n)`. -/
theorem comp_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (5 * g n) :=
  hf.comp (hg.const_mul 5)

/-- Closure of polynomially bounded functions under `n ↦ 3 * (n * 5) * f n`. -/
theorem const_mul_id_mul_const_mul (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 3 * (n * 5) * f n :=
  ((IsPolyBounded.id.mul (IsPolyBounded.const 5)).const_mul 3).mul hf

theorem comp_comp_id_mul_mul_const (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g (n) * (h n * 7)) :=
  hf.comp ((hg.comp IsPolyBounded.id).mul (hh.mul (IsPolyBounded.const 7)))

theorem const_mul_add_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 6 * f n + 7 * g n := by
  poly_bound

theorem comp_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (6 + g n) :=
  hf.comp ((IsPolyBounded.const 6).add hg)

theorem comp_id_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (n + g n) :=
  hf.comp (IsPolyBounded.id.add hg)

/-- Closure of polynomially bounded functions under `n ↦ f (6 * (4 * n))`. -/
theorem comp_const_mul_const_mul_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => f (6 * (4 * n)) :=
  hf.comp ((IsPolyBounded.id.const_mul 4).const_mul 6)

/-- Closure of polynomially bounded functions under `n ↦ (f n + n) * 8`. -/
theorem add_id_mul_const (hf : IsPolyBounded f) : IsPolyBounded fun n => (f n + n) * 8 := by
  poly_bound

theorem mul_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * 5 * g n := by
  poly_bound

theorem comp_id_add_const (hf : IsPolyBounded f) : IsPolyBounded fun n => f (n + 9) :=
  hf.comp (IsPolyBounded.id.add (IsPolyBounded.const 9))

theorem id_mul_add_const_mul_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => n * f n + 9 * n := by
  poly_bound

theorem mul_const_mul_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f n * 4 * n :=
  (hf.mul (IsPolyBounded.const 4)).mul IsPolyBounded.id

theorem const_mul_id_add_id_pow_three_add_id_add (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 5 * n + n ^ 3 + (n + f n) :=
  ((IsPolyBounded.id.const_mul 5).add (IsPolyBounded.id.pow 3)).add (IsPolyBounded.id.add hf)

theorem const_mul_id_add_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 2 * n + f n * g n :=
  (IsPolyBounded.id.const_mul 2).add (hf.mul hg)

theorem id_pow_three_add_id_add (hf : IsPolyBounded f) :
    IsPolyBounded fun n => n ^ 3 + n + f n :=
  ((IsPolyBounded.id.pow 3).add IsPolyBounded.id).add hf

/-- Closure of polynomially bounded functions under `n ↦ (f n + 9) * 8`. -/
theorem add_const_mul_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n + 9) * 8 :=
  (hf.add (IsPolyBounded.const 9)).mul (IsPolyBounded.const 8)

/-- Closure of polynomially bounded functions under `n ↦ 6 + f n + g n ^ 5 + h n`. -/
theorem const_add_add_pow_five_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => 6 + f n + g n ^ 5 + h n := by
  poly_bound

theorem const_mul_pow_two (hf : IsPolyBounded f) : IsPolyBounded fun n => 6 * f n ^ 2 :=
  (hf.pow 2).const_mul 6

theorem comp_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n) + n :=
  (hf.comp hg).add IsPolyBounded.id

theorem comp_const_mul_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f (6 * n) :=
  hf.comp (IsPolyBounded.id.const_mul 6)

theorem pow_two_pow_five (hf : IsPolyBounded f) : IsPolyBounded fun n => (f n ^ 2) ^ 5 :=
  (hf.pow 2).pow 5

theorem mul_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * g n * (h n * f n) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (g n + 5) * (7 + n)`. -/
theorem comp_add_const_mul_const_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n + 5) * (7 + n) :=
  (hf.comp (hg.add (IsPolyBounded.const 5))).mul ((IsPolyBounded.const 7).add IsPolyBounded.id)

theorem comp_id_add_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (n) + 6 * g n :=
  (hf.comp IsPolyBounded.id).add (hg.const_mul 6)

/-- Closure of polynomially bounded functions under `n ↦ f (g n) * 9`. -/
theorem comp_mul_const (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n) * 9 :=
  (hf.comp hg).mul (IsPolyBounded.const 9)

theorem comp_comp_add_const_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g (h n) + (4 + n)) :=
  hf.comp ((hg.comp hh).add ((IsPolyBounded.const 4).add IsPolyBounded.id))

theorem const_add_id_mul_add_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (7 + n) * (f n + 9) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ 4 * (f n * n + g n)`. -/
theorem const_mul_mul_id_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 4 * (f n * n + g n) := by
  poly_bound

theorem const_mul_mul_const_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (5 * (f n * 5)) ^ 5 := by
  poly_bound

theorem pow_three_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 3 + g n :=
  (hf.pow 3).add hg

theorem comp_id_add_id_pow_three (hf : IsPolyBounded f) :
    IsPolyBounded fun n => f ((n + n) ^ 3) :=
  hf.comp ((IsPolyBounded.id.add IsPolyBounded.id).pow 3)

theorem comp_comp_const_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g (6 + n)) :=
  hf.comp (hg.comp ((IsPolyBounded.const 6).add IsPolyBounded.id))

theorem comp_add_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) + (h n + n) :=
  (hf.comp hg).add (hh.add IsPolyBounded.id)

theorem pow_four_add_id_pow_three (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n ^ 4 + n) ^ 3 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ 3 + n + f n`. -/
theorem const_add_id_add (hf : IsPolyBounded f) : IsPolyBounded fun n => 3 + n + f n := by
  poly_bound

theorem pow_two_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 2 * g n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ (f n ^ 3) ^ 3`. -/
theorem pow_three_pow_three (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n ^ 3) ^ 3 := by
  poly_bound

theorem comp_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n * n) :=
  hf.comp (hg.mul IsPolyBounded.id)

theorem comp_mul_id_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n * n) * n :=
  (hf.comp (hg.mul IsPolyBounded.id)).mul IsPolyBounded.id

theorem comp_comp_mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g (h n)) * (f n + f n) :=
  (hf.comp (hg.comp hh)).mul (hf.add hf)

theorem comp_mul_id_mul_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n * n * (3 * h n)) :=
  hf.comp ((hg.mul IsPolyBounded.id).mul (hh.const_mul 3))

/-- Closure of polynomially bounded functions under `n ↦ 2 * ((n + f n) * n)`. -/
theorem const_mul_id_add_mul_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 2 * ((n + f n) * n) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f n * (g n * h n)`. -/
theorem mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * (g n * h n) := by
  poly_bound

theorem add_id_mul_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n + n) * (8 * g n) :=
  (hf.add IsPolyBounded.id).mul ((IsPolyBounded.const 8).mul hg)

/-- Closure of polynomially bounded functions under `n ↦ f (n) ^ 5`. -/
theorem comp_id_pow_five (hf : IsPolyBounded f) : IsPolyBounded fun n => f (n) ^ 5 :=
  (hf.comp IsPolyBounded.id).pow 5

theorem const_add_add_id_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 9 + f n + n + g n := by
  poly_bound

theorem comp_add_comp_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) + h (n) :=
  (hf.comp hg).add (hh.comp IsPolyBounded.id)

theorem const_mul_id_mul_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (8 * (n * f n)) ^ 5 :=
  ((IsPolyBounded.id.mul hf).const_mul 8).pow 5

theorem comp_add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) + h n + f n :=
  ((hf.comp hg).add hh).add hf

theorem pow_four_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 4 * g n := by
  poly_bound

theorem comp_mul_const_add_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n * 6 + h n ^ 5) :=
  hf.comp ((hg.mul (IsPolyBounded.const 6)).add (hh.pow 5))

theorem comp_add_id_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n) + (n + 6) :=
  (hf.comp hg).add (IsPolyBounded.id.add (IsPolyBounded.const 6))

theorem id_add_add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => n + f n + n := by
  poly_bound

theorem mul_const_add_id_mul_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => f n * 2 + n * n := by
  poly_bound

theorem mul_id_mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * n * (g n + h n) :=
  (hf.mul IsPolyBounded.id).mul (hg.add hh)

/-- Closure of polynomially bounded functions under `n ↦ (n + f n) * 8`. -/
theorem id_add_mul_const (hf : IsPolyBounded f) : IsPolyBounded fun n => (n + f n) * 8 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f n ^ 3 * g n`. -/
theorem pow_three_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 3 * g n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ (8 + f n) * (n * g n)`. -/
theorem const_add_mul_id_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (8 + f n) * (n * g n) :=
  ((IsPolyBounded.const 8).add hf).mul (IsPolyBounded.id.mul hg)

theorem comp_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f (n) :=
  hf.comp IsPolyBounded.id

theorem const_mul_mul_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 2 * f n * g n * n :=
  (((IsPolyBounded.const 2).mul hf).mul hg).mul IsPolyBounded.id

/-- Closure of polynomially bounded functions under `n ↦ f n + n`. -/
theorem add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f n + n :=
  hf.add IsPolyBounded.id

theorem pow_five_add_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 5 + g n + 5 :=
  ((hf.pow 5).add hg).add (IsPolyBounded.const 5)

theorem id_add_id_add_id_add (hf : IsPolyBounded f) :
    IsPolyBounded fun n => n + n + (n + f n) := by
  poly_bound

theorem const_mul_add_comp_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 4 * f n + g (n) :=
  ((IsPolyBounded.const 4).mul hf).add (hg.comp IsPolyBounded.id)

theorem id_mul_add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => n * f n + n :=
  (IsPolyBounded.id.mul hf).add IsPolyBounded.id

theorem add_const_mul_id_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n + 8 * n + g (h n) :=
  (hf.add (IsPolyBounded.id.const_mul 8)).add (hg.comp hh)

theorem add_mul_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n + g n) * (2 + h n) :=
  (hf.add hg).mul ((IsPolyBounded.const 2).add hh)

theorem comp_pow_three_add_const_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n) ^ 3 + (6 + n) :=
  ((hf.comp hg).pow 3).add ((IsPolyBounded.const 6).add IsPolyBounded.id)

theorem mul_const_mul_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n * 8 * g n) ^ 2 := by
  poly_bound

theorem mul_add_mul_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * ((g n + h n) * (3 * h n)) :=
  hf.mul ((hg.add hh).mul (hh.const_mul 3))

/-- Closure of polynomially bounded functions under `n ↦ (2 * f n * g n) ^ 4`. -/
theorem const_mul_mul_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (2 * f n * g n) ^ 4 :=
  ((hf.const_mul 2).mul hg).pow 4

theorem mul_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * g n + h (h n) :=
  (hf.mul hg).add (hh.comp hh)

theorem mul_id_pow_five (hf : IsPolyBounded f) : IsPolyBounded fun n => (f n * n) ^ 5 :=
  (hf.mul IsPolyBounded.id).pow 5

theorem const_add_add_mul_id_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (2 + (f n + g n)) * (n * h n) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (n * n)`. -/
theorem comp_id_mul_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f (n * n) :=
  hf.comp (IsPolyBounded.id.mul IsPolyBounded.id)

theorem mul_const_mul_id_pow_three (hf : IsPolyBounded f) :
    IsPolyBounded fun n => f n * 8 * n ^ 3 := by
  poly_bound

theorem const_mul_id_mul (hf : IsPolyBounded f) : IsPolyBounded fun n => 8 * n * f n :=
  (IsPolyBounded.id.const_mul 8).mul hf

theorem comp_add_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f ((g n + h n) ^ 4) :=
  hf.comp ((hg.add hh).pow 4)

theorem add_mul_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n + g n) * h n ^ 4 := by
  poly_bound

theorem const_mul_mul_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 7 * (f n * g n) ^ 2 :=
  ((hf.mul hg).pow 2).const_mul 7

theorem comp_id_pow_four (hf : IsPolyBounded f) : IsPolyBounded fun n => f (n ^ 4) :=
  hf.comp (IsPolyBounded.id.pow 4)

theorem pow_four_add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f n ^ 4 + n := by
  poly_bound

theorem mul_id_add_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * n + g n + n :=
  ((hf.mul IsPolyBounded.id).add hg).add IsPolyBounded.id

/-- Closure of polynomially bounded functions under `n ↦ (f n + g n) * n`. -/
theorem add_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n + g n) * n :=
  (hf.add hg).mul IsPolyBounded.id

theorem pow_three_add_id_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n ^ 3 + n) ^ 5 := by
  poly_bound

theorem pow_five_pow_four (hf : IsPolyBounded f) : IsPolyBounded fun n => (f n ^ 5) ^ 4 := by
  poly_bound

theorem const_mul_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => 6 * f n * (g n * h n) :=
  (hf.const_mul 6).mul (hg.mul hh)

theorem mul_id_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * n + g n :=
  (hf.mul IsPolyBounded.id).add hg

/-- Closure of polynomially bounded functions under `n ↦ 9 * f n * (9 * n)`. -/
theorem const_mul_mul_const_mul_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 9 * f n * (9 * n) :=
  (hf.const_mul 9).mul (IsPolyBounded.id.const_mul 9)

theorem id_mul_mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => n * f n * (g n + h n) := by
  poly_bound

theorem mul_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * g n * n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f n * g n + h n ^ 4`. -/
theorem mul_add_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * g n + h n ^ 4 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (g (h n)) * h n ^ 2`. -/
theorem comp_comp_mul_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g (h n)) * h n ^ 2 :=
  (hf.comp (hg.comp hh)).mul (hh.pow 2)

theorem id_mul_mul_id (hf : IsPolyBounded f) : IsPolyBounded fun n => n * f n * n := by
  poly_bound

theorem comp_id_mul_id_add_id_pow_three (hf : IsPolyBounded f) :
    IsPolyBounded fun n => f (n * n + n ^ 3) :=
  hf.comp ((IsPolyBounded.id.mul IsPolyBounded.id).add (IsPolyBounded.id.pow 3))

/-- Closure of polynomially bounded functions under `n ↦ 7 * ((f n + g n) * n)`. -/
theorem const_mul_add_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 7 * ((f n + g n) * n) := by
  poly_bound

theorem const_mul_id_mul_mul_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 5 * n * (f n * g n) + n := by
  poly_bound

theorem comp_const_add_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (8 + g n) ^ 3 :=
  (hf.comp ((IsPolyBounded.const 8).add hg)).pow 3

theorem const_mul_const_mul_add_comp_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 7 * (4 * f n + g (n)) :=
  ((hf.const_mul 4).add (hg.comp IsPolyBounded.id)).const_mul 7

theorem const_mul_mul_id (hf : IsPolyBounded f) : IsPolyBounded fun n => 9 * (f n * n) :=
  (hf.mul IsPolyBounded.id).const_mul 9

theorem comp_comp_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g (n)) :=
  hf.comp (hg.comp IsPolyBounded.id)

/-- Closure of polynomially bounded functions under `n ↦ f (2 * n + g n ^ 2)`. -/
theorem comp_const_mul_id_add_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (2 * n + g n ^ 2) :=
  hf.comp ((IsPolyBounded.id.const_mul 2).add (hg.pow 2))

theorem mul_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n * g n) ^ 4 :=
  (hf.mul hg).pow 4

theorem id_add_mul_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (n + f n) * g n ^ 3 :=
  (IsPolyBounded.id.add hf).mul (hg.pow 3)

/-- Closure of polynomially bounded functions under `n ↦ f (g n) * (h n * h n)`. -/
theorem comp_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) * (h n * h n) :=
  (hf.comp hg).mul (hh.mul hh)

theorem const_mul_add_id_add_id_pow_four (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 5 * f n + n + n ^ 4 := by
  poly_bound

theorem add_id_mul_mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n + n) * g n * (h n + f n) :=
  ((hf.add IsPolyBounded.id).mul hg).mul (hh.add hf)

theorem mul_mul_id_pow_two (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * g n * n ^ 2 := by
  poly_bound

theorem const_mul_const_mul_mul_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 7 * (5 * f n) * n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f n * g n * h n * (5 * g n)`. -/
theorem mul_mul_mul_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * g n * h n * (5 * g n) :=
  ((hf.mul hg).mul hh).mul (hg.const_mul 5)

theorem add_id_add_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n + n + (g n + n) :=
  (hf.add IsPolyBounded.id).add (hg.add IsPolyBounded.id)

theorem const_mul_comp_id_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 7 * f (n * g n) :=
  (hf.comp (IsPolyBounded.id.mul hg)).const_mul 7

theorem const_mul_add_id_mul_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 9 * ((f n + n) * n) := by
  poly_bound

theorem pow_five_pow_four_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f n ^ 5) ^ 4 + g n :=
  ((hf.pow 5).pow 4).add hg

theorem const_mul_id_mul_mul_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 2 * (n * f n * g n ^ 4) :=
  ((IsPolyBounded.id.mul hf).mul (hg.pow 4)).const_mul 2

/-- Closure of polynomially bounded functions under `n ↦ f (g n) + (h n + 8)`. -/
theorem comp_add_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) + (h n + 8) :=
  (hf.comp hg).add (hh.add (IsPolyBounded.const 8))

theorem comp_pow_three_mul_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n ^ 3 * h n ^ 5) :=
  hf.comp ((hg.pow 3).mul (hh.pow 5))

/-- Closure of polynomially bounded functions under `n ↦ (f n * 2) ^ 4`. -/
theorem mul_const_pow_four (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n * 2) ^ 4 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ (n + f n) * (n + g n)`. -/
theorem id_add_mul_id_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (n + f n) * (n + g n) :=
  (IsPolyBounded.id.add hf).mul (IsPolyBounded.id.add hg)

theorem const_mul_pow_five_add_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (8 * f n) ^ 5 + 8 * g n := by
  poly_bound

theorem id_add_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (n + f n) * g n := by
  poly_bound

theorem add_add_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n + g n + 8) * h n := by
  poly_bound

theorem pow_three_mul_id_mul_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => f n ^ 3 * (n * 7) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ (8 * f n) ^ 5 * g (h n) ^ 3`. -/
theorem const_mul_pow_five_mul_comp_pow_three (hf : IsPolyBounded f)
    (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (8 * f n) ^ 5 * g (h n) ^ 3 :=
  (((IsPolyBounded.const 8).mul hf).pow 5).mul ((hg.comp hh).pow 3)

theorem id_add_add_const_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (n + f n + 3) ^ 5 :=
  ((IsPolyBounded.id.add hf).add (IsPolyBounded.const 3)).pow 5

theorem comp_add_const_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n + 5 + h (h n)) :=
  hf.comp ((hg.add (IsPolyBounded.const 5)).add (hh.comp hh))

/-- Closure of polynomially bounded functions under `n ↦ f n * n * g n ^ 3 + h n ^ 4`. -/
theorem mul_id_mul_pow_three_add_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * n * g n ^ 3 + h n ^ 4 := by
  poly_bound

theorem comp_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n) ^ 4 :=
  (hf.comp hg).pow 4

theorem const_add_add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => 3 + f n + n :=
  ((IsPolyBounded.const 3).add hf).add IsPolyBounded.id

theorem pow_two (hf : IsPolyBounded f) : IsPolyBounded fun n => f n ^ 2 :=
  hf.pow 2

theorem add_id_pow_four (hf : IsPolyBounded f) : IsPolyBounded fun n => (f n + n) ^ 4 :=
  (hf.add IsPolyBounded.id).pow 4

theorem const_mul_comp_id_add_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => 9 * f (n) + g n * h n :=
  ((hf.comp IsPolyBounded.id).const_mul 9).add (hg.mul hh)

theorem add_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n + g n) * h n := by
  poly_bound

theorem id_mul_const_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => n * 4 * f n * g n := by
  poly_bound

theorem comp_pow_two_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (f (g n) ^ 2) ^ 4 :=
  ((hf.comp hg).pow 2).pow 4

theorem comp_id_pow_two (hf : IsPolyBounded f) : IsPolyBounded fun n => f (n ^ 2) :=
  hf.comp (IsPolyBounded.id.pow 2)

/-- Closure of polynomially bounded functions under `n ↦ (n ^ 3 + f n) ^ 5`. -/
theorem id_pow_three_add_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (n ^ 3 + f n) ^ 5 :=
  ((IsPolyBounded.id.pow 3).add hf).pow 5

/-- Closure of polynomially bounded functions under `n ↦ f n ^ 3 + g n * n`. -/
theorem pow_three_add_mul_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 3 + g n * n := by
  poly_bound

theorem id_pow_five_mul (hf : IsPolyBounded f) : IsPolyBounded fun n => n ^ 5 * f n := by
  poly_bound

theorem id_mul_add_pow_four (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => n * f n + g n ^ 4 :=
  (IsPolyBounded.id.mul hf).add (hg.pow 4)

theorem const_mul_pow_four (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (3 * f n) ^ 4 := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ (5 * f n) ^ 4 * (g n * h n)`. -/
theorem const_mul_pow_four_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (5 * f n) ^ 4 * (g n * h n) :=
  ((hf.const_mul 5).pow 4).mul (hg.mul hh)

/-- Closure of polynomially bounded functions under `n ↦ 3 * f (3 * g n)`. -/
theorem const_mul_comp_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 3 * f (3 * g n) :=
  (hf.comp (hg.const_mul 3)).const_mul 3

theorem comp_id_add_comp_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (n) + g (h n + 3) :=
  (hf.comp IsPolyBounded.id).add (hg.comp (hh.add (IsPolyBounded.const 3)))

/-- Closure of polynomially bounded functions under `n ↦ f n + n * n + g (h n)`. -/
theorem add_id_mul_id_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n + n * n + g (h n) :=
  (hf.add (IsPolyBounded.id.mul IsPolyBounded.id)).add (hg.comp hh)

theorem mul_const_add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * 4 + (g n + h n) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ 9 * f n * g n + (h n + f n)`. -/
theorem const_mul_mul_add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => 9 * f n * g n + (h n + f n) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ 2 * f n + g n * h n + h n`. -/
theorem const_mul_add_mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => 2 * f n + g n * h n + h n := by
  poly_bound

theorem mul_const_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * (9 * (g n * h n)) :=
  hf.mul ((hg.mul hh).const_mul 9)

theorem const_mul_add_id_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 3 * ((f n + n) * g n) :=
  ((hf.add IsPolyBounded.id).mul hg).const_mul 3

/-- Closure of polynomially bounded functions under `n ↦ f (g n) + h (n) + g n`. -/
theorem comp_add_comp_id_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) + h (n) + g n :=
  ((hf.comp hg).add (hh.comp IsPolyBounded.id)).add hg

theorem add_const_add_const_add_id_mul_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => f n + 6 + 7 + n * n := by
  poly_bound

theorem add_id_mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n + n) * (g n + h n) :=
  (hf.add IsPolyBounded.id).mul (hg.add hh)

theorem mul_const_mul_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * 4 * (g n + 9) := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ 8 + n + n + f n`. -/
theorem const_add_id_add_id_add (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 8 + n + n + f n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (n) * (5 * g n)`. -/
theorem comp_id_mul_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (n) * (5 * g n) :=
  (hf.comp IsPolyBounded.id).mul ((IsPolyBounded.const 5).mul hg)

theorem mul_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * (g n + n) := by
  poly_bound

theorem pow_two_mul_pow_four_add_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n ^ 2 * g n ^ 4 + (h n + n) :=
  ((hf.pow 2).mul (hg.pow 4)).add (hh.add IsPolyBounded.id)

theorem add_const_add_id (hf : IsPolyBounded f) : IsPolyBounded fun n => f n + 2 + n := by
  poly_bound

theorem pow_five_mul_mul_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n ^ 5 * g n * (h n + h n) :=
  ((hf.pow 5).mul hg).mul (hh.add hh)

theorem const_add_pow_two (hf : IsPolyBounded f) : IsPolyBounded fun n => (6 + f n) ^ 2 :=
  ((IsPolyBounded.const 6).add hf).pow 2

theorem id_add_pow_three (hf : IsPolyBounded f) : IsPolyBounded fun n => (n + f n) ^ 3 := by
  poly_bound

theorem pow_three_pow_two_pow_two (hf : IsPolyBounded f) :
    IsPolyBounded fun n => ((f n ^ 3) ^ 2) ^ 2 :=
  ((hf.pow 3).pow 2).pow 2

theorem comp_comp_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g (9 * h n)) :=
  hf.comp (hg.comp (hh.const_mul 9))

/-- Closure of polynomially bounded functions under `n ↦ f (g n) + (h n + n) + n`. -/
theorem comp_add_add_id_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) + (h n + n) + n :=
  ((hf.comp hg).add (hh.add IsPolyBounded.id)).add IsPolyBounded.id

/-- Closure of polynomially bounded functions under `n ↦ (f n + g n) ^ 4 * h n`. -/
theorem add_pow_four_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n + g n) ^ 4 * h n :=
  ((hf.add hg).pow 4).mul hh

/-- Closure of polynomially bounded functions under `n ↦ (f n * 3 + g n * h n) * h n`. -/
theorem mul_const_add_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n * 3 + g n * h n) * h n := by
  poly_bound

theorem const_add_mul_id_mul_id (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (2 + f n) * (n * n) :=
  ((IsPolyBounded.const 2).add hf).mul (IsPolyBounded.id.mul IsPolyBounded.id)

theorem add_add_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n + g n + (5 + h n) :=
  (hf.add hg).add ((IsPolyBounded.const 5).add hh)

/-- Closure of polynomially bounded functions under `n ↦ f n * g n + h n ^ 5`. -/
theorem mul_add_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * g n + h n ^ 5 := by
  poly_bound

theorem mul_add_mul_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n * g n + h n * h n) ^ 3 :=
  ((hf.mul hg).add (hh.mul hh)).pow 3

/-- Closure of polynomially bounded functions under `n ↦ f (g n) * h (f n)`. -/
theorem comp_mul_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (g n) * h (f n) :=
  (hf.comp hg).mul (hh.comp hf)

theorem const_add_add_id_add_add_id (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 7 + f n + (n + g n) + n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f (g n) * (n + 3)`. -/
theorem comp_mul_id_add_const (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f (g n) * (n + 3) :=
  (hf.comp hg).mul (IsPolyBounded.id.add (IsPolyBounded.const 3))

theorem const_mul_comp_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => 4 * f (g n * h n) :=
  (hf.comp (hg.mul hh)).const_mul 4

theorem const_mul_add_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => 4 * (f n + 9) :=
  (hf.add (IsPolyBounded.const 9)).const_mul 4

theorem mul_add_comp_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n * g n + h (f n)) ^ 5 :=
  ((hf.mul hg).add (hh.comp hf)).pow 5

theorem id_add_const_add_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => n + 5 + f (g n) :=
  (IsPolyBounded.id.add (IsPolyBounded.const 5)).add (hf.comp hg)

theorem add_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n + 7 + g n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f ((g n + h n) * (5 + g n))`. -/
theorem comp_add_mul_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f ((g n + h n) * (5 + g n)) :=
  hf.comp ((hg.add hh).mul ((IsPolyBounded.const 5).add hg))

theorem pow_two_add_pow_three (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n ^ 2 + g n ^ 3 :=
  (hf.pow 2).add (hg.pow 3)

/-- Closure of polynomially bounded functions under `n ↦ n * f n * 9`. -/
theorem id_mul_mul_const (hf : IsPolyBounded f) : IsPolyBounded fun n => n * f n * 9 := by
  poly_bound

theorem comp_const_mul_comp (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f (7 * g (h n)) :=
  hf.comp ((hg.comp hh).const_mul 7)

theorem const_mul_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (8 * f n) ^ 5 :=
  (hf.const_mul 8).pow 5

theorem mul_add_const_add (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => f n * g n + 3 + h n :=
  ((hf.mul hg).add (IsPolyBounded.const 3)).add hh

theorem mul_const_mul_id_pow_five (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (f n * 2 * n) ^ 5 :=
  ((hf.mul (IsPolyBounded.const 2)).mul IsPolyBounded.id).pow 5

theorem add_const_mul_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => (f n + 3) * (g n * h n) :=
  (hf.add (IsPolyBounded.const 3)).mul (hg.mul hh)

theorem const_mul_comp_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => 9 * f (g n) ^ 5 :=
  ((hf.comp hg).pow 5).const_mul 9

theorem const_mul_add_id_add_add_const_mul (hf : IsPolyBounded f) (hg : IsPolyBounded g)
    (hh : IsPolyBounded h) :
    IsPolyBounded fun n => 6 * f n + (n + g n) + 8 * h n := by
  poly_bound

/-- Closure of polynomially bounded functions under `n ↦ f ((g n + 5) * n ^ 5)`. -/
theorem comp_add_const_mul_id_pow_five (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f ((g n + 5) * n ^ 5) :=
  hf.comp ((hg.add (IsPolyBounded.const 5)).mul (IsPolyBounded.id.pow 5))

theorem id_mul_const_mul_add_const (hf : IsPolyBounded f) :
    IsPolyBounded fun n => n * 6 * (f n + 8) := by
  poly_bound

theorem mul_id_pow_four (hf : IsPolyBounded f) : IsPolyBounded fun n => (f n * n) ^ 4 := by
  poly_bound

theorem id_pow_five_pow_two_add_add (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => (n ^ 5) ^ 2 + (f n + g n) := by
  poly_bound

theorem const_add_id_mul_const_add (hf : IsPolyBounded f) :
    IsPolyBounded fun n => (3 + n) * (3 + f n) :=
  ((IsPolyBounded.const 3).add IsPolyBounded.id).mul ((IsPolyBounded.const 3).add hf)

end IsPolyBounded

end Complexity
