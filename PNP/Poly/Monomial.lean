import PNP.Poly.Tactic

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

theorem succ_pow_one_le_succ_pow_three (n : ℕ) : (n + 1) ^ 1 ≤ (n + 1) ^ 3 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_one_le_succ_pow_six (n : ℕ) : (n + 1) ^ 1 ≤ (n + 1) ^ 6 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_two_le_succ_pow_seven (n : ℕ) : (n + 1) ^ 2 ≤ (n + 1) ^ 7 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_two_le_succ_pow_eight (n : ℕ) : (n + 1) ^ 2 ≤ (n + 1) ^ 8 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_three_le_succ_pow_four (n : ℕ) : (n + 1) ^ 3 ≤ (n + 1) ^ 4 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_three_le_succ_pow_five (n : ℕ) : (n + 1) ^ 3 ≤ (n + 1) ^ 5 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_three_le_succ_pow_seven (n : ℕ) : (n + 1) ^ 3 ≤ (n + 1) ^ 7 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_three_le_succ_pow_eight (n : ℕ) : (n + 1) ^ 3 ≤ (n + 1) ^ 8 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_four_le_succ_pow_seven (n : ℕ) : (n + 1) ^ 4 ≤ (n + 1) ^ 7 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_four_le_succ_pow_eight (n : ℕ) : (n + 1) ^ 4 ≤ (n + 1) ^ 8 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_five_le_succ_pow_eight (n : ℕ) : (n + 1) ^ 5 ≤ (n + 1) ^ 8 :=
  succ_pow_le_succ_pow n (by decide)

theorem succ_pow_six_le_succ_pow_eight (n : ℕ) : (n + 1) ^ 6 ≤ (n + 1) ^ 8 :=
  succ_pow_le_succ_pow n (by decide)

theorem pow_two_le_succ_pow_two (n : ℕ) : n ^ 2 ≤ (n + 1) ^ 2 :=
  pow_le_succ_pow n (by decide)

theorem pow_three_le_succ_pow_five (n : ℕ) : n ^ 3 ≤ (n + 1) ^ 5 :=
  pow_le_succ_pow n (by decide)

theorem pow_four_le_succ_pow_five (n : ℕ) : n ^ 4 ≤ (n + 1) ^ 5 :=
  pow_le_succ_pow n (by decide)

theorem pow_five_le_succ_pow_seven (n : ℕ) : n ^ 5 ≤ (n + 1) ^ 7 :=
  pow_le_succ_pow n (by decide)

theorem pow_six_le_succ_pow_six (n : ℕ) : n ^ 6 ≤ (n + 1) ^ 6 :=
  pow_le_succ_pow n (by decide)

theorem pow_seven_le_succ_pow_nine (n : ℕ) : n ^ 7 ≤ (n + 1) ^ 9 :=
  pow_le_succ_pow n (by decide)

/-- An explicit monomial bound for `9 * n ^ 4 + 7 * n ^ 2 + 5 * n`. -/
theorem quartic_9_0_7_5_0_le (n : ℕ) : 9 * n ^ 4 + 7 * n ^ 2 + 5 * n ≤ 21 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quartic_9_0_7_5_0 :
    IsPolyBounded fun n => 9 * n ^ 4 + 7 * n ^ 2 + 5 * n :=
  ⟨21, 4, quartic_9_0_7_5_0_le⟩

/-- An explicit monomial bound for `2 * n ^ 3 + 8 * n ^ 2 + 16`. -/
theorem cubic_2_8_0_16_le (n : ℕ) : 2 * n ^ 3 + 8 * n ^ 2 + 16 ≤ 26 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_2_8_0_16 :
    IsPolyBounded fun n => 2 * n ^ 3 + 8 * n ^ 2 + 16 := by
  poly_bound

/-- An explicit monomial bound for `7 * n ^ 2 + 2 * n + 1`. -/
theorem quadratic_7_2_1_le (n : ℕ) : 7 * n ^ 2 + 2 * n + 1 ≤ 10 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_7_2_1 : IsPolyBounded fun n => 7 * n ^ 2 + 2 * n + 1 := by
  poly_bound

/-- An explicit monomial bound for `3 * n ^ 2 + 2 * n + 3`. -/
theorem quadratic_3_2_3_le (n : ℕ) : 3 * n ^ 2 + 2 * n + 3 ≤ 8 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_3_2_3 : IsPolyBounded fun n => 3 * n ^ 2 + 2 * n + 3 :=
  ⟨8, 2, quadratic_3_2_3_le⟩

/-- An explicit monomial bound for `7 * n + 9`. -/
theorem linear_7_9_le (n : ℕ) : 7 * n + 9 ≤ 16 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_7_9 : IsPolyBounded fun n => 7 * n + 9 :=
  ⟨16, 1, linear_7_9_le⟩

/-- An explicit monomial bound for `4 * n ^ 3 + 6 * n ^ 2 + 7 * n + 1`. -/
theorem cubic_4_6_7_1_le (n : ℕ) : 4 * n ^ 3 + 6 * n ^ 2 + 7 * n + 1 ≤ 18 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_4_6_7_1 :
    IsPolyBounded fun n => 4 * n ^ 3 + 6 * n ^ 2 + 7 * n + 1 := by
  poly_bound

/-- An explicit monomial bound for `9 * n ^ 4 + 5 * n ^ 3 + 1 * n ^ 2 + 5 * n + 8`. -/
theorem quartic_9_5_1_5_8_le (n : ℕ) :
    9 * n ^ 4 + 5 * n ^ 3 + 1 * n ^ 2 + 5 * n + 8 ≤ 28 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_9_5_1_5_8 :
    IsPolyBounded fun n => 9 * n ^ 4 + 5 * n ^ 3 + 1 * n ^ 2 + 5 * n + 8 :=
  ⟨28, 4, quartic_9_5_1_5_8_le⟩

/-- An explicit monomial bound for `1 * n ^ 5 + 8 * n ^ 4 + 7 * n ^ 3 + 3 * n ^ 2 + 3 * n + 7`. -/
theorem quintic_1_8_7_3_3_7_le (n : ℕ) :
    1 * n ^ 5 + 8 * n ^ 4 + 7 * n ^ 3 + 3 * n ^ 2 + 3 * n + 7 ≤ 29 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h6 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_1_8_7_3_3_7 :
    IsPolyBounded fun n => 1 * n ^ 5 + 8 * n ^ 4 + 7 * n ^ 3 + 3 * n ^ 2 + 3 * n + 7 :=
  ⟨29, 5, quintic_1_8_7_3_3_7_le⟩

/-- An explicit monomial bound for `7 * n ^ 2 + 12`. -/
theorem quadratic_7_0_12_le (n : ℕ) : 7 * n ^ 2 + 12 ≤ 19 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_7_0_12 : IsPolyBounded fun n => 7 * n ^ 2 + 12 :=
  ⟨19, 2, quadratic_7_0_12_le⟩

/-- An explicit monomial bound for `3 * n ^ 4 + 7 * n ^ 2 + 5 * n`. -/
theorem quartic_3_0_7_5_0_le (n : ℕ) : 3 * n ^ 4 + 7 * n ^ 2 + 5 * n ≤ 15 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quartic_3_0_7_5_0 :
    IsPolyBounded fun n => 3 * n ^ 4 + 7 * n ^ 2 + 5 * n :=
  ⟨15, 4, quartic_3_0_7_5_0_le⟩

/-- An explicit monomial bound for `1 * n ^ 4 + 16 * n ^ 2 + 9 * n + 12`. -/
theorem quartic_1_0_16_9_12_le (n : ℕ) :
    1 * n ^ 4 + 16 * n ^ 2 + 9 * n + 12 ≤ 38 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_1_0_16_9_12 :
    IsPolyBounded fun n => 1 * n ^ 4 + 16 * n ^ 2 + 9 * n + 12 :=
  ⟨38, 4, quartic_1_0_16_9_12_le⟩

/-- An explicit monomial bound for `8 * n ^ 3 + 5 * n ^ 2 + 2 * n + 5`. -/
theorem cubic_8_5_2_5_le (n : ℕ) : 8 * n ^ 3 + 5 * n ^ 2 + 2 * n + 5 ≤ 20 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_8_5_2_5 :
    IsPolyBounded fun n => 8 * n ^ 3 + 5 * n ^ 2 + 2 * n + 5 := by
  poly_bound

/-- An explicit monomial bound for `2 * n ^ 2 + 5 * n + 8`. -/
theorem quadratic_2_5_8_le (n : ℕ) : 2 * n ^ 2 + 5 * n + 8 ≤ 15 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_2_5_8 : IsPolyBounded fun n => 2 * n ^ 2 + 5 * n + 8 := by
  poly_bound

/-- An explicit monomial bound for `7 * n ^ 2 + 12 * n + 2`. -/
theorem quadratic_7_12_2_le (n : ℕ) : 7 * n ^ 2 + 12 * n + 2 ≤ 21 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_7_12_2 : IsPolyBounded fun n => 7 * n ^ 2 + 12 * n + 2 :=
  ⟨21, 2, quadratic_7_12_2_le⟩

/-- An explicit monomial bound for `4 * n ^ 5 + 5 * n ^ 2 + 7 * n + 6`. -/
theorem quintic_4_0_0_5_7_6_le (n : ℕ) :
    4 * n ^ 5 + 5 * n ^ 2 + 7 * n + 6 ≤ 22 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_4_0_0_5_7_6 :
    IsPolyBounded fun n => 4 * n ^ 5 + 5 * n ^ 2 + 7 * n + 6 :=
  ⟨22, 5, quintic_4_0_0_5_7_6_le⟩

/-- An explicit monomial bound for `7 * n + 4`. -/
theorem linear_7_4_le (n : ℕ) : 7 * n + 4 ≤ 11 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_7_4 : IsPolyBounded fun n => 7 * n + 4 := by
  poly_bound

/-- An explicit monomial bound for `6 * n ^ 3 + 6 * n ^ 2 + 7`. -/
theorem cubic_6_6_0_7_le (n : ℕ) : 6 * n ^ 3 + 6 * n ^ 2 + 7 ≤ 19 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_6_6_0_7 : IsPolyBounded fun n => 6 * n ^ 3 + 6 * n ^ 2 + 7 := by
  poly_bound

/-- An explicit monomial bound for `8 * n ^ 4 + 4 * n ^ 3 + 7 * n ^ 2 + 7 * n + 8`. -/
theorem quartic_8_4_7_7_8_le (n : ℕ) :
    8 * n ^ 4 + 4 * n ^ 3 + 7 * n ^ 2 + 7 * n + 8 ≤ 34 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_8_4_7_7_8 :
    IsPolyBounded fun n => 8 * n ^ 4 + 4 * n ^ 3 + 7 * n ^ 2 + 7 * n + 8 := by
  poly_bound

/-- An explicit monomial bound for `6 * n ^ 2 + 8 * n + 4`. -/
theorem quadratic_6_8_4_le (n : ℕ) : 6 * n ^ 2 + 8 * n + 4 ≤ 18 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_6_8_4 : IsPolyBounded fun n => 6 * n ^ 2 + 8 * n + 4 :=
  ⟨18, 2, quadratic_6_8_4_le⟩

/-- An explicit monomial bound for `2 * n ^ 2 + 12 * n`. -/
theorem quadratic_2_12_0_le (n : ℕ) : 2 * n ^ 2 + 12 * n ≤ 14 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quadratic_2_12_0 : IsPolyBounded fun n => 2 * n ^ 2 + 12 * n :=
  ⟨14, 2, quadratic_2_12_0_le⟩

/-- An explicit monomial bound for `2 * n ^ 4 + 5 * n ^ 2 + 7 * n + 1`. -/
theorem quartic_2_0_5_7_1_le (n : ℕ) :
    2 * n ^ 4 + 5 * n ^ 2 + 7 * n + 1 ≤ 15 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_2_0_5_7_1 :
    IsPolyBounded fun n => 2 * n ^ 4 + 5 * n ^ 2 + 7 * n + 1 := by
  poly_bound

/-- An explicit monomial bound for `4 * n ^ 3 + 8 * n ^ 2 + 1 * n + 7`. -/
theorem cubic_4_8_1_7_le (n : ℕ) : 4 * n ^ 3 + 8 * n ^ 2 + 1 * n + 7 ≤ 20 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_4_8_1_7 :
    IsPolyBounded fun n => 4 * n ^ 3 + 8 * n ^ 2 + 1 * n + 7 := by
  poly_bound

/-- An explicit monomial bound for `4 * n ^ 3 + 6 * n ^ 2 + 7 * n`. -/
theorem cubic_4_6_7_0_le (n : ℕ) : 4 * n ^ 3 + 6 * n ^ 2 + 7 * n ≤ 17 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_cubic_4_6_7_0 :
    IsPolyBounded fun n => 4 * n ^ 3 + 6 * n ^ 2 + 7 * n := by
  poly_bound

/-- An explicit monomial bound for `6 * n + 1`. -/
theorem linear_6_1_le (n : ℕ) : 6 * n + 1 ≤ 7 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_6_1 : IsPolyBounded fun n => 6 * n + 1 := by
  poly_bound

/-- An explicit monomial bound for `1 * n ^ 3 + 9 * n ^ 2 + 12 * n + 3`. -/
theorem cubic_1_9_12_3_le (n : ℕ) :
    1 * n ^ 3 + 9 * n ^ 2 + 12 * n + 3 ≤ 25 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_1_9_12_3 :
    IsPolyBounded fun n => 1 * n ^ 3 + 9 * n ^ 2 + 12 * n + 3 :=
  ⟨25, 3, cubic_1_9_12_3_le⟩

/-- An explicit monomial bound for `2 * n ^ 3 + 16 * n ^ 2 + 1 * n`. -/
theorem cubic_2_16_1_0_le (n : ℕ) : 2 * n ^ 3 + 16 * n ^ 2 + 1 * n ≤ 19 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_cubic_2_16_1_0 :
    IsPolyBounded fun n => 2 * n ^ 3 + 16 * n ^ 2 + 1 * n :=
  ⟨19, 3, cubic_2_16_1_0_le⟩

/-- An explicit monomial bound for `1 * n ^ 5 + 1 * n ^ 4 + 5 * n ^ 3 + 6 * n ^ 2 + 6 * n + 8`. -/
theorem quintic_1_1_5_6_6_8_le (n : ℕ) :
    1 * n ^ 5 + 1 * n ^ 4 + 5 * n ^ 3 + 6 * n ^ 2 + 6 * n + 8 ≤ 27 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h6 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_1_1_5_6_6_8 :
    IsPolyBounded fun n => 1 * n ^ 5 + 1 * n ^ 4 + 5 * n ^ 3 + 6 * n ^ 2 + 6 * n + 8 := by
  poly_bound

/-- An explicit monomial bound for `9 * n ^ 2 + 7 * n + 6`. -/
theorem quadratic_9_7_6_le (n : ℕ) : 9 * n ^ 2 + 7 * n + 6 ≤ 22 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_9_7_6 : IsPolyBounded fun n => 9 * n ^ 2 + 7 * n + 6 := by
  poly_bound

/-- An explicit monomial bound for `9 * n ^ 3 + 9 * n ^ 2 + 16 * n + 8`. -/
theorem cubic_9_9_16_8_le (n : ℕ) :
    9 * n ^ 3 + 9 * n ^ 2 + 16 * n + 8 ≤ 42 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_9_9_16_8 :
    IsPolyBounded fun n => 9 * n ^ 3 + 9 * n ^ 2 + 16 * n + 8 :=
  ⟨42, 3, cubic_9_9_16_8_le⟩

/-- An explicit monomial bound for `9 * n ^ 3 + 5 * n + 16`. -/
theorem cubic_9_0_5_16_le (n : ℕ) : 9 * n ^ 3 + 5 * n + 16 ≤ 30 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_9_0_5_16 : IsPolyBounded fun n => 9 * n ^ 3 + 5 * n + 16 := by
  poly_bound

/-- An explicit monomial bound for `3 * n ^ 2 + 8 * n`. -/
theorem quadratic_3_8_0_le (n : ℕ) : 3 * n ^ 2 + 8 * n ≤ 11 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quadratic_3_8_0 : IsPolyBounded fun n => 3 * n ^ 2 + 8 * n := by
  poly_bound

/-- An explicit monomial bound for `9 * n ^ 2 + 4 * n + 1`. -/
theorem quadratic_9_4_1_le (n : ℕ) : 9 * n ^ 2 + 4 * n + 1 ≤ 14 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_9_4_1 : IsPolyBounded fun n => 9 * n ^ 2 + 4 * n + 1 :=
  ⟨14, 2, quadratic_9_4_1_le⟩

/-- An explicit monomial bound for `5 * n ^ 4 + 5 * n ^ 3 + 5 * n ^ 2 + 6 * n + 7`. -/
theorem quartic_5_5_5_6_7_le (n : ℕ) :
    5 * n ^ 4 + 5 * n ^ 3 + 5 * n ^ 2 + 6 * n + 7 ≤ 28 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_5_5_5_6_7 :
    IsPolyBounded fun n => 5 * n ^ 4 + 5 * n ^ 3 + 5 * n ^ 2 + 6 * n + 7 := by
  poly_bound

/-- An explicit monomial bound for `3 * n ^ 4 + 1 * n ^ 3 + 8 * n ^ 2 + 7 * n + 2`. -/
theorem quartic_3_1_8_7_2_le (n : ℕ) :
    3 * n ^ 4 + 1 * n ^ 3 + 8 * n ^ 2 + 7 * n + 2 ≤ 21 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_3_1_8_7_2 :
    IsPolyBounded fun n => 3 * n ^ 4 + 1 * n ^ 3 + 8 * n ^ 2 + 7 * n + 2 :=
  ⟨21, 4, quartic_3_1_8_7_2_le⟩

/-- An explicit monomial bound for `7 * n + 16`. -/
theorem linear_7_16_le (n : ℕ) : 7 * n + 16 ≤ 23 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_7_16 : IsPolyBounded fun n => 7 * n + 16 := by
  poly_bound

/-- An explicit monomial bound for `6 * n ^ 5 + 1 * n ^ 4 + 4 * n ^ 3 + 4 * n ^ 2 + 1 * n + 4`. -/
theorem quintic_6_1_4_4_1_4_le (n : ℕ) :
    6 * n ^ 5 + 1 * n ^ 4 + 4 * n ^ 3 + 4 * n ^ 2 + 1 * n + 4 ≤ 20 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h6 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_6_1_4_4_1_4 :
    IsPolyBounded fun n => 6 * n ^ 5 + 1 * n ^ 4 + 4 * n ^ 3 + 4 * n ^ 2 + 1 * n + 4 := by
  poly_bound

/-- An explicit monomial bound for `5 * n ^ 3 + 12 * n ^ 2 + 5`. -/
theorem cubic_5_12_0_5_le (n : ℕ) : 5 * n ^ 3 + 12 * n ^ 2 + 5 ≤ 22 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_5_12_0_5 :
    IsPolyBounded fun n => 5 * n ^ 3 + 12 * n ^ 2 + 5 :=
  ⟨22, 3, cubic_5_12_0_5_le⟩

/-- An explicit monomial bound for `2 * n ^ 4 + 2 * n ^ 2 + 1`. -/
theorem quartic_2_0_2_0_1_le (n : ℕ) : 2 * n ^ 4 + 2 * n ^ 2 + 1 ≤ 5 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_2_0_2_0_1 :
    IsPolyBounded fun n => 2 * n ^ 4 + 2 * n ^ 2 + 1 :=
  ⟨5, 4, quartic_2_0_2_0_1_le⟩

/-- An explicit monomial bound for `3 * n + 1`. -/
theorem linear_3_1_le (n : ℕ) : 3 * n + 1 ≤ 4 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_3_1 : IsPolyBounded fun n => 3 * n + 1 := by
  poly_bound

/-- An explicit monomial bound for `1 * n ^ 2 + 12 * n + 6`. -/
theorem quadratic_1_12_6_le (n : ℕ) : 1 * n ^ 2 + 12 * n + 6 ≤ 19 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_1_12_6 : IsPolyBounded fun n => 1 * n ^ 2 + 12 * n + 6 :=
  ⟨19, 2, quadratic_1_12_6_le⟩

/-- An explicit monomial bound for `1 * n ^ 2 + 8 * n + 7`. -/
theorem quadratic_1_8_7_le (n : ℕ) : 1 * n ^ 2 + 8 * n + 7 ≤ 16 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_1_8_7 : IsPolyBounded fun n => 1 * n ^ 2 + 8 * n + 7 :=
  ⟨16, 2, quadratic_1_8_7_le⟩

/-- An explicit monomial bound for `1 * n ^ 2 + 3 * n + 2`. -/
theorem quadratic_1_3_2_le (n : ℕ) : 1 * n ^ 2 + 3 * n + 2 ≤ 6 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_1_3_2 : IsPolyBounded fun n => 1 * n ^ 2 + 3 * n + 2 := by
  poly_bound

/-- An explicit monomial bound for `1 * n ^ 2 + 4`. -/
theorem quadratic_1_0_4_le (n : ℕ) : 1 * n ^ 2 + 4 ≤ 5 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_1_0_4 : IsPolyBounded fun n => 1 * n ^ 2 + 4 :=
  ⟨5, 2, quadratic_1_0_4_le⟩

/-- An explicit monomial bound for `8 * n ^ 2 + 4 * n + 7`. -/
theorem quadratic_8_4_7_le (n : ℕ) : 8 * n ^ 2 + 4 * n + 7 ≤ 19 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_8_4_7 : IsPolyBounded fun n => 8 * n ^ 2 + 4 * n + 7 :=
  ⟨19, 2, quadratic_8_4_7_le⟩

/-- An explicit monomial bound for `4 * n ^ 3 + 16 * n ^ 2 + 4 * n + 16`. -/
theorem cubic_4_16_4_16_le (n : ℕ) :
    4 * n ^ 3 + 16 * n ^ 2 + 4 * n + 16 ≤ 40 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_4_16_4_16 :
    IsPolyBounded fun n => 4 * n ^ 3 + 16 * n ^ 2 + 4 * n + 16 :=
  ⟨40, 3, cubic_4_16_4_16_le⟩

/-- An explicit monomial bound for `9 * n + 1`. -/
theorem linear_9_1_le (n : ℕ) : 9 * n + 1 ≤ 10 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_9_1 : IsPolyBounded fun n => 9 * n + 1 := by
  poly_bound

/-- An explicit monomial bound for `1 * n ^ 2 + 4 * n + 8`. -/
theorem quadratic_1_4_8_le (n : ℕ) : 1 * n ^ 2 + 4 * n + 8 ≤ 13 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_1_4_8 : IsPolyBounded fun n => 1 * n ^ 2 + 4 * n + 8 :=
  ⟨13, 2, quadratic_1_4_8_le⟩

/-- An explicit monomial bound for `7 * n ^ 2 + 16 * n + 4`. -/
theorem quadratic_7_16_4_le (n : ℕ) : 7 * n ^ 2 + 16 * n + 4 ≤ 27 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_7_16_4 : IsPolyBounded fun n => 7 * n ^ 2 + 16 * n + 4 :=
  ⟨27, 2, quadratic_7_16_4_le⟩

/-- An explicit monomial bound for `6 * n ^ 2 + 5 * n + 7`. -/
theorem quadratic_6_5_7_le (n : ℕ) : 6 * n ^ 2 + 5 * n + 7 ≤ 18 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_6_5_7 : IsPolyBounded fun n => 6 * n ^ 2 + 5 * n + 7 :=
  ⟨18, 2, quadratic_6_5_7_le⟩

/-- An explicit monomial bound for `7 * n ^ 3 + 4 * n ^ 2 + 7 * n + 9`. -/
theorem cubic_7_4_7_9_le (n : ℕ) : 7 * n ^ 3 + 4 * n ^ 2 + 7 * n + 9 ≤ 27 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_7_4_7_9 :
    IsPolyBounded fun n => 7 * n ^ 3 + 4 * n ^ 2 + 7 * n + 9 := by
  poly_bound

/-- An explicit monomial bound for `3 * n ^ 4 + 16 * n ^ 3 + 7 * n ^ 2 + 5 * n`. -/
theorem quartic_3_16_7_5_0_le (n : ℕ) :
    3 * n ^ 4 + 16 * n ^ 3 + 7 * n ^ 2 + 5 * n ≤ 31 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quartic_3_16_7_5_0 :
    IsPolyBounded fun n => 3 * n ^ 4 + 16 * n ^ 3 + 7 * n ^ 2 + 5 * n :=
  ⟨31, 4, quartic_3_16_7_5_0_le⟩

/-- An explicit monomial bound for `3 * n ^ 3 + 2 * n ^ 2 + 5 * n`. -/
theorem cubic_3_2_5_0_le (n : ℕ) : 3 * n ^ 3 + 2 * n ^ 2 + 5 * n ≤ 10 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_cubic_3_2_5_0 :
    IsPolyBounded fun n => 3 * n ^ 3 + 2 * n ^ 2 + 5 * n :=
  ⟨10, 3, cubic_3_2_5_0_le⟩

/-- An explicit monomial bound for `5 * n ^ 3 + 6 * n ^ 2 + 7 * n + 5`. -/
theorem cubic_5_6_7_5_le (n : ℕ) : 5 * n ^ 3 + 6 * n ^ 2 + 7 * n + 5 ≤ 23 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_5_6_7_5 :
    IsPolyBounded fun n => 5 * n ^ 3 + 6 * n ^ 2 + 7 * n + 5 := by
  poly_bound

/-- An explicit monomial bound for `3 * n ^ 5 + 6 * n ^ 4 + 9 * n ^ 3 + 6 * n ^ 2 + 7 * n + 7`. -/
theorem quintic_3_6_9_6_7_7_le (n : ℕ) :
    3 * n ^ 5 + 6 * n ^ 4 + 9 * n ^ 3 + 6 * n ^ 2 + 7 * n + 7 ≤ 38 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h6 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_3_6_9_6_7_7 :
    IsPolyBounded fun n => 3 * n ^ 5 + 6 * n ^ 4 + 9 * n ^ 3 + 6 * n ^ 2 + 7 * n + 7 :=
  ⟨38, 5, quintic_3_6_9_6_7_7_le⟩

/-- An explicit monomial bound for `6 * n ^ 3 + 5 * n ^ 2 + 9 * n + 7`. -/
theorem cubic_6_5_9_7_le (n : ℕ) : 6 * n ^ 3 + 5 * n ^ 2 + 9 * n + 7 ≤ 27 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_6_5_9_7 :
    IsPolyBounded fun n => 6 * n ^ 3 + 5 * n ^ 2 + 9 * n + 7 :=
  ⟨27, 3, cubic_6_5_9_7_le⟩

/-- An explicit monomial bound for `4 * n ^ 3 + 8`. -/
theorem cubic_4_0_0_8_le (n : ℕ) : 4 * n ^ 3 + 8 ≤ 12 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_4_0_0_8 : IsPolyBounded fun n => 4 * n ^ 3 + 8 :=
  ⟨12, 3, cubic_4_0_0_8_le⟩

/-- An explicit monomial bound for `4 * n ^ 3 + 4 * n + 9`. -/
theorem cubic_4_0_4_9_le (n : ℕ) : 4 * n ^ 3 + 4 * n + 9 ≤ 17 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_4_0_4_9 : IsPolyBounded fun n => 4 * n ^ 3 + 4 * n + 9 :=
  ⟨17, 3, cubic_4_0_4_9_le⟩

/-- An explicit monomial bound for `9 * n ^ 5 + 3 * n ^ 4 + 6 * n ^ 3 + 16 * n ^ 2 + 16 * n + 2`. -/
theorem quintic_9_3_6_16_16_2_le (n : ℕ) :
    9 * n ^ 5 + 3 * n ^ 4 + 6 * n ^ 3 + 16 * n ^ 2 + 16 * n + 2 ≤ 52 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h6 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_9_3_6_16_16_2 :
    IsPolyBounded fun n => 9 * n ^ 5 + 3 * n ^ 4 + 6 * n ^ 3 + 16 * n ^ 2 + 16 * n + 2 :=
  ⟨52, 5, quintic_9_3_6_16_16_2_le⟩

/-- An explicit monomial bound for `2 * n ^ 4 + 5 * n ^ 2 + 7 * n + 12`. -/
theorem quartic_2_0_5_7_12_le (n : ℕ) :
    2 * n ^ 4 + 5 * n ^ 2 + 7 * n + 12 ≤ 26 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_2_0_5_7_12 :
    IsPolyBounded fun n => 2 * n ^ 4 + 5 * n ^ 2 + 7 * n + 12 := by
  poly_bound

/-- An explicit monomial bound for `4 * n ^ 3 + 1 * n ^ 2 + 7`. -/
theorem cubic_4_1_0_7_le (n : ℕ) : 4 * n ^ 3 + 1 * n ^ 2 + 7 ≤ 12 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_4_1_0_7 : IsPolyBounded fun n => 4 * n ^ 3 + 1 * n ^ 2 + 7 :=
  ⟨12, 3, cubic_4_1_0_7_le⟩

/-- An explicit monomial bound for `3 * n ^ 4 + 2 * n ^ 3 + 2 * n ^ 2 + 12 * n + 5`. -/
theorem quartic_3_2_2_12_5_le (n : ℕ) :
    3 * n ^ 4 + 2 * n ^ 3 + 2 * n ^ 2 + 12 * n + 5 ≤ 24 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_3_2_2_12_5 :
    IsPolyBounded fun n => 3 * n ^ 4 + 2 * n ^ 3 + 2 * n ^ 2 + 12 * n + 5 := by
  poly_bound

/-- An explicit monomial bound for `4 * n ^ 3 + 12 * n ^ 2 + 2`. -/
theorem cubic_4_12_0_2_le (n : ℕ) : 4 * n ^ 3 + 12 * n ^ 2 + 2 ≤ 18 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_4_12_0_2 :
    IsPolyBounded fun n => 4 * n ^ 3 + 12 * n ^ 2 + 2 := by
  poly_bound

/-- An explicit monomial bound for `8 * n ^ 5 + 9 * n ^ 4 + 8 * n ^ 3 + 5 * n ^ 2 + 1 * n + 12`. -/
theorem quintic_8_9_8_5_1_12_le (n : ℕ) :
    8 * n ^ 5 + 9 * n ^ 4 + 8 * n ^ 3 + 5 * n ^ 2 + 1 * n + 12 ≤ 43 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h6 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_8_9_8_5_1_12 :
    IsPolyBounded fun n => 8 * n ^ 5 + 9 * n ^ 4 + 8 * n ^ 3 + 5 * n ^ 2 + 1 * n + 12 :=
  ⟨43, 5, quintic_8_9_8_5_1_12_le⟩

/-- An explicit monomial bound for `9 * n ^ 2 + 1 * n + 3`. -/
theorem quadratic_9_1_3_le (n : ℕ) : 9 * n ^ 2 + 1 * n + 3 ≤ 13 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_9_1_3 : IsPolyBounded fun n => 9 * n ^ 2 + 1 * n + 3 :=
  ⟨13, 2, quadratic_9_1_3_le⟩

/-- An explicit monomial bound for `4 * n ^ 3 + 16 * n ^ 2 + 1 * n + 7`. -/
theorem cubic_4_16_1_7_le (n : ℕ) :
    4 * n ^ 3 + 16 * n ^ 2 + 1 * n + 7 ≤ 28 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_4_16_1_7 :
    IsPolyBounded fun n => 4 * n ^ 3 + 16 * n ^ 2 + 1 * n + 7 := by
  poly_bound

/-- An explicit monomial bound for `5 * n ^ 3 + 1 * n ^ 2 + 1 * n + 9`. -/
theorem cubic_5_1_1_9_le (n : ℕ) : 5 * n ^ 3 + 1 * n ^ 2 + 1 * n + 9 ≤ 16 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_5_1_1_9 :
    IsPolyBounded fun n => 5 * n ^ 3 + 1 * n ^ 2 + 1 * n + 9 := by
  poly_bound

/-- An explicit monomial bound for `5 * n ^ 4 + 12 * n ^ 3 + 8 * n ^ 2 + 3 * n + 7`. -/
theorem quartic_5_12_8_3_7_le (n : ℕ) :
    5 * n ^ 4 + 12 * n ^ 3 + 8 * n ^ 2 + 3 * n + 7 ≤ 35 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_5_12_8_3_7 :
    IsPolyBounded fun n => 5 * n ^ 4 + 12 * n ^ 3 + 8 * n ^ 2 + 3 * n + 7 :=
  ⟨35, 4, quartic_5_12_8_3_7_le⟩

/-- An explicit monomial bound for `1 * n ^ 4 + 4 * n ^ 3 + 2`. -/
theorem quartic_1_4_0_0_2_le (n : ℕ) : 1 * n ^ 4 + 4 * n ^ 3 + 2 ≤ 7 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_1_4_0_0_2 :
    IsPolyBounded fun n => 1 * n ^ 4 + 4 * n ^ 3 + 2 := by
  poly_bound

/-- An explicit monomial bound for `4 * n ^ 4 + 5 * n ^ 3 + 5 * n ^ 2 + 6`. -/
theorem quartic_4_5_5_0_6_le (n : ℕ) :
    4 * n ^ 4 + 5 * n ^ 3 + 5 * n ^ 2 + 6 ≤ 20 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_4_5_5_0_6 :
    IsPolyBounded fun n => 4 * n ^ 4 + 5 * n ^ 3 + 5 * n ^ 2 + 6 := by
  poly_bound

/-- An explicit monomial bound for `1 * n + 7`. -/
theorem linear_1_7_le (n : ℕ) : 1 * n + 7 ≤ 8 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_1_7 : IsPolyBounded fun n => 1 * n + 7 := by
  poly_bound

/-- An explicit monomial bound for `7 * n ^ 2 + 12 * n + 8`. -/
theorem quadratic_7_12_8_le (n : ℕ) : 7 * n ^ 2 + 12 * n + 8 ≤ 27 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_7_12_8 : IsPolyBounded fun n => 7 * n ^ 2 + 12 * n + 8 :=
  ⟨27, 2, quadratic_7_12_8_le⟩

/-- An explicit monomial bound for `4 * n ^ 5 + 12 * n ^ 3 + 7 * n + 2`. -/
theorem quintic_4_0_12_0_7_2_le (n : ℕ) :
    4 * n ^ 5 + 12 * n ^ 3 + 7 * n + 2 ≤ 25 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_4_0_12_0_7_2 :
    IsPolyBounded fun n => 4 * n ^ 5 + 12 * n ^ 3 + 7 * n + 2 :=
  ⟨25, 5, quintic_4_0_12_0_7_2_le⟩

/-- An explicit monomial bound for `2 * n + 6`. -/
theorem linear_2_6_le (n : ℕ) : 2 * n + 6 ≤ 8 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_2_6 : IsPolyBounded fun n => 2 * n + 6 :=
  ⟨8, 1, linear_2_6_le⟩

/-- An explicit monomial bound for `1 * n ^ 5 + 4 * n ^ 4 + 5 * n ^ 3 + 12 * n ^ 2 + 16`. -/
theorem quintic_1_4_5_12_0_16_le (n : ℕ) :
    1 * n ^ 5 + 4 * n ^ 4 + 5 * n ^ 3 + 12 * n ^ 2 + 16 ≤ 38 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_1_4_5_12_0_16 :
    IsPolyBounded fun n => 1 * n ^ 5 + 4 * n ^ 4 + 5 * n ^ 3 + 12 * n ^ 2 + 16 :=
  ⟨38, 5, quintic_1_4_5_12_0_16_le⟩

/-- An explicit monomial bound for `1 * n ^ 3 + 9 * n ^ 2 + 3 * n + 6`. -/
theorem cubic_1_9_3_6_le (n : ℕ) : 1 * n ^ 3 + 9 * n ^ 2 + 3 * n + 6 ≤ 19 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_1_9_3_6 :
    IsPolyBounded fun n => 1 * n ^ 3 + 9 * n ^ 2 + 3 * n + 6 := by
  poly_bound

/-- An explicit monomial bound for `9 * n ^ 4 + 12 * n ^ 3 + 5 * n ^ 2 + 8 * n`. -/
theorem quartic_9_12_5_8_0_le (n : ℕ) :
    9 * n ^ 4 + 12 * n ^ 3 + 5 * n ^ 2 + 8 * n ≤ 34 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quartic_9_12_5_8_0 :
    IsPolyBounded fun n => 9 * n ^ 4 + 12 * n ^ 3 + 5 * n ^ 2 + 8 * n :=
  ⟨34, 4, quartic_9_12_5_8_0_le⟩

/-- An explicit monomial bound for `7 * n ^ 2 + 12 * n + 6`. -/
theorem quadratic_7_12_6_le (n : ℕ) : 7 * n ^ 2 + 12 * n + 6 ≤ 25 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_7_12_6 : IsPolyBounded fun n => 7 * n ^ 2 + 12 * n + 6 :=
  ⟨25, 2, quadratic_7_12_6_le⟩

/-- An explicit monomial bound for `3 * n ^ 2 + 4 * n + 4`. -/
theorem quadratic_3_4_4_le (n : ℕ) : 3 * n ^ 2 + 4 * n + 4 ≤ 11 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_3_4_4 : IsPolyBounded fun n => 3 * n ^ 2 + 4 * n + 4 := by
  poly_bound

/-- An explicit monomial bound for `1 * n + 4`. -/
theorem linear_1_4_le (n : ℕ) : 1 * n + 4 ≤ 5 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_1_4 : IsPolyBounded fun n => 1 * n + 4 := by
  poly_bound

/-- An explicit monomial bound for `5 * n ^ 4 + 3 * n ^ 3 + 1 * n + 8`. -/
theorem quartic_5_3_0_1_8_le (n : ℕ) :
    5 * n ^ 4 + 3 * n ^ 3 + 1 * n + 8 ≤ 17 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_5_3_0_1_8 :
    IsPolyBounded fun n => 5 * n ^ 4 + 3 * n ^ 3 + 1 * n + 8 := by
  poly_bound

/-- An explicit monomial bound for `5 * n ^ 5 + 9 * n ^ 4 + 3 * n ^ 3 + 9 * n ^ 2 + 7 * n`. -/
theorem quintic_5_9_3_9_7_0_le (n : ℕ) :
    5 * n ^ 5 + 9 * n ^ 4 + 3 * n ^ 3 + 9 * n ^ 2 + 7 * n ≤ 33 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quintic_5_9_3_9_7_0 :
    IsPolyBounded fun n => 5 * n ^ 5 + 9 * n ^ 4 + 3 * n ^ 3 + 9 * n ^ 2 + 7 * n := by
  poly_bound

/-- An explicit monomial bound for `6 * n ^ 2 + 16 * n + 8`. -/
theorem quadratic_6_16_8_le (n : ℕ) : 6 * n ^ 2 + 16 * n + 8 ≤ 30 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_6_16_8 : IsPolyBounded fun n => 6 * n ^ 2 + 16 * n + 8 := by
  poly_bound

/-- An explicit monomial bound for `3 * n ^ 2 + 12 * n + 6`. -/
theorem quadratic_3_12_6_le (n : ℕ) : 3 * n ^ 2 + 12 * n + 6 ≤ 21 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_3_12_6 : IsPolyBounded fun n => 3 * n ^ 2 + 12 * n + 6 :=
  ⟨21, 2, quadratic_3_12_6_le⟩

/-- An explicit monomial bound for `3 * n ^ 4 + 4 * n ^ 3 + 1 * n ^ 2 + 5 * n + 4`. -/
theorem quartic_3_4_1_5_4_le (n : ℕ) :
    3 * n ^ 4 + 4 * n ^ 3 + 1 * n ^ 2 + 5 * n + 4 ≤ 17 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_3_4_1_5_4 :
    IsPolyBounded fun n => 3 * n ^ 4 + 4 * n ^ 3 + 1 * n ^ 2 + 5 * n + 4 := by
  poly_bound

/-- An explicit monomial bound for `2 * n + 12`. -/
theorem linear_2_12_le (n : ℕ) : 2 * n + 12 ≤ 14 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_2_12 : IsPolyBounded fun n => 2 * n + 12 := by
  poly_bound

/-- An explicit monomial bound for `2 * n ^ 3 + 8 * n ^ 2 + 7 * n + 6`. -/
theorem cubic_2_8_7_6_le (n : ℕ) : 2 * n ^ 3 + 8 * n ^ 2 + 7 * n + 6 ≤ 23 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_2_8_7_6 :
    IsPolyBounded fun n => 2 * n ^ 3 + 8 * n ^ 2 + 7 * n + 6 :=
  ⟨23, 3, cubic_2_8_7_6_le⟩

/-- An explicit monomial bound for `6 * n ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 7`. -/
theorem quartic_6_4_3_0_7_le (n : ℕ) :
    6 * n ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 7 ≤ 20 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_6_4_3_0_7 :
    IsPolyBounded fun n => 6 * n ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 7 := by
  poly_bound

/-- An explicit monomial bound for `9 * n ^ 2 + 1 * n + 7`. -/
theorem quadratic_9_1_7_le (n : ℕ) : 9 * n ^ 2 + 1 * n + 7 ≤ 17 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_9_1_7 : IsPolyBounded fun n => 9 * n ^ 2 + 1 * n + 7 := by
  poly_bound

/-- An explicit monomial bound for `1 * n + 5`. -/
theorem linear_1_5_le (n : ℕ) : 1 * n + 5 ≤ 6 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_1_5 : IsPolyBounded fun n => 1 * n + 5 := by
  poly_bound

/-- An explicit monomial bound for `2 * n ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 7 * n`. -/
theorem quartic_2_4_3_7_0_le (n : ℕ) :
    2 * n ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 7 * n ≤ 16 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quartic_2_4_3_7_0 :
    IsPolyBounded fun n => 2 * n ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 7 * n :=
  ⟨16, 4, quartic_2_4_3_7_0_le⟩

/-- An explicit monomial bound for `5 * n + 9`. -/
theorem linear_5_9_le (n : ℕ) : 5 * n + 9 ≤ 14 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_5_9 : IsPolyBounded fun n => 5 * n + 9 :=
  ⟨14, 1, linear_5_9_le⟩

/-- An explicit monomial bound for `2 * n ^ 2 + 1`. -/
theorem quadratic_2_0_1_le (n : ℕ) : 2 * n ^ 2 + 1 ≤ 3 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_2_0_1 : IsPolyBounded fun n => 2 * n ^ 2 + 1 := by
  poly_bound

/-- An explicit monomial bound for `7 * n ^ 5 + 8 * n ^ 4 + 3 * n ^ 3 + 9 * n ^ 2 + 2 * n + 4`. -/
theorem quintic_7_8_3_9_2_4_le (n : ℕ) :
    7 * n ^ 5 + 8 * n ^ 4 + 3 * n ^ 3 + 9 * n ^ 2 + 2 * n + 4 ≤ 33 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h6 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_7_8_3_9_2_4 :
    IsPolyBounded fun n => 7 * n ^ 5 + 8 * n ^ 4 + 3 * n ^ 3 + 9 * n ^ 2 + 2 * n + 4 :=
  ⟨33, 5, quintic_7_8_3_9_2_4_le⟩

/-- An explicit monomial bound for `9 * n ^ 5 + 1 * n ^ 4 + 7 * n ^ 2 + 7 * n`. -/
theorem quintic_9_1_0_7_7_0_le (n : ℕ) :
    9 * n ^ 5 + 1 * n ^ 4 + 7 * n ^ 2 + 7 * n ≤ 24 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quintic_9_1_0_7_7_0 :
    IsPolyBounded fun n => 9 * n ^ 5 + 1 * n ^ 4 + 7 * n ^ 2 + 7 * n := by
  poly_bound

/-- An explicit monomial bound for `3 * n ^ 3 + 9 * n ^ 2 + 1 * n + 1`. -/
theorem cubic_3_9_1_1_le (n : ℕ) : 3 * n ^ 3 + 9 * n ^ 2 + 1 * n + 1 ≤ 14 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_3_9_1_1 :
    IsPolyBounded fun n => 3 * n ^ 3 + 9 * n ^ 2 + 1 * n + 1 := by
  poly_bound

/-- An explicit monomial bound for `1 * n ^ 4 + 7 * n ^ 3 + 1 * n ^ 2 + 3 * n + 5`. -/
theorem quartic_1_7_1_3_5_le (n : ℕ) :
    1 * n ^ 4 + 7 * n ^ 3 + 1 * n ^ 2 + 3 * n + 5 ≤ 17 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_1_7_1_3_5 :
    IsPolyBounded fun n => 1 * n ^ 4 + 7 * n ^ 3 + 1 * n ^ 2 + 3 * n + 5 :=
  ⟨17, 4, quartic_1_7_1_3_5_le⟩

/-- An explicit monomial bound for `8 * n ^ 2 + 12 * n`. -/
theorem quadratic_8_12_0_le (n : ℕ) : 8 * n ^ 2 + 12 * n ≤ 20 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quadratic_8_12_0 : IsPolyBounded fun n => 8 * n ^ 2 + 12 * n :=
  ⟨20, 2, quadratic_8_12_0_le⟩

/-- An explicit monomial bound for `8 * n ^ 3 + 9 * n ^ 2 + 7 * n + 9`. -/
theorem cubic_8_9_7_9_le (n : ℕ) : 8 * n ^ 3 + 9 * n ^ 2 + 7 * n + 9 ≤ 33 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_8_9_7_9 :
    IsPolyBounded fun n => 8 * n ^ 3 + 9 * n ^ 2 + 7 * n + 9 :=
  ⟨33, 3, cubic_8_9_7_9_le⟩

/-- An explicit monomial bound for `9 * n ^ 3 + 3 * n ^ 2 + 2 * n + 1`. -/
theorem cubic_9_3_2_1_le (n : ℕ) : 9 * n ^ 3 + 3 * n ^ 2 + 2 * n + 1 ≤ 15 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_9_3_2_1 :
    IsPolyBounded fun n => 9 * n ^ 3 + 3 * n ^ 2 + 2 * n + 1 := by
  poly_bound

/-- An explicit monomial bound for `6 * n ^ 3 + 3 * n ^ 2 + 1 * n`. -/
theorem cubic_6_3_1_0_le (n : ℕ) : 6 * n ^ 3 + 3 * n ^ 2 + 1 * n ≤ 10 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_cubic_6_3_1_0 :
    IsPolyBounded fun n => 6 * n ^ 3 + 3 * n ^ 2 + 1 * n := by
  poly_bound

/-- An explicit monomial bound for `5 * n ^ 3 + 16 * n ^ 2 + 7`. -/
theorem cubic_5_16_0_7_le (n : ℕ) : 5 * n ^ 3 + 16 * n ^ 2 + 7 ≤ 28 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_5_16_0_7 :
    IsPolyBounded fun n => 5 * n ^ 3 + 16 * n ^ 2 + 7 := by
  poly_bound

/-- An explicit monomial bound for `2 * n ^ 4 + 7 * n ^ 3 + 6 * n ^ 2 + 8 * n + 9`. -/
theorem quartic_2_7_6_8_9_le (n : ℕ) :
    2 * n ^ 4 + 7 * n ^ 3 + 6 * n ^ 2 + 8 * n + 9 ≤ 32 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_2_7_6_8_9 :
    IsPolyBounded fun n => 2 * n ^ 4 + 7 * n ^ 3 + 6 * n ^ 2 + 8 * n + 9 := by
  poly_bound

/-- An explicit monomial bound for `2 * n ^ 2 + 3 * n`. -/
theorem quadratic_2_3_0_le (n : ℕ) : 2 * n ^ 2 + 3 * n ≤ 5 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quadratic_2_3_0 : IsPolyBounded fun n => 2 * n ^ 2 + 3 * n := by
  poly_bound

/-- An explicit monomial bound for `9 * n ^ 4 + 9 * n ^ 3 + 7 * n ^ 2 + 16 * n + 3`. -/
theorem quartic_9_9_7_16_3_le (n : ℕ) :
    9 * n ^ 4 + 9 * n ^ 3 + 7 * n ^ 2 + 16 * n + 3 ≤ 44 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_9_9_7_16_3 :
    IsPolyBounded fun n => 9 * n ^ 4 + 9 * n ^ 3 + 7 * n ^ 2 + 16 * n + 3 :=
  ⟨44, 4, quartic_9_9_7_16_3_le⟩

/-- An explicit monomial bound for `2 * n ^ 5 + 6 * n ^ 3 + 2 * n ^ 2 + 16 * n`. -/
theorem quintic_2_0_6_2_16_0_le (n : ℕ) :
    2 * n ^ 5 + 6 * n ^ 3 + 2 * n ^ 2 + 16 * n ≤ 26 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quintic_2_0_6_2_16_0 :
    IsPolyBounded fun n => 2 * n ^ 5 + 6 * n ^ 3 + 2 * n ^ 2 + 16 * n :=
  ⟨26, 5, quintic_2_0_6_2_16_0_le⟩

/-- An explicit monomial bound for `9 * n ^ 2 + 12 * n + 1`. -/
theorem quadratic_9_12_1_le (n : ℕ) : 9 * n ^ 2 + 12 * n + 1 ≤ 22 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_9_12_1 : IsPolyBounded fun n => 9 * n ^ 2 + 12 * n + 1 :=
  ⟨22, 2, quadratic_9_12_1_le⟩

/-- An explicit monomial bound for `3 * n ^ 3 + 4 * n ^ 2 + 2 * n + 8`. -/
theorem cubic_3_4_2_8_le (n : ℕ) : 3 * n ^ 3 + 4 * n ^ 2 + 2 * n + 8 ≤ 17 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_3_4_2_8 :
    IsPolyBounded fun n => 3 * n ^ 3 + 4 * n ^ 2 + 2 * n + 8 :=
  ⟨17, 3, cubic_3_4_2_8_le⟩

/-- An explicit monomial bound for `4 * n ^ 3 + 2 * n ^ 2 + 2 * n + 5`. -/
theorem cubic_4_2_2_5_le (n : ℕ) : 4 * n ^ 3 + 2 * n ^ 2 + 2 * n + 5 ≤ 13 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_4_2_2_5 :
    IsPolyBounded fun n => 4 * n ^ 3 + 2 * n ^ 2 + 2 * n + 5 :=
  ⟨13, 3, cubic_4_2_2_5_le⟩

/-- An explicit monomial bound for `8 * n ^ 5 + 12 * n ^ 4 + 8 * n ^ 3 + 9 * n ^ 2 + 1 * n + 9`. -/
theorem quintic_8_12_8_9_1_9_le (n : ℕ) :
    8 * n ^ 5 + 12 * n ^ 4 + 8 * n ^ 3 + 9 * n ^ 2 + 1 * n + 9 ≤ 47 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h6 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_8_12_8_9_1_9 :
    IsPolyBounded fun n => 8 * n ^ 5 + 12 * n ^ 4 + 8 * n ^ 3 + 9 * n ^ 2 + 1 * n + 9 := by
  poly_bound

/-- An explicit monomial bound for `9 * n ^ 5 + 9 * n ^ 3 + 12 * n ^ 2 + 8 * n + 9`. -/
theorem quintic_9_0_9_12_8_9_le (n : ℕ) :
    9 * n ^ 5 + 9 * n ^ 3 + 12 * n ^ 2 + 8 * n + 9 ≤ 47 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 5 := one_le_succ_pow n 5
  omega

theorem isPolyBounded_quintic_9_0_9_12_8_9 :
    IsPolyBounded fun n => 9 * n ^ 5 + 9 * n ^ 3 + 12 * n ^ 2 + 8 * n + 9 :=
  ⟨47, 5, quintic_9_0_9_12_8_9_le⟩

/-- An explicit monomial bound for `8 * n ^ 3 + 6 * n ^ 2 + 8 * n + 9`. -/
theorem cubic_8_6_8_9_le (n : ℕ) : 8 * n ^ 3 + 6 * n ^ 2 + 8 * n + 9 ≤ 31 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_8_6_8_9 :
    IsPolyBounded fun n => 8 * n ^ 3 + 6 * n ^ 2 + 8 * n + 9 := by
  poly_bound

/-- An explicit monomial bound for `4 * n + 3`. -/
theorem linear_4_3_le (n : ℕ) : 4 * n + 3 ≤ 7 * (n + 1) ^ 1 := by
  have h1 : n ≤ (n + 1) ^ 1 := le_succ_pow n (by decide)
  have h2 : 1 ≤ (n + 1) ^ 1 := one_le_succ_pow n 1
  omega

theorem isPolyBounded_linear_4_3 : IsPolyBounded fun n => 4 * n + 3 := by
  poly_bound

/-- An explicit monomial bound for `3 * n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 6 * n + 9`. -/
theorem quartic_3_4_6_6_9_le (n : ℕ) :
    3 * n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 6 * n + 9 ≤ 28 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_3_4_6_6_9 :
    IsPolyBounded fun n => 3 * n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 6 * n + 9 := by
  poly_bound

/-- An explicit monomial bound for `7 * n ^ 3 + 1 * n ^ 2 + 7 * n`. -/
theorem cubic_7_1_7_0_le (n : ℕ) : 7 * n ^ 3 + 1 * n ^ 2 + 7 * n ≤ 15 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_cubic_7_1_7_0 :
    IsPolyBounded fun n => 7 * n ^ 3 + 1 * n ^ 2 + 7 * n := by
  poly_bound

/-- An explicit monomial bound for `7 * n ^ 3 + 4 * n ^ 2 + 9 * n + 4`. -/
theorem cubic_7_4_9_4_le (n : ℕ) : 7 * n ^ 3 + 4 * n ^ 2 + 9 * n + 4 ≤ 24 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_7_4_9_4 :
    IsPolyBounded fun n => 7 * n ^ 3 + 4 * n ^ 2 + 9 * n + 4 := by
  poly_bound

/-- An explicit monomial bound for `7 * n ^ 3 + 16 * n ^ 2 + 4 * n + 16`. -/
theorem cubic_7_16_4_16_le (n : ℕ) :
    7 * n ^ 3 + 16 * n ^ 2 + 4 * n + 16 ≤ 43 * (n + 1) ^ 3 := by
  have h1 : n ^ 3 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 2 ≤ (n + 1) ^ 3 := pow_le_succ_pow n (by decide)
  have h3 : n ≤ (n + 1) ^ 3 := le_succ_pow n (by decide)
  have h4 : 1 ≤ (n + 1) ^ 3 := one_le_succ_pow n 3
  omega

theorem isPolyBounded_cubic_7_16_4_16 :
    IsPolyBounded fun n => 7 * n ^ 3 + 16 * n ^ 2 + 4 * n + 16 := by
  poly_bound

/-- An explicit monomial bound for `7 * n ^ 2 + 9 * n + 16`. -/
theorem quadratic_7_9_16_le (n : ℕ) : 7 * n ^ 2 + 9 * n + 16 ≤ 32 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_7_9_16 : IsPolyBounded fun n => 7 * n ^ 2 + 9 * n + 16 :=
  ⟨32, 2, quadratic_7_9_16_le⟩

/-- An explicit monomial bound for `4 * n ^ 2 + 16 * n + 5`. -/
theorem quadratic_4_16_5_le (n : ℕ) : 4 * n ^ 2 + 16 * n + 5 ≤ 25 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_4_16_5 : IsPolyBounded fun n => 4 * n ^ 2 + 16 * n + 5 :=
  ⟨25, 2, quadratic_4_16_5_le⟩

/-- An explicit monomial bound for `2 * n ^ 2 + 2 * n + 1`. -/
theorem quadratic_2_2_1_le (n : ℕ) : 2 * n ^ 2 + 2 * n + 1 ≤ 5 * (n + 1) ^ 2 := by
  have h1 : n ^ 2 ≤ (n + 1) ^ 2 := pow_le_succ_pow n (by decide)
  have h2 : n ≤ (n + 1) ^ 2 := le_succ_pow n (by decide)
  have h3 : 1 ≤ (n + 1) ^ 2 := one_le_succ_pow n 2
  omega

theorem isPolyBounded_quadratic_2_2_1 : IsPolyBounded fun n => 2 * n ^ 2 + 2 * n + 1 := by
  poly_bound

/-- An explicit monomial bound for `3 * n ^ 5 + 16 * n ^ 4 + 7 * n ^ 3 + 16 * n ^ 2 + 5 * n`. -/
theorem quintic_3_16_7_16_5_0_le (n : ℕ) :
    3 * n ^ 5 + 16 * n ^ 4 + 7 * n ^ 3 + 16 * n ^ 2 + 5 * n ≤ 47 * (n + 1) ^ 5 := by
  have h1 : n ^ 5 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 4 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 3 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h4 : n ^ 2 ≤ (n + 1) ^ 5 := pow_le_succ_pow n (by decide)
  have h5 : n ≤ (n + 1) ^ 5 := le_succ_pow n (by decide)
  omega

theorem isPolyBounded_quintic_3_16_7_16_5_0 :
    IsPolyBounded fun n => 3 * n ^ 5 + 16 * n ^ 4 + 7 * n ^ 3 + 16 * n ^ 2 + 5 * n := by
  poly_bound

/-- An explicit monomial bound for `5 * n ^ 4 + 7 * n ^ 3 + 9 * n ^ 2 + 7 * n + 7`. -/
theorem quartic_5_7_9_7_7_le (n : ℕ) :
    5 * n ^ 4 + 7 * n ^ 3 + 9 * n ^ 2 + 7 * n + 7 ≤ 35 * (n + 1) ^ 4 := by
  have h1 : n ^ 4 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h2 : n ^ 3 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h3 : n ^ 2 ≤ (n + 1) ^ 4 := pow_le_succ_pow n (by decide)
  have h4 : n ≤ (n + 1) ^ 4 := le_succ_pow n (by decide)
  have h5 : 1 ≤ (n + 1) ^ 4 := one_le_succ_pow n 4
  omega

theorem isPolyBounded_quartic_5_7_9_7_7 :
    IsPolyBounded fun n => 5 * n ^ 4 + 7 * n ^ 3 + 9 * n ^ 2 + 7 * n + 7 :=
  ⟨35, 4, quartic_5_7_9_7_7_le⟩

end Complexity
