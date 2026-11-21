import PNP.Data.Language

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
