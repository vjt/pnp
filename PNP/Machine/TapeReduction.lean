import PNP.Poly.Tactic
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

theorem simTime_pow_two (n : ℕ) : simTime (fun n => n ^ 2) n = (n ^ 2 + n + 2) ^ 2 := rfl

theorem isPolyBounded_simTime_pow_two : IsPolyBounded (simTime fun n => n ^ 2) :=
  isPolyBounded_simTime (IsPolyBounded.id.pow 2)

theorem simTime_pow_three (n : ℕ) : simTime (fun n => n ^ 3) n = (n ^ 3 + n + 2) ^ 2 := rfl

theorem isPolyBounded_simTime_pow_three : IsPolyBounded (simTime fun n => n ^ 3) :=
  isPolyBounded_simTime (IsPolyBounded.id.pow 3)

theorem simTime_pow_four (n : ℕ) : simTime (fun n => n ^ 4) n = (n ^ 4 + n + 2) ^ 2 := rfl

theorem isPolyBounded_simTime_pow_four : IsPolyBounded (simTime fun n => n ^ 4) :=
  isPolyBounded_simTime (IsPolyBounded.id.pow 4)

theorem simTime_pow_five (n : ℕ) : simTime (fun n => n ^ 5) n = (n ^ 5 + n + 2) ^ 2 := rfl

theorem isPolyBounded_simTime_pow_five : IsPolyBounded (simTime fun n => n ^ 5) :=
  isPolyBounded_simTime (IsPolyBounded.id.pow 5)

theorem simTime_pow_six (n : ℕ) : simTime (fun n => n ^ 6) n = (n ^ 6 + n + 2) ^ 2 := rfl

theorem isPolyBounded_simTime_pow_six : IsPolyBounded (simTime fun n => n ^ 6) :=
  isPolyBounded_simTime (IsPolyBounded.id.pow 6)

theorem simTime_pow_seven (n : ℕ) : simTime (fun n => n ^ 7) n = (n ^ 7 + n + 2) ^ 2 := rfl

theorem isPolyBounded_simTime_pow_seven : IsPolyBounded (simTime fun n => n ^ 7) :=
  isPolyBounded_simTime (IsPolyBounded.id.pow 7)

theorem simTime_succ_pow_two_le_four (n : ℕ) :
    simTime (fun n => (n + 1) ^ 2) n ≤ simTime (fun n => (n + 1) ^ 4) n :=
  simTime_mono (fun n => succ_pow_le_succ_pow n (by decide)) n

theorem simTime_succ_pow_three_le_five (n : ℕ) :
    simTime (fun n => (n + 1) ^ 3) n ≤ simTime (fun n => (n + 1) ^ 5) n :=
  simTime_mono (fun n => succ_pow_le_succ_pow n (by decide)) n

theorem simTime_succ_pow_four_le_five (n : ℕ) :
    simTime (fun n => (n + 1) ^ 4) n ≤ simTime (fun n => (n + 1) ^ 5) n :=
  simTime_mono (fun n => succ_pow_le_succ_pow n (by decide)) n

theorem simTime_succ_pow_five_le_six (n : ℕ) :
    simTime (fun n => (n + 1) ^ 5) n ≤ simTime (fun n => (n + 1) ^ 6) n :=
  simTime_mono (fun n => succ_pow_le_succ_pow n (by decide)) n

theorem simTime_const_one (n : ℕ) : simTime (fun _ => 1) n = (1 + n + 2) ^ 2 := rfl

theorem simTime_const_two (n : ℕ) : simTime (fun _ => 2) n = (2 + n + 2) ^ 2 := rfl

theorem simTime_const_three (n : ℕ) : simTime (fun _ => 3) n = (3 + n + 2) ^ 2 := rfl

theorem simTime_const_five (n : ℕ) : simTime (fun _ => 5) n = (5 + n + 2) ^ 2 := rfl

theorem simTime_const_eight (n : ℕ) : simTime (fun _ => 8) n = (8 + n + 2) ^ 2 := rfl

/-- The simulation can be iterated without leaving polynomial time. -/
theorem isPolyBounded_simTime_simTime (hT : IsPolyBounded T) :
    IsPolyBounded (simTime (simTime T)) :=
  isPolyBounded_simTime (isPolyBounded_simTime hT)

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

theorem AuxTM.exists_tm_of_runsInTime_pow_two {V : AuxTM}
    (hV : V.RunsInTime fun n => n ^ 2) :
    ∃ M : TM, M.RunsInTime (fun n => (n ^ 2 + n + 2) ^ 2) ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => n ^ 2 :=
  V.tape_reduction _ hV

theorem AuxTM.exists_tm_of_runsInTime_pow_three {V : AuxTM}
    (hV : V.RunsInTime fun n => n ^ 3) :
    ∃ M : TM, M.RunsInTime (fun n => (n ^ 3 + n + 2) ^ 2) ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => n ^ 3 :=
  V.tape_reduction _ hV

theorem AuxTM.exists_tm_of_runsInTime_pow_four {V : AuxTM}
    (hV : V.RunsInTime fun n => n ^ 4) :
    ∃ M : TM, M.RunsInTime (fun n => (n ^ 4 + n + 2) ^ 2) ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => n ^ 4 :=
  V.tape_reduction _ hV

theorem AuxTM.exists_tm_of_runsInTime_pow_five {V : AuxTM}
    (hV : V.RunsInTime fun n => n ^ 5) :
    ∃ M : TM, M.RunsInTime (fun n => (n ^ 5 + n + 2) ^ 2) ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => n ^ 5 :=
  V.tape_reduction _ hV

theorem AuxTM.exists_tm_of_runsInTime_pow_six {V : AuxTM}
    (hV : V.RunsInTime fun n => n ^ 6) :
    ∃ M : TM, M.RunsInTime (fun n => (n ^ 6 + n + 2) ^ 2) ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => n ^ 6 :=
  V.tape_reduction _ hV

theorem AuxTM.exists_polyTime_tm_of_runsInTime_2_1 {V : AuxTM}
    (hV : V.RunsInTime fun n => 2 * n ^ 1) :
    ∃ (M : TM) (T' : ℕ → ℕ), IsPolyBounded T' ∧ M.RunsInTime T' ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => 2 * n ^ 1 :=
  AuxTM.exists_polyTime_tm (IsPolyBounded.monomial 2 1) hV

theorem AuxTM.exists_polyTime_tm_of_runsInTime_3_2 {V : AuxTM}
    (hV : V.RunsInTime fun n => 3 * n ^ 2) :
    ∃ (M : TM) (T' : ℕ → ℕ), IsPolyBounded T' ∧ M.RunsInTime T' ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => 3 * n ^ 2 :=
  AuxTM.exists_polyTime_tm (IsPolyBounded.monomial 3 2) hV

theorem AuxTM.exists_polyTime_tm_of_runsInTime_1_3 {V : AuxTM}
    (hV : V.RunsInTime fun n => 1 * n ^ 3) :
    ∃ (M : TM) (T' : ℕ → ℕ), IsPolyBounded T' ∧ M.RunsInTime T' ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => 1 * n ^ 3 :=
  AuxTM.exists_polyTime_tm (IsPolyBounded.monomial 1 3) hV

theorem AuxTM.exists_polyTime_tm_of_runsInTime_4_2 {V : AuxTM}
    (hV : V.RunsInTime fun n => 4 * n ^ 2) :
    ∃ (M : TM) (T' : ℕ → ℕ), IsPolyBounded T' ∧ M.RunsInTime T' ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => 4 * n ^ 2 :=
  AuxTM.exists_polyTime_tm (IsPolyBounded.monomial 4 2) hV

theorem AuxTM.exists_polyTime_tm_of_runsInTime_2_4 {V : AuxTM}
    (hV : V.RunsInTime fun n => 2 * n ^ 4) :
    ∃ (M : TM) (T' : ℕ → ℕ), IsPolyBounded T' ∧ M.RunsInTime T' ∧
      ∀ x, x ∈ M.language ↔ x ∈ V.language fun n => 2 * n ^ 4 :=
  AuxTM.exists_polyTime_tm (IsPolyBounded.monomial 2 4) hV

end Complexity
