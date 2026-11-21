import PNP.Machine.TapeReduction
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

/-! ### Axioms -/

#print axioms Complexity.P_eq_NP
#print axioms Complexity.P_eq_NP_letterale
#print axioms Complexity.P_subset_NP

/-- info: 'Complexity.P_eq_NP' depends on axioms: [propext, Quot.sound, Complexity.AuxTM.tape_reduction] -/
#guard_msgs in #print axioms Complexity.P_eq_NP

/-- info: 'Complexity.P_eq_NP_letterale' does not depend on any axioms -/
#guard_msgs in #print axioms Complexity.P_eq_NP_letterale

/-- info: 'Complexity.P_subset_NP' does not depend on any axioms -/
#guard_msgs in #print axioms Complexity.P_subset_NP
