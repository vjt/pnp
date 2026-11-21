import PNP.Reduction.Basic

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
