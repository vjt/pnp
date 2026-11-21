import PNP.Machine.Compose
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
