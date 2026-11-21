/-!
# Words, languages and complexity classes

This file fixes the basic vocabulary used throughout the library: binary words,
languages (decision problems) and complexity classes, together with the order
structure on classes.

## Main definitions

* `Complexity.Word`: finite words over the binary alphabet.
* `Complexity.Language`: a set of words, i.e. a decision problem.
* `Complexity.ComplexityClass`: a set of languages.
* `Complexity.ComplexityClass.co`: the class of complements of a class.

## Main results

* `Complexity.Language.ext`: extensionality for languages.
* `Complexity.ComplexityClass.Subset.antisymm`: two classes that contain each
  other are equal.

## Implementation notes

The library does not depend on Mathlib, so the small amount of set-like
structure that is needed is developed here directly on predicates. `Language`
and `ComplexityClass` are definitions rather than abbreviations: membership goes
through the `Membership` instances, which keeps statements in the usual `w ∈ L`,
`L ∈ C` form.

We work over the binary alphabet throughout. This loses no generality, see
[AB09, Claim 1.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed.,
  Cengage Learning, 2013.
-/

set_option autoImplicit false

/-- Mathlib-compatible notation for the natural numbers. -/
notation "ℕ" => Nat

namespace Complexity

/-- Finite words over the binary alphabet. -/
abbrev Word : Type := List Bool

/-- A language, or decision problem, is a set of words. -/
def Language : Type := Word → Prop

namespace Language

instance : Membership Word Language := ⟨fun L w => L w⟩

variable {L L₁ L₂ L₃ : Language} {w : Word}

theorem mem_def : w ∈ L ↔ L w := Iff.rfl

/-- Two languages with the same words are equal. -/
@[ext] theorem ext (h : ∀ w, w ∈ L₁ ↔ w ∈ L₂) : L₁ = L₂ :=
  funext fun w => propext (h w)

/-- The empty language. -/
instance : EmptyCollection Language := ⟨fun _ => False⟩

/-- The language of all words. -/
def univ : Language := fun _ => True

/-- The complement of a language. -/
def compl (L : Language) : Language := fun w => w ∉ L

instance : Union Language := ⟨fun L₁ L₂ w => w ∈ L₁ ∨ w ∈ L₂⟩

instance : Inter Language := ⟨fun L₁ L₂ w => w ∈ L₁ ∧ w ∈ L₂⟩

/-- The preimage of a language under a map on words. -/
def preimage (f : Word → Word) (L : Language) : Language := fun w => f w ∈ L

@[simp] theorem not_mem_empty : w ∉ (∅ : Language) := fun h => h

@[simp] theorem mem_univ : w ∈ univ := trivial

@[simp] theorem mem_compl : w ∈ L.compl ↔ w ∉ L := Iff.rfl

@[simp] theorem mem_union : w ∈ L₁ ∪ L₂ ↔ w ∈ L₁ ∨ w ∈ L₂ := Iff.rfl

@[simp] theorem mem_inter : w ∈ L₁ ∩ L₂ ↔ w ∈ L₁ ∧ w ∈ L₂ := Iff.rfl

@[simp] theorem mem_preimage {f : Word → Word} : w ∈ L.preimage f ↔ f w ∈ L := Iff.rfl

theorem union_comm : ∀ w, w ∈ L₁ ∪ L₂ ↔ w ∈ L₂ ∪ L₁ := fun _ => Or.comm

theorem inter_comm : ∀ w, w ∈ L₁ ∩ L₂ ↔ w ∈ L₂ ∩ L₁ := fun _ => And.comm

theorem union_assoc : ∀ w, w ∈ (L₁ ∪ L₂) ∪ L₃ ↔ w ∈ L₁ ∪ (L₂ ∪ L₃) := fun _ => or_assoc

theorem inter_assoc : ∀ w, w ∈ (L₁ ∩ L₂) ∩ L₃ ↔ w ∈ L₁ ∩ (L₂ ∩ L₃) := fun _ => and_assoc

theorem compl_union : ∀ w, w ∈ (L₁ ∪ L₂).compl ↔ w ∈ L₁.compl ∩ L₂.compl :=
  fun _ => not_or

theorem not_mem_compl_of_mem (h : w ∈ L) : w ∉ L.compl := fun h' => h' h

theorem preimage_compl (f : Word → Word) :
    ∀ w, w ∈ (L.compl).preimage f ↔ w ∈ (L.preimage f).compl := fun _ => Iff.rfl

theorem preimage_preimage (f g : Word → Word) :
    ∀ w, w ∈ (L.preimage g).preimage f ↔ w ∈ L.preimage (g ∘ f) := fun _ => Iff.rfl

end Language

/-- A complexity class is a set of languages. -/
def ComplexityClass : Type := Language → Prop

namespace ComplexityClass

instance : Membership Language ComplexityClass := ⟨fun C L => C L⟩

instance : HasSubset ComplexityClass := ⟨fun C D => ∀ ⦃L : Language⦄, L ∈ C → L ∈ D⟩

variable {C D E : ComplexityClass} {L : Language}

theorem mem_def : L ∈ C ↔ C L := Iff.rfl

theorem subset_def : C ⊆ D ↔ ∀ ⦃L : Language⦄, L ∈ C → L ∈ D := Iff.rfl

/-- Two classes with the same languages are equal. -/
@[ext] theorem ext (h : ∀ L, L ∈ C ↔ L ∈ D) : C = D :=
  funext fun L => propext (h L)

theorem Subset.refl (C : ComplexityClass) : C ⊆ C := fun _ h => h

theorem Subset.trans (h₁ : C ⊆ D) (h₂ : D ⊆ E) : C ⊆ E := fun _ h => h₂ (h₁ h)

/-- Antisymmetry of inclusion: the standard way to prove that two classes
coincide. -/
theorem Subset.antisymm (h₁ : C ⊆ D) (h₂ : D ⊆ C) : C = D :=
  ext fun _ => ⟨fun h => h₁ h, fun h => h₂ h⟩

theorem Subset.of_eq (h : C = D) : C ⊆ D := h ▸ Subset.refl C

theorem eq_iff_subset_subset : C = D ↔ C ⊆ D ∧ D ⊆ C :=
  ⟨fun h => ⟨Subset.of_eq h, Subset.of_eq h.symm⟩, fun h => Subset.antisymm h.1 h.2⟩

/-- The class `co C` of complements of languages in `C`. -/
def co (C : ComplexityClass) : ComplexityClass := fun L => L.compl ∈ C

@[simp] theorem mem_co : L ∈ C.co ↔ L.compl ∈ C := Iff.rfl

theorem co_subset_co (h : C ⊆ D) : C.co ⊆ D.co := fun _ hL => h hL

end ComplexityClass

end Complexity
