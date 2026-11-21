/-!
# Finitely enumerated types

A minimal stand-in for Mathlib's `FinEnum`: a type together with an explicit
list of all its elements. Machines carry such a structure on their state space,
which is what makes them finite objects.

## Main definitions

* `Complexity.FinEnum`: the class.
* Instances for `Unit`, `Bool`, `Option`, sums and products.

## Implementation notes

The enumeration is not required to be free of duplicates, as only exhaustiveness
is ever used. This makes the instances for sums and products one-liners.
-/

set_option autoImplicit false

namespace Complexity

/-- A type with an explicit, exhaustive list of its elements. -/
class FinEnum (α : Type) where
  /-- The list of all elements. -/
  elems : List α
  /-- Every element occurs in `elems`. -/
  complete : ∀ a : α, a ∈ elems

namespace FinEnum

/-- The number of listed elements, an upper bound on the cardinality. -/
def card (α : Type) [FinEnum α] : Nat := (elems (α := α)).length

instance : FinEnum Unit := ⟨[()], fun _ => List.mem_singleton.2 rfl⟩

instance : FinEnum Bool := ⟨[false, true], fun b => by cases b <;> simp⟩

instance {α : Type} [FinEnum α] : FinEnum (Option α) where
  elems := none :: (elems (α := α)).map some
  complete
    | none => List.mem_cons_self _ _
    | some a => List.mem_cons_of_mem _ (List.mem_map_of_mem _ (complete a))

instance {α β : Type} [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β) where
  elems := (elems (α := α)).map Sum.inl ++ (elems (α := β)).map Sum.inr
  complete
    | .inl a => List.mem_append_left _ (List.mem_map_of_mem _ (complete a))
    | .inr b => List.mem_append_right _ (List.mem_map_of_mem _ (complete b))

instance {α β : Type} [FinEnum α] [FinEnum β] : FinEnum (α × β) where
  elems := (elems (α := α)).flatMap fun a => (elems (α := β)).map fun b => (a, b)
  complete := fun (a, b) =>
    List.mem_flatMap.2 ⟨a, complete a, List.mem_map_of_mem _ (complete b)⟩

theorem card_unit : card Unit = 1 := rfl

theorem card_bool : card Bool = 2 := rfl

theorem card_option (α : Type) [FinEnum α] : card (Option α) = card α + 1 := by
  simp [card, elems]

theorem card_sum (α β : Type) [FinEnum α] [FinEnum β] :
    card (α ⊕ β) = card α + card β := by
  simp [card, elems]

end FinEnum

end Complexity
