import PNP.Poly.Basic

/-!
# The `poly_bound` tactic

A small automation tactic for goals of the form `IsPolyBounded f`, where `f` is
built from polynomially bounded functions, constants and the identity using
addition, multiplication and powers.

## Main definitions

* `poly_bound`: closes `IsPolyBounded` goals by structural recursion on the
  function.

## Implementation notes

The tactic repeatedly applies the closure lemmas of `PNP.Poly.Basic` and
discharges the leaves with `assumption`. It is deliberately syntactic: the
lemmas are applied up to reducible unfolding only, so that a failed match is
cheap, and the goal is not normalised: it is meant for the bounds that arise when machines are
combined, which already have the right shape. Compositions are not handled,
because the higher-order unification problem `f (g n) =?= e n` has no most
general solution; use `IsPolyBounded.comp` explicitly.
-/

set_option autoImplicit false

namespace Complexity

/-- One step of `poly_bound`: apply the first closure lemma that matches. -/
syntax (name := polyBoundStep) "poly_bound_step" : tactic

macro_rules
  | `(tactic| poly_bound_step) =>
    `(tactic| with_reducible first
      | assumption
      | exact IsPolyBounded.id
      | exact IsPolyBounded.const _
      | apply IsPolyBounded.add
      | apply IsPolyBounded.mul
      | apply IsPolyBounded.pow)

/-- `poly_bound` proves goals of the form `IsPolyBounded fun n => e`, where `e` is
built from `n`, constants and polynomially bounded functions in the local
context using `+`, `*` and `^`. -/
syntax (name := polyBound) "poly_bound" : tactic

macro_rules
  | `(tactic| poly_bound) => `(tactic| (repeat' poly_bound_step) <;> done)

example {f g : ℕ → ℕ} (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded fun n => f n * g n + 3 * n ^ 2 + 1 := by
  poly_bound

end Complexity
