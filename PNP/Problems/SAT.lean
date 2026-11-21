import PNP.Data.Encoding
import PNP.Reduction.NPComplete

/-!
# Boolean satisfiability

Propositional formulas in conjunctive normal form, and the languages SAT and
3-SAT.

## Main definitions

* `Complexity.Literal`, `Complexity.Clause`, `Complexity.CNF`: formulas in
  conjunctive normal form.
* `Complexity.Literal.eval`, `Complexity.Clause.eval`, `Complexity.CNF.eval`:
  evaluation under an assignment.
* `Complexity.CNF.Satisfiable`: satisfiability.
* `Complexity.CNF.IsKCNF`: every clause has at most `k` literals.
* `Complexity.SAT`, `Complexity.ThreeSAT`: the languages.
* `Complexity.CookLevin`: the statement that SAT is NP-complete.

## Main results

* `Complexity.CNF.eval_append`: a conjunction holds iff both parts hold.
* `Complexity.CNF.not_satisfiable_of_nil_mem`: a formula with an empty clause is
  unsatisfiable.
* `Complexity.CNF.Satisfiable.of_subset`: satisfiability is antitone in the set
  of clauses.
* `Complexity.threeSAT_subset_SAT`: every yes-instance of 3-SAT is a yes-instance
  of SAT.
* `Complexity.CookLevin.sat_mem_P_iff`: given the Cook–Levin theorem, SAT ∈ P is
  equivalent to P = NP.

## Implementation notes

A literal is a variable index together with a polarity. Clauses and formulas are
lists, so that the encoding of a formula is obtained from the instances of
`PNP.Data.Encoding`. Assignments are total functions `ℕ → Bool`; only the values
on the variables that occur in a formula matter (`CNF.eval_congr`).

The Cook–Levin theorem [Coo71; Lev73] is stated as the proposition `CookLevin`
and is not proved in this file: the tableau construction requires a formalised
encoding of machine computations as formulas, which is left for future work. No
result outside this file depends on it.

## References

* [Coo71] S. A. Cook, *The complexity of theorem-proving procedures*, STOC 1971.
* [Lev73] L. A. Levin, *Universal sequential search problems*, 1973.
* [Kar72] R. M. Karp, *Reducibility among combinatorial problems*, 1972.
* [GJ79] M. R. Garey, D. S. Johnson, *Computers and Intractability*, problems
  LO1 and LO2.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Theorem 7.37.
-/

set_option autoImplicit false

namespace Complexity

/-- A literal: a variable, possibly negated. -/
structure Literal where
  /-- The index of the variable. -/
  var : ℕ
  /-- Whether the literal is negated. -/
  neg : Bool
  deriving DecidableEq, Repr

/-- A clause is a disjunction of literals. -/
abbrev Clause : Type := List Literal

/-- A formula in conjunctive normal form is a conjunction of clauses. -/
abbrev CNF : Type := List Clause

/-- A truth assignment. -/
abbrev Assignment : Type := ℕ → Bool

instance : Encoding Literal :=
  Encoding.ofLeftInverse (fun l => (l.var, l.neg)) (fun p => ⟨p.1, p.2⟩) fun _ => rfl

namespace Literal

/-- The value of a literal under an assignment. -/
def eval (σ : Assignment) (l : Literal) : Bool := σ l.var != l.neg

/-- The positive literal on variable `i`. -/
def pos (i : ℕ) : Literal := ⟨i, false⟩

/-- The complementary literal. -/
def not (l : Literal) : Literal := ⟨l.var, !l.neg⟩

@[simp] theorem eval_pos (σ : Assignment) (i : ℕ) : (pos i).eval σ = σ i := by
  simp [eval, pos]

@[simp] theorem eval_not (σ : Assignment) (l : Literal) : l.not.eval σ = !l.eval σ := by
  cases h : σ l.var <;> cases h' : l.neg <;> simp [eval, not, h, h']

@[simp] theorem not_not (l : Literal) : l.not.not = l := by
  cases l; simp [not]

theorem eval_congr {σ τ : Assignment} {l : Literal} (h : σ l.var = τ l.var) :
    l.eval σ = l.eval τ := by
  simp [eval, h]

end Literal

namespace Clause

/-- The value of a clause: some literal is true. -/
def eval (σ : Assignment) (c : Clause) : Bool := c.any (Literal.eval σ)

@[simp] theorem eval_nil (σ : Assignment) : eval σ [] = false := rfl

@[simp] theorem eval_cons (σ : Assignment) (l : Literal) (c : Clause) :
    eval σ (l :: c) = (l.eval σ || eval σ c) := rfl

@[simp] theorem eval_append (σ : Assignment) (c d : Clause) :
    eval σ (c ++ d) = (eval σ c || eval σ d) := by
  simp [eval]

theorem eval_eq_true_iff {σ : Assignment} {c : Clause} :
    eval σ c = true ↔ ∃ l, l ∈ c ∧ l.eval σ = true := by
  simp [eval]

theorem eval_of_mem {σ : Assignment} {c : Clause} {l : Literal} (hl : l ∈ c)
    (h : l.eval σ = true) : eval σ c = true :=
  eval_eq_true_iff.2 ⟨l, hl, h⟩

theorem eval_congr {σ τ : Assignment} {c : Clause} (h : ∀ l, l ∈ c → σ l.var = τ l.var) :
    eval σ c = eval τ c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    rw [eval_cons, eval_cons, Literal.eval_congr (h l (List.mem_cons_self _ _)),
      ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

end Clause

namespace CNF

/-- The value of a formula: every clause is true. -/
def eval (σ : Assignment) (φ : CNF) : Bool := φ.all (Clause.eval σ)

/-- A formula is satisfiable if some assignment makes it true. -/
def Satisfiable (φ : CNF) : Prop := ∃ σ : Assignment, eval σ φ = true

/-- Every clause of `φ` has at most `k` literals. -/
def IsKCNF (k : ℕ) (φ : CNF) : Prop := ∀ c, c ∈ φ → c.length ≤ k

instance (k : ℕ) (φ : CNF) : Decidable (IsKCNF k φ) :=
  inferInstanceAs (Decidable (∀ c, c ∈ φ → c.length ≤ k))

@[simp] theorem eval_nil (σ : Assignment) : eval σ [] = true := rfl

@[simp] theorem eval_cons (σ : Assignment) (c : Clause) (φ : CNF) :
    eval σ (c :: φ) = (Clause.eval σ c && eval σ φ) := rfl

@[simp] theorem eval_append (σ : Assignment) (φ ψ : CNF) :
    eval σ (φ ++ ψ) = (eval σ φ && eval σ ψ) := by
  simp [eval]

theorem eval_eq_true_iff {σ : Assignment} {φ : CNF} :
    eval σ φ = true ↔ ∀ c, c ∈ φ → Clause.eval σ c = true := by
  simp [eval]

theorem eval_congr {σ τ : Assignment} {φ : CNF}
    (h : ∀ c, c ∈ φ → ∀ l, l ∈ c → σ l.var = τ l.var) : eval σ φ = eval τ φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    rw [eval_cons, eval_cons, Clause.eval_congr (h c (List.mem_cons_self _ _)),
      ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]

/-- The empty formula is satisfiable. -/
theorem satisfiable_nil : Satisfiable [] := ⟨fun _ => false, rfl⟩

/-- A formula that contains the empty clause is unsatisfiable. -/
theorem not_satisfiable_of_nil_mem {φ : CNF} (h : [] ∈ φ) : ¬Satisfiable φ := by
  rintro ⟨σ, hσ⟩
  have := eval_eq_true_iff.1 hσ [] h
  simp at this

/-- A formula all of whose clauses occur in a satisfiable formula is
satisfiable. -/
theorem Satisfiable.of_subset {φ ψ : CNF} (hψ : Satisfiable ψ) (h : ∀ c, c ∈ φ → c ∈ ψ) :
    Satisfiable φ :=
  let ⟨σ, hσ⟩ := hψ
  ⟨σ, eval_eq_true_iff.2 fun c hc => eval_eq_true_iff.1 hσ c (h c hc)⟩

theorem Satisfiable.of_append_left {φ ψ : CNF} (h : Satisfiable (φ ++ ψ)) : Satisfiable φ :=
  h.of_subset fun _ hc => List.mem_append_left _ hc

theorem Satisfiable.of_append_right {φ ψ : CNF} (h : Satisfiable (φ ++ ψ)) : Satisfiable ψ :=
  h.of_subset fun _ hc => List.mem_append_right _ hc

theorem Satisfiable.of_cons {c : Clause} {φ : CNF} (h : Satisfiable (c :: φ)) : Satisfiable φ :=
  h.of_subset fun _ hc => List.mem_cons_of_mem _ hc

/-- A unit clause and its negation are jointly unsatisfiable. -/
theorem not_satisfiable_unit_not (l : Literal) : ¬Satisfiable [[l], [l.not]] := by
  rintro ⟨σ, hσ⟩
  cases h : l.eval σ <;> simp [eval, Clause.eval, h] at hσ

theorem isKCNF_nil (k : ℕ) : IsKCNF k [] := fun _ h => nomatch h

theorem IsKCNF.mono {k k' : ℕ} {φ : CNF} (h : IsKCNF k φ) (hk : k ≤ k') : IsKCNF k' φ :=
  fun c hc => Nat.le_trans (h c hc) hk

theorem IsKCNF.append {k : ℕ} {φ ψ : CNF} (hφ : IsKCNF k φ) (hψ : IsKCNF k ψ) :
    IsKCNF k (φ ++ ψ) :=
  fun c hc => (List.mem_append.1 hc).elim (hφ c) (hψ c)

theorem IsKCNF.of_cons {k : ℕ} {c : Clause} {φ : CNF} (h : IsKCNF k (c :: φ)) : IsKCNF k φ :=
  fun c' hc' => h c' (List.mem_cons_of_mem _ hc')

end CNF

/-- **SAT**: the language of satisfiable formulas in conjunctive normal form. -/
def SAT : Language := Encoding.languageOf CNF.Satisfiable

/-- **3-SAT**: the language of satisfiable formulas with at most three literals
per clause. -/
def ThreeSAT : Language := Encoding.languageOf fun φ : CNF => φ.IsKCNF 3 ∧ φ.Satisfiable

theorem encode_mem_SAT {φ : CNF} : Encoding.encode φ ∈ SAT ↔ φ.Satisfiable :=
  Encoding.mem_languageOf_encode

theorem encode_mem_ThreeSAT {φ : CNF} :
    Encoding.encode φ ∈ ThreeSAT ↔ φ.IsKCNF 3 ∧ φ.Satisfiable :=
  Encoding.mem_languageOf_encode

/-- Every yes-instance of 3-SAT is a yes-instance of SAT. -/
theorem threeSAT_subset_SAT {w : Word} (h : w ∈ ThreeSAT) : w ∈ SAT :=
  Encoding.languageOf_mono (fun _ h => h.2) h

/-- The **Cook–Levin theorem** [Coo71; Lev73], as a proposition: SAT is
NP-complete. -/
def CookLevin : Prop := NPComplete SAT

namespace CookLevin

/-- Given the Cook–Levin theorem, SAT ∈ P is equivalent to P = NP. -/
theorem sat_mem_P_iff (h : CookLevin) : SAT ∈ P ↔ P = NP := NPComplete.mem_P_iff h

/-- Given the Cook–Levin theorem, a language in NP to which SAT reduces is
NP-complete. This is the entry point for Karp's reductions [Kar72]. -/
theorem npComplete_of_reducible (h : CookLevin) {L : Language} (hL : L ∈ NP)
    (hred : SAT ≤ₚ L) : NPComplete L :=
  NPComplete.of_reducible h hL hred

end CookLevin

end Complexity
