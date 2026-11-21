import PNP.Machine.TM

/-!
# Sequential composition of Turing machines

Given machines `M₁` and `M₂`, the machine `TM.comp M₁ M₂` runs `M₁` to
completion and then starts `M₂` on the tape that `M₁` leaves behind.

## Main definitions

* `Complexity.TM.comp`: sequential composition.
* `Complexity.TM.inlCfg`, `Complexity.TM.inrCfg`: the embeddings of the
  configurations of the two components.

## Main results

* `Complexity.TM.exists_comp_run_inl`: the simulation lemma. If `M₁` halts within
  `t` steps, then after at most `t + 1` steps the composite is in the initial
  state of `M₂` on the tape left by `M₁`, and from there on it follows `M₂`.
* `Complexity.TM.Computes.comp`: if `M₁` computes `f` and `M₂` computes `g`, then
  `TM.comp M₁ M₂` computes `g ∘ f`, in time `T₁(n) + 1 + T₂(|f x|)`.
* `Complexity.TM.comp_runsInTime`, `Complexity.TM.mem_comp_language`: the same
  for a decider `M₂`; the composite decides the preimage of the language of `M₂`.

## Implementation notes

The state space of the composite is the sum `M₁.State ⊕ M₂.State`. A halting
configuration of `M₁` is linked to the initial state of `M₂` by a single extra
step that rewrites the scanned symbol with itself and does not move. No
rewinding is needed: `TM.Computes` requires `M₁` to halt in standard
configuration, which is literally the initial configuration of `M₂` on the
output.

The exact halting time of `M₁` is not known to the simulation lemma, only an
upper bound; this is why it is stated with an existential `t' ≤ t`. The
consequences are stated for arbitrary bounds using stability of halted runs.

## References

* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Theorem 7.31.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, §1.3.
-/

set_option autoImplicit false

namespace Complexity

namespace TM

/-- Sequential composition: run `M₁`, then run `M₂` on the resulting tape. -/
def comp (M₁ M₂ : TM) : TM where
  State := M₁.State ⊕ M₂.State
  start := .inl M₁.start
  accepting := fun q =>
    match q with
    | .inl _ => false
    | .inr q => M₂.accepting q
  δ := fun q a =>
    match q with
    | .inl q =>
      match M₁.δ q a with
      | some r => some (.inl r.1, r.2.1, r.2.2)
      | none => some (.inr M₂.start, a, .stay)
    | .inr q => (M₂.δ q a).map fun r => (.inr r.1, r.2.1, r.2.2)

variable {M₁ M₂ : TM}

/-- A configuration of the first component, as a configuration of the composite. -/
def inlCfg (c : Cfg M₁.State) : Cfg (comp M₁ M₂).State := ⟨.inl c.state, c.tape⟩

/-- A configuration of the second component, as a configuration of the composite. -/
def inrCfg (c : Cfg M₂.State) : Cfg (comp M₁ M₂).State := ⟨.inr c.state, c.tape⟩

/-! ### Transitions of the composite -/

theorem comp_δ_inl_of_some {q : M₁.State} {a : Symbol} {r : M₁.State × Symbol × Dir}
    (h : M₁.δ q a = some r) :
    (comp M₁ M₂).δ (.inl q) a = some (.inl r.1, r.2.1, r.2.2) := by
  show (match M₁.δ q a with
    | some r => some (Sum.inl r.1, r.2.1, r.2.2)
    | none => some (Sum.inr M₂.start, a, Dir.stay)) = _
  rw [h]

theorem comp_δ_inl_of_none {q : M₁.State} {a : Symbol} (h : M₁.δ q a = none) :
    (comp M₁ M₂).δ (.inl q) a = some (.inr M₂.start, a, .stay) := by
  show (match M₁.δ q a with
    | some r => some (Sum.inl r.1, r.2.1, r.2.2)
    | none => some (Sum.inr M₂.start, a, Dir.stay)) = _
  rw [h]

theorem comp_δ_inr (q : M₂.State) (a : Symbol) :
    (comp M₁ M₂).δ (.inr q) a = (M₂.δ q a).map fun r => (.inr r.1, r.2.1, r.2.2) := rfl

theorem comp_step_inl_of_step {c c' : Cfg M₁.State} (h : M₁.step c = some c') :
    (comp M₁ M₂).step (inlCfg c) = some (inlCfg c') := by
  unfold step at h
  cases hδ : M₁.δ c.state c.tape.head with
  | none => rw [hδ] at h; exact Option.noConfusion h
  | some r =>
    rw [hδ] at h
    cases h
    show Option.map _ ((comp M₁ M₂).δ (.inl c.state) c.tape.head) = _
    rw [comp_δ_inl_of_some hδ]
    rfl

theorem comp_step_inl_of_halted {c : Cfg M₁.State} (h : M₁.Halted c) :
    (comp M₁ M₂).step (inlCfg c) = some (inrCfg ⟨M₂.start, c.tape⟩) := by
  show Option.map _ ((comp M₁ M₂).δ (.inl c.state) c.tape.head) = _
  rw [comp_δ_inl_of_none (halted_iff.1 h)]
  rfl

theorem comp_step_inr (c : Cfg M₂.State) :
    (comp M₁ M₂).step (inrCfg c) = (M₂.step c).map inrCfg := by
  show Option.map _ ((comp M₁ M₂).δ (.inr c.state) c.tape.head) = _
  rw [comp_δ_inr]
  unfold step
  cases M₂.δ c.state c.tape.head <;> rfl

theorem comp_next_inr (c : Cfg M₂.State) :
    (comp M₁ M₂).next (inrCfg c) = inrCfg (M₂.next c) := by
  unfold next
  rw [comp_step_inr]
  cases M₂.step c <;> rfl

theorem comp_run_inr (t : ℕ) (c : Cfg M₂.State) :
    (comp M₁ M₂).run t (inrCfg c) = inrCfg (M₂.run t c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => rw [run_succ, comp_next_inr, ih, run_succ]

theorem comp_halted_inr {c : Cfg M₂.State} :
    (comp M₁ M₂).Halted (inrCfg c) ↔ M₂.Halted c := by
  unfold Halted
  rw [comp_step_inr]
  cases M₂.step c <;> simp

theorem not_comp_halted_inl (c : Cfg M₁.State) : ¬(comp M₁ M₂).Halted (inlCfg c) := by
  intro h
  cases hc : M₁.step c with
  | none => rw [Halted, comp_step_inl_of_halted hc] at h; exact Option.noConfusion h
  | some c' => rw [Halted, comp_step_inl_of_step hc] at h; exact Option.noConfusion h

/-! ### The simulation lemma -/

/-- If `M₁` halts within `t` steps from `c`, then within `t + 1` steps the
composite reaches the initial state of `M₂` on the tape left by `M₁`, and from
then on it simulates `M₂` step by step. -/
theorem exists_comp_run_inl {t : ℕ} {c : Cfg M₁.State} (h : M₁.Halted (M₁.run t c)) :
    ∃ t', t' ≤ t ∧ ∀ s, (comp M₁ M₂).run (t' + 1 + s) (inlCfg c) =
      inrCfg (M₂.run s ⟨M₂.start, (M₁.run t c).tape⟩) := by
  induction t generalizing c with
  | zero =>
    have h' : M₁.Halted c := h
    refine ⟨0, Nat.le_refl _, fun s => ?_⟩
    rw [Nat.zero_add, Nat.add_comm, run_succ, next_of_step (comp_step_inl_of_halted h'),
      comp_run_inr]
    rfl
  | succ t ih =>
    cases hc : M₁.step c with
    | none =>
      refine ⟨0, Nat.zero_le _, fun s => ?_⟩
      rw [run_of_halted hc, Nat.zero_add, Nat.add_comm, run_succ,
        next_of_step (comp_step_inl_of_halted hc), comp_run_inr]
    | some c' =>
      rw [run_succ, next_of_step hc] at h
      obtain ⟨t', ht', hrun⟩ := ih h
      refine ⟨t' + 1, Nat.succ_le_succ ht', fun s => ?_⟩
      have e : t' + 1 + 1 + s = t' + 1 + s + 1 := by omega
      rw [run_succ t c, next_of_step hc, e, run_succ,
        next_of_step (comp_step_inl_of_step hc)]
      exact hrun s

/-- If `M₁` halts within `t` steps and `M₂`, started on the tape left by `M₁`,
halts within `s` further steps, then every run of the composite of length at
least `t + 1 + s` ends in the final configuration of `M₂`. -/
theorem comp_run_of_halted {t s N : ℕ} {c : Cfg M₁.State} (h₁ : M₁.Halted (M₁.run t c))
    (h₂ : M₂.Halted (M₂.run s ⟨M₂.start, (M₁.run t c).tape⟩)) (hN : t + 1 + s ≤ N) :
    (comp M₁ M₂).run N (inlCfg c) = inrCfg (M₂.run s ⟨M₂.start, (M₁.run t c).tape⟩) := by
  obtain ⟨t', ht', hrun⟩ := exists_comp_run_inl (M₂ := M₂) h₁
  have hh : (comp M₁ M₂).Halted ((comp M₁ M₂).run (t' + 1 + s) (inlCfg c)) := by
    rw [hrun]
    exact comp_halted_inr.2 h₂
  rw [run_eq_of_halted_of_le hh (by omega), hrun]

variable {f g : Word → Word} {T₁ T₂ T : ℕ → ℕ}

/-- The run of the composite on input `x`, when `M₁` computes `f`. -/
theorem comp_run_init (h₁ : M₁.Computes f T₁) {x : Word} {s N : ℕ}
    (h₂ : M₂.HaltsIn s (f x)) (hN : T₁ x.length + 1 + s ≤ N) :
    (comp M₁ M₂).run N ((comp M₁ M₂).init x) = inrCfg (M₂.run s (M₂.init (f x))) := by
  have e : (⟨M₂.start, (M₁.run (T₁ x.length) (M₁.init x)).tape⟩ : Cfg M₂.State) =
      M₂.init (f x) := by
    rw [(h₁ x).2]
    rfl
  have hrun := comp_run_of_halted (M₂ := M₂) (s := s) (h₁ x).1 (by rw [e]; exact h₂) hN
  rw [e] at hrun
  exact hrun

/-! ### Composition of computed functions -/

/-- **Composition.** If `M₁` computes `f` in time `T₁` and `M₂` computes `g` in
time `T₂`, then `TM.comp M₁ M₂` computes `g ∘ f` in any time `T` with
`T₁(|x|) + 1 + T₂(|f x|) ≤ T(|x|)`. -/
theorem Computes.comp (h₁ : M₁.Computes f T₁) (h₂ : M₂.Computes g T₂)
    (hT : ∀ x : Word, T₁ x.length + 1 + T₂ (f x).length ≤ T x.length) :
    (TM.comp M₁ M₂).Computes (g ∘ f) T := by
  intro x
  have hrun := comp_run_init h₁ (h₂ (f x)).1 (hT x)
  constructor
  · unfold HaltsIn
    rw [hrun]
    exact comp_halted_inr.2 (h₂ (f x)).1
  · rw [hrun]
    exact (h₂ (f x)).2

/-- If `M₁` computes `f` and `M₂` always halts, so does the composite. -/
theorem comp_runsInTime (h₁ : M₁.Computes f T₁) (h₂ : M₂.RunsInTime T₂)
    (hT : ∀ x : Word, T₁ x.length + 1 + T₂ (f x).length ≤ T x.length) :
    (comp M₁ M₂).RunsInTime T := by
  intro x
  unfold HaltsIn
  rw [comp_run_init h₁ (h₂ (f x)) (hT x)]
  exact comp_halted_inr.2 (h₂ (f x))

/-- If `M₁` computes `f` and `M₂` always halts, the composite accepts the
preimage under `f` of the language of `M₂`. -/
theorem mem_comp_language (h₁ : M₁.Computes f T₁) (h₂ : M₂.RunsInTime T₂)
    (hT : ∀ x : Word, T₁ x.length + 1 + T₂ (f x).length ≤ T x.length) (x : Word) :
    x ∈ (comp M₁ M₂).language ↔ f x ∈ M₂.language := by
  rw [(comp_runsInTime h₁ h₂ hT).mem_language_iff, h₂.mem_language_iff,
    comp_run_init h₁ (h₂ (f x)) (hT x)]
  exact Iff.rfl

end TM

end Complexity
