import PNP.Machine.TM

/-!
# Machines with an auxiliary tape

A Turing machine with a second, read-only *auxiliary* tape next to its work
tape. The auxiliary tape holds additional input: a certificate, a witness or an
advice string. This is the machine model underlying verifiers.

## Main definitions

* `Complexity.AuxTM`: a Turing machine with a read-only auxiliary tape.
* `Complexity.AuxCfg`: configurations (state, work tape, auxiliary tape).
* `Complexity.AuxTM.step`, `Complexity.AuxTM.run`: the semantics, as for `TM`.
* `Complexity.AuxTM.RunsInTime`: the machine halts within the bound for every
  input and every content of the auxiliary tape.
* `Complexity.AuxTM.language`: the language accepted within a resource bound.
* `Complexity.TM.toAuxTM`: a single-tape machine as an auxiliary-tape machine
  that never looks at its auxiliary tape.

## Main results

* `Complexity.AuxTM.run_eq_of_halted_of_le`: a halted run is stable.
* `Complexity.AuxTM.language_mono`: the accepted language grows with the bound.
* `Complexity.TM.toAuxTM_run`: `M.toAuxTM` simulates `M` step by step.
* `Complexity.TM.mem_toAuxTM_language`: `M.toAuxTM` and `M` accept the same
  language.

## Implementation notes

The auxiliary tape is read-only: a transition may move its head but cannot write
to it. The input is placed on the work tape, as for `TM`.

`AuxTM.language V T` is the language of `V` relative to the resource bound `T`,
which limits both the running time and the length of the auxiliary input that is
taken into account, as in [Sip13, Definition 7.18] and [AB09, Definition 2.1]. A
machine that halts within `T` steps cannot read more than `T` cells of its
auxiliary tape, so using one bound for both loses nothing.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Definitions 2.1 and 4.19 (certificate tapes).
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Definition 7.18.
-/

set_option autoImplicit false

namespace Complexity

/-- A configuration of an auxiliary-tape machine over the state space `Q`. -/
structure AuxCfg (Q : Type) where
  state : Q
  work : Tape
  aux : Tape

/-- A deterministic Turing machine with a work tape and a read-only auxiliary
tape. -/
structure AuxTM where
  /-- The state space. -/
  State : Type
  [finEnum : FinEnum State]
  /-- The initial state. -/
  start : State
  /-- The accepting states. -/
  accepting : State → Bool
  /-- The transition function: from the state and the two scanned symbols to the
  new state, the symbol written on the work tape, and the two head movements. -/
  δ : State → Symbol → Symbol → Option (State × Symbol × Dir × Dir)

namespace AuxTM

attribute [instance] AuxTM.finEnum

variable (V : AuxTM)

/-- One step of the machine, or `none` if the configuration is halting. -/
def step (c : AuxCfg V.State) : Option (AuxCfg V.State) :=
  (V.δ c.state c.work.head c.aux.head).map fun r =>
    ⟨r.1, (c.work.write r.2.1).move r.2.2.1, c.aux.move r.2.2.2⟩

/-- A configuration is halted if no transition applies. -/
def Halted (c : AuxCfg V.State) : Prop := V.step c = none

/-- One step of the machine, idling on halted configurations. -/
def next (c : AuxCfg V.State) : AuxCfg V.State := (V.step c).getD c

/-- The configuration after `t` steps. -/
def run : ℕ → AuxCfg V.State → AuxCfg V.State
  | 0, c => c
  | t + 1, c => run t (V.next c)

/-- The initial configuration on input `x` with auxiliary input `w`. -/
def init (x w : Word) : AuxCfg V.State := ⟨V.start, Tape.ofWord x, Tape.ofWord w⟩

/-- `V` halts on input `x` with auxiliary input `w` within `t` steps. -/
def HaltsIn (t : ℕ) (x w : Word) : Prop := V.Halted (V.run t (V.init x w))

/-- `V` halts within `T x.length` steps on every input `x`, whatever the content
of the auxiliary tape. -/
def RunsInTime (T : ℕ → ℕ) : Prop := ∀ x w : Word, V.HaltsIn (T x.length) x w

/-- `V` halts on `(x, w)` within `t` steps, in an accepting state. -/
def AcceptsIn (t : ℕ) (x w : Word) : Prop :=
  V.HaltsIn t x w ∧ V.accepting (V.run t (V.init x w)).state = true

/-- The language of `V` relative to the resource bound `T`: the inputs `x`
accepted within `T x.length` steps for an auxiliary input of length at most
`T x.length`. -/
def language (T : ℕ → ℕ) : Language :=
  fun x => ∃ w : Word, w.length ≤ T x.length ∧ V.AcceptsIn (T x.length) x w

variable {V}
variable {c : AuxCfg V.State} {s t : ℕ} {x w : Word}

theorem halted_iff : V.Halted c ↔ V.δ c.state c.work.head c.aux.head = none := by
  unfold Halted step
  cases V.δ c.state c.work.head c.aux.head <;> simp

theorem next_of_halted (h : V.Halted c) : V.next c = c := by
  unfold next
  rw [show V.step c = none from h]
  rfl

theorem next_of_step {c' : AuxCfg V.State} (h : V.step c = some c') : V.next c = c' := by
  unfold next
  rw [h]
  rfl

@[simp] theorem run_zero (c : AuxCfg V.State) : V.run 0 c = c := rfl

theorem run_succ (t : ℕ) (c : AuxCfg V.State) : V.run (t + 1) c = V.run t (V.next c) := rfl

theorem run_add (s t : ℕ) (c : AuxCfg V.State) : V.run (s + t) c = V.run t (V.run s c) := by
  induction s generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ s ih => rw [Nat.add_right_comm, run_succ, ih, run_succ]

theorem run_of_halted (h : V.Halted c) (t : ℕ) : V.run t c = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, next_of_halted h, ih]

/-- Once a run has halted it does not change any more. -/
theorem run_eq_of_halted_of_le (h : V.Halted (V.run s c)) (hst : s ≤ t) :
    V.run t c = V.run s c := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hst
  rw [run_add, run_of_halted h]

/-- The auxiliary tape is read-only: a step changes at most the head position. -/
theorem aux_step_eq {c' : AuxCfg V.State} (h : V.step c = some c') :
    ∃ d : Dir, c'.aux = c.aux.move d := by
  unfold step at h
  cases hδ : V.δ c.state c.work.head c.aux.head with
  | none => rw [hδ] at h; exact Option.noConfusion h
  | some r => rw [hδ] at h; cases h; exact ⟨_, rfl⟩

theorem HaltsIn.mono (h : V.HaltsIn s x w) (hst : s ≤ t) : V.HaltsIn t x w := by
  unfold HaltsIn at h ⊢
  rw [run_eq_of_halted_of_le h hst]
  exact h

theorem RunsInTime.mono {T T' : ℕ → ℕ} (h : V.RunsInTime T) (hT : ∀ n, T n ≤ T' n) :
    V.RunsInTime T' :=
  fun x w => (h x w).mono (hT x.length)

theorem AcceptsIn.mono (h : V.AcceptsIn s x w) (hst : s ≤ t) : V.AcceptsIn t x w :=
  ⟨h.1.mono hst, by rw [run_eq_of_halted_of_le h.1 hst]; exact h.2⟩

theorem mem_language {T : ℕ → ℕ} :
    x ∈ V.language T ↔ ∃ w : Word, w.length ≤ T x.length ∧ V.AcceptsIn (T x.length) x w :=
  Iff.rfl

/-- The accepted language grows with the resource bound. -/
theorem language_mono {T T' : ℕ → ℕ} (hT : ∀ n, T n ≤ T' n) {x : Word}
    (h : x ∈ V.language T) : x ∈ V.language T' :=
  let ⟨w, hw, ha⟩ := h
  ⟨w, Nat.le_trans hw (hT x.length), ha.mono (hT x.length)⟩

end AuxTM

namespace TM

variable (M : TM)

/-- A single-tape machine, viewed as an auxiliary-tape machine that ignores its
auxiliary tape. -/
def toAuxTM : AuxTM where
  State := M.State
  start := M.start
  accepting := M.accepting
  δ := fun q a _ => (M.δ q a).map fun r => (r.1, r.2.1, r.2.2, Dir.stay)

variable {M}

/-- A configuration of `M` together with an auxiliary tape. -/
def withAux (c : Cfg M.State) (u : Tape) : AuxCfg M.toAuxTM.State := ⟨c.state, c.tape, u⟩

theorem toAuxTM_step (c : Cfg M.State) (u : Tape) :
    M.toAuxTM.step (withAux c u) = (M.step c).map fun c' => withAux c' u := by
  show Option.map _ (Option.map _ (M.δ c.state c.tape.head)) = Option.map _ (M.step c)
  unfold step
  cases M.δ c.state c.tape.head <;> rfl

theorem toAuxTM_next (c : Cfg M.State) (u : Tape) :
    M.toAuxTM.next (withAux c u) = withAux (M.next c) u := by
  unfold next AuxTM.next
  rw [toAuxTM_step]
  cases M.step c <;> rfl

/-- `M.toAuxTM` simulates `M` step by step and never touches its auxiliary tape. -/
theorem toAuxTM_run (t : ℕ) (c : Cfg M.State) (u : Tape) :
    M.toAuxTM.run t (withAux c u) = withAux (M.run t c) u := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => rw [AuxTM.run_succ, toAuxTM_next, ih, run_succ]

theorem toAuxTM_halted {c : Cfg M.State} {u : Tape} :
    M.toAuxTM.Halted (withAux c u) ↔ M.Halted c := by
  unfold Halted AuxTM.Halted
  rw [toAuxTM_step]
  cases M.step c with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some c' => exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h⟩

theorem toAuxTM_haltsIn {t : ℕ} {x w : Word} : M.toAuxTM.HaltsIn t x w ↔ M.HaltsIn t x := by
  show M.toAuxTM.Halted (M.toAuxTM.run t (withAux (M.init x) (Tape.ofWord w))) ↔ _
  rw [toAuxTM_run]
  exact toAuxTM_halted

theorem toAuxTM_acceptsIn {t : ℕ} {x w : Word} :
    M.toAuxTM.AcceptsIn t x w ↔ M.AcceptsIn t x := by
  show _ ∧ M.accepting (M.toAuxTM.run t (withAux (M.init x) (Tape.ofWord w))).state = true ↔ _
  rw [toAuxTM_run]
  exact and_congr_left fun _ => toAuxTM_haltsIn

theorem toAuxTM_runsInTime {T : ℕ → ℕ} (h : M.RunsInTime T) : M.toAuxTM.RunsInTime T :=
  fun x _ => toAuxTM_haltsIn.2 (h x)

/-- `M.toAuxTM` accepts, within any time bound for `M`, exactly the language of
`M`: the auxiliary input is irrelevant, so the empty one will do. -/
theorem mem_toAuxTM_language {T : ℕ → ℕ} (h : M.RunsInTime T) (x : Word) :
    x ∈ M.toAuxTM.language T ↔ x ∈ M.language := by
  constructor
  · rintro ⟨w, -, ha⟩
    exact (toAuxTM_acceptsIn.1 ha).accepts
  · intro hx
    exact ⟨[], Nat.zero_le _, toAuxTM_acceptsIn.2 ⟨h x, (accepts_iff_of_haltsIn (h x)).1 hx⟩⟩

end TM

end Complexity
