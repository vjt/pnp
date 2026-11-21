import PNP.Data.FinEnum
import PNP.Machine.Tape

/-!
# Turing machines

Deterministic single-tape Turing machines over the binary alphabet, with a
small-step semantics, time-bounded runs, acceptance and computed functions.

## Main definitions

* `Complexity.TM`: a deterministic single-tape Turing machine.
* `Complexity.Cfg`: configurations (state and tape).
* `Complexity.TM.step`: the partial one-step transition function.
* `Complexity.TM.run`: the total `t`-step run, which idles on halted
  configurations.
* `Complexity.TM.HaltsIn`, `Complexity.TM.RunsInTime`: time bounds.
* `Complexity.TM.Accepts`, `Complexity.TM.language`: acceptance.
* `Complexity.TM.Computes`: `M` computes the function `f` within a time bound.
* `Complexity.TM.compl`: the machine with accepting and rejecting states swapped.

## Main results

* `Complexity.TM.run_eq_of_halted_of_le`: a halted run is stable.
* `Complexity.TM.accepts_iff_of_haltsIn`: acceptance can be read off at any time
  at which the machine has halted (determinism).
* `Complexity.TM.mem_language_compl`: swapping the accepting states complements
  the language of a machine that always halts.
* `Complexity.TM.Computes.length_le`: the output of a machine is at most as long
  as its input plus its running time.

## Implementation notes

A machine halts when its transition function is undefined, as in Mathlib's
`Turing.TM0`. Acceptance is a property of the halting state. A machine computes
`f` if on input `x` it halts in *standard configuration*: tape `Tape.ofWord (f x)`,
head on the first symbol. Thanks to the normal form of tapes this is an equation,
and it is what makes sequential composition (`PNP.Machine.Compose`) a matter of
identifying the final configuration of one machine with the initial
configuration of the next.

The state space is an arbitrary finitely enumerated type rather than `Fin n`,
which keeps constructions such as sums of state spaces free of index arithmetic.

## References

* [Tur36] A. M. Turing, *On computable numbers, with an application to the
  Entscheidungsproblem*, Proc. London Math. Soc. 42 (1936).
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Definitions
  3.3, 7.1 and 7.28.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Definitions 1.1 and 1.3.
-/

set_option autoImplicit false

namespace Complexity

/-- A configuration over the state space `Q`: the current state and the tape. -/
structure Cfg (Q : Type) where
  state : Q
  tape : Tape

/-- A deterministic single-tape Turing machine over the binary alphabet. -/
structure TM where
  /-- The state space. -/
  State : Type
  [finEnum : FinEnum State]
  /-- The initial state. -/
  start : State
  /-- The accepting states. Only relevant for halting states. -/
  accepting : State → Bool
  /-- The transition function. The machine halts where it is undefined. -/
  δ : State → Symbol → Option (State × Symbol × Dir)

namespace TM

attribute [instance] TM.finEnum

variable (M : TM)

/-- One step of the machine, or `none` if the configuration is halting. -/
def step (c : Cfg M.State) : Option (Cfg M.State) :=
  (M.δ c.state c.tape.head).map fun r => ⟨r.1, (c.tape.write r.2.1).move r.2.2⟩

/-- A configuration is halted if no transition applies. -/
def Halted (c : Cfg M.State) : Prop := M.step c = none

/-- One step of the machine, idling on halted configurations. -/
def next (c : Cfg M.State) : Cfg M.State := (M.step c).getD c

/-- The configuration after `t` steps. -/
def run : ℕ → Cfg M.State → Cfg M.State
  | 0, c => c
  | t + 1, c => run t (M.next c)

/-- The initial configuration on input `x`. -/
def init (x : Word) : Cfg M.State := ⟨M.start, Tape.ofWord x⟩

/-- `M` halts on input `x` within `t` steps. -/
def HaltsIn (t : ℕ) (x : Word) : Prop := M.Halted (M.run t (M.init x))

/-- `M` halts on every input `x` within `T x.length` steps. -/
def RunsInTime (T : ℕ → ℕ) : Prop := ∀ x : Word, M.HaltsIn (T x.length) x

/-- `M` halts on `x` within `t` steps, in an accepting state. -/
def AcceptsIn (t : ℕ) (x : Word) : Prop :=
  M.HaltsIn t x ∧ M.accepting (M.run t (M.init x)).state = true

/-- `M` accepts `x`. -/
def Accepts (x : Word) : Prop := ∃ t, M.AcceptsIn t x

/-- The language accepted by `M`. -/
def language : Language := fun x => M.Accepts x

/-- `M` computes `f` in time `T`: on input `x` it halts within `T x.length`
steps in standard configuration, with `f x` on the tape. -/
def Computes (f : Word → Word) (T : ℕ → ℕ) : Prop :=
  ∀ x : Word, M.HaltsIn (T x.length) x ∧
    (M.run (T x.length) (M.init x)).tape = Tape.ofWord (f x)

variable {M}
variable {c : Cfg M.State} {s t : ℕ} {x : Word}

/-! ### The step function -/

theorem step_eq_none_iff : M.step c = none ↔ M.δ c.state c.tape.head = none := by
  unfold step
  cases M.δ c.state c.tape.head <;> simp

theorem halted_iff : M.Halted c ↔ M.δ c.state c.tape.head = none := step_eq_none_iff

theorem step_of_δ {q : M.State} {a : Symbol} {d : Dir}
    (h : M.δ c.state c.tape.head = some (q, a, d)) :
    M.step c = some ⟨q, (c.tape.write a).move d⟩ := by
  unfold step
  rw [h]
  rfl

theorem next_of_halted (h : M.Halted c) : M.next c = c := by
  unfold next
  rw [show M.step c = none from h]
  rfl

theorem next_of_step {c' : Cfg M.State} (h : M.step c = some c') : M.next c = c' := by
  unfold next
  rw [h]
  rfl

theorem length_tape_step_le {c' : Cfg M.State} (h : M.step c = some c') :
    c'.tape.length ≤ c.tape.length + 1 := by
  unfold step at h
  cases hδ : M.δ c.state c.tape.head with
  | none => rw [hδ] at h; exact Option.noConfusion h
  | some r => rw [hδ] at h; cases h; exact Tape.length_write_move_le _ _ _

theorem length_tape_next_le (c : Cfg M.State) :
    (M.next c).tape.length ≤ c.tape.length + 1 := by
  cases h : M.step c with
  | none => rw [next_of_halted h]; exact Nat.le_succ _
  | some c' => rw [next_of_step h]; exact length_tape_step_le h

/-! ### Runs -/

@[simp] theorem run_zero (c : Cfg M.State) : M.run 0 c = c := rfl

theorem run_succ (t : ℕ) (c : Cfg M.State) : M.run (t + 1) c = M.run t (M.next c) := rfl

theorem run_add (s t : ℕ) (c : Cfg M.State) : M.run (s + t) c = M.run t (M.run s c) := by
  induction s generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ s ih => rw [Nat.add_right_comm, run_succ, ih, run_succ]

theorem run_succ' (t : ℕ) (c : Cfg M.State) : M.run (t + 1) c = M.next (M.run t c) :=
  run_add t 1 c

theorem run_of_halted (h : M.Halted c) (t : ℕ) : M.run t c = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, next_of_halted h, ih]

/-- Once a run has halted it does not change any more. -/
theorem run_eq_of_halted_of_le (h : M.Halted (M.run s c)) (hst : s ≤ t) :
    M.run t c = M.run s c := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hst
  rw [run_add, run_of_halted h]

theorem halted_run_of_le (h : M.Halted (M.run s c)) (hst : s ≤ t) :
    M.Halted (M.run t c) := by
  rw [run_eq_of_halted_of_le h hst]
  exact h

/-- The tape grows by at most one cell per step. -/
theorem length_tape_run_le (t : ℕ) (c : Cfg M.State) :
    (M.run t c).tape.length ≤ c.tape.length + t := by
  induction t generalizing c with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    rw [run_succ]
    have h₁ := ih (M.next c)
    have h₂ := length_tape_next_le c
    omega

/-! ### Time bounds and acceptance -/

theorem HaltsIn.mono (h : M.HaltsIn s x) (hst : s ≤ t) : M.HaltsIn t x :=
  halted_run_of_le h hst

theorem RunsInTime.mono {T T' : ℕ → ℕ} (h : M.RunsInTime T) (hT : ∀ n, T n ≤ T' n) :
    M.RunsInTime T' :=
  fun x => (h x).mono (hT x.length)

theorem AcceptsIn.mono (h : M.AcceptsIn s x) (hst : s ≤ t) : M.AcceptsIn t x :=
  ⟨h.1.mono hst, by rw [run_eq_of_halted_of_le h.1 hst]; exact h.2⟩

theorem AcceptsIn.accepts (h : M.AcceptsIn t x) : M.Accepts x := ⟨t, h⟩

theorem mem_language : x ∈ M.language ↔ M.Accepts x := Iff.rfl

/-- Determinism: if `M` has halted on `x` by time `t`, then it accepts `x` iff
the state reached at time `t` is accepting. -/
theorem accepts_iff_of_haltsIn (h : M.HaltsIn t x) :
    M.Accepts x ↔ M.accepting (M.run t (M.init x)).state = true := by
  constructor
  · rintro ⟨s, hs, ha⟩
    rcases Nat.le_total s t with hst | hts
    · rw [run_eq_of_halted_of_le hs hst]; exact ha
    · rw [← run_eq_of_halted_of_le h hts]; exact ha
  · intro ha
    exact ⟨t, h, ha⟩

/-- A halting run that ends in an accepting state witnesses membership. -/
theorem mem_language_of_run (h : M.HaltsIn t x)
    (ha : M.accepting (M.run t (M.init x)).state = true) : x ∈ M.language :=
  ⟨t, h, ha⟩

/-- A halting run that ends in a rejecting state witnesses non-membership. -/
theorem not_mem_language_of_run (h : M.HaltsIn t x)
    (ha : M.accepting (M.run t (M.init x)).state = false) : x ∉ M.language := by
  intro hx
  rw [(accepts_iff_of_haltsIn h).1 hx] at ha
  exact Bool.noConfusion ha

theorem RunsInTime.mem_language_iff {T : ℕ → ℕ} (h : M.RunsInTime T) (x : Word) :
    x ∈ M.language ↔ M.accepting (M.run (T x.length) (M.init x)).state = true :=
  accepts_iff_of_haltsIn (h x)

/-! ### Computed functions -/

theorem Computes.runsInTime {f : Word → Word} {T : ℕ → ℕ} (h : M.Computes f T) :
    M.RunsInTime T :=
  fun x => (h x).1

theorem Computes.mono {f : Word → Word} {T T' : ℕ → ℕ} (h : M.Computes f T)
    (hT : ∀ n, T n ≤ T' n) : M.Computes f T' :=
  fun x => ⟨(h x).1.mono (hT x.length), by
    rw [run_eq_of_halted_of_le (h x).1 (hT x.length)]; exact (h x).2⟩

/-- The output of a machine is at most as long as its input plus its running
time: a step extends the tape by at most one cell. -/
theorem Computes.length_le {f : Word → Word} {T : ℕ → ℕ} (h : M.Computes f T) (x : Word) :
    (f x).length ≤ x.length + 1 + T x.length := by
  have h₁ := length_tape_run_le (T x.length) (M.init x)
  rw [(h x).2] at h₁
  have h₂ := Tape.length_le_length_ofWord (f x)
  have h₃ : (M.init x).tape.length ≤ x.length + 1 := Tape.length_ofWord_le x
  omega

/-- A machine determines the function it computes. -/
theorem Computes.unique {f g : Word → Word} {T T' : ℕ → ℕ} (hf : M.Computes f T)
    (hg : M.Computes g T') (x : Word) : f x = g x := by
  apply Tape.ofWord_injective
  rw [← (hf x).2, ← (hg x).2]
  rcases Nat.le_total (T x.length) (T' x.length) with h | h
  · exact congrArg Cfg.tape (run_eq_of_halted_of_le (hf x).1 h).symm
  · exact congrArg Cfg.tape (run_eq_of_halted_of_le (hg x).1 h)

/-! ### Complementation -/

variable (M) in
/-- The machine `M` with accepting and rejecting states swapped. -/
def compl : TM := { M with accepting := fun q => !M.accepting q }

@[simp] theorem compl_step (c : Cfg M.State) : M.compl.step c = M.step c := rfl

@[simp] theorem compl_next (c : Cfg M.State) : M.compl.next c = M.next c := rfl

@[simp] theorem compl_init (x : Word) : M.compl.init x = M.init x := rfl

theorem compl_halted : M.compl.Halted c ↔ M.Halted c := Iff.rfl

@[simp] theorem compl_run (t : ℕ) (c : Cfg M.State) : M.compl.run t c = M.run t c := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    show M.compl.run t (M.next c) = M.run t (M.next c)
    exact ih _

theorem compl_haltsIn : M.compl.HaltsIn t x ↔ M.HaltsIn t x := by
  show M.Halted (M.compl.run t (M.init x)) ↔ M.Halted (M.run t (M.init x))
  rw [compl_run]

theorem compl_runsInTime {T : ℕ → ℕ} (h : M.RunsInTime T) : M.compl.RunsInTime T :=
  fun x => compl_haltsIn.2 (h x)

/-- For a machine that always halts, swapping the accepting states complements
the accepted language. -/
theorem mem_language_compl {T : ℕ → ℕ} (h : M.RunsInTime T) (x : Word) :
    x ∈ M.compl.language ↔ x ∉ M.language := by
  have h₁ := (compl_runsInTime h).mem_language_iff x
  rw [compl_run] at h₁
  rw [h₁, h.mem_language_iff x]
  show (!M.accepting (M.run (T x.length) (M.init x)).state) = true ↔
    ¬M.accepting (M.run (T x.length) (M.init x)).state = true
  cases M.accepting (M.run (T x.length) (M.init x)).state <;> simp

/-! ### The identity machine -/

/-- The machine that halts immediately. It computes the identity in time `0`. -/
def idle : TM where
  State := Unit
  start := ()
  accepting := fun _ => true
  δ := fun _ _ => none

theorem idle_halted (c : Cfg idle.State) : idle.Halted c := rfl

theorem idle_computes (T : ℕ → ℕ) : idle.Computes id T := by
  intro x
  have h := run_of_halted (idle_halted (idle.init x)) (T x.length)
  exact ⟨by unfold HaltsIn; rw [h]; exact idle_halted _, by rw [h]; rfl⟩

theorem idle_runsInTime (T : ℕ → ℕ) : idle.RunsInTime T := (idle_computes T).runsInTime

theorem mem_language_idle (x : Word) : x ∈ idle.language := ⟨0, rfl, rfl⟩

end TM

end Complexity
