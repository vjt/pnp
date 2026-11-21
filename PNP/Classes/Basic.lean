import PNP.Poly.Basic
import PNP.Machine.AuxTM

/-!
# The classes P, NP and coNP

## Main definitions

* `Complexity.DTIME`: languages decided by a single-tape machine within a given
  time bound.
* `Complexity.P`: languages decided in polynomial time.
* `Complexity.NP`: languages with polynomial-time verifiers and polynomially
  bounded certificates.
* `Complexity.coNP`: complements of languages in NP.

## Main results

* `Complexity.P_subset_NP`: P ⊆ NP.
* `Complexity.compl_mem_P`: P is closed under complement.
* `Complexity.P_subset_coNP`: P ⊆ coNP.
* `Complexity.DTIME_subset_P`: `DTIME T ⊆ P` for polynomially bounded `T`.

## Implementation notes

`P` is defined with deciders: a machine that halts within a polynomial bound on
every input and accepts exactly the words of the language
[Sip13, Definition 7.12]. `NP` is defined with verifiers
[Sip13, Definitions 7.18 and 7.19; AB09, Definition 2.1]: an auxiliary-tape
machine `V` and a polynomial bound `T` such that `x ∈ L` iff `V` accepts `x`
within `T(|x|)` steps for some certificate of length at most `T(|x|)` on the
auxiliary tape. The certificate tape formulation is equivalent to the one with
pairs `⟨x, c⟩` on a single tape and avoids fixing a pairing function at this
stage.

The inclusion P ⊆ NP is proved by letting the verifier ignore its certificate
(`TM.toAuxTM`).

## References

* [Cob65] A. Cobham, *The intrinsic computational difficulty of functions*, 1965.
* [Edm65] J. Edmonds, *Paths, trees, and flowers*, Canad. J. Math. 17 (1965).
* [Coo71] S. A. Cook, *The complexity of theorem-proving procedures*, STOC 1971.
* [Lev73] L. A. Levin, *Universal sequential search problems*, Probl. Peredachi
  Inf. 9 (1973).
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, §7.2–7.3.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Chapters 1–2.
-/

set_option autoImplicit false

namespace Complexity

/-- `DTIME T` is the class of languages decided by a single-tape machine that
halts within `T n` steps on inputs of length `n`. -/
def DTIME (T : ℕ → ℕ) : ComplexityClass :=
  fun L => ∃ M : TM, M.RunsInTime T ∧ ∀ x, x ∈ M.language ↔ x ∈ L

/-- **P**: the class of languages decided in polynomial time. -/
def P : ComplexityClass :=
  fun L => ∃ (M : TM) (T : ℕ → ℕ), IsPolyBounded T ∧ M.RunsInTime T ∧
    ∀ x, x ∈ M.language ↔ x ∈ L

/-- **NP**: the class of languages with a polynomial-time verifier and
polynomially bounded certificates. -/
def NP : ComplexityClass :=
  fun L => ∃ (V : AuxTM) (T : ℕ → ℕ), IsPolyBounded T ∧ V.RunsInTime T ∧
    ∀ x, x ∈ V.language T ↔ x ∈ L

/-- **coNP**: the class of complements of languages in NP. -/
def coNP : ComplexityClass := NP.co

variable {L L₁ L₂ : Language} {T : ℕ → ℕ}

theorem mem_DTIME_iff :
    L ∈ DTIME T ↔ ∃ M : TM, M.RunsInTime T ∧ ∀ x, x ∈ M.language ↔ x ∈ L := Iff.rfl

theorem mem_P_iff :
    L ∈ P ↔ ∃ (M : TM) (T : ℕ → ℕ), IsPolyBounded T ∧ M.RunsInTime T ∧
      ∀ x, x ∈ M.language ↔ x ∈ L := Iff.rfl

theorem mem_NP_iff :
    L ∈ NP ↔ ∃ (V : AuxTM) (T : ℕ → ℕ), IsPolyBounded T ∧ V.RunsInTime T ∧
      ∀ x, x ∈ V.language T ↔ x ∈ L := Iff.rfl

theorem mem_coNP_iff : L ∈ coNP ↔ L.compl ∈ NP := Iff.rfl

/-! ### Deterministic time -/

theorem DTIME_mono {T T' : ℕ → ℕ} (h : ∀ n, T n ≤ T' n) : DTIME T ⊆ DTIME T' :=
  fun _ ⟨M, hM, hL⟩ => ⟨M, hM.mono h, hL⟩

/-- `DTIME T ⊆ P` for every polynomially bounded `T`. -/
theorem DTIME_subset_P (hT : IsPolyBounded T) : DTIME T ⊆ P :=
  fun _ ⟨M, hM, hL⟩ => ⟨M, T, hT, hM, hL⟩

theorem mem_P_iff_exists_DTIME : L ∈ P ↔ ∃ T, IsPolyBounded T ∧ L ∈ DTIME T :=
  ⟨fun ⟨M, T, hT, hM, hL⟩ => ⟨T, hT, M, hM, hL⟩, fun ⟨_, hT, h⟩ => DTIME_subset_P hT h⟩

/-- Membership in a class defined by machines only depends on the words of the
language. -/
theorem mem_P_of_iff (h : ∀ x, x ∈ L₁ ↔ x ∈ L₂) (h₁ : L₁ ∈ P) : L₂ ∈ P :=
  let ⟨M, T, hT, hM, hL⟩ := h₁
  ⟨M, T, hT, hM, fun x => (hL x).trans (h x)⟩

theorem mem_NP_of_iff (h : ∀ x, x ∈ L₁ ↔ x ∈ L₂) (h₁ : L₁ ∈ NP) : L₂ ∈ NP :=
  let ⟨V, T, hT, hV, hL⟩ := h₁
  ⟨V, T, hT, hV, fun x => (hL x).trans (h x)⟩

/-! ### P ⊆ NP -/

/-- **P ⊆ NP.** A decider is a verifier that ignores its certificate. -/
theorem P_subset_NP : P ⊆ NP :=
  fun _ ⟨M, T, hT, hM, hL⟩ =>
    ⟨M.toAuxTM, T, hT, TM.toAuxTM_runsInTime hM,
      fun x => (TM.mem_toAuxTM_language hM x).trans (hL x)⟩

/-! ### Closure properties of P -/

/-- P is closed under complement: swap the accepting and rejecting states. -/
theorem compl_mem_P (h : L ∈ P) : L.compl ∈ P :=
  let ⟨M, T, hT, hM, hL⟩ := h
  ⟨M.compl, T, hT, TM.compl_runsInTime hM,
    fun x => (TM.mem_language_compl hM x).trans (not_congr (hL x))⟩

/-- **P ⊆ coNP.** -/
theorem P_subset_coNP : P ⊆ coNP :=
  fun _ h => P_subset_NP (compl_mem_P h)

theorem P_subset_NP_inter_coNP (h : L ∈ P) : L ∈ NP ∧ L ∈ coNP :=
  ⟨P_subset_NP h, P_subset_coNP h⟩

/-- The language of all words is in P. -/
theorem univ_mem_P : Language.univ ∈ P :=
  ⟨TM.idle, fun _ => 0, IsPolyBounded.const 0, TM.idle_runsInTime _,
    fun x => ⟨fun _ => trivial, fun _ => TM.mem_language_idle x⟩⟩

/-- The empty language is in P. -/
theorem empty_mem_P : (∅ : Language) ∈ P :=
  mem_P_of_iff
    (fun x => ⟨fun (h : x ∉ Language.univ) => h trivial,
      fun (h : x ∈ (∅ : Language)) => absurd h Language.not_mem_empty⟩)
    (compl_mem_P univ_mem_P)

theorem univ_mem_NP : Language.univ ∈ NP := P_subset_NP univ_mem_P

theorem empty_mem_NP : (∅ : Language) ∈ NP := P_subset_NP empty_mem_P

end Complexity
