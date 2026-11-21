import PNP.Reduction.Basic

/-!
# Examples of Turing machines

Three small machines, used to test the definitions of `PNP.Machine.TM` on
concrete inputs.

## Main definitions

* `Complexity.TM.parity`: accepts the words with an even number of ones.
* `Complexity.TM.containsOne`: accepts the words that contain a one.
* `Complexity.TM.flipFirst`: negates the first bit of its input.
* `Complexity.TM.flipFirstFn`: the function computed by `flipFirst`.

## Main results

* `Complexity.TM.flipFirst_computes`: `flipFirst` computes `flipFirstFn` in one
  step.
* `Complexity.TM.polyTimeComputable_flipFirstFn`: hence `flipFirstFn` is
  polynomial-time computable.
* Test vectors: for a fixed set of inputs, membership in the languages of
  `parity` and `containsOne`, halting times of `parity`, and the output tape of
  `flipFirst`.

## Implementation notes

The test vectors are proved by evaluating the machines in the kernel
(`rfl`), through `TM.mem_language_of_run` and `TM.not_mem_language_of_run`.
-/

set_option autoImplicit false

namespace Complexity

namespace TM

/-- A machine that accepts the words with an even number of ones. It scans the
input once from left to right, keeping the parity in its state. -/
def parity : TM where
  State := Bool
  start := false
  accepting := fun q => !q
  δ := fun q a =>
    match a with
    | none => none
    | some b => some (q != b, some b, Dir.right)

/-- A machine that accepts the words containing a one. It scans the input from
left to right and stops at the first one. -/
def containsOne : TM where
  State := Bool
  start := false
  accepting := fun q => q
  δ := fun q a =>
    match q, a with
    | false, some false => some (false, some false, Dir.right)
    | false, some true => some (true, some true, Dir.stay)
    | _, _ => none

/-- A machine that negates the first bit of its input and halts. -/
def flipFirst : TM where
  State := Bool
  start := false
  accepting := fun _ => true
  δ := fun q a =>
    match q, a with
    | false, some b => some (true, some (!b), Dir.stay)
    | _, _ => none

/-- Negate the first bit of a word. -/
def flipFirstFn : Word → Word
  | [] => []
  | b :: w => (!b) :: w

/-- `flipFirst` computes `flipFirstFn` in one step. -/
theorem flipFirst_computes : flipFirst.Computes flipFirstFn fun _ => 1 := by
  intro x
  cases x with
  | nil => exact ⟨rfl, rfl⟩
  | cons b w => cases b <;> exact ⟨rfl, rfl⟩

theorem polyTimeComputable_flipFirstFn : PolyTimeComputable flipFirstFn :=
  ⟨flipFirst, fun _ => 1, IsPolyBounded.const 1, flipFirst_computes⟩

theorem flipFirstFn_flipFirstFn (x : Word) : flipFirstFn (flipFirstFn x) = x := by
  cases x with
  | nil => rfl
  | cons b w => cases b <;> rfl

theorem length_flipFirstFn (x : Word) : (flipFirstFn x).length = x.length := by
  cases x <;> rfl

/-! ### Test vectors for `parity` -/

theorem mem_language_parity_nil : [] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 0) rfl rfl

theorem mem_language_parity_0 : [false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 1) rfl rfl

theorem not_mem_language_parity_1 : [true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 1) rfl rfl

theorem mem_language_parity_00 : [false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 2) rfl rfl

theorem not_mem_language_parity_01 : [false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 2) rfl rfl

theorem not_mem_language_parity_10 : [true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 2) rfl rfl

theorem mem_language_parity_11 : [true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 2) rfl rfl

theorem mem_language_parity_000 : [false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 3) rfl rfl

theorem not_mem_language_parity_001 : [false, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 3) rfl rfl

theorem not_mem_language_parity_010 : [false, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 3) rfl rfl

theorem mem_language_parity_011 : [false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 3) rfl rfl

theorem not_mem_language_parity_100 : [true, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 3) rfl rfl

theorem mem_language_parity_101 : [true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 3) rfl rfl

theorem not_mem_language_parity_111 : [true, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 3) rfl rfl

theorem mem_language_parity_0000 : [false, false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem not_mem_language_parity_0001 : [false, false, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem not_mem_language_parity_0010 : [false, false, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem mem_language_parity_0011 : [false, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem not_mem_language_parity_0100 : [false, true, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem mem_language_parity_0101 : [false, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem mem_language_parity_0110 : [false, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem not_mem_language_parity_1000 : [true, false, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem mem_language_parity_1001 : [true, false, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem mem_language_parity_1010 : [true, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem not_mem_language_parity_1011 : [true, false, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem mem_language_parity_1100 : [true, true, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem not_mem_language_parity_1101 : [true, true, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem not_mem_language_parity_1110 : [true, true, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem mem_language_parity_1111 : [true, true, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 4) rfl rfl

theorem not_mem_language_parity_00001 :
    [false, false, false, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_00011 : [false, false, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_00100 :
    [false, false, true, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_00101 : [false, false, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_00110 : [false, false, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_00111 :
    [false, false, true, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_01010 : [false, true, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_01101 :
    [false, true, true, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_01110 :
    [false, true, true, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_01111 : [false, true, true, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_10000 :
    [true, false, false, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_10001 : [true, false, false, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_10010 : [true, false, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_10011 :
    [true, false, false, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_10100 : [true, false, true, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_10101 :
    [true, false, true, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_10110 :
    [true, false, true, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_10111 : [true, false, true, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_11011 : [true, true, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_11100 :
    [true, true, true, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_11101 : [true, true, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_11110 : [true, true, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem not_mem_language_parity_11111 :
    [true, true, true, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 5) rfl rfl

theorem mem_language_parity_000000 :
    [false, false, false, false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_000101 :
    [false, false, false, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_000110 :
    [false, false, false, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_001000 :
    [false, false, true, false, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_001001 :
    [false, false, true, false, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_001110 :
    [false, false, true, true, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_001111 :
    [false, false, true, true, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_010010 :
    [false, true, false, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_010011 :
    [false, true, false, false, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_011001 :
    [false, true, true, false, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_011010 :
    [false, true, true, false, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_011100 :
    [false, true, true, true, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_011101 :
    [false, true, true, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_011110 :
    [false, true, true, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_011111 :
    [false, true, true, true, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_100010 :
    [true, false, false, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_100110 :
    [true, false, false, true, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_100111 :
    [true, false, false, true, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_101001 :
    [true, false, true, false, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_101010 :
    [true, false, true, false, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_101100 :
    [true, false, true, true, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_101110 :
    [true, false, true, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_110101 :
    [true, true, false, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_110110 :
    [true, true, false, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_111011 :
    [true, true, true, false, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem not_mem_language_parity_111110 :
    [true, true, true, true, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 6) rfl rfl

theorem mem_language_parity_0000000 :
    [false, false, false, false, false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_0000001 :
    [false, false, false, false, false, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0000101 :
    [false, false, false, false, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0000110 :
    [false, false, false, false, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_0001000 :
    [false, false, false, true, false, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0001010 :
    [false, false, false, true, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_0001101 :
    [false, false, false, true, true, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0001111 :
    [false, false, false, true, true, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0011000 :
    [false, false, true, true, false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_0011111 :
    [false, false, true, true, true, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0100001 :
    [false, true, false, false, false, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0100010 :
    [false, true, false, false, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0100111 :
    [false, true, false, false, true, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0110011 :
    [false, true, true, false, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_0110100 :
    [false, true, true, false, true, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_0110101 :
    [false, true, true, false, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_0110111 :
    [false, true, true, false, true, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_0111011 :
    [false, true, true, true, false, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1000110 :
    [true, false, false, false, true, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_1001101 :
    [true, false, false, true, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1001111 :
    [true, false, false, true, true, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_1010000 :
    [true, false, true, false, false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1010001 :
    [true, false, true, false, false, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_1010101 :
    [true, false, true, false, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1010111 :
    [true, false, true, false, true, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_1011001 :
    [true, false, true, true, false, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1100001 :
    [true, true, false, false, false, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1100100 :
    [true, true, false, false, true, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1101011 :
    [true, true, false, true, false, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_1101111 :
    [true, true, false, true, true, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1110011 :
    [true, true, true, false, false, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1110101 :
    [true, true, true, false, true, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_1111010 :
    [true, true, true, true, false, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_1111011 :
    [true, true, true, true, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_1111101 :
    [true, true, true, true, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem mem_language_parity_1111110 :
    [true, true, true, true, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 7) rfl rfl

theorem not_mem_language_parity_00001101 :
    [false, false, false, false, true, true, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_00010010 :
    [false, false, false, true, false, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_00010100 :
    [false, false, false, true, false, true, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_00010101 :
    [false, false, false, true, false, true, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_00110011 :
    [false, false, true, true, false, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_01000100 :
    [false, true, false, false, false, true, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_01001000 :
    [false, true, false, false, true, false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_01001010 :
    [false, true, false, false, true, false, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_01100101 :
    [false, true, true, false, false, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_01100111 :
    [false, true, true, false, false, true, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_01101011 :
    [false, true, true, false, true, false, true, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_01111000 :
    [false, true, true, true, true, false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_01111011 :
    [false, true, true, true, true, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_10000001 :
    [true, false, false, false, false, false, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_10000010 :
    [true, false, false, false, false, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_10001000 :
    [true, false, false, false, true, false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_10001011 :
    [true, false, false, false, true, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_10001100 :
    [true, false, false, false, true, true, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_10010011 :
    [true, false, false, true, false, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_10011111 :
    [true, false, false, true, true, true, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_10100011 :
    [true, false, true, false, false, false, true, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_10100110 :
    [true, false, true, false, false, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_10101110 :
    [true, false, true, false, true, true, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_10110100 :
    [true, false, true, true, false, true, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_11001001 :
    [true, true, false, false, true, false, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_11001100 :
    [true, true, false, false, true, true, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_11010000 :
    [true, true, false, true, false, false, false, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_11011001 :
    [true, true, false, true, true, false, false, true] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_11100010 :
    [true, true, true, false, false, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_11100110 :
    [true, true, true, false, false, true, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_11101000 :
    [true, true, true, false, true, false, false, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_11101010 :
    [true, true, true, false, true, false, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem not_mem_language_parity_11110010 :
    [true, true, true, true, false, false, true, false] ∉ parity.language :=
  not_mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_11110101 :
    [true, true, true, true, false, true, false, true] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_11110110 :
    [true, true, true, true, false, true, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

theorem mem_language_parity_11111010 :
    [true, true, true, true, true, false, true, false] ∈ parity.language :=
  mem_language_of_run (M := parity) (t := 8) rfl rfl

/-! ### Test vectors for `containsOne` -/

theorem not_mem_language_containsOne_nil : [] ∉ containsOne.language :=
  not_mem_language_of_run (M := containsOne) (t := 0) rfl rfl

theorem not_mem_language_containsOne_0 : [false] ∉ containsOne.language :=
  not_mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1 : [true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem not_mem_language_containsOne_00 : [false, false] ∉ containsOne.language :=
  not_mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01 : [false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_10 : [true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11 : [true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem not_mem_language_containsOne_000 : [false, false, false] ∉ containsOne.language :=
  not_mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_001 : [false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_010 : [false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_011 : [false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_100 : [true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_101 : [true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_111 : [true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem not_mem_language_containsOne_0000 :
    [false, false, false, false] ∉ containsOne.language :=
  not_mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_0001 :
    [false, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_0010 :
    [false, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_0011 :
    [false, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_0100 :
    [false, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_0101 :
    [false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_0110 :
    [false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_1000 :
    [true, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1001 :
    [true, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1010 :
    [true, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1011 :
    [true, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1100 :
    [true, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1101 :
    [true, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1110 :
    [true, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1111 : [true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_00001 :
    [false, false, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 5) rfl rfl

theorem mem_language_containsOne_00011 :
    [false, false, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_00100 :
    [false, false, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_00101 :
    [false, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_00110 :
    [false, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_00111 :
    [false, false, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_01010 :
    [false, true, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01101 :
    [false, true, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01110 :
    [false, true, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01111 :
    [false, true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_10000 :
    [true, false, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10001 :
    [true, false, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10010 :
    [true, false, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10011 :
    [true, false, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10100 :
    [true, false, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10101 :
    [true, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10110 :
    [true, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10111 :
    [true, false, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11011 :
    [true, true, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11100 :
    [true, true, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11101 :
    [true, true, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11110 :
    [true, true, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11111 :
    [true, true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem not_mem_language_containsOne_000000 :
    [false, false, false, false, false, false] ∉ containsOne.language :=
  not_mem_language_of_run (M := containsOne) (t := 6) rfl rfl

theorem mem_language_containsOne_000101 :
    [false, false, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_000110 :
    [false, false, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_001000 :
    [false, false, true, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_001001 :
    [false, false, true, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_001110 :
    [false, false, true, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_001111 :
    [false, false, true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_010010 :
    [false, true, false, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_010011 :
    [false, true, false, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_011001 :
    [false, true, true, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_011010 :
    [false, true, true, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_011100 :
    [false, true, true, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_011101 :
    [false, true, true, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_011110 :
    [false, true, true, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_011111 :
    [false, true, true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_100010 :
    [true, false, false, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_100110 :
    [true, false, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_100111 :
    [true, false, false, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_101001 :
    [true, false, true, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_101010 :
    [true, false, true, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_101100 :
    [true, false, true, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_101110 :
    [true, false, true, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_110101 :
    [true, true, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_110110 :
    [true, true, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_111011 :
    [true, true, true, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_111110 :
    [true, true, true, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem not_mem_language_containsOne_0000000 :
    [false, false, false, false, false, false, false] ∉ containsOne.language :=
  not_mem_language_of_run (M := containsOne) (t := 7) rfl rfl

theorem mem_language_containsOne_0000001 :
    [false, false, false, false, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 7) rfl rfl

theorem mem_language_containsOne_0000101 :
    [false, false, false, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 5) rfl rfl

theorem mem_language_containsOne_0000110 :
    [false, false, false, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 5) rfl rfl

theorem mem_language_containsOne_0001000 :
    [false, false, false, true, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_0001010 :
    [false, false, false, true, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_0001101 :
    [false, false, false, true, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_0001111 :
    [false, false, false, true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_0011000 :
    [false, false, true, true, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_0011111 :
    [false, false, true, true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_0100001 :
    [false, true, false, false, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_0100010 :
    [false, true, false, false, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_0100111 :
    [false, true, false, false, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_0110011 :
    [false, true, true, false, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_0110100 :
    [false, true, true, false, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_0110101 :
    [false, true, true, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_0110111 :
    [false, true, true, false, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_0111011 :
    [false, true, true, true, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_1000110 :
    [true, false, false, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1001101 :
    [true, false, false, true, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1001111 :
    [true, false, false, true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1010000 :
    [true, false, true, false, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1010001 :
    [true, false, true, false, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1010101 :
    [true, false, true, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1010111 :
    [true, false, true, false, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1011001 :
    [true, false, true, true, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1100001 :
    [true, true, false, false, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1100100 :
    [true, true, false, false, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1101011 :
    [true, true, false, true, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1101111 :
    [true, true, false, true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1110011 :
    [true, true, true, false, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1110101 :
    [true, true, true, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1111010 :
    [true, true, true, true, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1111011 :
    [true, true, true, true, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1111101 :
    [true, true, true, true, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_1111110 :
    [true, true, true, true, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_00001101 :
    [false, false, false, false, true, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 5) rfl rfl

theorem mem_language_containsOne_00010010 :
    [false, false, false, true, false, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_00010100 :
    [false, false, false, true, false, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_00010101 :
    [false, false, false, true, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 4) rfl rfl

theorem mem_language_containsOne_00110011 :
    [false, false, true, true, false, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 3) rfl rfl

theorem mem_language_containsOne_01000100 :
    [false, true, false, false, false, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01001000 :
    [false, true, false, false, true, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01001010 :
    [false, true, false, false, true, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01100101 :
    [false, true, true, false, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01100111 :
    [false, true, true, false, false, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01101011 :
    [false, true, true, false, true, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01111000 :
    [false, true, true, true, true, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_01111011 :
    [false, true, true, true, true, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 2) rfl rfl

theorem mem_language_containsOne_10000001 :
    [true, false, false, false, false, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10000010 :
    [true, false, false, false, false, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10001000 :
    [true, false, false, false, true, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10001011 :
    [true, false, false, false, true, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10001100 :
    [true, false, false, false, true, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10010011 :
    [true, false, false, true, false, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10011111 :
    [true, false, false, true, true, true, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10100011 :
    [true, false, true, false, false, false, true, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10100110 :
    [true, false, true, false, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10101110 :
    [true, false, true, false, true, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_10110100 :
    [true, false, true, true, false, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11001001 :
    [true, true, false, false, true, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11001100 :
    [true, true, false, false, true, true, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11010000 :
    [true, true, false, true, false, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11011001 :
    [true, true, false, true, true, false, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11100010 :
    [true, true, true, false, false, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11100110 :
    [true, true, true, false, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11101000 :
    [true, true, true, false, true, false, false, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11101010 :
    [true, true, true, false, true, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11110010 :
    [true, true, true, true, false, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11110101 :
    [true, true, true, true, false, true, false, true] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11110110 :
    [true, true, true, true, false, true, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

theorem mem_language_containsOne_11111010 :
    [true, true, true, true, true, false, true, false] ∈ containsOne.language :=
  mem_language_of_run (M := containsOne) (t := 1) rfl rfl

/-! ### Running times -/

theorem parity_haltsIn_0 : parity.HaltsIn 1 [false] :=
  rfl

theorem parity_haltsIn_1 : parity.HaltsIn 1 [true] :=
  rfl

theorem parity_haltsIn_001 : parity.HaltsIn 3 [false, false, true] :=
  rfl

theorem parity_haltsIn_010 : parity.HaltsIn 3 [false, true, false] :=
  rfl

theorem parity_haltsIn_100 : parity.HaltsIn 3 [true, false, false] :=
  rfl

theorem parity_haltsIn_101 : parity.HaltsIn 3 [true, false, true] :=
  rfl

theorem parity_haltsIn_111 : parity.HaltsIn 3 [true, true, true] :=
  rfl

theorem parity_haltsIn_0000 : parity.HaltsIn 4 [false, false, false, false] :=
  rfl

theorem parity_haltsIn_0001 : parity.HaltsIn 4 [false, false, false, true] :=
  rfl

theorem parity_haltsIn_0011 : parity.HaltsIn 4 [false, false, true, true] :=
  rfl

theorem parity_haltsIn_0100 : parity.HaltsIn 4 [false, true, false, false] :=
  rfl

theorem parity_haltsIn_0110 : parity.HaltsIn 4 [false, true, true, false] :=
  rfl

theorem parity_haltsIn_1000 : parity.HaltsIn 4 [true, false, false, false] :=
  rfl

theorem parity_haltsIn_1001 : parity.HaltsIn 4 [true, false, false, true] :=
  rfl

theorem parity_haltsIn_1010 : parity.HaltsIn 4 [true, false, true, false] :=
  rfl

theorem parity_haltsIn_1011 : parity.HaltsIn 4 [true, false, true, true] :=
  rfl

theorem parity_haltsIn_1100 : parity.HaltsIn 4 [true, true, false, false] :=
  rfl

theorem parity_haltsIn_1101 : parity.HaltsIn 4 [true, true, false, true] :=
  rfl

theorem parity_haltsIn_1110 : parity.HaltsIn 4 [true, true, true, false] :=
  rfl

theorem parity_haltsIn_00101 : parity.HaltsIn 5 [false, false, true, false, true] :=
  rfl

theorem parity_haltsIn_00110 : parity.HaltsIn 5 [false, false, true, true, false] :=
  rfl

theorem parity_haltsIn_00111 : parity.HaltsIn 5 [false, false, true, true, true] :=
  rfl

theorem parity_haltsIn_01010 : parity.HaltsIn 5 [false, true, false, true, false] :=
  rfl

theorem parity_haltsIn_01110 : parity.HaltsIn 5 [false, true, true, true, false] :=
  rfl

theorem parity_haltsIn_10011 : parity.HaltsIn 5 [true, false, false, true, true] :=
  rfl

theorem parity_haltsIn_10100 : parity.HaltsIn 5 [true, false, true, false, false] :=
  rfl

theorem parity_haltsIn_10111 : parity.HaltsIn 5 [true, false, true, true, true] :=
  rfl

theorem parity_haltsIn_11100 : parity.HaltsIn 5 [true, true, true, false, false] :=
  rfl

theorem parity_haltsIn_11101 : parity.HaltsIn 5 [true, true, true, false, true] :=
  rfl

theorem parity_haltsIn_11110 : parity.HaltsIn 5 [true, true, true, true, false] :=
  rfl

theorem parity_haltsIn_000000 :
    parity.HaltsIn 6 [false, false, false, false, false, false] :=
  rfl

theorem parity_haltsIn_000101 :
    parity.HaltsIn 6 [false, false, false, true, false, true] :=
  rfl

theorem parity_haltsIn_001111 : parity.HaltsIn 6 [false, false, true, true, true, true] :=
  rfl

theorem parity_haltsIn_010010 :
    parity.HaltsIn 6 [false, true, false, false, true, false] :=
  rfl

theorem parity_haltsIn_011010 :
    parity.HaltsIn 6 [false, true, true, false, true, false] :=
  rfl

theorem parity_haltsIn_011100 :
    parity.HaltsIn 6 [false, true, true, true, false, false] :=
  rfl

theorem parity_haltsIn_011110 : parity.HaltsIn 6 [false, true, true, true, true, false] :=
  rfl

theorem parity_haltsIn_100010 :
    parity.HaltsIn 6 [true, false, false, false, true, false] :=
  rfl

theorem parity_haltsIn_100111 : parity.HaltsIn 6 [true, false, false, true, true, true] :=
  rfl

theorem parity_haltsIn_101010 :
    parity.HaltsIn 6 [true, false, true, false, true, false] :=
  rfl

theorem parity_haltsIn_101100 :
    parity.HaltsIn 6 [true, false, true, true, false, false] :=
  rfl

theorem parity_haltsIn_110101 : parity.HaltsIn 6 [true, true, false, true, false, true] :=
  rfl

theorem parity_haltsIn_0000000 :
    parity.HaltsIn 7 [false, false, false, false, false, false, false] :=
  rfl

theorem parity_haltsIn_0001010 :
    parity.HaltsIn 7 [false, false, false, true, false, true, false] :=
  rfl

theorem parity_haltsIn_0001101 :
    parity.HaltsIn 7 [false, false, false, true, true, false, true] :=
  rfl

theorem parity_haltsIn_0001111 :
    parity.HaltsIn 7 [false, false, false, true, true, true, true] :=
  rfl

theorem parity_haltsIn_0011000 :
    parity.HaltsIn 7 [false, false, true, true, false, false, false] :=
  rfl

theorem parity_haltsIn_0100111 :
    parity.HaltsIn 7 [false, true, false, false, true, true, true] :=
  rfl

theorem parity_haltsIn_0110100 :
    parity.HaltsIn 7 [false, true, true, false, true, false, false] :=
  rfl

theorem parity_haltsIn_0110111 :
    parity.HaltsIn 7 [false, true, true, false, true, true, true] :=
  rfl

theorem parity_haltsIn_1000110 :
    parity.HaltsIn 7 [true, false, false, false, true, true, false] :=
  rfl

theorem parity_haltsIn_1001101 :
    parity.HaltsIn 7 [true, false, false, true, true, false, true] :=
  rfl

theorem parity_haltsIn_1001111 :
    parity.HaltsIn 7 [true, false, false, true, true, true, true] :=
  rfl

theorem parity_haltsIn_1010000 :
    parity.HaltsIn 7 [true, false, true, false, false, false, false] :=
  rfl

theorem parity_haltsIn_1100001 :
    parity.HaltsIn 7 [true, true, false, false, false, false, true] :=
  rfl

theorem parity_haltsIn_1100100 :
    parity.HaltsIn 7 [true, true, false, false, true, false, false] :=
  rfl

theorem parity_haltsIn_1101011 :
    parity.HaltsIn 7 [true, true, false, true, false, true, true] :=
  rfl

theorem parity_haltsIn_1110101 :
    parity.HaltsIn 7 [true, true, true, false, true, false, true] :=
  rfl

theorem parity_haltsIn_1111011 :
    parity.HaltsIn 7 [true, true, true, true, false, true, true] :=
  rfl

theorem parity_haltsIn_1111110 :
    parity.HaltsIn 7 [true, true, true, true, true, true, false] :=
  rfl

theorem parity_haltsIn_00010010 :
    parity.HaltsIn 8 [false, false, false, true, false, false, true, false] :=
  rfl

theorem parity_haltsIn_00110011 :
    parity.HaltsIn 8 [false, false, true, true, false, false, true, true] :=
  rfl

theorem parity_haltsIn_01000100 :
    parity.HaltsIn 8 [false, true, false, false, false, true, false, false] :=
  rfl

theorem parity_haltsIn_01001000 :
    parity.HaltsIn 8 [false, true, false, false, true, false, false, false] :=
  rfl

theorem parity_haltsIn_01001010 :
    parity.HaltsIn 8 [false, true, false, false, true, false, true, false] :=
  rfl

theorem parity_haltsIn_01111000 :
    parity.HaltsIn 8 [false, true, true, true, true, false, false, false] :=
  rfl

theorem parity_haltsIn_10000010 :
    parity.HaltsIn 8 [true, false, false, false, false, false, true, false] :=
  rfl

theorem parity_haltsIn_10001000 :
    parity.HaltsIn 8 [true, false, false, false, true, false, false, false] :=
  rfl

theorem parity_haltsIn_10100110 :
    parity.HaltsIn 8 [true, false, true, false, false, true, true, false] :=
  rfl

theorem parity_haltsIn_10110100 :
    parity.HaltsIn 8 [true, false, true, true, false, true, false, false] :=
  rfl

theorem parity_haltsIn_11001001 :
    parity.HaltsIn 8 [true, true, false, false, true, false, false, true] :=
  rfl

theorem parity_haltsIn_11010000 :
    parity.HaltsIn 8 [true, true, false, true, false, false, false, false] :=
  rfl

theorem parity_haltsIn_11100110 :
    parity.HaltsIn 8 [true, true, true, false, false, true, true, false] :=
  rfl

theorem parity_haltsIn_11101000 :
    parity.HaltsIn 8 [true, true, true, false, true, false, false, false] :=
  rfl

theorem parity_haltsIn_11101010 :
    parity.HaltsIn 8 [true, true, true, false, true, false, true, false] :=
  rfl

theorem parity_haltsIn_11110010 :
    parity.HaltsIn 8 [true, true, true, true, false, false, true, false] :=
  rfl

theorem parity_haltsIn_11111010 :
    parity.HaltsIn 8 [true, true, true, true, true, false, true, false] :=
  rfl

/-! ### Test vectors for `flipFirst` -/

theorem flipFirst_run_0 :
    (flipFirst.run 1 (flipFirst.init [false])).tape = Tape.ofWord [true] :=
  rfl

theorem flipFirst_run_01 :
    (flipFirst.run 1 (flipFirst.init [false, true])).tape = Tape.ofWord [true, true] :=
  rfl

theorem flipFirst_run_000 :
    (flipFirst.run 1 (flipFirst.init [false, false, false])).tape =
      Tape.ofWord [true, false, false] :=
  rfl

theorem flipFirst_run_010 :
    (flipFirst.run 1 (flipFirst.init [false, true, false])).tape =
      Tape.ofWord [true, true, false] :=
  rfl

theorem flipFirst_run_111 :
    (flipFirst.run 1 (flipFirst.init [true, true, true])).tape =
      Tape.ofWord [false, true, true] :=
  rfl

theorem flipFirst_run_0000 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, false])).tape =
      Tape.ofWord [true, false, false, false] :=
  rfl

theorem flipFirst_run_0001 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, true])).tape =
      Tape.ofWord [true, false, false, true] :=
  rfl

theorem flipFirst_run_0010 :
    (flipFirst.run 1 (flipFirst.init [false, false, true, false])).tape =
      Tape.ofWord [true, false, true, false] :=
  rfl

theorem flipFirst_run_0011 :
    (flipFirst.run 1 (flipFirst.init [false, false, true, true])).tape =
      Tape.ofWord [true, false, true, true] :=
  rfl

theorem flipFirst_run_0100 :
    (flipFirst.run 1 (flipFirst.init [false, true, false, false])).tape =
      Tape.ofWord [true, true, false, false] :=
  rfl

theorem flipFirst_run_0110 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, false])).tape =
      Tape.ofWord [true, true, true, false] :=
  rfl

theorem flipFirst_run_1000 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, false])).tape =
      Tape.ofWord [false, false, false, false] :=
  rfl

theorem flipFirst_run_1011 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, true])).tape =
      Tape.ofWord [false, false, true, true] :=
  rfl

theorem flipFirst_run_1100 :
    (flipFirst.run 1 (flipFirst.init [true, true, false, false])).tape =
      Tape.ofWord [false, true, false, false] :=
  rfl

theorem flipFirst_run_1110 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, false])).tape =
      Tape.ofWord [false, true, true, false] :=
  rfl

theorem flipFirst_run_1111 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, true])).tape =
      Tape.ofWord [false, true, true, true] :=
  rfl

theorem flipFirst_run_00001 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, false, true])).tape =
      Tape.ofWord [true, false, false, false, true] :=
  rfl

theorem flipFirst_run_00011 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, true, true])).tape =
      Tape.ofWord [true, false, false, true, true] :=
  rfl

theorem flipFirst_run_00111 :
    (flipFirst.run 1 (flipFirst.init [false, false, true, true, true])).tape =
      Tape.ofWord [true, false, true, true, true] :=
  rfl

theorem flipFirst_run_01101 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, false, true])).tape =
      Tape.ofWord [true, true, true, false, true] :=
  rfl

theorem flipFirst_run_01110 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, true, false])).tape =
      Tape.ofWord [true, true, true, true, false] :=
  rfl

theorem flipFirst_run_01111 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, true, true])).tape =
      Tape.ofWord [true, true, true, true, true] :=
  rfl

theorem flipFirst_run_10011 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, true, true])).tape =
      Tape.ofWord [false, false, false, true, true] :=
  rfl

theorem flipFirst_run_10100 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, false, false])).tape =
      Tape.ofWord [false, false, true, false, false] :=
  rfl

theorem flipFirst_run_10101 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, false, true])).tape =
      Tape.ofWord [false, false, true, false, true] :=
  rfl

theorem flipFirst_run_10111 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, true, true])).tape =
      Tape.ofWord [false, false, true, true, true] :=
  rfl

theorem flipFirst_run_11101 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, false, true])).tape =
      Tape.ofWord [false, true, true, false, true] :=
  rfl

theorem flipFirst_run_11111 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, true, true])).tape =
      Tape.ofWord [false, true, true, true, true] :=
  rfl

theorem flipFirst_run_000000 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, false, false, false])).tape =
      Tape.ofWord [true, false, false, false, false, false] :=
  rfl

theorem flipFirst_run_000101 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, true, false, true])).tape =
      Tape.ofWord [true, false, false, true, false, true] :=
  rfl

theorem flipFirst_run_000110 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, true, true, false])).tape =
      Tape.ofWord [true, false, false, true, true, false] :=
  rfl

theorem flipFirst_run_001000 :
    (flipFirst.run 1 (flipFirst.init [false, false, true, false, false, false])).tape =
      Tape.ofWord [true, false, true, false, false, false] :=
  rfl

theorem flipFirst_run_001001 :
    (flipFirst.run 1 (flipFirst.init [false, false, true, false, false, true])).tape =
      Tape.ofWord [true, false, true, false, false, true] :=
  rfl

theorem flipFirst_run_001110 :
    (flipFirst.run 1 (flipFirst.init [false, false, true, true, true, false])).tape =
      Tape.ofWord [true, false, true, true, true, false] :=
  rfl

theorem flipFirst_run_001111 :
    (flipFirst.run 1 (flipFirst.init [false, false, true, true, true, true])).tape =
      Tape.ofWord [true, false, true, true, true, true] :=
  rfl

theorem flipFirst_run_010011 :
    (flipFirst.run 1 (flipFirst.init [false, true, false, false, true, true])).tape =
      Tape.ofWord [true, true, false, false, true, true] :=
  rfl

theorem flipFirst_run_011001 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, false, false, true])).tape =
      Tape.ofWord [true, true, true, false, false, true] :=
  rfl

theorem flipFirst_run_011010 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, false, true, false])).tape =
      Tape.ofWord [true, true, true, false, true, false] :=
  rfl

theorem flipFirst_run_011100 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, true, false, false])).tape =
      Tape.ofWord [true, true, true, true, false, false] :=
  rfl

theorem flipFirst_run_011101 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, true, false, true])).tape =
      Tape.ofWord [true, true, true, true, false, true] :=
  rfl

theorem flipFirst_run_011110 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, true, true, false])).tape =
      Tape.ofWord [true, true, true, true, true, false] :=
  rfl

theorem flipFirst_run_100010 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, false, true, false])).tape =
      Tape.ofWord [false, false, false, false, true, false] :=
  rfl

theorem flipFirst_run_100110 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, true, true, false])).tape =
      Tape.ofWord [false, false, false, true, true, false] :=
  rfl

theorem flipFirst_run_101010 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, false, true, false])).tape =
      Tape.ofWord [false, false, true, false, true, false] :=
  rfl

theorem flipFirst_run_101110 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, true, true, false])).tape =
      Tape.ofWord [false, false, true, true, true, false] :=
  rfl

theorem flipFirst_run_111011 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, false, true, true])).tape =
      Tape.ofWord [false, true, true, false, true, true] :=
  rfl

theorem flipFirst_run_0000000 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, false, false, false, false])).tape =
      Tape.ofWord [true, false, false, false, false, false, false] :=
  rfl

theorem flipFirst_run_0000001 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, false, false, false, true])).tape =
      Tape.ofWord [true, false, false, false, false, false, true] :=
  rfl

theorem flipFirst_run_0001010 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, true, false, true, false])).tape =
      Tape.ofWord [true, false, false, true, false, true, false] :=
  rfl

theorem flipFirst_run_0011000 :
    (flipFirst.run 1 (flipFirst.init [false, false, true, true, false, false, false])).tape =
      Tape.ofWord [true, false, true, true, false, false, false] :=
  rfl

theorem flipFirst_run_0100001 :
    (flipFirst.run 1 (flipFirst.init [false, true, false, false, false, false, true])).tape =
      Tape.ofWord [true, true, false, false, false, false, true] :=
  rfl

theorem flipFirst_run_0100111 :
    (flipFirst.run 1 (flipFirst.init [false, true, false, false, true, true, true])).tape =
      Tape.ofWord [true, true, false, false, true, true, true] :=
  rfl

theorem flipFirst_run_0111011 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, true, false, true, true])).tape =
      Tape.ofWord [true, true, true, true, false, true, true] :=
  rfl

theorem flipFirst_run_1000110 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, false, true, true, false])).tape =
      Tape.ofWord [false, false, false, false, true, true, false] :=
  rfl

theorem flipFirst_run_1001101 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, true, true, false, true])).tape =
      Tape.ofWord [false, false, false, true, true, false, true] :=
  rfl

theorem flipFirst_run_1001111 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, true, true, true, true])).tape =
      Tape.ofWord [false, false, false, true, true, true, true] :=
  rfl

theorem flipFirst_run_1010101 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, false, true, false, true])).tape =
      Tape.ofWord [false, false, true, false, true, false, true] :=
  rfl

theorem flipFirst_run_1010111 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, false, true, true, true])).tape =
      Tape.ofWord [false, false, true, false, true, true, true] :=
  rfl

theorem flipFirst_run_1011001 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, true, false, false, true])).tape =
      Tape.ofWord [false, false, true, true, false, false, true] :=
  rfl

theorem flipFirst_run_1100001 :
    (flipFirst.run 1 (flipFirst.init [true, true, false, false, false, false, true])).tape =
      Tape.ofWord [false, true, false, false, false, false, true] :=
  rfl

theorem flipFirst_run_1100100 :
    (flipFirst.run 1 (flipFirst.init [true, true, false, false, true, false, false])).tape =
      Tape.ofWord [false, true, false, false, true, false, false] :=
  rfl

theorem flipFirst_run_1110011 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, false, false, true, true])).tape =
      Tape.ofWord [false, true, true, false, false, true, true] :=
  rfl

theorem flipFirst_run_1110101 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, false, true, false, true])).tape =
      Tape.ofWord [false, true, true, false, true, false, true] :=
  rfl

theorem flipFirst_run_1111011 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, true, false, true, true])).tape =
      Tape.ofWord [false, true, true, true, false, true, true] :=
  rfl

theorem flipFirst_run_1111110 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, true, true, true, false])).tape =
      Tape.ofWord [false, true, true, true, true, true, false] :=
  rfl

theorem flipFirst_run_00010010 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, true, false, false, true, false])).tape =
      Tape.ofWord [true, false, false, true, false, false, true, false] :=
  rfl

theorem flipFirst_run_00010100 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, true, false, true, false, false])).tape =
      Tape.ofWord [true, false, false, true, false, true, false, false] :=
  rfl

theorem flipFirst_run_00010101 :
    (flipFirst.run 1 (flipFirst.init [false, false, false, true, false, true, false, true])).tape =
      Tape.ofWord [true, false, false, true, false, true, false, true] :=
  rfl

theorem flipFirst_run_00110011 :
    (flipFirst.run 1 (flipFirst.init [false, false, true, true, false, false, true, true])).tape =
      Tape.ofWord [true, false, true, true, false, false, true, true] :=
  rfl

theorem flipFirst_run_01000100 :
    (flipFirst.run 1 (flipFirst.init [false, true, false, false, false, true, false, false])).tape =
      Tape.ofWord [true, true, false, false, false, true, false, false] :=
  rfl

theorem flipFirst_run_01001000 :
    (flipFirst.run 1 (flipFirst.init [false, true, false, false, true, false, false, false])).tape =
      Tape.ofWord [true, true, false, false, true, false, false, false] :=
  rfl

theorem flipFirst_run_01001010 :
    (flipFirst.run 1 (flipFirst.init [false, true, false, false, true, false, true, false])).tape =
      Tape.ofWord [true, true, false, false, true, false, true, false] :=
  rfl

theorem flipFirst_run_01111000 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, true, true, false, false, false])).tape =
      Tape.ofWord [true, true, true, true, true, false, false, false] :=
  rfl

theorem flipFirst_run_01111011 :
    (flipFirst.run 1 (flipFirst.init [false, true, true, true, true, false, true, true])).tape =
      Tape.ofWord [true, true, true, true, true, false, true, true] :=
  rfl

theorem flipFirst_run_10000001 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, false, false, false, false, true])).tape =
      Tape.ofWord [false, false, false, false, false, false, false, true] :=
  rfl

theorem flipFirst_run_10001011 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, false, true, false, true, true])).tape =
      Tape.ofWord [false, false, false, false, true, false, true, true] :=
  rfl

theorem flipFirst_run_10001100 :
    (flipFirst.run 1 (flipFirst.init [true, false, false, false, true, true, false, false])).tape =
      Tape.ofWord [false, false, false, false, true, true, false, false] :=
  rfl

theorem flipFirst_run_10100011 :
    (flipFirst.run 1 (flipFirst.init [true, false, true, false, false, false, true, true])).tape =
      Tape.ofWord [false, false, true, false, false, false, true, true] :=
  rfl

theorem flipFirst_run_11001001 :
    (flipFirst.run 1 (flipFirst.init [true, true, false, false, true, false, false, true])).tape =
      Tape.ofWord [false, true, false, false, true, false, false, true] :=
  rfl

theorem flipFirst_run_11011001 :
    (flipFirst.run 1 (flipFirst.init [true, true, false, true, true, false, false, true])).tape =
      Tape.ofWord [false, true, false, true, true, false, false, true] :=
  rfl

theorem flipFirst_run_11100010 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, false, false, false, true, false])).tape =
      Tape.ofWord [false, true, true, false, false, false, true, false] :=
  rfl

theorem flipFirst_run_11101000 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, false, true, false, false, false])).tape =
      Tape.ofWord [false, true, true, false, true, false, false, false] :=
  rfl

theorem flipFirst_run_11101010 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, false, true, false, true, false])).tape =
      Tape.ofWord [false, true, true, false, true, false, true, false] :=
  rfl

theorem flipFirst_run_11110010 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, true, false, false, true, false])).tape =
      Tape.ofWord [false, true, true, true, false, false, true, false] :=
  rfl

theorem flipFirst_run_11110101 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, true, false, true, false, true])).tape =
      Tape.ofWord [false, true, true, true, false, true, false, true] :=
  rfl

theorem flipFirst_run_11111010 :
    (flipFirst.run 1 (flipFirst.init [true, true, true, true, true, false, true, false])).tape =
      Tape.ofWord [false, true, true, true, true, false, true, false] :=
  rfl

end TM

end Complexity
