import PNP.Problems.SAT

/-!
# Small instances of SAT

A collection of small formulas with known status, in the spirit of the uniform
random 3-SAT families `uf` and `uuf` of SATLIB [HS00]. They serve as test
vectors for the evaluation functions, for the encoding, and for the membership
lemmas of `PNP.Problems.SAT`.

## Main definitions

* `Complexity.uf_n_m_i`: the `i`-th satisfiable instance with `n` variables and
  `m` clauses.
* `Complexity.uuf_n_m_i`: the `i`-th unsatisfiable instance with `n` variables
  and `m` clauses.

## Main results

For each satisfiable instance: a satisfying assignment, the bound on the clause
width, and membership of the encoding in 3-SAT. For each unsatisfiable instance:
a proof of unsatisfiability by case analysis on the variables, and
non-membership of the encoding in SAT.

## References

* [HS00] H. H. Hoos, T. Stützle, *SATLIB: An online resource for research on
  SAT*, in *SAT 2000*, IOS Press, 2000.
-/

set_option autoImplicit false

namespace Complexity

/-! ### Satisfiable instances -/

/-- A satisfiable instance with 3 variables and 4 clauses. -/
def uf_3_4_01 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩],
   [⟨1, true⟩, ⟨2, false⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨2, false⟩]]

theorem satisfiable_uf_3_4_01 : uf_3_4_01.Satisfiable :=
  ⟨fun i => [false, false, false].getD i false, rfl⟩

theorem isKCNF_uf_3_4_01 : uf_3_4_01.IsKCNF 3 := by decide

theorem encode_uf_3_4_01_mem_ThreeSAT : Encoding.encode uf_3_4_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_4_01, satisfiable_uf_3_4_01⟩

theorem encode_uf_3_4_01_mem_SAT : Encoding.encode uf_3_4_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_4_01_mem_ThreeSAT

/-- A satisfiable instance with 6 variables and 4 clauses. -/
def uf_6_4_01 : CNF :=
  [[⟨3, false⟩, ⟨5, false⟩], [⟨2, false⟩, ⟨4, false⟩], [⟨0, false⟩, ⟨3, false⟩, ⟨5, false⟩],
   [⟨1, false⟩, ⟨2, true⟩, ⟨3, true⟩]]

theorem satisfiable_uf_6_4_01 : uf_6_4_01.Satisfiable :=
  ⟨fun i => [false, true, true, true, false, true].getD i false, rfl⟩

theorem isKCNF_uf_6_4_01 : uf_6_4_01.IsKCNF 3 := by decide

theorem encode_uf_6_4_01_mem_ThreeSAT : Encoding.encode uf_6_4_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_6_4_01, satisfiable_uf_6_4_01⟩

theorem encode_uf_6_4_01_mem_SAT : Encoding.encode uf_6_4_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_6_4_01_mem_ThreeSAT

theorem eval_uf_6_4_01_eq_false :
    uf_6_4_01.eval (fun i => [false, false, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 6 variables and 8 clauses. -/
def uf_6_8_01 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩, ⟨3, false⟩], [⟨2, true⟩, ⟨3, false⟩, ⟨5, true⟩],
   [⟨3, true⟩, ⟨5, false⟩], [⟨0, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨4, false⟩, ⟨5, false⟩],
   [⟨0, false⟩, ⟨3, false⟩, ⟨4, true⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨1, false⟩, ⟨3, true⟩]]

theorem satisfiable_uf_6_8_01 : uf_6_8_01.Satisfiable :=
  ⟨fun i => [false, true, false, true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_6_8_01 : uf_6_8_01.IsKCNF 3 := by decide

theorem encode_uf_6_8_01_mem_ThreeSAT : Encoding.encode uf_6_8_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_6_8_01, satisfiable_uf_6_8_01⟩

theorem encode_uf_6_8_01_mem_SAT : Encoding.encode uf_6_8_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_6_8_01_mem_ThreeSAT

theorem eval_uf_6_8_01_eq_false :
    uf_6_8_01.eval (fun i => [false, false, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 4 variables and 6 clauses. -/
def uf_4_6_01 : CNF :=
  [[⟨0, true⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨2, true⟩, ⟨3, false⟩], [⟨1, true⟩, ⟨3, true⟩],
   [⟨0, true⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨3, false⟩], [⟨1, true⟩, ⟨2, true⟩]]

theorem satisfiable_uf_4_6_01 : uf_4_6_01.Satisfiable :=
  ⟨fun i => [false, false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_4_6_01 : uf_4_6_01.IsKCNF 3 := by decide

theorem encode_uf_4_6_01_mem_ThreeSAT : Encoding.encode uf_4_6_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_6_01, satisfiable_uf_4_6_01⟩

theorem encode_uf_4_6_01_mem_SAT : Encoding.encode uf_4_6_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_4_6_01_mem_ThreeSAT

/-- A satisfiable instance with 4 variables and 5 clauses. -/
def uf_4_5_01 : CNF :=
  [[⟨1, false⟩, ⟨3, true⟩], [⟨1, false⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨1, true⟩],
   [⟨0, true⟩, ⟨1, false⟩], [⟨0, false⟩, ⟨2, false⟩]]

theorem satisfiable_uf_4_5_01 : uf_4_5_01.Satisfiable :=
  ⟨fun i => [false, true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_4_5_01 : uf_4_5_01.IsKCNF 3 := by decide

theorem encode_uf_4_5_01_mem_ThreeSAT : Encoding.encode uf_4_5_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_5_01, satisfiable_uf_4_5_01⟩

theorem eval_uf_4_5_01_eq_false :
    uf_4_5_01.eval (fun i => [false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 5 variables and 3 clauses. -/
def uf_5_3_01 : CNF :=
  [[⟨1, false⟩, ⟨2, true⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨2, false⟩, ⟨3, true⟩],
   [⟨2, false⟩, ⟨3, true⟩, ⟨4, false⟩]]

theorem satisfiable_uf_5_3_01 : uf_5_3_01.Satisfiable :=
  ⟨fun i => [false, false, false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_5_3_01 : uf_5_3_01.IsKCNF 3 := by decide

theorem encode_uf_5_3_01_mem_ThreeSAT : Encoding.encode uf_5_3_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_3_01, satisfiable_uf_5_3_01⟩

theorem encode_uf_5_3_01_mem_SAT : Encoding.encode uf_5_3_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_5_3_01_mem_ThreeSAT

theorem eval_uf_5_3_01_eq_false :
    uf_5_3_01.eval (fun i => [false, false, true, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 3 variables and 5 clauses. -/
def uf_3_5_01 : CNF :=
  [[⟨1, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨1, false⟩, ⟨2, false⟩],
   [⟨0, false⟩, ⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩]]

theorem satisfiable_uf_3_5_01 : uf_3_5_01.Satisfiable :=
  ⟨fun i => [true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_3_5_01 : uf_3_5_01.IsKCNF 3 := by decide

theorem encode_uf_3_5_01_mem_ThreeSAT : Encoding.encode uf_3_5_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_5_01, satisfiable_uf_3_5_01⟩

theorem encode_uf_3_5_01_mem_SAT : Encoding.encode uf_3_5_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_5_01_mem_ThreeSAT

theorem eval_uf_3_5_01_eq_false :
    uf_3_5_01.eval (fun i => [false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 3 variables and 3 clauses. -/
def uf_3_3_01 : CNF :=
  [[⟨0, true⟩, ⟨1, true⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, true⟩],
   [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_3_01 : uf_3_3_01.Satisfiable :=
  ⟨fun i => [false, false, false].getD i false, rfl⟩

theorem isKCNF_uf_3_3_01 : uf_3_3_01.IsKCNF 3 := by decide

theorem encode_uf_3_3_01_mem_ThreeSAT : Encoding.encode uf_3_3_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_3_01, satisfiable_uf_3_3_01⟩

theorem encode_uf_3_3_01_mem_SAT : Encoding.encode uf_3_3_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_3_01_mem_ThreeSAT

theorem eval_uf_3_3_01_eq_false :
    uf_3_3_01.eval (fun i => [false, true, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 5 variables and 5 clauses. -/
def uf_5_5_01 : CNF :=
  [[⟨0, false⟩, ⟨2, true⟩, ⟨3, false⟩], [⟨1, false⟩, ⟨3, false⟩, ⟨4, true⟩],
   [⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨0, true⟩, ⟨3, true⟩], [⟨0, true⟩, ⟨1, true⟩]]

theorem satisfiable_uf_5_5_01 : uf_5_5_01.Satisfiable :=
  ⟨fun i => [false, false, true, true, false].getD i false, rfl⟩

theorem isKCNF_uf_5_5_01 : uf_5_5_01.IsKCNF 3 := by decide

theorem encode_uf_5_5_01_mem_ThreeSAT : Encoding.encode uf_5_5_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_5_01, satisfiable_uf_5_5_01⟩

theorem encode_uf_5_5_01_mem_SAT : Encoding.encode uf_5_5_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_5_5_01_mem_ThreeSAT

/-- A satisfiable instance with 5 variables and 4 clauses. -/
def uf_5_4_01 : CNF :=
  [[⟨2, false⟩, ⟨3, false⟩, ⟨4, true⟩], [⟨1, false⟩, ⟨2, false⟩],
   [⟨0, false⟩, ⟨2, true⟩, ⟨3, true⟩], [⟨0, false⟩, ⟨2, false⟩, ⟨4, true⟩]]

theorem satisfiable_uf_5_4_01 : uf_5_4_01.Satisfiable :=
  ⟨fun i => [true, true, true, false, false].getD i false, rfl⟩

theorem isKCNF_uf_5_4_01 : uf_5_4_01.IsKCNF 3 := by decide

theorem encode_uf_5_4_01_mem_ThreeSAT : Encoding.encode uf_5_4_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_4_01, satisfiable_uf_5_4_01⟩

/-- A satisfiable instance with 3 variables and 4 clauses. -/
def uf_3_4_02 : CNF :=
  [[⟨0, true⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩], [⟨1, true⟩, ⟨2, false⟩],
   [⟨0, false⟩, ⟨1, true⟩, ⟨2, false⟩]]

theorem satisfiable_uf_3_4_02 : uf_3_4_02.Satisfiable :=
  ⟨fun i => [false, false, false].getD i false, rfl⟩

theorem isKCNF_uf_3_4_02 : uf_3_4_02.IsKCNF 3 := by decide

theorem encode_uf_3_4_02_mem_ThreeSAT : Encoding.encode uf_3_4_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_4_02, satisfiable_uf_3_4_02⟩

/-- A satisfiable instance with 4 variables and 3 clauses. -/
def uf_4_3_01 : CNF :=
  [[⟨0, true⟩, ⟨1, false⟩, ⟨3, true⟩], [⟨0, true⟩, ⟨2, false⟩, ⟨3, false⟩],
   [⟨0, false⟩, ⟨3, true⟩]]

theorem satisfiable_uf_4_3_01 : uf_4_3_01.Satisfiable :=
  ⟨fun i => [true, true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_4_3_01 : uf_4_3_01.IsKCNF 3 := by decide

theorem encode_uf_4_3_01_mem_ThreeSAT : Encoding.encode uf_4_3_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_3_01, satisfiable_uf_4_3_01⟩

/-- A satisfiable instance with 4 variables and 5 clauses. -/
def uf_4_5_02 : CNF :=
  [[⟨0, false⟩, ⟨1, true⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨3, false⟩],
   [⟨0, true⟩, ⟨1, false⟩, ⟨3, true⟩], [⟨0, false⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, true⟩]]

theorem satisfiable_uf_4_5_02 : uf_4_5_02.Satisfiable :=
  ⟨fun i => [true, true, false, true].getD i false, rfl⟩

theorem isKCNF_uf_4_5_02 : uf_4_5_02.IsKCNF 3 := by decide

theorem encode_uf_4_5_02_mem_ThreeSAT : Encoding.encode uf_4_5_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_5_02, satisfiable_uf_4_5_02⟩

theorem eval_uf_4_5_02_eq_false :
    uf_4_5_02.eval (fun i => [false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 5 variables and 5 clauses. -/
def uf_5_5_02 : CNF :=
  [[⟨1, true⟩, ⟨3, true⟩], [⟨1, false⟩, ⟨2, false⟩, ⟨4, false⟩], [⟨0, false⟩, ⟨4, false⟩],
   [⟨1, false⟩, ⟨2, true⟩, ⟨4, false⟩], [⟨0, true⟩, ⟨1, true⟩]]

theorem satisfiable_uf_5_5_02 : uf_5_5_02.Satisfiable :=
  ⟨fun i => [false, true, true, false, true].getD i false, rfl⟩

theorem isKCNF_uf_5_5_02 : uf_5_5_02.IsKCNF 3 := by decide

theorem encode_uf_5_5_02_mem_ThreeSAT : Encoding.encode uf_5_5_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_5_02, satisfiable_uf_5_5_02⟩

theorem encode_uf_5_5_02_mem_SAT : Encoding.encode uf_5_5_02 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_5_5_02_mem_ThreeSAT

/-- A satisfiable instance with 3 variables and 3 clauses. -/
def uf_3_3_02 : CNF :=
  [[⟨0, true⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨1, false⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_3_02 : uf_3_3_02.Satisfiable :=
  ⟨fun i => [false, false, false].getD i false, rfl⟩

theorem isKCNF_uf_3_3_02 : uf_3_3_02.IsKCNF 3 := by decide

theorem encode_uf_3_3_02_mem_ThreeSAT : Encoding.encode uf_3_3_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_3_02, satisfiable_uf_3_3_02⟩

theorem encode_uf_3_3_02_mem_SAT : Encoding.encode uf_3_3_02 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_3_02_mem_ThreeSAT

/-- A satisfiable instance with 3 variables and 6 clauses. -/
def uf_3_6_01 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨2, false⟩],
   [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩], [⟨1, true⟩, ⟨2, false⟩], [⟨1, false⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_6_01 : uf_3_6_01.Satisfiable :=
  ⟨fun i => [true, false, false].getD i false, rfl⟩

theorem isKCNF_uf_3_6_01 : uf_3_6_01.IsKCNF 3 := by decide

theorem encode_uf_3_6_01_mem_ThreeSAT : Encoding.encode uf_3_6_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_6_01, satisfiable_uf_3_6_01⟩

theorem encode_uf_3_6_01_mem_SAT : Encoding.encode uf_3_6_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_6_01_mem_ThreeSAT

theorem eval_uf_3_6_01_eq_false :
    uf_3_6_01.eval (fun i => [false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 5 variables and 6 clauses. -/
def uf_5_6_01 : CNF :=
  [[⟨0, false⟩, ⟨1, true⟩, ⟨2, true⟩], [⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩],
   [⟨0, false⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨2, false⟩, ⟨4, true⟩],
   [⟨1, true⟩, ⟨3, true⟩, ⟨4, false⟩], [⟨0, true⟩, ⟨2, false⟩]]

theorem satisfiable_uf_5_6_01 : uf_5_6_01.Satisfiable :=
  ⟨fun i => [false, true, false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_5_6_01 : uf_5_6_01.IsKCNF 3 := by decide

theorem encode_uf_5_6_01_mem_ThreeSAT : Encoding.encode uf_5_6_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_6_01, satisfiable_uf_5_6_01⟩

theorem eval_uf_5_6_01_eq_false :
    uf_5_6_01.eval (fun i => [true, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 4 variables and 8 clauses. -/
def uf_4_8_01 : CNF :=
  [[⟨2, false⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨2, true⟩, ⟨3, true⟩],
   [⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩],
   [⟨1, false⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨1, false⟩], [⟨0, false⟩, ⟨3, false⟩],
   [⟨0, false⟩, ⟨2, false⟩, ⟨3, true⟩]]

theorem satisfiable_uf_4_8_01 : uf_4_8_01.Satisfiable :=
  ⟨fun i => [true, true, false, true].getD i false, rfl⟩

theorem isKCNF_uf_4_8_01 : uf_4_8_01.IsKCNF 3 := by decide

theorem encode_uf_4_8_01_mem_ThreeSAT : Encoding.encode uf_4_8_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_8_01, satisfiable_uf_4_8_01⟩

/-- A satisfiable instance with 3 variables and 3 clauses. -/
def uf_3_3_03 : CNF :=
  [[⟨0, true⟩, ⟨1, true⟩, ⟨2, false⟩], [⟨0, true⟩, ⟨1, false⟩],
   [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_3_03 : uf_3_3_03.Satisfiable :=
  ⟨fun i => [false, false, true].getD i false, rfl⟩

theorem isKCNF_uf_3_3_03 : uf_3_3_03.IsKCNF 3 := by decide

theorem encode_uf_3_3_03_mem_ThreeSAT : Encoding.encode uf_3_3_03 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_3_03, satisfiable_uf_3_3_03⟩

/-- A satisfiable instance with 4 variables and 5 clauses. -/
def uf_4_5_03 : CNF :=
  [[⟨1, true⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨2, false⟩, ⟨3, true⟩],
   [⟨0, true⟩, ⟨1, true⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, true⟩], [⟨0, true⟩, ⟨2, true⟩]]

theorem satisfiable_uf_4_5_03 : uf_4_5_03.Satisfiable :=
  ⟨fun i => [true, false, false, false].getD i false, rfl⟩

theorem isKCNF_uf_4_5_03 : uf_4_5_03.IsKCNF 3 := by decide

theorem encode_uf_4_5_03_mem_ThreeSAT : Encoding.encode uf_4_5_03 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_5_03, satisfiable_uf_4_5_03⟩

theorem encode_uf_4_5_03_mem_SAT : Encoding.encode uf_4_5_03 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_4_5_03_mem_ThreeSAT

/-- A satisfiable instance with 5 variables and 6 clauses. -/
def uf_5_6_02 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩], [⟨0, false⟩, ⟨3, false⟩], [⟨2, false⟩, ⟨3, true⟩, ⟨4, false⟩],
   [⟨2, false⟩, ⟨4, true⟩], [⟨1, false⟩, ⟨3, false⟩, ⟨4, false⟩],
   [⟨0, false⟩, ⟨2, false⟩, ⟨3, true⟩]]

theorem satisfiable_uf_5_6_02 : uf_5_6_02.Satisfiable :=
  ⟨fun i => [false, true, true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_5_6_02 : uf_5_6_02.IsKCNF 3 := by decide

theorem encode_uf_5_6_02_mem_ThreeSAT : Encoding.encode uf_5_6_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_6_02, satisfiable_uf_5_6_02⟩

theorem encode_uf_5_6_02_mem_SAT : Encoding.encode uf_5_6_02 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_5_6_02_mem_ThreeSAT

/-- A satisfiable instance with 6 variables and 8 clauses. -/
def uf_6_8_02 : CNF :=
  [[⟨0, false⟩, ⟨3, false⟩, ⟨5, false⟩], [⟨0, false⟩, ⟨1, true⟩], [⟨1, true⟩, ⟨4, true⟩],
   [⟨2, false⟩, ⟨4, true⟩, ⟨5, false⟩], [⟨2, true⟩, ⟨3, false⟩], [⟨0, false⟩, ⟨5, true⟩],
   [⟨1, true⟩, ⟨2, true⟩, ⟨4, true⟩], [⟨0, true⟩, ⟨2, true⟩, ⟨5, false⟩]]

theorem satisfiable_uf_6_8_02 : uf_6_8_02.Satisfiable :=
  ⟨fun i => [true, false, true, true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_6_8_02 : uf_6_8_02.IsKCNF 3 := by decide

theorem encode_uf_6_8_02_mem_ThreeSAT : Encoding.encode uf_6_8_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_6_8_02, satisfiable_uf_6_8_02⟩

theorem eval_uf_6_8_02_eq_false :
    uf_6_8_02.eval (fun i => [false, false, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 3 variables and 3 clauses. -/
def uf_3_3_04 : CNF :=
  [[⟨0, true⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨2, false⟩],
   [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_3_04 : uf_3_3_04.Satisfiable :=
  ⟨fun i => [false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_3_3_04 : uf_3_3_04.IsKCNF 3 := by decide

theorem encode_uf_3_3_04_mem_ThreeSAT : Encoding.encode uf_3_3_04 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_3_04, satisfiable_uf_3_3_04⟩

theorem encode_uf_3_3_04_mem_SAT : Encoding.encode uf_3_3_04 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_3_04_mem_ThreeSAT

theorem eval_uf_3_3_04_eq_false :
    uf_3_3_04.eval (fun i => [false, true, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 5 variables and 8 clauses. -/
def uf_5_8_01 : CNF :=
  [[⟨0, false⟩, ⟨4, false⟩], [⟨1, false⟩, ⟨2, true⟩, ⟨4, true⟩], [⟨2, false⟩, ⟨3, false⟩],
   [⟨0, true⟩, ⟨1, true⟩, ⟨3, true⟩], [⟨0, true⟩, ⟨2, false⟩, ⟨3, false⟩],
   [⟨2, false⟩, ⟨3, true⟩, ⟨4, false⟩], [⟨2, false⟩, ⟨4, false⟩],
   [⟨0, false⟩, ⟨1, true⟩, ⟨3, true⟩]]

theorem satisfiable_uf_5_8_01 : uf_5_8_01.Satisfiable :=
  ⟨fun i => [true, true, true, false, true].getD i false, rfl⟩

theorem isKCNF_uf_5_8_01 : uf_5_8_01.IsKCNF 3 := by decide

theorem encode_uf_5_8_01_mem_ThreeSAT : Encoding.encode uf_5_8_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_8_01, satisfiable_uf_5_8_01⟩

theorem eval_uf_5_8_01_eq_false :
    uf_5_8_01.eval (fun i => [false, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 3 variables and 5 clauses. -/
def uf_3_5_02 : CNF :=
  [[⟨1, true⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, false⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_5_02 : uf_3_5_02.Satisfiable :=
  ⟨fun i => [true, false, false].getD i false, rfl⟩

theorem isKCNF_uf_3_5_02 : uf_3_5_02.IsKCNF 3 := by decide

theorem encode_uf_3_5_02_mem_ThreeSAT : Encoding.encode uf_3_5_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_5_02, satisfiable_uf_3_5_02⟩

theorem encode_uf_3_5_02_mem_SAT : Encoding.encode uf_3_5_02 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_5_02_mem_ThreeSAT

theorem eval_uf_3_5_02_eq_false :
    uf_3_5_02.eval (fun i => [false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 3 variables and 5 clauses. -/
def uf_3_5_03 : CNF :=
  [[⟨0, true⟩, ⟨2, false⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨1, true⟩, ⟨2, false⟩], [⟨1, false⟩, ⟨2, false⟩], [⟨0, true⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_5_03 : uf_3_5_03.Satisfiable :=
  ⟨fun i => [false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_3_5_03 : uf_3_5_03.IsKCNF 3 := by decide

theorem encode_uf_3_5_03_mem_ThreeSAT : Encoding.encode uf_3_5_03 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_5_03, satisfiable_uf_3_5_03⟩

theorem encode_uf_3_5_03_mem_SAT : Encoding.encode uf_3_5_03 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_5_03_mem_ThreeSAT

theorem eval_uf_3_5_03_eq_false :
    uf_3_5_03.eval (fun i => [false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 3 variables and 7 clauses. -/
def uf_3_7_01 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, false⟩], [⟨1, false⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, true⟩],
   [⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_7_01 : uf_3_7_01.Satisfiable :=
  ⟨fun i => [true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_3_7_01 : uf_3_7_01.IsKCNF 3 := by decide

theorem encode_uf_3_7_01_mem_ThreeSAT : Encoding.encode uf_3_7_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_7_01, satisfiable_uf_3_7_01⟩

theorem encode_uf_3_7_01_mem_SAT : Encoding.encode uf_3_7_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_7_01_mem_ThreeSAT

/-- A satisfiable instance with 3 variables and 4 clauses. -/
def uf_3_4_03 : CNF :=
  [[⟨1, false⟩, ⟨2, false⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨1, true⟩, ⟨2, false⟩]]

theorem satisfiable_uf_3_4_03 : uf_3_4_03.Satisfiable :=
  ⟨fun i => [false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_3_4_03 : uf_3_4_03.IsKCNF 3 := by decide

theorem encode_uf_3_4_03_mem_ThreeSAT : Encoding.encode uf_3_4_03 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_4_03, satisfiable_uf_3_4_03⟩

theorem eval_uf_3_4_03_eq_false :
    uf_3_4_03.eval (fun i => [false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 6 variables and 6 clauses. -/
def uf_6_6_01 : CNF :=
  [[⟨3, false⟩, ⟨5, true⟩], [⟨3, true⟩, ⟨5, false⟩], [⟨0, true⟩, ⟨3, true⟩],
   [⟨2, false⟩, ⟨4, true⟩], [⟨0, true⟩, ⟨5, true⟩], [⟨1, false⟩, ⟨3, true⟩]]

theorem satisfiable_uf_6_6_01 : uf_6_6_01.Satisfiable :=
  ⟨fun i => [false, true, true, false, true, false].getD i false, rfl⟩

theorem isKCNF_uf_6_6_01 : uf_6_6_01.IsKCNF 3 := by decide

theorem encode_uf_6_6_01_mem_ThreeSAT : Encoding.encode uf_6_6_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_6_6_01, satisfiable_uf_6_6_01⟩

theorem encode_uf_6_6_01_mem_SAT : Encoding.encode uf_6_6_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_6_6_01_mem_ThreeSAT

theorem eval_uf_6_6_01_eq_false :
    uf_6_6_01.eval (fun i => [false, false, false, true, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 3 variables and 4 clauses. -/
def uf_3_4_04 : CNF :=
  [[⟨1, true⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩], [⟨1, false⟩, ⟨2, false⟩],
   [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_4_04 : uf_3_4_04.Satisfiable :=
  ⟨fun i => [false, false, true].getD i false, rfl⟩

theorem isKCNF_uf_3_4_04 : uf_3_4_04.IsKCNF 3 := by decide

theorem encode_uf_3_4_04_mem_ThreeSAT : Encoding.encode uf_3_4_04 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_4_04, satisfiable_uf_3_4_04⟩

theorem encode_uf_3_4_04_mem_SAT : Encoding.encode uf_3_4_04 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_4_04_mem_ThreeSAT

/-- A satisfiable instance with 4 variables and 5 clauses. -/
def uf_4_5_04 : CNF :=
  [[⟨0, false⟩, ⟨1, true⟩, ⟨3, true⟩], [⟨2, true⟩, ⟨3, false⟩],
   [⟨0, false⟩, ⟨1, false⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨3, true⟩],
   [⟨1, true⟩, ⟨2, false⟩, ⟨3, false⟩]]

theorem satisfiable_uf_4_5_04 : uf_4_5_04.Satisfiable :=
  ⟨fun i => [false, false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_4_5_04 : uf_4_5_04.IsKCNF 3 := by decide

theorem encode_uf_4_5_04_mem_ThreeSAT : Encoding.encode uf_4_5_04 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_5_04, satisfiable_uf_4_5_04⟩

theorem encode_uf_4_5_04_mem_SAT : Encoding.encode uf_4_5_04 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_4_5_04_mem_ThreeSAT

/-- A satisfiable instance with 6 variables and 8 clauses. -/
def uf_6_8_03 : CNF :=
  [[⟨0, false⟩, ⟨4, false⟩], [⟨2, false⟩, ⟨4, false⟩], [⟨3, true⟩, ⟨5, true⟩],
   [⟨0, false⟩, ⟨2, true⟩, ⟨4, true⟩], [⟨2, false⟩, ⟨3, true⟩, ⟨4, false⟩],
   [⟨2, false⟩, ⟨3, false⟩], [⟨1, true⟩, ⟨2, false⟩], [⟨4, true⟩, ⟨5, false⟩]]

theorem satisfiable_uf_6_8_03 : uf_6_8_03.Satisfiable :=
  ⟨fun i => [true, false, true, false, false, true].getD i false, rfl⟩

theorem isKCNF_uf_6_8_03 : uf_6_8_03.IsKCNF 3 := by decide

theorem encode_uf_6_8_03_mem_ThreeSAT : Encoding.encode uf_6_8_03 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_6_8_03, satisfiable_uf_6_8_03⟩

theorem encode_uf_6_8_03_mem_SAT : Encoding.encode uf_6_8_03 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_6_8_03_mem_ThreeSAT

/-- A satisfiable instance with 4 variables and 4 clauses. -/
def uf_4_4_01 : CNF :=
  [[⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨1, false⟩, ⟨2, false⟩, ⟨3, true⟩],
   [⟨1, false⟩, ⟨2, true⟩], [⟨1, true⟩, ⟨2, false⟩]]

theorem satisfiable_uf_4_4_01 : uf_4_4_01.Satisfiable :=
  ⟨fun i => [false, false, false, false].getD i false, rfl⟩

theorem isKCNF_uf_4_4_01 : uf_4_4_01.IsKCNF 3 := by decide

theorem encode_uf_4_4_01_mem_ThreeSAT : Encoding.encode uf_4_4_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_4_01, satisfiable_uf_4_4_01⟩

theorem encode_uf_4_4_01_mem_SAT : Encoding.encode uf_4_4_01 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_4_4_01_mem_ThreeSAT

theorem eval_uf_4_4_01_eq_false :
    uf_4_4_01.eval (fun i => [true, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 4 variables and 4 clauses. -/
def uf_4_4_02 : CNF :=
  [[⟨1, false⟩, ⟨2, true⟩, ⟨3, true⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨3, true⟩],
   [⟨0, true⟩, ⟨1, true⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩]]

theorem satisfiable_uf_4_4_02 : uf_4_4_02.Satisfiable :=
  ⟨fun i => [false, true, true, false].getD i false, rfl⟩

theorem isKCNF_uf_4_4_02 : uf_4_4_02.IsKCNF 3 := by decide

theorem encode_uf_4_4_02_mem_ThreeSAT : Encoding.encode uf_4_4_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_4_02, satisfiable_uf_4_4_02⟩

theorem eval_uf_4_4_02_eq_false :
    uf_4_4_02.eval (fun i => [true, true, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 5 variables and 6 clauses. -/
def uf_5_6_03 : CNF :=
  [[⟨1, false⟩, ⟨2, false⟩, ⟨4, false⟩], [⟨2, true⟩, ⟨3, true⟩, ⟨4, true⟩],
   [⟨2, true⟩, ⟨4, false⟩], [⟨0, false⟩, ⟨3, false⟩, ⟨4, false⟩], [⟨1, false⟩, ⟨4, true⟩],
   [⟨0, false⟩, ⟨2, false⟩, ⟨4, false⟩]]

theorem satisfiable_uf_5_6_03 : uf_5_6_03.Satisfiable :=
  ⟨fun i => [false, true, false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_5_6_03 : uf_5_6_03.IsKCNF 3 := by decide

theorem encode_uf_5_6_03_mem_ThreeSAT : Encoding.encode uf_5_6_03 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_6_03, satisfiable_uf_5_6_03⟩

theorem encode_uf_5_6_03_mem_SAT : Encoding.encode uf_5_6_03 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_5_6_03_mem_ThreeSAT

theorem eval_uf_5_6_03_eq_false :
    uf_5_6_03.eval (fun i => [false, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 4 variables and 8 clauses. -/
def uf_4_8_02 : CNF :=
  [[⟨0, true⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨3, true⟩],
   [⟨0, false⟩, ⟨1, true⟩, ⟨3, true⟩], [⟨1, true⟩, ⟨2, false⟩, ⟨3, false⟩],
   [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩], [⟨0, false⟩, ⟨1, false⟩, ⟨3, true⟩],
   [⟨0, true⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩]]

theorem satisfiable_uf_4_8_02 : uf_4_8_02.Satisfiable :=
  ⟨fun i => [false, false, false, false].getD i false, rfl⟩

theorem isKCNF_uf_4_8_02 : uf_4_8_02.IsKCNF 3 := by decide

theorem encode_uf_4_8_02_mem_ThreeSAT : Encoding.encode uf_4_8_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_4_8_02, satisfiable_uf_4_8_02⟩

theorem encode_uf_4_8_02_mem_SAT : Encoding.encode uf_4_8_02 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_4_8_02_mem_ThreeSAT

theorem eval_uf_4_8_02_eq_false :
    uf_4_8_02.eval (fun i => [true, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 6 variables and 7 clauses. -/
def uf_6_7_01 : CNF :=
  [[⟨3, false⟩, ⟨4, true⟩], [⟨1, true⟩, ⟨3, true⟩, ⟨4, false⟩], [⟨0, false⟩, ⟨1, false⟩],
   [⟨1, false⟩, ⟨2, true⟩], [⟨1, true⟩, ⟨2, false⟩, ⟨5, true⟩],
   [⟨0, true⟩, ⟨1, true⟩, ⟨2, false⟩], [⟨1, true⟩, ⟨2, true⟩, ⟨4, true⟩]]

theorem satisfiable_uf_6_7_01 : uf_6_7_01.Satisfiable :=
  ⟨fun i => [true, false, false, true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_6_7_01 : uf_6_7_01.IsKCNF 3 := by decide

theorem encode_uf_6_7_01_mem_ThreeSAT : Encoding.encode uf_6_7_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_6_7_01, satisfiable_uf_6_7_01⟩

/-- A satisfiable instance with 5 variables and 6 clauses. -/
def uf_5_6_04 : CNF :=
  [[⟨0, false⟩, ⟨2, false⟩, ⟨4, true⟩], [⟨1, false⟩, ⟨3, true⟩],
   [⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨1, true⟩, ⟨4, false⟩],
   [⟨0, true⟩, ⟨1, true⟩, ⟨4, true⟩], [⟨0, false⟩, ⟨1, false⟩, ⟨2, true⟩]]

theorem satisfiable_uf_5_6_04 : uf_5_6_04.Satisfiable :=
  ⟨fun i => [false, true, true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_5_6_04 : uf_5_6_04.IsKCNF 3 := by decide

theorem encode_uf_5_6_04_mem_ThreeSAT : Encoding.encode uf_5_6_04 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_6_04, satisfiable_uf_5_6_04⟩

theorem encode_uf_5_6_04_mem_SAT : Encoding.encode uf_5_6_04 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_5_6_04_mem_ThreeSAT

theorem eval_uf_5_6_04_eq_false :
    uf_5_6_04.eval (fun i => [true, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 5 variables and 6 clauses. -/
def uf_5_6_05 : CNF :=
  [[⟨2, false⟩, ⟨4, true⟩], [⟨0, true⟩, ⟨3, true⟩, ⟨4, true⟩], [⟨0, false⟩, ⟨4, false⟩],
   [⟨0, false⟩, ⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩],
   [⟨1, false⟩, ⟨2, false⟩, ⟨3, false⟩]]

theorem satisfiable_uf_5_6_05 : uf_5_6_05.Satisfiable :=
  ⟨fun i => [false, false, true, true, true].getD i false, rfl⟩

theorem isKCNF_uf_5_6_05 : uf_5_6_05.IsKCNF 3 := by decide

theorem encode_uf_5_6_05_mem_ThreeSAT : Encoding.encode uf_5_6_05 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_6_05, satisfiable_uf_5_6_05⟩

theorem encode_uf_5_6_05_mem_SAT : Encoding.encode uf_5_6_05 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_5_6_05_mem_ThreeSAT

theorem eval_uf_5_6_05_eq_false :
    uf_5_6_05.eval (fun i => [false, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 6 variables and 6 clauses. -/
def uf_6_6_02 : CNF :=
  [[⟨1, true⟩, ⟨4, false⟩, ⟨5, true⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨2, false⟩],
   [⟨2, true⟩, ⟨3, true⟩, ⟨4, false⟩], [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩],
   [⟨0, false⟩, ⟨1, true⟩, ⟨5, true⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨3, true⟩]]

theorem satisfiable_uf_6_6_02 : uf_6_6_02.Satisfiable :=
  ⟨fun i => [true, false, false, true, false, true].getD i false, rfl⟩

theorem isKCNF_uf_6_6_02 : uf_6_6_02.IsKCNF 3 := by decide

theorem encode_uf_6_6_02_mem_ThreeSAT : Encoding.encode uf_6_6_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_6_6_02, satisfiable_uf_6_6_02⟩

theorem eval_uf_6_6_02_eq_false :
    uf_6_6_02.eval (fun i => [false, false, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 3 variables and 3 clauses. -/
def uf_3_3_05 : CNF :=
  [[⟨1, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨2, false⟩],
   [⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩]]

theorem satisfiable_uf_3_3_05 : uf_3_3_05.Satisfiable :=
  ⟨fun i => [true, true, false].getD i false, rfl⟩

theorem isKCNF_uf_3_3_05 : uf_3_3_05.IsKCNF 3 := by decide

theorem encode_uf_3_3_05_mem_ThreeSAT : Encoding.encode uf_3_3_05 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_3_05, satisfiable_uf_3_3_05⟩

theorem eval_uf_3_3_05_eq_false :
    uf_3_3_05.eval (fun i => [true, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 6 variables and 4 clauses. -/
def uf_6_4_02 : CNF :=
  [[⟨3, true⟩, ⟨5, false⟩], [⟨0, false⟩, ⟨4, true⟩], [⟨1, true⟩, ⟨2, false⟩],
   [⟨0, true⟩, ⟨4, false⟩]]

theorem satisfiable_uf_6_4_02 : uf_6_4_02.Satisfiable :=
  ⟨fun i => [true, false, false, false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_6_4_02 : uf_6_4_02.IsKCNF 3 := by decide

theorem encode_uf_6_4_02_mem_ThreeSAT : Encoding.encode uf_6_4_02 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_6_4_02, satisfiable_uf_6_4_02⟩

theorem encode_uf_6_4_02_mem_SAT : Encoding.encode uf_6_4_02 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_6_4_02_mem_ThreeSAT

theorem eval_uf_6_4_02_eq_false :
    uf_6_4_02.eval (fun i => [true, false, false, false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 3 variables and 8 clauses. -/
def uf_3_8_01 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨2, false⟩],
   [⟨0, false⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨0, true⟩, ⟨1, true⟩],
   [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩],
   [⟨1, false⟩, ⟨2, false⟩]]

theorem satisfiable_uf_3_8_01 : uf_3_8_01.Satisfiable :=
  ⟨fun i => [false, true, false].getD i false, rfl⟩

theorem isKCNF_uf_3_8_01 : uf_3_8_01.IsKCNF 3 := by decide

theorem encode_uf_3_8_01_mem_ThreeSAT : Encoding.encode uf_3_8_01 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_8_01, satisfiable_uf_3_8_01⟩

theorem eval_uf_3_8_01_eq_false :
    uf_3_8_01.eval (fun i => [false, false, false].getD i false) = false :=
  rfl

/-- A satisfiable instance with 5 variables and 5 clauses. -/
def uf_5_5_03 : CNF :=
  [[⟨1, false⟩, ⟨3, false⟩], [⟨0, false⟩, ⟨3, false⟩], [⟨0, true⟩, ⟨4, true⟩],
   [⟨0, true⟩, ⟨1, false⟩], [⟨2, false⟩, ⟨3, true⟩, ⟨4, false⟩]]

theorem satisfiable_uf_5_5_03 : uf_5_5_03.Satisfiable :=
  ⟨fun i => [false, true, false, true, true].getD i false, rfl⟩

theorem isKCNF_uf_5_5_03 : uf_5_5_03.IsKCNF 3 := by decide

theorem encode_uf_5_5_03_mem_ThreeSAT : Encoding.encode uf_5_5_03 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_5_5_03, satisfiable_uf_5_5_03⟩

theorem encode_uf_5_5_03_mem_SAT : Encoding.encode uf_5_5_03 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_5_5_03_mem_ThreeSAT

/-- A satisfiable instance with 3 variables and 3 clauses. -/
def uf_3_3_06 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨2, true⟩]]

theorem satisfiable_uf_3_3_06 : uf_3_3_06.Satisfiable :=
  ⟨fun i => [true, true, false].getD i false, rfl⟩

theorem isKCNF_uf_3_3_06 : uf_3_3_06.IsKCNF 3 := by decide

theorem encode_uf_3_3_06_mem_ThreeSAT : Encoding.encode uf_3_3_06 ∈ ThreeSAT :=
  encode_mem_ThreeSAT.2 ⟨isKCNF_uf_3_3_06, satisfiable_uf_3_3_06⟩

theorem encode_uf_3_3_06_mem_SAT : Encoding.encode uf_3_3_06 ∈ SAT :=
  threeSAT_subset_SAT encode_uf_3_3_06_mem_ThreeSAT

theorem eval_uf_3_3_06_eq_false :
    uf_3_3_06.eval (fun i => [false, false, false].getD i false) = false :=
  rfl

/-! ### Unsatisfiable instances -/

/-- An unsatisfiable instance with 2 variables and 4 clauses. -/
def uuf_2_4_01 : CNF :=
  [[⟨0, false⟩, ⟨1, true⟩], [⟨1, true⟩], [⟨0, true⟩], [⟨0, false⟩]]

theorem not_satisfiable_uuf_2_4_01 : ¬uuf_2_4_01.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_4_01, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_4_01_not_mem_SAT : Encoding.encode uuf_2_4_01 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_4_01 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 3 clauses. -/
def uuf_2_3_01 : CNF :=
  [[⟨0, true⟩], [⟨0, false⟩, ⟨1, false⟩], [⟨1, true⟩]]

theorem not_satisfiable_uuf_2_3_01 : ¬uuf_2_3_01.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_3_01, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_3_01_not_mem_SAT : Encoding.encode uuf_2_3_01 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_3_01 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 5 clauses. -/
def uuf_2_5_01 : CNF :=
  [[⟨0, false⟩, ⟨1, true⟩], [⟨0, false⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨1, false⟩], [⟨0, true⟩],
   [⟨1, true⟩]]

theorem not_satisfiable_uuf_2_5_01 : ¬uuf_2_5_01.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_5_01, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_5_01_not_mem_SAT : Encoding.encode uuf_2_5_01 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_5_01 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 5 clauses. -/
def uuf_2_5_02 : CNF :=
  [[⟨0, true⟩], [⟨1, false⟩], [⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨1, true⟩]]

theorem not_satisfiable_uuf_2_5_02 : ¬uuf_2_5_02.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_5_02, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_5_02_not_mem_SAT : Encoding.encode uuf_2_5_02 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_5_02 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 4 clauses. -/
def uuf_2_4_02 : CNF :=
  [[⟨1, false⟩], [⟨0, false⟩, ⟨1, false⟩], [⟨1, true⟩], [⟨0, true⟩, ⟨1, true⟩]]

theorem not_satisfiable_uuf_2_4_02 : ¬uuf_2_4_02.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_4_02, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_4_02_not_mem_SAT : Encoding.encode uuf_2_4_02 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_4_02 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 4 clauses. -/
def uuf_2_4_03 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩], [⟨0, false⟩], [⟨1, true⟩], [⟨1, false⟩]]

theorem not_satisfiable_uuf_2_4_03 : ¬uuf_2_4_03.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_4_03, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_4_03_not_mem_SAT : Encoding.encode uuf_2_4_03 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_4_03 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 3 clauses. -/
def uuf_2_3_02 : CNF :=
  [[⟨0, true⟩, ⟨1, false⟩], [⟨0, false⟩], [⟨1, true⟩]]

theorem not_satisfiable_uuf_2_3_02 : ¬uuf_2_3_02.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_3_02, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_3_02_not_mem_SAT : Encoding.encode uuf_2_3_02 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_3_02 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 5 clauses. -/
def uuf_2_5_03 : CNF :=
  [[⟨0, true⟩, ⟨1, true⟩], [⟨0, true⟩], [⟨0, false⟩], [⟨0, true⟩, ⟨1, false⟩], [⟨1, true⟩]]

theorem not_satisfiable_uuf_2_5_03 : ¬uuf_2_5_03.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_5_03, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_5_03_not_mem_SAT : Encoding.encode uuf_2_5_03 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_5_03 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 4 clauses. -/
def uuf_2_4_04 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩], [⟨1, false⟩], [⟨1, true⟩], [⟨0, true⟩]]

theorem not_satisfiable_uuf_2_4_04 : ¬uuf_2_4_04.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_4_04, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_4_04_not_mem_SAT : Encoding.encode uuf_2_4_04 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_4_04 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 6 clauses. -/
def uuf_2_6_01 : CNF :=
  [[⟨0, false⟩, ⟨1, true⟩], [⟨1, true⟩], [⟨0, true⟩], [⟨0, false⟩], [⟨1, false⟩],
   [⟨0, true⟩, ⟨1, true⟩]]

theorem not_satisfiable_uuf_2_6_01 : ¬uuf_2_6_01.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_6_01, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_6_01_not_mem_SAT : Encoding.encode uuf_2_6_01 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_6_01 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 3 variables and 7 clauses. -/
def uuf_3_7_01 : CNF :=
  [[⟨1, true⟩, ⟨2, false⟩], [⟨1, true⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨1, false⟩], [⟨0, false⟩, ⟨1, true⟩], [⟨1, false⟩, ⟨2, false⟩],
   [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩]]

theorem not_satisfiable_uuf_3_7_01 : ¬uuf_3_7_01.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
    simp [uuf_3_7_01, CNF.eval, Clause.eval, Literal.eval, h0, h1, h2] at hσ

theorem encode_uuf_3_7_01_not_mem_SAT : Encoding.encode uuf_3_7_01 ∉ SAT :=
  fun h => not_satisfiable_uuf_3_7_01 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 5 clauses. -/
def uuf_2_5_04 : CNF :=
  [[⟨0, true⟩], [⟨0, false⟩, ⟨1, true⟩], [⟨1, false⟩], [⟨0, false⟩], [⟨0, false⟩, ⟨1, false⟩]]

theorem not_satisfiable_uuf_2_5_04 : ¬uuf_2_5_04.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_5_04, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_5_04_not_mem_SAT : Encoding.encode uuf_2_5_04 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_5_04 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 3 clauses. -/
def uuf_2_3_03 : CNF :=
  [[⟨0, false⟩], [⟨0, true⟩], [⟨1, false⟩]]

theorem not_satisfiable_uuf_2_3_03 : ¬uuf_2_3_03.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_3_03, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_3_03_not_mem_SAT : Encoding.encode uuf_2_3_03 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_3_03 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 5 clauses. -/
def uuf_2_5_05 : CNF :=
  [[⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩], [⟨0, false⟩], [⟨0, true⟩], [⟨0, false⟩, ⟨1, true⟩]]

theorem not_satisfiable_uuf_2_5_05 : ¬uuf_2_5_05.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_5_05, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_5_05_not_mem_SAT : Encoding.encode uuf_2_5_05 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_5_05 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 4 clauses. -/
def uuf_2_4_05 : CNF :=
  [[⟨0, false⟩, ⟨1, true⟩], [⟨0, false⟩], [⟨0, true⟩, ⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩]]

theorem not_satisfiable_uuf_2_4_05 : ¬uuf_2_4_05.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_4_05, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_4_05_not_mem_SAT : Encoding.encode uuf_2_4_05 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_4_05 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 4 clauses. -/
def uuf_2_4_06 : CNF :=
  [[⟨0, true⟩], [⟨0, false⟩], [⟨0, true⟩, ⟨1, true⟩], [⟨1, true⟩]]

theorem not_satisfiable_uuf_2_4_06 : ¬uuf_2_4_06.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_4_06, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_4_06_not_mem_SAT : Encoding.encode uuf_2_4_06 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_4_06 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 4 clauses. -/
def uuf_2_4_07 : CNF :=
  [[⟨0, false⟩, ⟨1, false⟩], [⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩], [⟨1, false⟩]]

theorem not_satisfiable_uuf_2_4_07 : ¬uuf_2_4_07.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_4_07, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_4_07_not_mem_SAT : Encoding.encode uuf_2_4_07 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_4_07 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 3 variables and 8 clauses. -/
def uuf_3_8_01 : CNF :=
  [[⟨0, true⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, false⟩],
   [⟨0, true⟩, ⟨1, true⟩], [⟨0, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, false⟩, ⟨2, true⟩],
   [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩]]

theorem not_satisfiable_uuf_3_8_01 : ¬uuf_3_8_01.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
    simp [uuf_3_8_01, CNF.eval, Clause.eval, Literal.eval, h0, h1, h2] at hσ

theorem encode_uuf_3_8_01_not_mem_SAT : Encoding.encode uuf_3_8_01 ∉ SAT :=
  fun h => not_satisfiable_uuf_3_8_01 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 4 clauses. -/
def uuf_2_4_08 : CNF :=
  [[⟨1, false⟩], [⟨0, true⟩, ⟨1, false⟩], [⟨0, true⟩], [⟨0, false⟩, ⟨1, true⟩]]

theorem not_satisfiable_uuf_2_4_08 : ¬uuf_2_4_08.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_4_08, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_4_08_not_mem_SAT : Encoding.encode uuf_2_4_08 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_4_08 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 6 clauses. -/
def uuf_2_6_02 : CNF :=
  [[⟨0, true⟩], [⟨1, true⟩], [⟨0, false⟩, ⟨1, true⟩], [⟨0, false⟩, ⟨1, false⟩],
   [⟨0, true⟩, ⟨1, false⟩], [⟨1, false⟩]]

theorem not_satisfiable_uuf_2_6_02 : ¬uuf_2_6_02.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_6_02, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_6_02_not_mem_SAT : Encoding.encode uuf_2_6_02 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_6_02 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 4 clauses. -/
def uuf_2_4_09 : CNF :=
  [[⟨0, true⟩, ⟨1, false⟩], [⟨0, false⟩], [⟨0, true⟩, ⟨1, true⟩], [⟨1, true⟩]]

theorem not_satisfiable_uuf_2_4_09 : ¬uuf_2_4_09.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_4_09, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_4_09_not_mem_SAT : Encoding.encode uuf_2_4_09 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_4_09 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 3 variables and 8 clauses. -/
def uuf_3_8_02 : CNF :=
  [[⟨0, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, false⟩], [⟨0, false⟩, ⟨2, false⟩],
   [⟨1, true⟩, ⟨2, true⟩], [⟨0, true⟩, ⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩],
   [⟨1, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨2, true⟩]]

theorem not_satisfiable_uuf_3_8_02 : ¬uuf_3_8_02.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
    simp [uuf_3_8_02, CNF.eval, Clause.eval, Literal.eval, h0, h1, h2] at hσ

theorem encode_uuf_3_8_02_not_mem_SAT : Encoding.encode uuf_3_8_02 ∉ SAT :=
  fun h => not_satisfiable_uuf_3_8_02 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 3 variables and 9 clauses. -/
def uuf_3_9_01 : CNF :=
  [[⟨0, true⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨1, false⟩],
   [⟨0, false⟩, ⟨1, true⟩, ⟨2, false⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨2, false⟩],
   [⟨0, false⟩, ⟨1, true⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨2, true⟩]]

theorem not_satisfiable_uuf_3_9_01 : ¬uuf_3_9_01.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
    simp [uuf_3_9_01, CNF.eval, Clause.eval, Literal.eval, h0, h1, h2] at hσ

theorem encode_uuf_3_9_01_not_mem_SAT : Encoding.encode uuf_3_9_01 ∉ SAT :=
  fun h => not_satisfiable_uuf_3_9_01 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 3 variables and 7 clauses. -/
def uuf_3_7_02 : CNF :=
  [[⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, false⟩], [⟨1, false⟩, ⟨2, true⟩],
   [⟨0, false⟩, ⟨1, true⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨1, true⟩, ⟨2, false⟩],
   [⟨0, true⟩, ⟨2, false⟩], [⟨0, false⟩, ⟨2, true⟩]]

theorem not_satisfiable_uuf_3_7_02 : ¬uuf_3_7_02.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
    simp [uuf_3_7_02, CNF.eval, Clause.eval, Literal.eval, h0, h1, h2] at hσ

theorem encode_uuf_3_7_02_not_mem_SAT : Encoding.encode uuf_3_7_02 ∉ SAT :=
  fun h => not_satisfiable_uuf_3_7_02 (encode_mem_SAT.1 h)

/-- An unsatisfiable instance with 2 variables and 5 clauses. -/
def uuf_2_5_06 : CNF :=
  [[⟨0, true⟩], [⟨0, false⟩], [⟨1, false⟩], [⟨1, true⟩], [⟨0, true⟩, ⟨1, false⟩]]

theorem not_satisfiable_uuf_2_5_06 : ¬uuf_2_5_06.Satisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [uuf_2_5_06, CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

theorem encode_uuf_2_5_06_not_mem_SAT : Encoding.encode uuf_2_5_06 ∉ SAT :=
  fun h => not_satisfiable_uuf_2_5_06 (encode_mem_SAT.1 h)

end Complexity
