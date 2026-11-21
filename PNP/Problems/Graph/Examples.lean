import PNP.Problems.HamCycle

/-!
# Small instances of the graph problems

Cliques, independent sets, vertex covers and Hamiltonian cycles in small members
of the standard families of `PNP.Problems.Graph`: complete graphs, cycles, paths,
stars and complete bipartite graphs.

## Main results

* `Complexity.Graph.hasClique_complete_5` and relatives: `Kₙ` has a clique with
  `n` vertices.
* `Complexity.Graph.hasHamCycle_cycle_5` and relatives: `Cₙ` is Hamiltonian, and
  its encoding is in HAM-CYCLE.
* `Complexity.Graph.hasVertexCover_cycle_5` and relatives: `Cₙ` has a vertex
  cover with `⌈n / 2⌉` vertices and an independent set with `⌊n / 2⌋` vertices.
* `Complexity.Graph.hasVertexCover_completeBipartite_2_3` and relatives: the
  smaller side of `K_{m,n}` is a vertex cover, the larger side is independent.

## Implementation notes

All predicates involved are decidable, and the statements are proved by
`decide`. The witnesses are given explicitly, so the kernel only has to check
them.
-/

set_option autoImplicit false

namespace Complexity

namespace Graph

/-! ### Complete graphs -/

theorem isClique_complete_1 : (complete 1).IsClique [0] := by decide

theorem hasClique_complete_1 : (complete 1).HasClique 1 :=
  ⟨[0], by decide, rfl, isClique_complete_1⟩

theorem isClique_complete_2 : (complete 2).IsClique [0, 1] := by decide

theorem hasClique_complete_2 : (complete 2).HasClique 2 :=
  ⟨[0, 1], by decide, rfl, isClique_complete_2⟩

theorem isVertexCover_complete_2 : (complete 2).IsVertexCover [1] := by decide

theorem not_isIndependentSet_complete_2 : ¬(complete 2).IsIndependentSet [0, 1] := by decide

theorem isClique_complete_3 : (complete 3).IsClique [0, 1, 2] := by decide

theorem hasClique_complete_3 : (complete 3).HasClique 3 :=
  ⟨[0, 1, 2], by decide, rfl, isClique_complete_3⟩

theorem isVertexCover_complete_3 : (complete 3).IsVertexCover [1, 2] := by decide

theorem not_isIndependentSet_complete_3 : ¬(complete 3).IsIndependentSet [0, 1] := by decide

theorem isHamCycle_complete_3 : (complete 3).IsHamCycle [1, 0, 2] := by decide

theorem hasHamCycle_complete_3 : (complete 3).HasHamCycle :=
  ⟨_, isHamCycle_complete_3⟩

theorem isClique_complete_4 : (complete 4).IsClique [0, 1, 2, 3] := by decide

theorem hasClique_complete_4 : (complete 4).HasClique 4 :=
  ⟨[0, 1, 2, 3], by decide, rfl, isClique_complete_4⟩

theorem isVertexCover_complete_4 : (complete 4).IsVertexCover [1, 2, 3] := by decide

theorem not_isIndependentSet_complete_4 : ¬(complete 4).IsIndependentSet [0, 1] := by decide

theorem isHamCycle_complete_4 : (complete 4).IsHamCycle [0, 1, 3, 2] := by decide

theorem hasHamCycle_complete_4 : (complete 4).HasHamCycle :=
  ⟨_, isHamCycle_complete_4⟩

theorem isClique_complete_5 : (complete 5).IsClique [0, 1, 2, 3, 4] := by decide

theorem hasClique_complete_5 : (complete 5).HasClique 5 :=
  ⟨[0, 1, 2, 3, 4], by decide, rfl, isClique_complete_5⟩

theorem isVertexCover_complete_5 : (complete 5).IsVertexCover [1, 2, 3, 4] := by decide

theorem not_isIndependentSet_complete_5 : ¬(complete 5).IsIndependentSet [0, 1] := by decide

theorem isHamCycle_complete_5 : (complete 5).IsHamCycle [2, 1, 4, 3, 0] := by decide

theorem hasHamCycle_complete_5 : (complete 5).HasHamCycle :=
  ⟨_, isHamCycle_complete_5⟩

theorem isClique_complete_6 : (complete 6).IsClique [0, 1, 2, 3, 4, 5] := by decide

theorem hasClique_complete_6 : (complete 6).HasClique 6 :=
  ⟨[0, 1, 2, 3, 4, 5], by decide, rfl, isClique_complete_6⟩

theorem isVertexCover_complete_6 : (complete 6).IsVertexCover [1, 2, 3, 4, 5] := by decide

theorem not_isIndependentSet_complete_6 : ¬(complete 6).IsIndependentSet [0, 1] := by decide

theorem isHamCycle_complete_6 : (complete 6).IsHamCycle [0, 1, 2, 5, 4, 3] := by decide

theorem hasHamCycle_complete_6 : (complete 6).HasHamCycle :=
  ⟨_, isHamCycle_complete_6⟩

theorem isClique_complete_7 : (complete 7).IsClique [0, 1, 2, 3, 4, 5, 6] := by decide

theorem hasClique_complete_7 : (complete 7).HasClique 7 :=
  ⟨[0, 1, 2, 3, 4, 5, 6], by decide, rfl, isClique_complete_7⟩

theorem isVertexCover_complete_7 : (complete 7).IsVertexCover [1, 2, 3, 4, 5, 6] := by decide

theorem not_isIndependentSet_complete_7 : ¬(complete 7).IsIndependentSet [0, 1] := by decide

theorem isHamCycle_complete_7 : (complete 7).IsHamCycle [3, 0, 2, 6, 4, 5, 1] := by decide

theorem hasHamCycle_complete_7 : (complete 7).HasHamCycle :=
  ⟨_, isHamCycle_complete_7⟩

theorem isClique_complete_8 : (complete 8).IsClique [0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem hasClique_complete_8 : (complete 8).HasClique 8 :=
  ⟨[0, 1, 2, 3, 4, 5, 6, 7], by decide, rfl, isClique_complete_8⟩

theorem isVertexCover_complete_8 : (complete 8).IsVertexCover [1, 2, 3, 4, 5, 6, 7] := by decide

theorem not_isIndependentSet_complete_8 : ¬(complete 8).IsIndependentSet [0, 1] := by decide

theorem isHamCycle_complete_8 : (complete 8).IsHamCycle [1, 5, 6, 7, 2, 4, 0, 3] := by decide

theorem hasHamCycle_complete_8 : (complete 8).HasHamCycle :=
  ⟨_, isHamCycle_complete_8⟩

/-! ### Cycles -/

theorem isHamCycle_cycle_3 : (cycle 3).IsHamCycle [0, 1, 2] := by decide

theorem hasHamCycle_cycle_3 : (cycle 3).HasHamCycle :=
  ⟨_, isHamCycle_cycle_3⟩

theorem encode_cycle_3_mem_HAM_CYCLE : Encoding.encode (cycle 3) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_3

theorem isVertexCover_cycle_3 : (cycle 3).IsVertexCover [0, 2] := by decide

theorem hasVertexCover_cycle_3 : (cycle 3).HasVertexCover 2 :=
  ⟨[0, 2], by decide, by decide, isVertexCover_cycle_3⟩

theorem isIndependentSet_cycle_3 : (cycle 3).IsIndependentSet [0] := by decide

theorem hasIndependentSet_cycle_3 : (cycle 3).HasIndependentSet 1 :=
  ⟨[0], by decide, rfl, isIndependentSet_cycle_3⟩

theorem isHamCycle_cycle_4 : (cycle 4).IsHamCycle [0, 1, 2, 3] := by decide

theorem hasHamCycle_cycle_4 : (cycle 4).HasHamCycle :=
  ⟨_, isHamCycle_cycle_4⟩

theorem encode_cycle_4_mem_HAM_CYCLE : Encoding.encode (cycle 4) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_4

theorem isVertexCover_cycle_4 : (cycle 4).IsVertexCover [0, 2] := by decide

theorem hasVertexCover_cycle_4 : (cycle 4).HasVertexCover 2 :=
  ⟨[0, 2], by decide, by decide, isVertexCover_cycle_4⟩

theorem isIndependentSet_cycle_4 : (cycle 4).IsIndependentSet [0, 2] := by decide

theorem hasIndependentSet_cycle_4 : (cycle 4).HasIndependentSet 2 :=
  ⟨[0, 2], by decide, rfl, isIndependentSet_cycle_4⟩

theorem not_isClique_cycle_4 : ¬(cycle 4).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_5 : (cycle 5).IsHamCycle [0, 1, 2, 3, 4] := by decide

theorem hasHamCycle_cycle_5 : (cycle 5).HasHamCycle :=
  ⟨_, isHamCycle_cycle_5⟩

theorem encode_cycle_5_mem_HAM_CYCLE : Encoding.encode (cycle 5) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_5

theorem isVertexCover_cycle_5 : (cycle 5).IsVertexCover [0, 2, 4] := by decide

theorem hasVertexCover_cycle_5 : (cycle 5).HasVertexCover 3 :=
  ⟨[0, 2, 4], by decide, by decide, isVertexCover_cycle_5⟩

theorem isIndependentSet_cycle_5 : (cycle 5).IsIndependentSet [0, 2] := by decide

theorem hasIndependentSet_cycle_5 : (cycle 5).HasIndependentSet 2 :=
  ⟨[0, 2], by decide, rfl, isIndependentSet_cycle_5⟩

theorem not_isClique_cycle_5 : ¬(cycle 5).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_6 : (cycle 6).IsHamCycle [0, 1, 2, 3, 4, 5] := by decide

theorem hasHamCycle_cycle_6 : (cycle 6).HasHamCycle :=
  ⟨_, isHamCycle_cycle_6⟩

theorem encode_cycle_6_mem_HAM_CYCLE : Encoding.encode (cycle 6) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_6

theorem isVertexCover_cycle_6 : (cycle 6).IsVertexCover [0, 2, 4] := by decide

theorem hasVertexCover_cycle_6 : (cycle 6).HasVertexCover 3 :=
  ⟨[0, 2, 4], by decide, by decide, isVertexCover_cycle_6⟩

theorem isIndependentSet_cycle_6 : (cycle 6).IsIndependentSet [0, 2, 4] := by decide

theorem hasIndependentSet_cycle_6 : (cycle 6).HasIndependentSet 3 :=
  ⟨[0, 2, 4], by decide, rfl, isIndependentSet_cycle_6⟩

theorem not_isClique_cycle_6 : ¬(cycle 6).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_7 : (cycle 7).IsHamCycle [0, 1, 2, 3, 4, 5, 6] := by decide

theorem hasHamCycle_cycle_7 : (cycle 7).HasHamCycle :=
  ⟨_, isHamCycle_cycle_7⟩

theorem encode_cycle_7_mem_HAM_CYCLE : Encoding.encode (cycle 7) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_7

theorem isVertexCover_cycle_7 : (cycle 7).IsVertexCover [0, 2, 4, 6] := by decide

theorem hasVertexCover_cycle_7 : (cycle 7).HasVertexCover 4 :=
  ⟨[0, 2, 4, 6], by decide, by decide, isVertexCover_cycle_7⟩

theorem isIndependentSet_cycle_7 : (cycle 7).IsIndependentSet [0, 2, 4] := by decide

theorem hasIndependentSet_cycle_7 : (cycle 7).HasIndependentSet 3 :=
  ⟨[0, 2, 4], by decide, rfl, isIndependentSet_cycle_7⟩

theorem not_isClique_cycle_7 : ¬(cycle 7).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_8 : (cycle 8).IsHamCycle [0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem hasHamCycle_cycle_8 : (cycle 8).HasHamCycle :=
  ⟨_, isHamCycle_cycle_8⟩

theorem encode_cycle_8_mem_HAM_CYCLE : Encoding.encode (cycle 8) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_8

theorem isVertexCover_cycle_8 : (cycle 8).IsVertexCover [0, 2, 4, 6] := by decide

theorem hasVertexCover_cycle_8 : (cycle 8).HasVertexCover 4 :=
  ⟨[0, 2, 4, 6], by decide, by decide, isVertexCover_cycle_8⟩

theorem isIndependentSet_cycle_8 : (cycle 8).IsIndependentSet [0, 2, 4, 6] := by decide

theorem hasIndependentSet_cycle_8 : (cycle 8).HasIndependentSet 4 :=
  ⟨[0, 2, 4, 6], by decide, rfl, isIndependentSet_cycle_8⟩

theorem not_isClique_cycle_8 : ¬(cycle 8).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_9 : (cycle 9).IsHamCycle [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide

theorem hasHamCycle_cycle_9 : (cycle 9).HasHamCycle :=
  ⟨_, isHamCycle_cycle_9⟩

theorem encode_cycle_9_mem_HAM_CYCLE : Encoding.encode (cycle 9) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_9

theorem isVertexCover_cycle_9 : (cycle 9).IsVertexCover [0, 2, 4, 6, 8] := by decide

theorem hasVertexCover_cycle_9 : (cycle 9).HasVertexCover 5 :=
  ⟨[0, 2, 4, 6, 8], by decide, by decide, isVertexCover_cycle_9⟩

theorem isIndependentSet_cycle_9 : (cycle 9).IsIndependentSet [0, 2, 4, 6] := by decide

theorem hasIndependentSet_cycle_9 : (cycle 9).HasIndependentSet 4 :=
  ⟨[0, 2, 4, 6], by decide, rfl, isIndependentSet_cycle_9⟩

theorem not_isClique_cycle_9 : ¬(cycle 9).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_10 : (cycle 10).IsHamCycle [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide

theorem hasHamCycle_cycle_10 : (cycle 10).HasHamCycle :=
  ⟨_, isHamCycle_cycle_10⟩

theorem encode_cycle_10_mem_HAM_CYCLE : Encoding.encode (cycle 10) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_10

theorem isVertexCover_cycle_10 : (cycle 10).IsVertexCover [0, 2, 4, 6, 8] := by decide

theorem hasVertexCover_cycle_10 : (cycle 10).HasVertexCover 5 :=
  ⟨[0, 2, 4, 6, 8], by decide, by decide, isVertexCover_cycle_10⟩

theorem isIndependentSet_cycle_10 : (cycle 10).IsIndependentSet [0, 2, 4, 6, 8] := by decide

theorem hasIndependentSet_cycle_10 : (cycle 10).HasIndependentSet 5 :=
  ⟨[0, 2, 4, 6, 8], by decide, rfl, isIndependentSet_cycle_10⟩

theorem not_isClique_cycle_10 : ¬(cycle 10).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_11 : (cycle 11).IsHamCycle [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide

theorem hasHamCycle_cycle_11 : (cycle 11).HasHamCycle :=
  ⟨_, isHamCycle_cycle_11⟩

theorem encode_cycle_11_mem_HAM_CYCLE : Encoding.encode (cycle 11) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_11

theorem isVertexCover_cycle_11 : (cycle 11).IsVertexCover [0, 2, 4, 6, 8, 10] := by decide

theorem hasVertexCover_cycle_11 : (cycle 11).HasVertexCover 6 :=
  ⟨[0, 2, 4, 6, 8, 10], by decide, by decide, isVertexCover_cycle_11⟩

theorem isIndependentSet_cycle_11 : (cycle 11).IsIndependentSet [0, 2, 4, 6, 8] := by decide

theorem hasIndependentSet_cycle_11 : (cycle 11).HasIndependentSet 5 :=
  ⟨[0, 2, 4, 6, 8], by decide, rfl, isIndependentSet_cycle_11⟩

theorem not_isClique_cycle_11 : ¬(cycle 11).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_12 :
    (cycle 12).IsHamCycle [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by decide

theorem hasHamCycle_cycle_12 : (cycle 12).HasHamCycle :=
  ⟨_, isHamCycle_cycle_12⟩

theorem encode_cycle_12_mem_HAM_CYCLE : Encoding.encode (cycle 12) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_12

theorem isVertexCover_cycle_12 : (cycle 12).IsVertexCover [0, 2, 4, 6, 8, 10] := by decide

theorem hasVertexCover_cycle_12 : (cycle 12).HasVertexCover 6 :=
  ⟨[0, 2, 4, 6, 8, 10], by decide, by decide, isVertexCover_cycle_12⟩

theorem isIndependentSet_cycle_12 : (cycle 12).IsIndependentSet [0, 2, 4, 6, 8, 10] := by decide

theorem hasIndependentSet_cycle_12 : (cycle 12).HasIndependentSet 6 :=
  ⟨[0, 2, 4, 6, 8, 10], by decide, rfl, isIndependentSet_cycle_12⟩

theorem not_isClique_cycle_12 : ¬(cycle 12).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_13 :
    (cycle 13).IsHamCycle [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by decide

theorem hasHamCycle_cycle_13 : (cycle 13).HasHamCycle :=
  ⟨_, isHamCycle_cycle_13⟩

theorem encode_cycle_13_mem_HAM_CYCLE : Encoding.encode (cycle 13) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_13

theorem isVertexCover_cycle_13 : (cycle 13).IsVertexCover [0, 2, 4, 6, 8, 10, 12] := by decide

theorem hasVertexCover_cycle_13 : (cycle 13).HasVertexCover 7 :=
  ⟨[0, 2, 4, 6, 8, 10, 12], by decide, by decide, isVertexCover_cycle_13⟩

theorem isIndependentSet_cycle_13 : (cycle 13).IsIndependentSet [0, 2, 4, 6, 8, 10] := by decide

theorem hasIndependentSet_cycle_13 : (cycle 13).HasIndependentSet 6 :=
  ⟨[0, 2, 4, 6, 8, 10], by decide, rfl, isIndependentSet_cycle_13⟩

theorem not_isClique_cycle_13 : ¬(cycle 13).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_14 :
    (cycle 14).IsHamCycle [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := by decide

theorem hasHamCycle_cycle_14 : (cycle 14).HasHamCycle :=
  ⟨_, isHamCycle_cycle_14⟩

theorem encode_cycle_14_mem_HAM_CYCLE : Encoding.encode (cycle 14) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_14

theorem isVertexCover_cycle_14 : (cycle 14).IsVertexCover [0, 2, 4, 6, 8, 10, 12] := by decide

theorem hasVertexCover_cycle_14 : (cycle 14).HasVertexCover 7 :=
  ⟨[0, 2, 4, 6, 8, 10, 12], by decide, by decide, isVertexCover_cycle_14⟩

theorem isIndependentSet_cycle_14 : (cycle 14).IsIndependentSet [0, 2, 4, 6, 8, 10, 12] := by decide

theorem hasIndependentSet_cycle_14 : (cycle 14).HasIndependentSet 7 :=
  ⟨[0, 2, 4, 6, 8, 10, 12], by decide, rfl, isIndependentSet_cycle_14⟩

theorem not_isClique_cycle_14 : ¬(cycle 14).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_15 :
    (cycle 15).IsHamCycle [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by decide

theorem hasHamCycle_cycle_15 : (cycle 15).HasHamCycle :=
  ⟨_, isHamCycle_cycle_15⟩

theorem encode_cycle_15_mem_HAM_CYCLE : Encoding.encode (cycle 15) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_15

theorem isVertexCover_cycle_15 : (cycle 15).IsVertexCover [0, 2, 4, 6, 8, 10, 12, 14] := by decide

theorem hasVertexCover_cycle_15 : (cycle 15).HasVertexCover 8 :=
  ⟨[0, 2, 4, 6, 8, 10, 12, 14], by decide, by decide, isVertexCover_cycle_15⟩

theorem isIndependentSet_cycle_15 : (cycle 15).IsIndependentSet [0, 2, 4, 6, 8, 10, 12] := by decide

theorem hasIndependentSet_cycle_15 : (cycle 15).HasIndependentSet 7 :=
  ⟨[0, 2, 4, 6, 8, 10, 12], by decide, rfl, isIndependentSet_cycle_15⟩

theorem not_isClique_cycle_15 : ¬(cycle 15).IsClique [0, 1, 2] := by decide

theorem isHamCycle_cycle_16 :
    (cycle 16).IsHamCycle [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide

theorem hasHamCycle_cycle_16 : (cycle 16).HasHamCycle :=
  ⟨_, isHamCycle_cycle_16⟩

theorem encode_cycle_16_mem_HAM_CYCLE : Encoding.encode (cycle 16) ∈ HAM_CYCLE :=
  encode_mem_HAM_CYCLE.2 hasHamCycle_cycle_16

theorem isVertexCover_cycle_16 : (cycle 16).IsVertexCover [0, 2, 4, 6, 8, 10, 12, 14] := by decide

theorem hasVertexCover_cycle_16 : (cycle 16).HasVertexCover 8 :=
  ⟨[0, 2, 4, 6, 8, 10, 12, 14], by decide, by decide, isVertexCover_cycle_16⟩

theorem isIndependentSet_cycle_16 :
    (cycle 16).IsIndependentSet [0, 2, 4, 6, 8, 10, 12, 14] := by decide

theorem hasIndependentSet_cycle_16 : (cycle 16).HasIndependentSet 8 :=
  ⟨[0, 2, 4, 6, 8, 10, 12, 14], by decide, rfl, isIndependentSet_cycle_16⟩

theorem not_isClique_cycle_16 : ¬(cycle 16).IsClique [0, 1, 2] := by decide

/-! ### Paths -/

theorem isVertexCover_path_2 : (path 2).IsVertexCover [1] := by decide

theorem hasVertexCover_path_2 : (path 2).HasVertexCover 1 :=
  ⟨[1], by decide, by decide, isVertexCover_path_2⟩

theorem isIndependentSet_path_2 : (path 2).IsIndependentSet [0] := by decide

theorem hasIndependentSet_path_2 : (path 2).HasIndependentSet 1 :=
  ⟨[0], by decide, rfl, isIndependentSet_path_2⟩

theorem isClique_path_2 : (path 2).IsClique [0, 1] := by decide

theorem isVertexCover_path_3 : (path 3).IsVertexCover [1] := by decide

theorem hasVertexCover_path_3 : (path 3).HasVertexCover 1 :=
  ⟨[1], by decide, by decide, isVertexCover_path_3⟩

theorem isIndependentSet_path_3 : (path 3).IsIndependentSet [0, 2] := by decide

theorem hasIndependentSet_path_3 : (path 3).HasIndependentSet 2 :=
  ⟨[0, 2], by decide, rfl, isIndependentSet_path_3⟩

theorem isClique_path_3 : (path 3).IsClique [0, 1] := by decide

theorem isVertexCover_path_4 : (path 4).IsVertexCover [1, 3] := by decide

theorem hasVertexCover_path_4 : (path 4).HasVertexCover 2 :=
  ⟨[1, 3], by decide, by decide, isVertexCover_path_4⟩

theorem isIndependentSet_path_4 : (path 4).IsIndependentSet [0, 2] := by decide

theorem hasIndependentSet_path_4 : (path 4).HasIndependentSet 2 :=
  ⟨[0, 2], by decide, rfl, isIndependentSet_path_4⟩

theorem isClique_path_4 : (path 4).IsClique [0, 1] := by decide

theorem isVertexCover_path_5 : (path 5).IsVertexCover [1, 3] := by decide

theorem hasVertexCover_path_5 : (path 5).HasVertexCover 2 :=
  ⟨[1, 3], by decide, by decide, isVertexCover_path_5⟩

theorem isIndependentSet_path_5 : (path 5).IsIndependentSet [0, 2, 4] := by decide

theorem hasIndependentSet_path_5 : (path 5).HasIndependentSet 3 :=
  ⟨[0, 2, 4], by decide, rfl, isIndependentSet_path_5⟩

theorem isClique_path_5 : (path 5).IsClique [0, 1] := by decide

theorem isVertexCover_path_6 : (path 6).IsVertexCover [1, 3, 5] := by decide

theorem hasVertexCover_path_6 : (path 6).HasVertexCover 3 :=
  ⟨[1, 3, 5], by decide, by decide, isVertexCover_path_6⟩

theorem isIndependentSet_path_6 : (path 6).IsIndependentSet [0, 2, 4] := by decide

theorem hasIndependentSet_path_6 : (path 6).HasIndependentSet 3 :=
  ⟨[0, 2, 4], by decide, rfl, isIndependentSet_path_6⟩

theorem isClique_path_6 : (path 6).IsClique [0, 1] := by decide

theorem isVertexCover_path_7 : (path 7).IsVertexCover [1, 3, 5] := by decide

theorem hasVertexCover_path_7 : (path 7).HasVertexCover 3 :=
  ⟨[1, 3, 5], by decide, by decide, isVertexCover_path_7⟩

theorem isIndependentSet_path_7 : (path 7).IsIndependentSet [0, 2, 4, 6] := by decide

theorem hasIndependentSet_path_7 : (path 7).HasIndependentSet 4 :=
  ⟨[0, 2, 4, 6], by decide, rfl, isIndependentSet_path_7⟩

theorem isClique_path_7 : (path 7).IsClique [0, 1] := by decide

theorem isVertexCover_path_8 : (path 8).IsVertexCover [1, 3, 5, 7] := by decide

theorem hasVertexCover_path_8 : (path 8).HasVertexCover 4 :=
  ⟨[1, 3, 5, 7], by decide, by decide, isVertexCover_path_8⟩

theorem isIndependentSet_path_8 : (path 8).IsIndependentSet [0, 2, 4, 6] := by decide

theorem hasIndependentSet_path_8 : (path 8).HasIndependentSet 4 :=
  ⟨[0, 2, 4, 6], by decide, rfl, isIndependentSet_path_8⟩

theorem isClique_path_8 : (path 8).IsClique [0, 1] := by decide

theorem isVertexCover_path_9 : (path 9).IsVertexCover [1, 3, 5, 7] := by decide

theorem hasVertexCover_path_9 : (path 9).HasVertexCover 4 :=
  ⟨[1, 3, 5, 7], by decide, by decide, isVertexCover_path_9⟩

theorem isIndependentSet_path_9 : (path 9).IsIndependentSet [0, 2, 4, 6, 8] := by decide

theorem hasIndependentSet_path_9 : (path 9).HasIndependentSet 5 :=
  ⟨[0, 2, 4, 6, 8], by decide, rfl, isIndependentSet_path_9⟩

theorem isClique_path_9 : (path 9).IsClique [0, 1] := by decide

theorem isVertexCover_path_10 : (path 10).IsVertexCover [1, 3, 5, 7, 9] := by decide

theorem hasVertexCover_path_10 : (path 10).HasVertexCover 5 :=
  ⟨[1, 3, 5, 7, 9], by decide, by decide, isVertexCover_path_10⟩

theorem isIndependentSet_path_10 : (path 10).IsIndependentSet [0, 2, 4, 6, 8] := by decide

theorem hasIndependentSet_path_10 : (path 10).HasIndependentSet 5 :=
  ⟨[0, 2, 4, 6, 8], by decide, rfl, isIndependentSet_path_10⟩

theorem isClique_path_10 : (path 10).IsClique [0, 1] := by decide

theorem isVertexCover_path_11 : (path 11).IsVertexCover [1, 3, 5, 7, 9] := by decide

theorem hasVertexCover_path_11 : (path 11).HasVertexCover 5 :=
  ⟨[1, 3, 5, 7, 9], by decide, by decide, isVertexCover_path_11⟩

theorem isIndependentSet_path_11 : (path 11).IsIndependentSet [0, 2, 4, 6, 8, 10] := by decide

theorem hasIndependentSet_path_11 : (path 11).HasIndependentSet 6 :=
  ⟨[0, 2, 4, 6, 8, 10], by decide, rfl, isIndependentSet_path_11⟩

theorem isClique_path_11 : (path 11).IsClique [0, 1] := by decide

theorem isVertexCover_path_12 : (path 12).IsVertexCover [1, 3, 5, 7, 9, 11] := by decide

theorem hasVertexCover_path_12 : (path 12).HasVertexCover 6 :=
  ⟨[1, 3, 5, 7, 9, 11], by decide, by decide, isVertexCover_path_12⟩

theorem isIndependentSet_path_12 : (path 12).IsIndependentSet [0, 2, 4, 6, 8, 10] := by decide

theorem hasIndependentSet_path_12 : (path 12).HasIndependentSet 6 :=
  ⟨[0, 2, 4, 6, 8, 10], by decide, rfl, isIndependentSet_path_12⟩

theorem isClique_path_12 : (path 12).IsClique [0, 1] := by decide

theorem isVertexCover_path_13 : (path 13).IsVertexCover [1, 3, 5, 7, 9, 11] := by decide

theorem hasVertexCover_path_13 : (path 13).HasVertexCover 6 :=
  ⟨[1, 3, 5, 7, 9, 11], by decide, by decide, isVertexCover_path_13⟩

theorem isIndependentSet_path_13 : (path 13).IsIndependentSet [0, 2, 4, 6, 8, 10, 12] := by decide

theorem hasIndependentSet_path_13 : (path 13).HasIndependentSet 7 :=
  ⟨[0, 2, 4, 6, 8, 10, 12], by decide, rfl, isIndependentSet_path_13⟩

theorem isClique_path_13 : (path 13).IsClique [0, 1] := by decide

theorem isVertexCover_path_14 : (path 14).IsVertexCover [1, 3, 5, 7, 9, 11, 13] := by decide

theorem hasVertexCover_path_14 : (path 14).HasVertexCover 7 :=
  ⟨[1, 3, 5, 7, 9, 11, 13], by decide, by decide, isVertexCover_path_14⟩

theorem isIndependentSet_path_14 : (path 14).IsIndependentSet [0, 2, 4, 6, 8, 10, 12] := by decide

theorem hasIndependentSet_path_14 : (path 14).HasIndependentSet 7 :=
  ⟨[0, 2, 4, 6, 8, 10, 12], by decide, rfl, isIndependentSet_path_14⟩

theorem isClique_path_14 : (path 14).IsClique [0, 1] := by decide

theorem isVertexCover_path_15 : (path 15).IsVertexCover [1, 3, 5, 7, 9, 11, 13] := by decide

theorem hasVertexCover_path_15 : (path 15).HasVertexCover 7 :=
  ⟨[1, 3, 5, 7, 9, 11, 13], by decide, by decide, isVertexCover_path_15⟩

theorem isIndependentSet_path_15 :
    (path 15).IsIndependentSet [0, 2, 4, 6, 8, 10, 12, 14] := by decide

theorem hasIndependentSet_path_15 : (path 15).HasIndependentSet 8 :=
  ⟨[0, 2, 4, 6, 8, 10, 12, 14], by decide, rfl, isIndependentSet_path_15⟩

theorem isClique_path_15 : (path 15).IsClique [0, 1] := by decide

/-! ### Stars -/

theorem isIndependentSet_star_2 : (star 2).IsIndependentSet [1, 2] := by decide

theorem hasIndependentSet_star_2 : (star 2).HasIndependentSet 2 :=
  ⟨[1, 2], by decide, rfl, isIndependentSet_star_2⟩

theorem not_isClique_star_2 : ¬(star 2).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_3 : (star 3).IsIndependentSet [1, 2, 3] := by decide

theorem hasIndependentSet_star_3 : (star 3).HasIndependentSet 3 :=
  ⟨[1, 2, 3], by decide, rfl, isIndependentSet_star_3⟩

theorem not_isClique_star_3 : ¬(star 3).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_4 : (star 4).IsIndependentSet [1, 2, 3, 4] := by decide

theorem hasIndependentSet_star_4 : (star 4).HasIndependentSet 4 :=
  ⟨[1, 2, 3, 4], by decide, rfl, isIndependentSet_star_4⟩

theorem not_isClique_star_4 : ¬(star 4).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_5 : (star 5).IsIndependentSet [1, 2, 3, 4, 5] := by decide

theorem hasIndependentSet_star_5 : (star 5).HasIndependentSet 5 :=
  ⟨[1, 2, 3, 4, 5], by decide, rfl, isIndependentSet_star_5⟩

theorem not_isClique_star_5 : ¬(star 5).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_6 : (star 6).IsIndependentSet [1, 2, 3, 4, 5, 6] := by decide

theorem hasIndependentSet_star_6 : (star 6).HasIndependentSet 6 :=
  ⟨[1, 2, 3, 4, 5, 6], by decide, rfl, isIndependentSet_star_6⟩

theorem not_isClique_star_6 : ¬(star 6).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_7 : (star 7).IsIndependentSet [1, 2, 3, 4, 5, 6, 7] := by decide

theorem hasIndependentSet_star_7 : (star 7).HasIndependentSet 7 :=
  ⟨[1, 2, 3, 4, 5, 6, 7], by decide, rfl, isIndependentSet_star_7⟩

theorem not_isClique_star_7 : ¬(star 7).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_8 : (star 8).IsIndependentSet [1, 2, 3, 4, 5, 6, 7, 8] := by decide

theorem hasIndependentSet_star_8 : (star 8).HasIndependentSet 8 :=
  ⟨[1, 2, 3, 4, 5, 6, 7, 8], by decide, rfl, isIndependentSet_star_8⟩

theorem not_isClique_star_8 : ¬(star 8).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_9 : (star 9).IsIndependentSet [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide

theorem hasIndependentSet_star_9 : (star 9).HasIndependentSet 9 :=
  ⟨[1, 2, 3, 4, 5, 6, 7, 8, 9], by decide, rfl, isIndependentSet_star_9⟩

theorem not_isClique_star_9 : ¬(star 9).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_10 :
    (star 10).IsIndependentSet [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide

theorem hasIndependentSet_star_10 : (star 10).HasIndependentSet 10 :=
  ⟨[1, 2, 3, 4, 5, 6, 7, 8, 9, 10], by decide, rfl, isIndependentSet_star_10⟩

theorem not_isClique_star_10 : ¬(star 10).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_11 :
    (star 11).IsIndependentSet [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by decide

theorem hasIndependentSet_star_11 : (star 11).HasIndependentSet 11 :=
  ⟨[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], by decide, rfl, isIndependentSet_star_11⟩

theorem not_isClique_star_11 : ¬(star 11).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_12 :
    (star 12).IsIndependentSet [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by decide

theorem hasIndependentSet_star_12 : (star 12).HasIndependentSet 12 :=
  ⟨[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], by decide, rfl, isIndependentSet_star_12⟩

theorem not_isClique_star_12 : ¬(star 12).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_13 :
    (star 13).IsIndependentSet [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := by decide

theorem hasIndependentSet_star_13 : (star 13).HasIndependentSet 13 :=
  ⟨[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], by decide, rfl, isIndependentSet_star_13⟩

theorem not_isClique_star_13 : ¬(star 13).IsClique [0, 1, 2] := by decide

theorem isIndependentSet_star_14 :
    (star 14).IsIndependentSet [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by decide

theorem hasIndependentSet_star_14 : (star 14).HasIndependentSet 14 :=
  ⟨[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], by decide, rfl, isIndependentSet_star_14⟩

theorem not_isClique_star_14 : ¬(star 14).IsClique [0, 1, 2] := by decide

/-! ### Complete bipartite graphs -/

theorem isVertexCover_completeBipartite_2_2 :
    (completeBipartite 2 2).IsVertexCover [0, 1] := by decide

theorem hasVertexCover_completeBipartite_2_2 : (completeBipartite 2 2).HasVertexCover 2 :=
  ⟨[0, 1], by decide, by decide, isVertexCover_completeBipartite_2_2⟩

theorem isIndependentSet_completeBipartite_2_2 :
    (completeBipartite 2 2).IsIndependentSet [2, 3] := by decide

theorem hasIndependentSet_completeBipartite_2_2 : (completeBipartite 2 2).HasIndependentSet 2 :=
  ⟨[2, 3], by decide, rfl, isIndependentSet_completeBipartite_2_2⟩

theorem not_isClique_completeBipartite_2_2 :
    ¬(completeBipartite 2 2).IsClique [0, 1, 2] := by decide

theorem isHamCycle_completeBipartite_2_2 :
    (completeBipartite 2 2).IsHamCycle [0, 2, 1, 3] := by decide

theorem hasHamCycle_completeBipartite_2_2 : (completeBipartite 2 2).HasHamCycle :=
  ⟨_, isHamCycle_completeBipartite_2_2⟩

theorem isVertexCover_completeBipartite_2_3 :
    (completeBipartite 2 3).IsVertexCover [0, 1] := by decide

theorem hasVertexCover_completeBipartite_2_3 : (completeBipartite 2 3).HasVertexCover 2 :=
  ⟨[0, 1], by decide, by decide, isVertexCover_completeBipartite_2_3⟩

theorem isIndependentSet_completeBipartite_2_3 :
    (completeBipartite 2 3).IsIndependentSet [2, 3, 4] := by decide

theorem hasIndependentSet_completeBipartite_2_3 : (completeBipartite 2 3).HasIndependentSet 3 :=
  ⟨[2, 3, 4], by decide, rfl, isIndependentSet_completeBipartite_2_3⟩

theorem not_isClique_completeBipartite_2_3 :
    ¬(completeBipartite 2 3).IsClique [0, 1, 2] := by decide

theorem isVertexCover_completeBipartite_2_4 :
    (completeBipartite 2 4).IsVertexCover [0, 1] := by decide

theorem hasVertexCover_completeBipartite_2_4 : (completeBipartite 2 4).HasVertexCover 2 :=
  ⟨[0, 1], by decide, by decide, isVertexCover_completeBipartite_2_4⟩

theorem isIndependentSet_completeBipartite_2_4 :
    (completeBipartite 2 4).IsIndependentSet [2, 3, 4, 5] := by decide

theorem hasIndependentSet_completeBipartite_2_4 : (completeBipartite 2 4).HasIndependentSet 4 :=
  ⟨[2, 3, 4, 5], by decide, rfl, isIndependentSet_completeBipartite_2_4⟩

theorem not_isClique_completeBipartite_2_4 :
    ¬(completeBipartite 2 4).IsClique [0, 1, 2] := by decide

theorem isVertexCover_completeBipartite_2_5 :
    (completeBipartite 2 5).IsVertexCover [0, 1] := by decide

theorem hasVertexCover_completeBipartite_2_5 : (completeBipartite 2 5).HasVertexCover 2 :=
  ⟨[0, 1], by decide, by decide, isVertexCover_completeBipartite_2_5⟩

theorem isIndependentSet_completeBipartite_2_5 :
    (completeBipartite 2 5).IsIndependentSet [2, 3, 4, 5, 6] := by decide

theorem hasIndependentSet_completeBipartite_2_5 : (completeBipartite 2 5).HasIndependentSet 5 :=
  ⟨[2, 3, 4, 5, 6], by decide, rfl, isIndependentSet_completeBipartite_2_5⟩

theorem not_isClique_completeBipartite_2_5 :
    ¬(completeBipartite 2 5).IsClique [0, 1, 2] := by decide

theorem isVertexCover_completeBipartite_2_6 :
    (completeBipartite 2 6).IsVertexCover [0, 1] := by decide

theorem hasVertexCover_completeBipartite_2_6 : (completeBipartite 2 6).HasVertexCover 2 :=
  ⟨[0, 1], by decide, by decide, isVertexCover_completeBipartite_2_6⟩

theorem isIndependentSet_completeBipartite_2_6 :
    (completeBipartite 2 6).IsIndependentSet [2, 3, 4, 5, 6, 7] := by decide

theorem hasIndependentSet_completeBipartite_2_6 : (completeBipartite 2 6).HasIndependentSet 6 :=
  ⟨[2, 3, 4, 5, 6, 7], by decide, rfl, isIndependentSet_completeBipartite_2_6⟩

theorem not_isClique_completeBipartite_2_6 :
    ¬(completeBipartite 2 6).IsClique [0, 1, 2] := by decide

theorem isVertexCover_completeBipartite_2_7 :
    (completeBipartite 2 7).IsVertexCover [0, 1] := by decide

theorem hasVertexCover_completeBipartite_2_7 : (completeBipartite 2 7).HasVertexCover 2 :=
  ⟨[0, 1], by decide, by decide, isVertexCover_completeBipartite_2_7⟩

theorem isIndependentSet_completeBipartite_2_7 :
    (completeBipartite 2 7).IsIndependentSet [2, 3, 4, 5, 6, 7, 8] := by decide

theorem hasIndependentSet_completeBipartite_2_7 : (completeBipartite 2 7).HasIndependentSet 7 :=
  ⟨[2, 3, 4, 5, 6, 7, 8], by decide, rfl, isIndependentSet_completeBipartite_2_7⟩

theorem not_isClique_completeBipartite_2_7 :
    ¬(completeBipartite 2 7).IsClique [0, 1, 2] := by decide

theorem isVertexCover_completeBipartite_3_3 :
    (completeBipartite 3 3).IsVertexCover [0, 1, 2] := by decide

theorem hasVertexCover_completeBipartite_3_3 : (completeBipartite 3 3).HasVertexCover 3 :=
  ⟨[0, 1, 2], by decide, by decide, isVertexCover_completeBipartite_3_3⟩

theorem isIndependentSet_completeBipartite_3_3 :
    (completeBipartite 3 3).IsIndependentSet [3, 4, 5] := by decide

theorem hasIndependentSet_completeBipartite_3_3 : (completeBipartite 3 3).HasIndependentSet 3 :=
  ⟨[3, 4, 5], by decide, rfl, isIndependentSet_completeBipartite_3_3⟩

theorem not_isClique_completeBipartite_3_3 :
    ¬(completeBipartite 3 3).IsClique [0, 1, 3] := by decide

theorem isHamCycle_completeBipartite_3_3 :
    (completeBipartite 3 3).IsHamCycle [0, 3, 1, 4, 2, 5] := by decide

theorem hasHamCycle_completeBipartite_3_3 : (completeBipartite 3 3).HasHamCycle :=
  ⟨_, isHamCycle_completeBipartite_3_3⟩

theorem isVertexCover_completeBipartite_3_4 :
    (completeBipartite 3 4).IsVertexCover [0, 1, 2] := by decide

theorem hasVertexCover_completeBipartite_3_4 : (completeBipartite 3 4).HasVertexCover 3 :=
  ⟨[0, 1, 2], by decide, by decide, isVertexCover_completeBipartite_3_4⟩

theorem isIndependentSet_completeBipartite_3_4 :
    (completeBipartite 3 4).IsIndependentSet [3, 4, 5, 6] := by decide

theorem hasIndependentSet_completeBipartite_3_4 : (completeBipartite 3 4).HasIndependentSet 4 :=
  ⟨[3, 4, 5, 6], by decide, rfl, isIndependentSet_completeBipartite_3_4⟩

theorem not_isClique_completeBipartite_3_4 :
    ¬(completeBipartite 3 4).IsClique [0, 1, 3] := by decide

theorem isVertexCover_completeBipartite_3_5 :
    (completeBipartite 3 5).IsVertexCover [0, 1, 2] := by decide

theorem hasVertexCover_completeBipartite_3_5 : (completeBipartite 3 5).HasVertexCover 3 :=
  ⟨[0, 1, 2], by decide, by decide, isVertexCover_completeBipartite_3_5⟩

theorem isIndependentSet_completeBipartite_3_5 :
    (completeBipartite 3 5).IsIndependentSet [3, 4, 5, 6, 7] := by decide

theorem hasIndependentSet_completeBipartite_3_5 : (completeBipartite 3 5).HasIndependentSet 5 :=
  ⟨[3, 4, 5, 6, 7], by decide, rfl, isIndependentSet_completeBipartite_3_5⟩

theorem not_isClique_completeBipartite_3_5 :
    ¬(completeBipartite 3 5).IsClique [0, 1, 3] := by decide

theorem isVertexCover_completeBipartite_3_6 :
    (completeBipartite 3 6).IsVertexCover [0, 1, 2] := by decide

theorem hasVertexCover_completeBipartite_3_6 : (completeBipartite 3 6).HasVertexCover 3 :=
  ⟨[0, 1, 2], by decide, by decide, isVertexCover_completeBipartite_3_6⟩

theorem isIndependentSet_completeBipartite_3_6 :
    (completeBipartite 3 6).IsIndependentSet [3, 4, 5, 6, 7, 8] := by decide

theorem hasIndependentSet_completeBipartite_3_6 : (completeBipartite 3 6).HasIndependentSet 6 :=
  ⟨[3, 4, 5, 6, 7, 8], by decide, rfl, isIndependentSet_completeBipartite_3_6⟩

theorem not_isClique_completeBipartite_3_6 :
    ¬(completeBipartite 3 6).IsClique [0, 1, 3] := by decide

theorem isVertexCover_completeBipartite_3_7 :
    (completeBipartite 3 7).IsVertexCover [0, 1, 2] := by decide

theorem hasVertexCover_completeBipartite_3_7 : (completeBipartite 3 7).HasVertexCover 3 :=
  ⟨[0, 1, 2], by decide, by decide, isVertexCover_completeBipartite_3_7⟩

theorem isIndependentSet_completeBipartite_3_7 :
    (completeBipartite 3 7).IsIndependentSet [3, 4, 5, 6, 7, 8, 9] := by decide

theorem hasIndependentSet_completeBipartite_3_7 : (completeBipartite 3 7).HasIndependentSet 7 :=
  ⟨[3, 4, 5, 6, 7, 8, 9], by decide, rfl, isIndependentSet_completeBipartite_3_7⟩

theorem not_isClique_completeBipartite_3_7 :
    ¬(completeBipartite 3 7).IsClique [0, 1, 3] := by decide

theorem isVertexCover_completeBipartite_4_4 :
    (completeBipartite 4 4).IsVertexCover [0, 1, 2, 3] := by decide

theorem hasVertexCover_completeBipartite_4_4 : (completeBipartite 4 4).HasVertexCover 4 :=
  ⟨[0, 1, 2, 3], by decide, by decide, isVertexCover_completeBipartite_4_4⟩

theorem isIndependentSet_completeBipartite_4_4 :
    (completeBipartite 4 4).IsIndependentSet [4, 5, 6, 7] := by decide

theorem hasIndependentSet_completeBipartite_4_4 : (completeBipartite 4 4).HasIndependentSet 4 :=
  ⟨[4, 5, 6, 7], by decide, rfl, isIndependentSet_completeBipartite_4_4⟩

theorem not_isClique_completeBipartite_4_4 :
    ¬(completeBipartite 4 4).IsClique [0, 1, 4] := by decide

theorem isHamCycle_completeBipartite_4_4 :
    (completeBipartite 4 4).IsHamCycle [0, 4, 1, 5, 2, 6, 3, 7] := by decide

theorem hasHamCycle_completeBipartite_4_4 : (completeBipartite 4 4).HasHamCycle :=
  ⟨_, isHamCycle_completeBipartite_4_4⟩

theorem isVertexCover_completeBipartite_4_5 :
    (completeBipartite 4 5).IsVertexCover [0, 1, 2, 3] := by decide

theorem hasVertexCover_completeBipartite_4_5 : (completeBipartite 4 5).HasVertexCover 4 :=
  ⟨[0, 1, 2, 3], by decide, by decide, isVertexCover_completeBipartite_4_5⟩

theorem isIndependentSet_completeBipartite_4_5 :
    (completeBipartite 4 5).IsIndependentSet [4, 5, 6, 7, 8] := by decide

theorem hasIndependentSet_completeBipartite_4_5 : (completeBipartite 4 5).HasIndependentSet 5 :=
  ⟨[4, 5, 6, 7, 8], by decide, rfl, isIndependentSet_completeBipartite_4_5⟩

theorem not_isClique_completeBipartite_4_5 :
    ¬(completeBipartite 4 5).IsClique [0, 1, 4] := by decide

theorem isVertexCover_completeBipartite_4_6 :
    (completeBipartite 4 6).IsVertexCover [0, 1, 2, 3] := by decide

theorem hasVertexCover_completeBipartite_4_6 : (completeBipartite 4 6).HasVertexCover 4 :=
  ⟨[0, 1, 2, 3], by decide, by decide, isVertexCover_completeBipartite_4_6⟩

theorem isIndependentSet_completeBipartite_4_6 :
    (completeBipartite 4 6).IsIndependentSet [4, 5, 6, 7, 8, 9] := by decide

theorem hasIndependentSet_completeBipartite_4_6 : (completeBipartite 4 6).HasIndependentSet 6 :=
  ⟨[4, 5, 6, 7, 8, 9], by decide, rfl, isIndependentSet_completeBipartite_4_6⟩

theorem not_isClique_completeBipartite_4_6 :
    ¬(completeBipartite 4 6).IsClique [0, 1, 4] := by decide

theorem isVertexCover_completeBipartite_4_7 :
    (completeBipartite 4 7).IsVertexCover [0, 1, 2, 3] := by decide

theorem hasVertexCover_completeBipartite_4_7 : (completeBipartite 4 7).HasVertexCover 4 :=
  ⟨[0, 1, 2, 3], by decide, by decide, isVertexCover_completeBipartite_4_7⟩

theorem isIndependentSet_completeBipartite_4_7 :
    (completeBipartite 4 7).IsIndependentSet [4, 5, 6, 7, 8, 9, 10] := by decide

theorem hasIndependentSet_completeBipartite_4_7 : (completeBipartite 4 7).HasIndependentSet 7 :=
  ⟨[4, 5, 6, 7, 8, 9, 10], by decide, rfl, isIndependentSet_completeBipartite_4_7⟩

theorem not_isClique_completeBipartite_4_7 :
    ¬(completeBipartite 4 7).IsClique [0, 1, 4] := by decide

theorem isVertexCover_completeBipartite_5_5 :
    (completeBipartite 5 5).IsVertexCover [0, 1, 2, 3, 4] := by decide

theorem hasVertexCover_completeBipartite_5_5 : (completeBipartite 5 5).HasVertexCover 5 :=
  ⟨[0, 1, 2, 3, 4], by decide, by decide, isVertexCover_completeBipartite_5_5⟩

theorem isIndependentSet_completeBipartite_5_5 :
    (completeBipartite 5 5).IsIndependentSet [5, 6, 7, 8, 9] := by decide

theorem hasIndependentSet_completeBipartite_5_5 : (completeBipartite 5 5).HasIndependentSet 5 :=
  ⟨[5, 6, 7, 8, 9], by decide, rfl, isIndependentSet_completeBipartite_5_5⟩

theorem not_isClique_completeBipartite_5_5 :
    ¬(completeBipartite 5 5).IsClique [0, 1, 5] := by decide

theorem isHamCycle_completeBipartite_5_5 :
    (completeBipartite 5 5).IsHamCycle [0, 5, 1, 6, 2, 7, 3, 8, 4, 9] := by decide

theorem hasHamCycle_completeBipartite_5_5 : (completeBipartite 5 5).HasHamCycle :=
  ⟨_, isHamCycle_completeBipartite_5_5⟩

theorem isVertexCover_completeBipartite_5_6 :
    (completeBipartite 5 6).IsVertexCover [0, 1, 2, 3, 4] := by decide

theorem hasVertexCover_completeBipartite_5_6 : (completeBipartite 5 6).HasVertexCover 5 :=
  ⟨[0, 1, 2, 3, 4], by decide, by decide, isVertexCover_completeBipartite_5_6⟩

theorem isIndependentSet_completeBipartite_5_6 :
    (completeBipartite 5 6).IsIndependentSet [5, 6, 7, 8, 9, 10] := by decide

theorem hasIndependentSet_completeBipartite_5_6 : (completeBipartite 5 6).HasIndependentSet 6 :=
  ⟨[5, 6, 7, 8, 9, 10], by decide, rfl, isIndependentSet_completeBipartite_5_6⟩

theorem not_isClique_completeBipartite_5_6 :
    ¬(completeBipartite 5 6).IsClique [0, 1, 5] := by decide

theorem isVertexCover_completeBipartite_5_7 :
    (completeBipartite 5 7).IsVertexCover [0, 1, 2, 3, 4] := by decide

theorem hasVertexCover_completeBipartite_5_7 : (completeBipartite 5 7).HasVertexCover 5 :=
  ⟨[0, 1, 2, 3, 4], by decide, by decide, isVertexCover_completeBipartite_5_7⟩

theorem isIndependentSet_completeBipartite_5_7 :
    (completeBipartite 5 7).IsIndependentSet [5, 6, 7, 8, 9, 10, 11] := by decide

theorem hasIndependentSet_completeBipartite_5_7 : (completeBipartite 5 7).HasIndependentSet 7 :=
  ⟨[5, 6, 7, 8, 9, 10, 11], by decide, rfl, isIndependentSet_completeBipartite_5_7⟩

theorem not_isClique_completeBipartite_5_7 :
    ¬(completeBipartite 5 7).IsClique [0, 1, 5] := by decide

theorem isVertexCover_completeBipartite_6_6 :
    (completeBipartite 6 6).IsVertexCover [0, 1, 2, 3, 4, 5] := by decide

theorem hasVertexCover_completeBipartite_6_6 : (completeBipartite 6 6).HasVertexCover 6 :=
  ⟨[0, 1, 2, 3, 4, 5], by decide, by decide, isVertexCover_completeBipartite_6_6⟩

theorem isIndependentSet_completeBipartite_6_6 :
    (completeBipartite 6 6).IsIndependentSet [6, 7, 8, 9, 10, 11] := by decide

theorem hasIndependentSet_completeBipartite_6_6 : (completeBipartite 6 6).HasIndependentSet 6 :=
  ⟨[6, 7, 8, 9, 10, 11], by decide, rfl, isIndependentSet_completeBipartite_6_6⟩

theorem not_isClique_completeBipartite_6_6 :
    ¬(completeBipartite 6 6).IsClique [0, 1, 6] := by decide

theorem isHamCycle_completeBipartite_6_6 :
    (completeBipartite 6 6).IsHamCycle [0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11] := by decide

theorem hasHamCycle_completeBipartite_6_6 : (completeBipartite 6 6).HasHamCycle :=
  ⟨_, isHamCycle_completeBipartite_6_6⟩

theorem isVertexCover_completeBipartite_6_7 :
    (completeBipartite 6 7).IsVertexCover [0, 1, 2, 3, 4, 5] := by decide

theorem hasVertexCover_completeBipartite_6_7 : (completeBipartite 6 7).HasVertexCover 6 :=
  ⟨[0, 1, 2, 3, 4, 5], by decide, by decide, isVertexCover_completeBipartite_6_7⟩

theorem isIndependentSet_completeBipartite_6_7 :
    (completeBipartite 6 7).IsIndependentSet [6, 7, 8, 9, 10, 11, 12] := by decide

theorem hasIndependentSet_completeBipartite_6_7 : (completeBipartite 6 7).HasIndependentSet 7 :=
  ⟨[6, 7, 8, 9, 10, 11, 12], by decide, rfl, isIndependentSet_completeBipartite_6_7⟩

theorem not_isClique_completeBipartite_6_7 :
    ¬(completeBipartite 6 7).IsClique [0, 1, 6] := by decide

theorem isVertexCover_completeBipartite_7_7 :
    (completeBipartite 7 7).IsVertexCover [0, 1, 2, 3, 4, 5, 6] := by decide

theorem hasVertexCover_completeBipartite_7_7 : (completeBipartite 7 7).HasVertexCover 7 :=
  ⟨[0, 1, 2, 3, 4, 5, 6], by decide, by decide, isVertexCover_completeBipartite_7_7⟩

theorem isIndependentSet_completeBipartite_7_7 :
    (completeBipartite 7 7).IsIndependentSet [7, 8, 9, 10, 11, 12, 13] := by decide

theorem hasIndependentSet_completeBipartite_7_7 : (completeBipartite 7 7).HasIndependentSet 7 :=
  ⟨[7, 8, 9, 10, 11, 12, 13], by decide, rfl, isIndependentSet_completeBipartite_7_7⟩

theorem not_isClique_completeBipartite_7_7 :
    ¬(completeBipartite 7 7).IsClique [0, 1, 7] := by decide

theorem isHamCycle_completeBipartite_7_7 :
    (completeBipartite 7 7).IsHamCycle [0, 7, 1, 8, 2, 9, 3, 10, 4, 11, 5, 12, 6, 13] := by decide

theorem hasHamCycle_completeBipartite_7_7 : (completeBipartite 7 7).HasHamCycle :=
  ⟨_, isHamCycle_completeBipartite_7_7⟩

end Graph

end Complexity
