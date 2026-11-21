import PNP.Problems.Graph

/-!
# Hamiltonian cycles

## Main definitions

* `Complexity.Graph.IsCycle`: consecutive vertices of a list, taken cyclically,
  are adjacent.
* `Complexity.Graph.IsHamCycle`: a cycle through every vertex exactly once.
* `Complexity.Graph.HasHamCycle`: the graph is Hamiltonian.
* `Complexity.HAM_CYCLE`: the language of Hamiltonian graphs.

## Main results

* `Complexity.Graph.IsCycle.mono`: cycles are preserved by adding edges.
* `Complexity.Graph.HasHamCycle.mono`: so is Hamiltonicity, on a fixed vertex set.
* `Complexity.Graph.HasHamCycle.three_le_order`: a Hamiltonian graph has at least
  three vertices.

## Implementation notes

A cycle is a list of vertices; the edge from the last vertex back to the first
is handled by indexing modulo the length. A Hamiltonian cycle is required to
have at least three vertices, which excludes the degenerate "cycles" of length
one and two that the cyclic indexing would otherwise allow.

## References

* [Kar72] R. M. Karp, *Reducibility among combinatorial problems*, 1972.
* [GJ79] M. R. Garey, D. S. Johnson, *Computers and Intractability*, problem
  GT37.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Theorem 7.46.
-/

set_option autoImplicit false

namespace Complexity

namespace Graph

variable {G H : Graph} {c : List ℕ}

/-- Cyclically consecutive vertices of `c` are adjacent. -/
def IsCycle (G : Graph) (c : List ℕ) : Prop :=
  ∀ i, i < c.length → G.Adj (c.getD i 0) (c.getD ((i + 1) % c.length) 0)

/-- `c` is a Hamiltonian cycle of `G`: it visits every vertex exactly once and
cyclically consecutive vertices are adjacent. -/
def IsHamCycle (G : Graph) (c : List ℕ) : Prop :=
  3 ≤ G.order ∧ G.IsVertexSet c ∧ c.length = G.order ∧ G.IsCycle c

instance (G : Graph) (c : List ℕ) : Decidable (G.IsCycle c) :=
  inferInstanceAs
    (Decidable (∀ i, i < c.length → G.Adj (c.getD i 0) (c.getD ((i + 1) % c.length) 0)))

instance (G : Graph) (c : List ℕ) : Decidable (G.IsHamCycle c) :=
  inferInstanceAs (Decidable (3 ≤ G.order ∧ G.IsVertexSet c ∧ c.length = G.order ∧ G.IsCycle c))

/-- `G` has a Hamiltonian cycle. -/
def HasHamCycle (G : Graph) : Prop := ∃ c, G.IsHamCycle c

theorem isCycle_nil (G : Graph) : G.IsCycle [] := fun _ h => absurd h (Nat.not_lt_zero _)

/-- Cycles are preserved by adding edges. -/
theorem IsCycle.mono (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges) (h : G.IsCycle c) : H.IsCycle c :=
  fun i hi => (h i hi).mono hGH

theorem IsHamCycle.three_le_order (h : G.IsHamCycle c) : 3 ≤ G.order := h.1

theorem IsHamCycle.isVertexSet (h : G.IsHamCycle c) : G.IsVertexSet c := h.2.1

theorem IsHamCycle.length_eq (h : G.IsHamCycle c) : c.length = G.order := h.2.2.1

theorem IsHamCycle.isCycle (h : G.IsHamCycle c) : G.IsCycle c := h.2.2.2

theorem IsHamCycle.nodup (h : G.IsHamCycle c) : c.Nodup := h.isVertexSet.1

theorem IsHamCycle.lt_order_of_mem (h : G.IsHamCycle c) {v : ℕ} (hv : v ∈ c) : v < G.order :=
  h.isVertexSet.2 v hv

theorem IsHamCycle.ne_nil (h : G.IsHamCycle c) : c ≠ [] := by
  intro hc
  have h₁ := h.length_eq
  have h₂ := h.three_le_order
  rw [hc] at h₁
  simp at h₁
  omega

/-- Hamiltonian cycles are preserved by adding edges on the same vertex set. -/
theorem IsHamCycle.mono (ho : G.order = H.order) (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges)
    (h : G.IsHamCycle c) : H.IsHamCycle c :=
  ⟨ho ▸ h.1, ⟨h.nodup, fun _ hv => ho ▸ h.lt_order_of_mem hv⟩, ho ▸ h.length_eq, h.isCycle.mono hGH⟩

theorem HasHamCycle.mono (ho : G.order = H.order) (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges)
    (h : G.HasHamCycle) : H.HasHamCycle :=
  let ⟨c, hc⟩ := h
  ⟨c, hc.mono ho hGH⟩

/-- A Hamiltonian graph has at least three vertices. -/
theorem HasHamCycle.three_le_order (h : G.HasHamCycle) : 3 ≤ G.order :=
  let ⟨_, hc⟩ := h
  hc.three_le_order

theorem not_hasHamCycle_of_order_lt (h : G.order < 3) : ¬G.HasHamCycle :=
  fun hG => Nat.not_le_of_lt h hG.three_le_order

/-- A graph without edges is not Hamiltonian. -/
theorem not_hasHamCycle_edgeless (n : ℕ) : ¬(edgeless n).HasHamCycle := by
  rintro ⟨c, h3, -, hlen, hc⟩
  have h0 : 0 < c.length := by rw [hlen]; exact Nat.lt_of_lt_of_le (by decide) h3
  exact (hc 0 h0).2.elim (fun h => nomatch h) (fun h => nomatch h)

end Graph

/-- **HAM-CYCLE**: the language of graphs with a Hamiltonian cycle. -/
def HAM_CYCLE : Language := Encoding.languageOf Graph.HasHamCycle

theorem encode_mem_HAM_CYCLE {G : Graph} : Encoding.encode G ∈ HAM_CYCLE ↔ G.HasHamCycle :=
  Encoding.mem_languageOf_encode

end Complexity
