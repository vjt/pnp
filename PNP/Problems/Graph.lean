import PNP.Data.Encoding
import PNP.Reduction.NPComplete

/-!
# Graph problems: CLIQUE, INDEPENDENT-SET and VERTEX-COVER

Finite simple graphs given by edge lists, and three of Karp's problems on them.

## Main definitions

* `Complexity.Graph`: a finite graph on the vertices `0, …, order - 1`, given by
  a list of edges.
* `Complexity.Graph.Adj`: the (symmetric, irreflexive) adjacency relation.
* `Complexity.Graph.IsClique`, `Complexity.Graph.IsIndependentSet`,
  `Complexity.Graph.IsVertexCover`: the three notions, for lists of vertices.
* `Complexity.Graph.IsCompl`: two graphs are complementary.
* `Complexity.CLIQUE`, `Complexity.INDEPENDENT_SET`, `Complexity.VERTEX_COVER`:
  the languages.
* `Complexity.Graph.complete`, `Complexity.Graph.cycle`, `Complexity.Graph.path`,
  `Complexity.Graph.star`, `Complexity.Graph.completeBipartite`: standard
  families.

## Main results

* `Complexity.Graph.isClique_iff_isIndependentSet_of_isCompl`: cliques of a graph
  are the independent sets of its complement [Kar72].
* `Complexity.Graph.isVertexCover_iff_isIndependentSet_of_compl`: a set of
  vertices is a vertex cover iff its complement is independent [GJ79, Lemma 3.1].
* `Complexity.Graph.isVertexCover_iff_forall_adj`: vertex covers in terms of
  adjacency.

## Implementation notes

A graph is an edge list on an initial segment of `ℕ`; this is the representation
that is encoded as a word. Adjacency is derived from the edge list by
symmetrising and discarding loops, so no well-formedness condition is imposed on
instances and every word that decodes to a `Graph` is a legal instance.

Vertex sets are duplicate-free lists of vertices. All predicates on them are
decidable, which is used for the small cases in `PNP.Problems.Graph.Examples`.

The two classical equivalences are proved at the level of the combinatorial
predicates. The corresponding maps on encodings (complementing an edge list,
replacing `k` by `n - k`) are computable in polynomial time; their machine-level
implementation is not part of this file.

## References

* [Kar72] R. M. Karp, *Reducibility among combinatorial problems*, 1972.
* [GJ79] M. R. Garey, D. S. Johnson, *Computers and Intractability*, §3.1 and
  problems GT1, GT19, GT20.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, Theorems 7.32
  and 7.44.
-/

set_option autoImplicit false

namespace Complexity

/-- A finite graph on the vertices `0, …, order - 1`, given by a list of edges. -/
structure Graph where
  /-- The number of vertices. -/
  order : ℕ
  /-- The list of edges. Orientation, repetitions and loops are irrelevant. -/
  edges : List (ℕ × ℕ)
  deriving DecidableEq, Repr

instance : Encoding Graph :=
  Encoding.ofLeftInverse (fun G => (G.order, G.edges)) (fun p => ⟨p.1, p.2⟩) fun _ => rfl

namespace Graph

variable {G H : Graph} {S S' : List ℕ} {u v : ℕ}

/-- Two distinct vertices are adjacent if they are joined by an edge, in either
orientation. -/
def Adj (G : Graph) (u v : ℕ) : Prop := u ≠ v ∧ ((u, v) ∈ G.edges ∨ (v, u) ∈ G.edges)

instance (G : Graph) (u v : ℕ) : Decidable (G.Adj u v) :=
  inferInstanceAs (Decidable (u ≠ v ∧ ((u, v) ∈ G.edges ∨ (v, u) ∈ G.edges)))

/-- A duplicate-free list of vertices of `G`. -/
def IsVertexSet (G : Graph) (S : List ℕ) : Prop := S.Nodup ∧ ∀ v, v ∈ S → v < G.order

/-- Any two distinct vertices of `S` are adjacent. -/
def IsClique (G : Graph) (S : List ℕ) : Prop :=
  ∀ u, u ∈ S → ∀ v, v ∈ S → u ≠ v → G.Adj u v

/-- No two vertices of `S` are adjacent. -/
def IsIndependentSet (G : Graph) (S : List ℕ) : Prop :=
  ∀ u, u ∈ S → ∀ v, v ∈ S → ¬G.Adj u v

/-- Every edge that is not a loop has an endpoint in `S`. -/
def IsVertexCover (G : Graph) (S : List ℕ) : Prop :=
  ∀ e, e ∈ G.edges → e.1 ≠ e.2 → e.1 ∈ S ∨ e.2 ∈ S

instance (G : Graph) (S : List ℕ) : Decidable (G.IsVertexSet S) :=
  inferInstanceAs (Decidable (S.Nodup ∧ ∀ v, v ∈ S → v < G.order))

instance (G : Graph) (S : List ℕ) : Decidable (G.IsClique S) :=
  inferInstanceAs (Decidable (∀ u, u ∈ S → ∀ v, v ∈ S → u ≠ v → G.Adj u v))

instance (G : Graph) (S : List ℕ) : Decidable (G.IsIndependentSet S) :=
  inferInstanceAs (Decidable (∀ u, u ∈ S → ∀ v, v ∈ S → ¬G.Adj u v))

instance (G : Graph) (S : List ℕ) : Decidable (G.IsVertexCover S) :=
  inferInstanceAs (Decidable (∀ e, e ∈ G.edges → e.1 ≠ e.2 → e.1 ∈ S ∨ e.2 ∈ S))

/-- `G` has a clique with `k` vertices. -/
def HasClique (G : Graph) (k : ℕ) : Prop :=
  ∃ S, G.IsVertexSet S ∧ S.length = k ∧ G.IsClique S

/-- `G` has an independent set with `k` vertices. -/
def HasIndependentSet (G : Graph) (k : ℕ) : Prop :=
  ∃ S, G.IsVertexSet S ∧ S.length = k ∧ G.IsIndependentSet S

/-- `G` has a vertex cover with at most `k` vertices. -/
def HasVertexCover (G : Graph) (k : ℕ) : Prop :=
  ∃ S, G.IsVertexSet S ∧ S.length ≤ k ∧ G.IsVertexCover S

/-- `H` is a complement of `G`: distinct vertices are adjacent in `H` iff they
are not adjacent in `G`. -/
def IsCompl (G H : Graph) : Prop := ∀ u v, u ≠ v → (H.Adj u v ↔ ¬G.Adj u v)

/-! ### Adjacency -/

theorem Adj.ne (h : G.Adj u v) : u ≠ v := h.1

theorem Adj.symm (h : G.Adj u v) : G.Adj v u := ⟨fun e => h.1 e.symm, h.2.symm⟩

theorem adj_comm : G.Adj u v ↔ G.Adj v u := ⟨Adj.symm, Adj.symm⟩

theorem not_adj_self (G : Graph) (v : ℕ) : ¬G.Adj v v := fun h => h.1 rfl

theorem adj_of_mem_edges (h : (u, v) ∈ G.edges) (hne : u ≠ v) : G.Adj u v := ⟨hne, Or.inl h⟩

/-- Adjacency is monotone in the edge list. -/
theorem Adj.mono (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges) (h : G.Adj u v) : H.Adj u v :=
  ⟨h.1, h.2.imp (hGH _) (hGH _)⟩

theorem IsCompl.symm (h : G.IsCompl H) : H.IsCompl G := by
  intro u v hne
  have := h u v hne
  constructor
  · intro hG hH
    exact this.1 hH hG
  · intro hH
    exact Decidable.by_contra fun hG => hH (this.2 hG)

/-! ### Cliques and independent sets -/

theorem isClique_nil (G : Graph) : G.IsClique [] := fun _ h => nomatch h

theorem isClique_singleton (G : Graph) (v : ℕ) : G.IsClique [v] := by
  intro a ha b hb hne
  rw [List.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) hne

theorem isIndependentSet_nil (G : Graph) : G.IsIndependentSet [] := fun _ h => nomatch h

theorem isIndependentSet_singleton (G : Graph) (v : ℕ) : G.IsIndependentSet [v] := by
  intro a ha b hb
  rw [List.mem_singleton] at ha hb
  rw [ha, hb]
  exact G.not_adj_self v

/-- A subset of a clique is a clique. -/
theorem IsClique.subset (h : G.IsClique S) (hS : ∀ v, v ∈ S' → v ∈ S) : G.IsClique S' :=
  fun a ha b hb => h a (hS a ha) b (hS b hb)

/-- A subset of an independent set is independent. -/
theorem IsIndependentSet.subset (h : G.IsIndependentSet S) (hS : ∀ v, v ∈ S' → v ∈ S) :
    G.IsIndependentSet S' :=
  fun a ha b hb => h a (hS a ha) b (hS b hb)

/-- Cliques are preserved by adding edges. -/
theorem IsClique.mono (hGH : ∀ e, e ∈ G.edges → e ∈ H.edges) (h : G.IsClique S) :
    H.IsClique S :=
  fun a ha b hb hne => (h a ha b hb hne).mono hGH

/-- Independent sets are preserved by removing edges. -/
theorem IsIndependentSet.anti (hHG : ∀ e, e ∈ H.edges → e ∈ G.edges)
    (h : G.IsIndependentSet S) : H.IsIndependentSet S :=
  fun a ha b hb hadj => h a ha b hb (hadj.mono hHG)

theorem isIndependentSet_iff :
    G.IsIndependentSet S ↔ ∀ u v, G.Adj u v → u ∉ S ∨ v ∉ S := by
  constructor
  · intro h a b hadj
    exact Decidable.not_and_iff_or_not.1 fun hab => h a hab.1 b hab.2 hadj
  · intro h a ha b hb hadj
    exact (h a b hadj).elim (fun hn => hn ha) (fun hn => hn hb)

/-- **Cliques and independent sets** [Kar72]. A set of vertices is a clique of
`G` iff it is an independent set of the complement of `G`. -/
theorem isClique_iff_isIndependentSet_of_isCompl (h : G.IsCompl H) :
    G.IsClique S ↔ H.IsIndependentSet S := by
  constructor
  · intro hS a ha b hb hadj
    exact (h a b hadj.ne).1 hadj (hS a ha b hb hadj.ne)
  · intro hS a ha b hb hne
    exact Decidable.by_contra fun hG => hS a ha b hb ((h a b hne).2 hG)

theorem hasClique_iff_hasIndependentSet_of_isCompl (h : G.IsCompl H) (ho : G.order = H.order)
    (k : ℕ) : G.HasClique k ↔ H.HasIndependentSet k := by
  constructor
  · rintro ⟨S, ⟨hnd, hlt⟩, hk, hS⟩
    exact ⟨S, ⟨hnd, fun v hv => ho ▸ hlt v hv⟩, hk,
      (isClique_iff_isIndependentSet_of_isCompl h).1 hS⟩
  · rintro ⟨S, ⟨hnd, hlt⟩, hk, hS⟩
    exact ⟨S, ⟨hnd, fun v hv => ho ▸ hlt v hv⟩, hk,
      (isClique_iff_isIndependentSet_of_isCompl h).2 hS⟩

/-! ### Vertex covers -/

/-- A set of vertices is a vertex cover iff it meets every pair of adjacent
vertices. -/
theorem isVertexCover_iff_forall_adj :
    G.IsVertexCover S ↔ ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S := by
  constructor
  · intro h a b hadj
    rcases hadj.2 with he | he
    · exact h (a, b) he hadj.1
    · exact (h (b, a) he fun e => hadj.1 e.symm).symm
  · intro h e he hne
    exact h e.1 e.2 ⟨hne, Or.inl he⟩

theorem isVertexCover_nil_edges (S : List ℕ) (n : ℕ) : (Graph.mk n []).IsVertexCover S :=
  fun _ h => nomatch h

/-- A superset of a vertex cover is a vertex cover. -/
theorem IsVertexCover.superset (h : G.IsVertexCover S) (hS : ∀ v, v ∈ S → v ∈ S') :
    G.IsVertexCover S' :=
  fun e he hne => (h e he hne).imp (hS _) (hS _)

/-- Vertex covers are preserved by removing edges. -/
theorem IsVertexCover.anti (hHG : ∀ e, e ∈ H.edges → e ∈ G.edges) (h : G.IsVertexCover S) :
    H.IsVertexCover S :=
  fun e he => h e (hHG e he)

/-- **Vertex covers and independent sets** [GJ79, Lemma 3.1]. If `T` is the
complement of `S`, then `S` is independent iff `T` is a vertex cover. -/
theorem isVertexCover_iff_isIndependentSet_of_compl {T : List ℕ} (h : ∀ v, v ∈ T ↔ v ∉ S) :
    G.IsVertexCover T ↔ G.IsIndependentSet S := by
  rw [isVertexCover_iff_forall_adj, isIndependentSet_iff]
  constructor
  · intro hT a b hadj
    exact (hT a b hadj).imp (h a).1 (h b).1
  · intro hS a b hadj
    exact (hS a b hadj).imp (h a).2 (h b).2

/-! ### Trivial instances -/

theorem isVertexSet_nil (G : Graph) : G.IsVertexSet [] := ⟨List.nodup_nil, fun _ h => nomatch h⟩

theorem hasClique_zero (G : Graph) : G.HasClique 0 := ⟨[], G.isVertexSet_nil, rfl, G.isClique_nil⟩

theorem hasIndependentSet_zero (G : Graph) : G.HasIndependentSet 0 :=
  ⟨[], G.isVertexSet_nil, rfl, G.isIndependentSet_nil⟩

theorem HasVertexCover.mono {k k' : ℕ} (h : G.HasVertexCover k) (hk : k ≤ k') :
    G.HasVertexCover k' :=
  let ⟨S, hS, hlen, hc⟩ := h
  ⟨S, hS, Nat.le_trans hlen hk, hc⟩

theorem hasVertexCover_of_edges_nil (n k : ℕ) : (Graph.mk n []).HasVertexCover k :=
  ⟨[], isVertexSet_nil _, Nat.zero_le _, isVertexCover_nil_edges _ _⟩

/-! ### Standard families -/

/-- The complete graph on `n` vertices. -/
def complete (n : ℕ) : Graph :=
  ⟨n, ((List.range (n * n)).map fun i => (i / n, i % n)).filter fun e => e.1 < e.2⟩

/-- The cycle on `n` vertices. -/
def cycle (n : ℕ) : Graph := ⟨n, (List.range n).map fun i => (i, (i + 1) % n)⟩

/-- The path on `n` vertices. -/
def path (n : ℕ) : Graph := ⟨n, (List.range (n - 1)).map fun i => (i, i + 1)⟩

/-- The star with centre `0` and `n` leaves. -/
def star (n : ℕ) : Graph := ⟨n + 1, (List.range n).map fun i => (0, i + 1)⟩

/-- The complete bipartite graph with sides `0, …, m - 1` and `m, …, m + n - 1`. -/
def completeBipartite (m n : ℕ) : Graph :=
  ⟨m + n, (List.range (m * n)).map fun i => (i / n, m + i % n)⟩

/-- The graph on `n` vertices without edges. -/
def edgeless (n : ℕ) : Graph := ⟨n, []⟩

@[simp] theorem order_complete (n : ℕ) : (complete n).order = n := rfl

@[simp] theorem order_cycle (n : ℕ) : (cycle n).order = n := rfl

@[simp] theorem order_path (n : ℕ) : (path n).order = n := rfl

@[simp] theorem order_star (n : ℕ) : (star n).order = n + 1 := rfl

@[simp] theorem order_completeBipartite (m n : ℕ) : (completeBipartite m n).order = m + n := rfl

theorem isIndependentSet_edgeless (n : ℕ) (S : List ℕ) : (edgeless n).IsIndependentSet S :=
  fun _ _ _ _ h => h.2.elim (fun h => nomatch h) (fun h => nomatch h)

/-- The centre of a star is a vertex cover. -/
theorem isVertexCover_star (n : ℕ) : (star n).IsVertexCover [0] := by
  intro e he _
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  exact Or.inl (List.mem_singleton.2 rfl)

theorem hasVertexCover_star (n : ℕ) : (star n).HasVertexCover 1 :=
  ⟨[0], ⟨by decide, fun v hv => by
    rw [List.mem_singleton.1 hv]; exact Nat.succ_pos n⟩, Nat.le_refl _, isVertexCover_star n⟩

end Graph

/-- **CLIQUE**: pairs `(G, k)` such that `G` has a clique with `k` vertices. -/
def CLIQUE : Language := Encoding.languageOf fun p : Graph × ℕ => p.1.HasClique p.2

/-- **INDEPENDENT-SET**: pairs `(G, k)` such that `G` has an independent set with
`k` vertices. -/
def INDEPENDENT_SET : Language :=
  Encoding.languageOf fun p : Graph × ℕ => p.1.HasIndependentSet p.2

/-- **VERTEX-COVER**: pairs `(G, k)` such that `G` has a vertex cover with at
most `k` vertices. -/
def VERTEX_COVER : Language := Encoding.languageOf fun p : Graph × ℕ => p.1.HasVertexCover p.2

theorem encode_mem_CLIQUE {G : Graph} {k : ℕ} :
    Encoding.encode (G, k) ∈ CLIQUE ↔ G.HasClique k :=
  Encoding.mem_languageOf_encode

theorem encode_mem_INDEPENDENT_SET {G : Graph} {k : ℕ} :
    Encoding.encode (G, k) ∈ INDEPENDENT_SET ↔ G.HasIndependentSet k :=
  Encoding.mem_languageOf_encode

theorem encode_mem_VERTEX_COVER {G : Graph} {k : ℕ} :
    Encoding.encode (G, k) ∈ VERTEX_COVER ↔ G.HasVertexCover k :=
  Encoding.mem_languageOf_encode

/-- On encodings of complementary graphs, CLIQUE and INDEPENDENT-SET agree. -/
theorem encode_mem_CLIQUE_iff_of_isCompl {G H : Graph} (h : G.IsCompl H)
    (ho : G.order = H.order) (k : ℕ) :
    Encoding.encode (G, k) ∈ CLIQUE ↔ Encoding.encode (H, k) ∈ INDEPENDENT_SET := by
  rw [encode_mem_CLIQUE, encode_mem_INDEPENDENT_SET]
  exact Graph.hasClique_iff_hasIndependentSet_of_isCompl h ho k

end Complexity
