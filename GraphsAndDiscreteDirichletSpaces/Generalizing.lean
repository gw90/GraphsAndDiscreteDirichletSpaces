import Mathlib

#check Graph

#check SimpleGraph

#check Digraph

open NNReal

structure WeightedGraph (V E : Type*) extends Graph V E where
  edgeWeight : E → ℝ≥0
  notEdge_weightZero : e ∉ edgeSet → edgeWeight e = 0
  vertexWeight : V → ℝ≥0


structure Graph' (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β → α → α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet := by grind

structure SimpleGraph' (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Symmetric Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph

variable (E : Type u)

structure MySimpleGraph (V : Type u) extends Graph (V : Type u) (E : Type u) where
  Adj : V → V → Prop
  Adj_def {w v} : Adj w v ↔ ∃ e, IsLink e w v
  symm : Symmetric Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
  no_multiEdge {e w v e'} : IsLink e w v ∧ IsLink e' w v → e = e'

namespace MySimpleGraph
variable {ι : Sort*} {V : Type u} (G : MySimpleGraph V _) {a b c u v w : V} {e : Sym2 V}

@[simp]
protected theorem irrefl {v : V} : ¬G.Adj v v :=
  G.loopless.irrefl v

theorem adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u :=
  ⟨fun x => G.symm x, fun x => G.symm x⟩

@[symm]
theorem adj_symm (h : G.Adj u v) : G.Adj v u :=
  G.symm h

theorem Adj.symm {u v : V} (h : G.Adj u v) : G.Adj v u :=
  G.symm h

theorem ne_of_adj (h : G.Adj a b) : a ≠ b := by
  rintro rfl
  exact G.irrefl h

protected theorem Adj.ne {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : a ≠ b :=
  G.ne_of_adj h

protected theorem Adj.ne' {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : b ≠ a :=
  h.ne.symm

theorem ne_of_adj_of_not_adj {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x) : v ≠ w := fun h' =>
  hn (h' ▸ h)

theorem adj_injective : Injective (Adj : SimpleGraph V → V → V → Prop) :=
  fun _ _ => SimpleGraph.ext

-- the source doesn't deal with multi-edges (have to generalize?
-- https://math.stackexchange.com/questions/4949364/laplacian-matrix-for-a-multi-graph
-- get distinction between normalized and unnormalized graph laplacian

/-
To-do:
- write up everything informally first (in a proper latex notebook)
- informally colledge each definition and its conditions
- vacuously formalize the conditions
- formalize the definiton of the general version
- formalize each special case (statement only)
- formalize the proofs
-/
