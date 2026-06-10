import Mathlib

open NNReal

@[ext]
structure BasicWeightedGraph (X : Type*) extends SimpleGraph X where
  edgeWeight : X → X → ℝ≥0
  edgeWeight_symm : IsSymmOp edgeWeight
  edgeDef (u v : X) : Adj u v ↔ 0 < edgeWeight u v -- make a lemma for the contrapositive of this

@[ext]
structure WeightedGraph (X : Type*) extends BasicWeightedGraph X where
  killingTerm : X → ℝ≥0

-- Define predicates to recover simple graphs and produce them
-- Do everything for WeightedGraph, then include special cases

variable {X : Type*} (G : WeightedGraph X)

-- Maybe let this be a special corollary that uniquely includes decidability hypotheses
-- #check fun x y ↦ if G.Adj x y then 1 else 0

--instance {x y : X} : Decidable (G.Adj x y) := by infer_instance

structure StandardWeights (G : WeightedGraph X) : Prop where
  edgeWeight_Adj_iff : G.Adj x y ↔ G.edgeWeight x y = 1
  edgeWeight_NotAdj_iff : ¬ G.Adj x y ↔ G.edgeWeight x y = 0
  killingTerm_zero : G.killingTerm = 0

@[simp]
lemma standardWeights_edgeWeight_neq_zero_iff_eq_one (h : StandardWeights G) :
    G.edgeWeight x y ≠ 0 ↔ G.Adj x y := by
  contrapose
  exact h.edgeWeight_NotAdj_iff.symm

@[simp]
lemma standardWeights_edgeWeight_neq_one_iff_eq_zero (h : StandardWeights G) :
    G.edgeWeight x y ≠ 1 ↔ ¬ G.Adj x y := by
  contrapose
  exact h.edgeWeight_Adj_iff.symm

-- include way to produce graph with standardweights from simpleGraph

-- Example 0.2 (Graphs with standard weights)
lemma standardWeightEdgeSet (h : StandardWeights G) :
    s(v, w) ∈ G.edgeSet ↔ G.edgeWeight v w = 1 := (G.mem_edgeSet).trans h.edgeWeight_Adj_iff

variable [Fintype X]

def WeightedGraph.degree (x : X) : ℝ≥0 :=
  ∑ y, (G.edgeWeight x y) + (G.killingTerm x)

noncomputable
instance : Fintype ↑(G.neighborSet x) := Fintype.ofFinite (G.neighborSet x)

lemma degreeWithStandardWeights (h : StandardWeights G) (x : X) :
    G.degree x = G.toSimpleGraph.degree x := by
  simp only [WeightedGraph.degree, h.killingTerm_zero, Pi.zero_apply, add_zero,
    ← G.card_neighborFinset_eq_degree, G.neighborFinset_def, SimpleGraph.neighborSet,
    Finset.cast_card]
  rw [← Finset.sum_filter_ne_zero]
  congr! with y hy
  · grind [standardWeights_edgeWeight_neq_zero_iff_eq_one]
  exact h.edgeWeight_Adj_iff.mp ((G.toSimpleGraph.mem_neighborFinset x y).mp hy)
