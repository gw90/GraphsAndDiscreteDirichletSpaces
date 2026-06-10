import Mathlib

open NNReal

-- Definition 0.1 (Graph over finite X)
@[ext]
structure GraphOver (X : Type*) extends SimpleGraph X where
  edgeWeight : X → X → ℝ≥0
  edgeWeight_symm : IsSymmOp edgeWeight
  /- the property below is why we don't use existing EdgeLabeling API.
  We want non-adjacent vertices to have an edge weight of 0-/
  edgeDef (u v : X) : Adj u v ↔ 0 < edgeWeight u v -- make a lemma for the contrapositive of this
  killingTerm : X → ℝ≥0

set_option linter.unusedFintypeInType false
namespace GraphOver

abbrev b {X : Type*} (G : GraphOver X) := G.edgeWeight
abbrev c {X : Type*} (G : GraphOver X) := G.killingTerm

variable {X : Type*} (G : GraphOver X) (x y : X)

structure StandardWeights (G : GraphOver X) : Prop where
  edgeWeight_binary : ∀ x y : X, G.b x y = 0 ∨ G.b x y = 1
  killingTerm_zero : ∀ x : X, G.c x = 0

-- To-do: define a coercion for when we have Standard Weights

-- Example 0.2 (Graphs with standard weights)
lemma standardWeightEdgeSet (h : StandardWeights G) :
    s(v, w) ∈ G.edgeSet ↔ G.b v w = 1 := by
  constructor
  · intro h'
    have hyp := h.edgeWeight_binary v w
    cases hyp with
    | inl h_1 => simp_all [G.edgeDef v w]
    | inr h_2 => exact h_2
  intro h'
  have hyp := h.edgeWeight_binary v w
  cases hyp with
  | inl h_1 => simp_all
  | inr h_2 => simp_all [G.edgeDef v w]

variable [Fintype X] -- I should be able to eliminate this though, shouldn't I?
-- Definition 0.3 (Degree)
def deg (x : X) : ℝ≥0 :=
  ∑ y, (G.b x y) + (G.c x)

noncomputable
instance : DecidableRel G.Adj := by exact Classical.decRel G.Adj

noncomputable
instance : Fintype ↑(G.neighborSet x) := by exact Fintype.ofFinite ↑(G.neighborSet x)

--set_option linter.unusedDecidableInType false
-- Example 0.4 (Combinatorial Degree)
lemma degreeWithStandardWeights (h : StandardWeights G) (x : X) :
    G.deg x = G.degree x := by
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_def]
  unfold SimpleGraph.neighborSet
  unfold deg
  rw [h.killingTerm_zero, add_zero]
  rw [Finset.cast_card]
  rw [← Finset.sum_filter_ne_zero]
  have (y : X) : G.b x y ≠ 0 → G.b x y = 1 := by
    have := h.edgeWeight_binary x y
    intro h
    cases this with
    | inl h1 => simp_all
    | inr h2 => exact h2
  have : ∑ x_1 with G.b x x_1 ≠ 0, G.b x x_1 =
      ∑ x_1 with G.b x x_1 ≠ 0, 1 := by
    congr!
    simp_all
  rw [this]
  congr with a
  constructor
  · intro h
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have : 0 < G.b x a := by exact pos_of_ne_zero h
    simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (G.edgeDef x a).mpr this
  simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  intro h
  suffices G.b x a > 0 by exact pos_iff_ne_zero.mp this
  exact (G.edgeDef x a).mp h

lemma degreeWithStandardWeightsCard (h : StandardWeights G) (x : X) :
    G.deg x = (G.neighborFinset x).card := by
  rw [degreeWithStandardWeights G h x]
  simp


end GraphOver
