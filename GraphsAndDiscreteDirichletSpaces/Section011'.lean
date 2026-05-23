import Mathlib

open NNReal

-- Definition 0.1 (Graph over finite X)
@[ext]
structure GraphOver (X : Type*) extends SimpleGraph X where
  edgeWeight : X → X → ℝ≥0
  edgeDef (u v : X) : Adj u v ↔ edgeWeight u v > 0
  killingTerm : X → ℝ≥0

set_option linter.unusedFintypeInType false
namespace GraphOver

variable {X : Type*} (G : GraphOver X) (x y : X)
variable [Fintype X] -- I should be able to eliminate this though, shouldn't I?

structure StandardWeights (G : GraphOver X) : Prop where
  edgeWeight_binary : ∀ x y : X, G.edgeWeight x y ∈ {n | n = 0 ∨ n = 1}
  edgeWeight_binary' : ∀ x y : X, G.edgeWeight x y = 0 ∨ G.edgeWeight x y = 1
  killingTerm_zero : ∀ x : X, G.killingTerm x = 0

-- Example 0.2 (Graphs with standard weights)
lemma standardWeightEdgeSet (h : StandardWeights G) :
    s(v, w) ∈ G.edgeSet ↔ G.edgeWeight v w = 1 := by
  constructor
  · intro h'
    have hyp := h.edgeWeight_binary' v w
    cases hyp with
    | inl h_1 => simp_all [G.edgeDef v w]
    | inr h_2 => exact h_2
  intro h'
  have hyp := h.edgeWeight_binary' v w
  cases hyp with
  | inl h_1 => simp_all
  | inr h_2 => simp_all [G.edgeDef v w]

-- Definition 0.3 (Degree)
def deg (x : X) : ℝ≥0 :=
  ∑ y, (G.edgeWeight x y) + (G.killingTerm x)

variable [DecidableRel G.Adj]

noncomputable
instance : Fintype ↑(G.neighborSet x) := by exact Fintype.ofFinite ↑(G.neighborSet x)

-- Example 0.4 (Combinatorial Degree)
lemma degreeWithStandardWeights (h : StandardWeights G) (x : X) :
    G.deg x = G.degree x := by
  rw [← G.card_neighborFinset_eq_degree]
  
  sorry

lemma degreeWithStandardWeightsCard (h : StandardWeights G) (x : X) :
    G.deg x = (G.neighborFinset x).card := by
  rw [degreeWithStandardWeights G h x]
  simp


end GraphOver
