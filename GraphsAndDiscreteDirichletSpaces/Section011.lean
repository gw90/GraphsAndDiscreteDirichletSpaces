import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Order
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

open NNReal
/-
@[ext]
structure edgeWeight X where
  toFun : X → X → ℝ≥0
  symm : ∀ ⦃x y : X⦄, toFun x y = toFun y x
  no_loop : ∀ ⦃x : X⦄, toFun x x = 0

@[ext]
structure killingTerm X where
  toFun : X → ℝ≥0
-/
-- Definition 0.1 (Graph over finite X)
@[ext]
structure finiteGraphOver X where
  finiteVertices : Fintype X
  b : X → X → ℝ≥0
  symm : ∀ ⦃x y : X⦄, b x y = b y x
  no_loop : ∀ ⦃x : X⦄, b x x = 0
  c : X → ℝ≥0

set_option linter.unusedFintypeInType false
namespace finiteGraphOver

variable {X : Type*} (G : finiteGraphOver X) (x : X)
--instance : Fintype X := G.finiteVertices
variable [Fintype X] -- I should be able to eliminate this though, shouldn't I?

def isEdge (e : X × X) := 0 < G.b e.1 e.2

def edgeSet := {(x, y) : X × X | 0 < G.b x y}

lemma edge_def (e : X × X) : e ∈ G.edgeSet ↔ G.isEdge e := by rfl

lemma edgeSet_def (e : X × X) : e ∈ G.edgeSet ↔ 0 < G.b e.1 e.2 := by rfl

lemma isEdge_def (e : X × X) : G.isEdge e ↔ 0 < G.b e.1 e.2 := by rfl

def neighbors (x y : X) := 0 < G.b x y

noncomputable
instance : DecidablePred (G.neighbors x) := instDecidablePredComp

structure StandardWeights : Prop where
  b_binary : ∀ x y : X, G.b x y ∈ {n | n = 0 ∨ n = 1}
  b_binary' : ∀ x y : X, G.b x y = 0 ∨ G.b x y = 1
  c_zero : ∀ x : X, G.c x = 0

-- Example 0.2 (Graphs with standard weights)
lemma standardWeightEdgeSet (h : StandardWeights G) :
    G.edgeSet = {(x, y) : X × X | G.b x y = 1} := by
  ext e
  simp only [edgeSet_def, Set.mem_setOf_eq]
  have hyp := h.b_binary' e.1 e.2
  cases hyp with
  | inl h_1 => simp_all only [lt_self_iff_false, zero_ne_one]
  | inr h_2 => simp_all only [zero_lt_one]

-- Definition 0.3 (Degree)
def degree (x : X) : ℝ≥0 :=
  ∑ y, (G.b x y) + (G.c x)

-- Example 0.4 (Combinatorial Degree)
lemma degreeWithStandardWeights (h : StandardWeights G) (x : X) :
    G.degree x = ∑ y with G.neighbors x y, 1 := by
  simp only [degree, h.c_zero, add_zero, neighbors]
  have hyp := h.b_binary' x
  have gt0isEq1 (y : X) : 0 < G.b x y ↔ G.b x y = 1 := by
    constructor
    · have := hyp y
      intro
      cases this with
      | inl h1 => simp_all only [lt_self_iff_false]
      | inr h2 => simp_all only [zero_lt_one]
    · intro
      simp_all only [zero_lt_one]
  have sumEqSumOfNon0 : ∑ y, G.b x y = ∑ y with G.b x y ≠ 0, G.b x y :=
    Eq.symm (Finset.sum_filter_ne_zero Finset.univ)
  have neq0iff1 (y : X) : G.b x y ≠ 0 ↔ G.b x y = 1 := by
    constructor
    · have := hyp y
      intro a
      cases this with
      | inl h1 => simp_all only [ne_eq, not_true_eq_false]
      | inr h2 => exact h2
    · exact fun a ↦ ne_zero_of_eq_one a
  simp only [sumEqSumOfNon0, gt0isEq1, neq0iff1]
  apply Finset.sum_congr -- alternatively use congr!; simp_all
  · rfl
  simp

lemma degreeWithStandardWeightsCard (h : StandardWeights G) (x : X) :
    G.degree x = Finset.card {y | G.neighbors x y} := by
  simp [degreeWithStandardWeights G h x]

end finiteGraphOver
