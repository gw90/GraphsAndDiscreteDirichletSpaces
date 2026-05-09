import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

#check LinearMap.BilinForm.toMatrix' (R₁ := ℝ)

open NNReal

@[ext]
structure edgeWeight X where
  toFun : X → X → ℝ≥0
  symm : ∀ ⦃x y : X⦄, toFun x y = toFun y x
  no_loop : ∀ ⦃x : X⦄, toFun x x = 0

@[ext]
structure killingTerm X where
  toFun : X → ℝ≥0

-- Definition 0.1 (Graph over finite X)
@[ext]
structure finiteGraphOver X where
  finiteVertices : Fintype X
  vertices := finiteVertices.elems
  b : edgeWeight X
  c : killingTerm X

namespace finiteGraphOver

variable {X : Type*} (g : finiteGraphOver X) (x : X)

def isEdge (e : X × X) := 0 < g.b.toFun e.1 e.2

def edgeSet := {(x, y) : X × X | 0 < g.b.toFun x y}

lemma edge_def (e : X × X) : e ∈ g.edgeSet ↔ g.isEdge e := by rfl

lemma edgeSet_def (e : X × X) : e ∈ g.edgeSet ↔ 0 < g.b.toFun e.1 e.2 := by rfl

lemma isEdge_def (e : X × X) : g.isEdge e ↔ 0 < g.b.toFun e.1 e.2 := by rfl

def neighbors (x y : X) := 0 < g.b.toFun x y

noncomputable
instance : DecidablePred (g.neighbors x) := instDecidablePredComp

structure StandardWeights : Prop where
  b_binary : ∀ x y : X, g.b.toFun x y ∈ {n | n = 0 ∨ n = 1}
  b_binary' : ∀ x y : X, g.b.toFun x y = 0 ∨ g.b.toFun x y = 1
  c_zero : ∀ x : X, g.c.toFun x = 0

-- Example 0.2 (Graphs with standard weights)
lemma standardWeightEdgeSet (h : StandardWeights g) :
    g.edgeSet = {(x, y) : X × X | g.b.toFun x y = 1} := by
  ext e
  simp only [edgeSet_def, Set.mem_setOf_eq]
  have hyp := h.b_binary' e.1 e.2
  cases hyp with
  | inl h_1 => simp_all only [lt_self_iff_false, zero_ne_one]
  | inr h_2 => simp_all only [zero_lt_one]

-- Definition 0.3 (Degree)
def degree (x : X) : ℝ≥0 :=
  ∑ y ∈ g.vertices, (g.b.toFun x y) + (g.c.toFun x)

-- Example 0.4 (Combinatorial Degree)
lemma degreeWithStandardWeights (h : StandardWeights g) (x : X) :
    g.degree x = ∑ y ∈ g.vertices with g.neighbors x y, 1 := by
  simp only [degree, h.c_zero, add_zero, neighbors]
  have hyp := h.b_binary' x
  have gt0isEq1 (y : X) : 0 < g.b.toFun x y ↔ g.b.toFun x y = 1 := by
    constructor
    · have := hyp y
      intro a
      cases this with
      | inl h1 => simp_all only [lt_self_iff_false]
      | inr h2 => simp_all only [zero_lt_one]
    · intro a
      simp_all only [zero_lt_one]
  have setGt0Eq1 : {y ∈ g.vertices | 0 < g.b.toFun x y} = {y ∈ g.vertices | g.b.toFun x y = 1} := by
    simp_all only
  have ignore0 := Finset.sum_filter_ne_zero g.vertices (f := (fun y ↦ g.b.toFun x y))
  rw [setGt0Eq1]
  rw [← ignore0]
  have (y : X) : g.b.toFun x y ≠ 0 ↔ g.b.toFun x y = 1 := by
    constructor
    · have := hyp y
      intro a
      cases this with
      | inl h1 => simp_all only [ne_eq, not_true_eq_false]
      | inr h2 => exact h2
    · exact fun a ↦ ne_zero_of_eq_one a
  have : ∑ x_1 ∈ g.vertices with g.b.toFun x x_1 ≠ 0, g.b.toFun x x_1 =
    ∑ x_1 ∈ g.vertices with g.b.toFun x x_1 = 1, g.b.toFun x x_1 := by
    simp_all only [ne_eq]
  rw [this]
  apply Finset.sum_congr -- try re-working using this from beginning
  · rfl
  simp

lemma degreeWithStandardWeightsCard (h : StandardWeights g) (x : X) :
    g.degree x = {y ∈ g.vertices | g.neighbors x y}.card := by
  simp [degreeWithStandardWeights g h x]

end finiteGraphOver
