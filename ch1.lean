import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Order
import Mathlib.LinearAlgebra.BilinearMap

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

variable {X : Type*} (G : finiteGraphOver X) (x : X)

def isEdge (e : X × X) := 0 < G.b.toFun e.1 e.2

def edgeSet := {(x, y) : X × X | 0 < G.b.toFun x y}

lemma edge_def (e : X × X) : e ∈ G.edgeSet ↔ G.isEdge e := by rfl

lemma edgeSet_def (e : X × X) : e ∈ G.edgeSet ↔ 0 < G.b.toFun e.1 e.2 := by rfl

lemma isEdge_def (e : X × X) : G.isEdge e ↔ 0 < G.b.toFun e.1 e.2 := by rfl

def neighbors (x y : X) := 0 < G.b.toFun x y

noncomputable
instance : DecidablePred (G.neighbors x) := instDecidablePredComp

structure StandardWeights : Prop where
  b_binary : ∀ x y : X, G.b.toFun x y ∈ {n | n = 0 ∨ n = 1}
  b_binary' : ∀ x y : X, G.b.toFun x y = 0 ∨ G.b.toFun x y = 1
  c_zero : ∀ x : X, G.c.toFun x = 0

-- Example 0.2 (Graphs with standard weights)
lemma standardWeightEdgeSet (h : StandardWeights G) :
    G.edgeSet = {(x, y) : X × X | G.b.toFun x y = 1} := by
  ext e
  simp only [edgeSet_def, Set.mem_setOf_eq]
  have hyp := h.b_binary' e.1 e.2
  cases hyp with
  | inl h_1 => simp_all only [lt_self_iff_false, zero_ne_one]
  | inr h_2 => simp_all only [zero_lt_one]

-- Definition 0.3 (Degree)
def degree (x : X) : ℝ≥0 :=
  ∑ y ∈ G.vertices, (G.b.toFun x y) + (G.c.toFun x)

-- Example 0.4 (Combinatorial Degree)
lemma degreeWithStandardWeights (h : StandardWeights G) (x : X) :
    G.degree x = ∑ y ∈ G.vertices with G.neighbors x y, 1 := by
  simp only [degree, h.c_zero, add_zero, neighbors]
  have hyp := h.b_binary' x
  have gt0isEq1 (y : X) : 0 < G.b.toFun x y ↔ G.b.toFun x y = 1 := by
    constructor
    · have := hyp y
      intro a
      cases this with
      | inl h1 => simp_all only [lt_self_iff_false]
      | inr h2 => simp_all only [zero_lt_one]
    · intro a
      simp_all only [zero_lt_one]
  have setGt0Eq1 : {y ∈ G.vertices | 0 < G.b.toFun x y} = {y ∈ G.vertices | G.b.toFun x y = 1} := by
    simp_all only
  have ignore0 := Finset.sum_filter_ne_zero G.vertices (f := (fun y ↦ G.b.toFun x y))
  rw [setGt0Eq1, ← ignore0]
  have (y : X) : G.b.toFun x y ≠ 0 ↔ G.b.toFun x y = 1 := by
    constructor
    · have := hyp y
      intro a
      cases this with
      | inl h1 => simp_all only [ne_eq, not_true_eq_false]
      | inr h2 => exact h2
    · exact fun a ↦ ne_zero_of_eq_one a
  have : ∑ x_1 ∈ G.vertices with G.b.toFun x x_1 ≠ 0, G.b.toFun x x_1 =
    ∑ x_1 ∈ G.vertices with G.b.toFun x x_1 = 1, G.b.toFun x x_1 := by
    simp_all only [ne_eq]
  rw [this]
  apply Finset.sum_congr -- try re-working using this from beginning
  · rfl
  simp

lemma degreeWithStandardWeightsCard (h : StandardWeights G) (x : X) :
    G.degree x = {y ∈ G.vertices | G.neighbors x y}.card := by
  simp [degreeWithStandardWeights G h x]

-- Section 0.1.2
--variable [TopologicalSpace X] [DiscreteTopology X]
--variable {F : Type*} [ContinuousMapClass F X ℝ] (f : F)
-- Don't deal with topologies, just consider all functions

noncomputable
def Qfun (f g : X → ℝ) :=
  (1/2) * ∑ x ∈ G.vertices, ∑ y ∈ G.vertices, (G.b.toFun x y) * (f x - f y) * (g x - g y) +
    ∑ x ∈ G.vertices, (G.c.toFun x) * f x * g x

instance Q' : IsBilinearMap (R := ℝ) G.Qfun where
  add_left f g h := by
    unfold Qfun
    apply sub_eq_zero.mp
    simp [sub_add_eq_sub_sub]
    ring_nf
    simp [Finset.sum_add_distrib]
    ring
  smul_left c f g := by
    unfold Qfun
    field_simp
    ring_nf
    simp [Finset.sum_add_distrib]
    ring_nf
    simp [Finset.mul_sum (a := c)]
    ring_nf
  add_right f g h := by
    unfold Qfun
    apply sub_eq_zero.mp
    simp [sub_add_eq_sub_sub]
    ring_nf
    simp [Finset.sum_add_distrib]
    ring
  smul_right c f g := by
    unfold Qfun
    ring_nf
    simp [Finset.sum_add_distrib]
    ring_nf
    simp [Finset.mul_sum (a := c)]
    ring_nf
    apply sub_eq_zero.mp
    ring_nf

noncomputable
def Q := G.Q'.toLinearMap

lemma Q_apply : G.Q f g = G.Qfun f g := by rfl

#check G.Q



end finiteGraphOver
