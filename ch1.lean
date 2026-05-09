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
  vertices : Finset X
  allVertices : ∀ (x : X), x ∈ vertices
  b : edgeWeight X
  c : killingTerm X

namespace finiteGraphOver

variable {X : Type*} (g : finiteGraphOver X)

def isEdge (e : X × X) := 0 < g.b.toFun e.1 e.2

def edgeSet := {(x, y) : X × X | 0 < g.b.toFun x y}

lemma edge_def (e : X × X) : e ∈ g.edgeSet ↔ g.isEdge e := by rfl

lemma edgeSet_def (e : X × X) : e ∈ g.edgeSet ↔ 0 < g.b.toFun e.1 e.2 := by rfl

lemma isEdge_def (e : X × X) : e ∈ g.edgeSet ↔ 0 < g.b.toFun e.1 e.2 := by rfl

def neighbors (x y : X) := 0 < g.b.toFun x y

structure StandardWeights : Prop where
  b_binary : ∀ x y : X, g.b.toFun x y ∈ {n | n = 0 ∨ n = 1}
  b_binary' : ∀ x y : X, g.b.toFun x y = 0 ∨ g.b.toFun x y = 1
  c_zero : ∀ x : X, g.c.toFun x = 0

-- Example 0.2 (Graphs with standard weights)
example (g : finiteGraphOver X) (h : StandardWeights g) :
    g.edgeSet = {(x, y) : X × X | g.b.toFun x y = 1} := by
  ext e
  simp only [edgeSet_def, Set.mem_setOf_eq]
  have hyp := h.b_binary' e.1 e.2
  cases hyp with
  | inl h_1 => simp_all only [lt_self_iff_false, zero_ne_one]
  | inr h_2 => simp_all only [zero_lt_one]

-- Definition 0.3 (Degree)
def degree (g : finiteGraphOver X) (x : X) : ℝ≥0 :=
  ∑ y : g.vertices, (g.b.toFun x y) + (g.c.toFun x)
