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

structure finiteGraphOver X where
  edgeSet : Finset X
  b : edgeWeight X
  c : killingTerm X

variable {X : Type*}
variable (myGraph : finiteGraphOver X)

#check myGraph.b.toFun

def degree (g : finiteGraphOver X) (x : X) : ℝ≥0 :=
  ∑ y ∈ g.edgeSet, (g.b.toFun x y) + (g.c.toFun x)

variable (myEdge : X)

#check myGraph
#check degree myGraph myEdge
