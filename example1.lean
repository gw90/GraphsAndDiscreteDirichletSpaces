import Mathlib

open NNReal

class myFiniteStructure (X : Type*) extends Fintype X where
  b : X → X → ℝ≥0 -- edgeWeight
  symm : ∀ ⦃x y : X⦄, b x y = b y x
  no_loop : ∀ ⦃x : X⦄, b x x = 0
  c : X → ℝ≥0 -- kiling term

variable {C : Type*} (G : myFiniteStructure C)

#check G.b

#check ∑ (x : C), 1
