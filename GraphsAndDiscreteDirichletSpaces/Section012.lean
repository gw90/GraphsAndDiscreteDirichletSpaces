import GraphsAndDiscreteDirichletSpaces.Section011

open NNReal

set_option linter.unusedFintypeInType false
namespace finiteGraphOver

variable {X : Type*} (G : finiteGraphOver X) (x : X) [Fintype X]

-- Section 0.1.2
--variable [TopologicalSpace X] [DiscreteTopology X]
--variable {F : Type*} [ContinuousMapClass F X ℝ] (f : F)
-- Don't deal with topologies, just consider all functions

noncomputable
instance : DecidableEq X := Classical.typeDecidableEq X

-- Operators
noncomputable
def stdBasis := (Pi.basisFun (η := X) (R := ℝ))

noncomputable
def matrixAssociatedToOp (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) :=
  LinearMap.toMatrix stdBasis stdBasis L

noncomputable
def opInducedByMatrix (M : Matrix X X ℝ) :=
  (LinearMap.toMatrix stdBasis stdBasis).symm M

scoped notation "𝟙_" y:max => Pi.single y 1

lemma opMatrixEntryVal (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (x y : X) :
    (matrixAssociatedToOp L) x y = L (𝟙_y) x := by
  simp [matrixAssociatedToOp, stdBasis, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_apply]

lemma opDef (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (f : X → ℝ) :
  (L f) x = ∑ y, (matrixAssociatedToOp L) x y * f y := by
  unfold matrixAssociatedToOp
  have : f = stdBasis.equivFun.symm f := by rfl
  nth_rw 1 [this, Module.Basis.equivFun_symm_apply stdBasis f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr
  ext y
  rw [mul_comm]
  congr

-- can I get this notion of symmetry out of Mathlib somehow?
-- I don't want to have to define an inner product
def IsSymmOp (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := (matrixAssociatedToOp L).IsSymm

-- remember to really prove every little statement

-- Forms

open LinearMap

noncomputable
def matrixAssociatedToForm (Q : LinearMap.BilinForm ℝ (X → ℝ)) :=
  BilinForm.toMatrix' (n := X) (R₁ := ℝ) Q

noncomputable
def formInducedByMatrix (M : Matrix X X ℝ) : (X → ℝ) →ₗ[ℝ] (X → ℝ) →ₗ[ℝ] ℝ :=
  (Matrix.toBilin' M)

example (Q : LinearMap.BilinForm ℝ (X → ℝ)) (x y : X) :
    Q (𝟙_x) (𝟙_y) = (matrixAssociatedToForm Q) x y := by rfl

example (Q : LinearMap.BilinForm ℝ (X → ℝ)) (x : X) :
    Q (𝟙_x) 1 = ∑ z, (matrixAssociatedToForm Q) x z := by
  unfold matrixAssociatedToForm
  simp only [BilinForm.toMatrix'_apply, ← map_sum, Finset.univ_sum_single]
  rfl

-- a form is symmetric iff associated matrix is symmetric
#check LinearMap.BilinForm.isSymm_iff_basis stdBasis
#check (LinearMap.BilinForm.isSymm_iff_basis stdBasis).mpr
#check LinearMap.BilinForm.isSymm_iff
#check LinearMap.BilinForm.isSymm_def
#check stdBasis (X := X)

example (l : Matrix X X ℝ) (hypl : Matrix.IsSymm l) (f g : X → ℝ) :
    (formInducedByMatrix l) f g = ∑ x, ∑ y, l x y * f x * g y := by
  --unfold formInducedByMatrix
  -- show that the form is symmetric if matrix is symmetric
  have : BilinForm.IsSymm (formInducedByMatrix l) := by
    unfold formInducedByMatrix
    sorry
  have := BilinForm.isSymm_def.mp this
  have := Matrix.IsSymm.ext_iff.mp hypl
  -- do this on paper
  sorry

-- put 4-part eqn from p. 9

noncomputable
def associatedFormFun (f g : X → ℝ) :=
  (1/2) * ∑ x, ∑ y, (G.b x y) * (f x - f y) * (g x - g y) +
    ∑ x, (G.c x) * f x * g x

open Finset

instance associatedFormBilinearMap : IsBilinearMap (R := ℝ) G.associatedFormFun where
  add_left f g h := by
    unfold associatedFormFun
    apply sub_eq_zero.mp
    simp [sub_add_eq_sub_sub]
    ring_nf
    simp [sum_add_distrib]
    ring
  smul_left c f g := by
    unfold associatedFormFun
    field_simp
    ring_nf
    simp [sum_add_distrib]
    ring_nf
    simp [mul_sum]
    ring_nf
  add_right f g h := by
    unfold associatedFormFun
    apply sub_eq_zero.mp
    simp [sub_add_eq_sub_sub]
    ring_nf
    simp [sum_add_distrib]
    ring
  smul_right c f g := by
    unfold associatedFormFun
    ring_nf
    simp [sum_add_distrib]
    ring_nf
    simp [mul_sum]
    ring_nf
    apply sub_eq_zero.mp
    ring_nf

noncomputable
def associatedForm := G.associatedFormBilinearMap.toLinearMap

lemma associatedForm_apply {f g} : G.associatedForm f g = G.associatedFormFun f g := by rfl

-- resume at p. 10

end finiteGraphOver
