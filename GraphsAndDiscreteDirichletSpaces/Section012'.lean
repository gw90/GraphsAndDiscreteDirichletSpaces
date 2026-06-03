import GraphsAndDiscreteDirichletSpaces.Section011'

open NNReal

set_option linter.unusedFintypeInType false
namespace GraphOver

variable {X : Type*} (G : GraphOver X) (x : X) [Fintype X]

-- Section 0.1.2
--variable [TopologicalSpace X] [DiscreteTopology X]
--variable {F : Type*} [ContinuousMapClass F X ℝ] (f : F)
-- Don't deal with topologies, just consider all functions

noncomputable
instance : DecidableEq X := Classical.typeDecidableEq X

-- Operators
/-A natural basis for C (X) consists of characteristic functions 1x
which take the value 1 at x and are 0 otherwise.-/
noncomputable
def stdBasis := (Pi.basisFun (η := X) (R := ℝ))

scoped notation "𝟙_" y:max => Pi.single y 1

noncomputable
def matrixAssociatedToOp (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) :=
  LinearMap.toMatrix stdBasis stdBasis L

-- Matrix associated to L
noncomputable
abbrev l_Op (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := matrixAssociatedToOp L

noncomputable
def opInducedByMatrix (M : Matrix X X ℝ) :=
  (LinearMap.toMatrix stdBasis stdBasis).symm M

-- Operator induced by Matrix M (or what should really be l)
noncomputable
abbrev L (M : Matrix X X ℝ) := opInducedByMatrix M

-- A direct calculation gives that l (x, y) = L1y (x)
lemma opMatrixEntryVal (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (x y : X) :
    (l_Op L) x y = L (𝟙_y) x := by
  simp [matrixAssociatedToOp, stdBasis, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_apply]

/-
Clearly, to any operator L, there exists a unique function l : X × X −→ R with
L f (x) =  ∑︁  y ∈X  l(x, y) f (y)  for all f ∈ C (X) and x ∈ X.
-/
lemma opDef (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (f : X → ℝ) :
  (L f) x = ∑ y, (l_Op L) x y * f y := by
  unfold l_Op
  have : f = stdBasis.equivFun.symm f := by rfl
  nth_rw 1 [this, Module.Basis.equivFun_symm_apply stdBasis f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr
  ext y
  rw [mul_comm]
  congr

-- can I get this notion of symmetry out of Mathlib somehow?
-- I don't want to have to define an inner product
-- L is a symmetric operator when l is a symmetric matrix
/-We say that L is an operator on C (X) with symmetric matrix if l is symmetric
or call L a symmetric operator in this case.-/
def IsSymmOp (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := (l_Op L).IsSymm

-- maybe use IsSymmOp from Mathlib.Logic.OpClass?

-- WTS: self adjoint iff induced matrix is symmetric

-- remember to really prove every little statement

-- Forms

open LinearMap

/-A form over X is a map  Q : C (X) × C (X) −→ R  which is bilinear-/
#check LinearMap.BilinForm ℝ (X → ℝ)

/-A form Q is called symmetric if Q satisfies Q( f , g) = Q(g, f ) for all f , g ∈ C (X)-/
-- maybe use IsSymmOp from Mathlib.Logic.OpClass?

/-For the values of Q on the diagonal {( f , f ) | f ∈ C (X)} of C (X) × C (X) we will
use the notation  Q( f ) = Q( f , f )-/

variable (Q : LinearMap.BilinForm ℝ (X → ℝ))

/-
In particular, when Q is symmetric, we get  Q( f + g) = Q( f ) + 2Q( f , g) + Q(g).
-/
example {f g : X → ℝ} (h : Q.IsSymm) :
    Q (f + g) (f + g) = Q f f + 2 * (Q f g) + Q g g := by
  simp_all [h.eq]
  ring

/-If Q is a form, then there exists a unique function l : X × X −→ R with
Q( f , g) =  ∑︁  x,y∈X  l(x, y) f (x)g(y)
for all f , g ∈ C (X). We call Q the form induced by the matrix l-/
noncomputable
def formInducedByMatrix (M : Matrix X X ℝ) : (X → ℝ) →ₗ[ℝ] (X → ℝ) →ₗ[ℝ] ℝ :=
  (Matrix.toBilin' M)

/-and l the matrix associated to Q-/
noncomputable
def matrixAssociatedToForm :=
  BilinForm.toMatrix' (n := X) (R₁ := ℝ) Q

noncomputable
abbrev l_Bilin := matrixAssociatedToForm Q

/-
We note that Q(1x, 1y) = l (x, y) for all x, y ∈ X
-/
example (x y : X) :
    Q (𝟙_x) (𝟙_y) = (l_Bilin Q) x y := by rfl

/-
and Q(1x, 1) =  Í  z∈X l (x, z) where 1 denotes the function which is 1 on all vertices
-/
example (x : X) :
    Q (𝟙_x) 1 = ∑ z, (l_Bilin Q) x z := by
  unfold l_Bilin
  unfold matrixAssociatedToForm
  simp only [BilinForm.toMatrix'_apply, ← map_sum, Finset.univ_sum_single]
  rfl

/-
In particular, Q is symmetric if and only if the associated matrix l is symmetric.
-/
-- Note: this would be a good mathlib lemma
example : Q.IsSymm ↔ (l_Bilin Q).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff, LinearMap.isSymm_def, Matrix.IsSymm.ext_iff]
  unfold l_Bilin
  unfold matrixAssociatedToForm
  simp only [Real.ringHom_apply, BilinForm.toMatrix'_apply]
  constructor
  · intro h i j
    exact Real.ext_cauchy (congrArg Real.cauchy (h (𝟙_j) (𝟙_i)))
  intro h f g
  -- decompose f and g into basis vectors, then use linearity
  have : f = stdBasis.equivFun.symm f := by rfl
  rw [this, Module.Basis.equivFun_symm_apply stdBasis f]
  have : g = stdBasis.equivFun.symm g := by rfl
  rw [this, Module.Basis.equivFun_symm_apply stdBasis g]
  unfold stdBasis
  simp only [Pi.basisFun_apply, map_sum, map_smul, LinearMap.coe_sum, coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  ring_nf
  simp only [h]
  ring_nf

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

end GraphOver
