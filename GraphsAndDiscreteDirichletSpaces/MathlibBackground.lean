import Mathlib


open NNReal

open LinearMap

set_option linter.unusedFintypeInType false

variable {X : Type*} (x : X) [Fintype X]

noncomputable
instance : DecidableEq X := Classical.typeDecidableEq X

-- these will each need to be added in a standard basis section in the
-- appropriate files

-- Operators
/-A natural basis for C (X) consists of characteristic functions 1x
which take the value 1 at x and are 0 otherwise.-/
noncomputable
def stdBasis := (Pi.basisFun (η := X) (R := ℝ))

noncomputable
abbrev basisFunc (y : X) : X → ℝ := Pi.single y 1

notation "𝟙_" y:max => basisFunc y

noncomputable
def matrixAssociatedToOp (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) :=
  L.toMatrix stdBasis stdBasis

-- Matrix associated to L
noncomputable
abbrev l_Op (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := matrixAssociatedToOp L

noncomputable
def opInducedByMatrix (M : Matrix X X ℝ) := M.toLin stdBasis stdBasis

#check Matrix.toLin

-- Operator induced by Matrix M (or what should really be l)
noncomputable
abbrev L_Mat (M : Matrix X X ℝ) := opInducedByMatrix M

/-If Q is a form, then there exists a unique function l : X × X −→ R with
Q( f , g) =  ∑︁  x,y∈X  l(x, y) f (x)g(y)
for all f , g ∈ C (X). We call Q the form induced by the matrix l-/
noncomputable
def formInducedByMatrix (M : Matrix X X ℝ) : (X → ℝ) →ₗ[ℝ] (X → ℝ) →ₗ[ℝ] ℝ :=
  (Matrix.toBilin' M)

/-and l the matrix associated to Q-/
noncomputable
def matrixAssociatedToForm (Q : LinearMap.BilinForm ℝ (X → ℝ)) :=
  Q.toMatrix' (n := X) (R₁ := ℝ)

noncomputable
abbrev l_Bilin (Q : LinearMap.BilinForm ℝ (X → ℝ)) := matrixAssociatedToForm Q

noncomputable
abbrev Q_Mat (l : Matrix X X ℝ) := formInducedByMatrix l

noncomputable
abbrev L_Bilin (Q : LinearMap.BilinForm ℝ (X → ℝ)) :=
  (LinearMap.toMatrix stdBasis stdBasis).symm (Q.toMatrix' (n := X) (R₁ := ℝ))

noncomputable
abbrev Q_Op (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := (L.toMatrix stdBasis stdBasis).toBilin'

variable (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) -- L is linear map
variable (Q : LinearMap.BilinForm ℝ (X → ℝ)) -- Q is bilinear form
variable (M : Matrix X X ℝ) -- M is matrix
#check Q
-- Notational conventions for inducing matrices, operators, and bilinear forms from one another
#check l_Op
#check L.toMatrix stdBasis stdBasis

lemma LinearMap.toMatrix_standardBasis_def (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (f : X → ℝ) :
  (L f) x = ∑ y, (L.toMatrix stdBasis stdBasis) x y * f y := by
  have : f = stdBasis.equivFun.symm f := by rfl
  nth_rw 1 [this, Module.Basis.equivFun_symm_apply stdBasis f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr with y
  rw [mul_comm]
  congr

lemma LinearMap.toMatrix_standardBasis_entry_def (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (x y : X) :
    (L.toMatrix stdBasis stdBasis) x y = L (𝟙_y) x := by
  simp [stdBasis, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_apply]

#check l_Bilin
#check Q.toMatrix' (n := X) (R₁ := ℝ)

#check L_Mat
#check M.toLin stdBasis stdBasis

variable (f g : X → ℝ) (l : Matrix X X ℝ)
lemma GreensFormula_basic_left (h : l.IsSymm) :
    ∑ (x : X), ∑ (y : X), (l x y) * f x * g y
    = ∑ (y : X), ((l.toLin stdBasis stdBasis) f) y * g y := by
  simp only [stdBasis, Matrix.toLin_apply,
    Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : f = stdBasis.equivFun.symm f := by rfl
  rw [this, Module.Basis.equivFun_symm_apply stdBasis f]
  have (x : X) : (((Pi.basisFun ℝ X).repr (𝟙_x)) : X → ℝ) = 𝟙_x := by
    simp_all only [Module.Basis.equivFun_symm_apply]; rfl
  simp only [stdBasis, Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum,
    map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, this]
  rw [Finset.sum_comm]
  congr with y
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Matrix.mulVec_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_smul,
    Matrix.transpose_apply] -- the next line cannot be merged into this for some reaon
  simp only [mul_comm, ← Finset.mul_sum]
  congr with x
  rw [Matrix.IsSymm.apply h y x]

lemma GreensFormula_basic_right :
    ∑ (x : X), ∑ (y : X), (l x y) * f x * g y
    = ∑ (x : X), f x * (l.toLin stdBasis stdBasis g) x := by
  conv => congr; congr; rfl; ext z; congr; rfl; ext y; rw [mul_assoc, mul_comm (a := f z),
    ← mul_assoc]
  simp only [stdBasis, Matrix.toLin_apply,
    Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : g = stdBasis.equivFun.symm g := by rfl
  rw [this, Module.Basis.equivFun_symm_apply stdBasis g]
  have (x : X) : (((Pi.basisFun ℝ X).repr (𝟙_x)) : X → ℝ) = 𝟙_x := by
    simp_all only [Module.Basis.equivFun_symm_apply]; rfl
  simp only [stdBasis, Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum,
    map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, this]
  congr with y
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Matrix.mulVec_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_smul,
    Matrix.transpose_apply] -- the next line cannot be merged into this for some reaon
  simp only [mul_comm, ← Finset.mul_sum]

lemma GreensFormula_inter (h : l.IsSymm) : ∑ (y : X), ((l.toLin stdBasis stdBasis) f) y * g y =
    ∑ (x : X), f x * (l.toLin stdBasis stdBasis g) x :=
  (GreensFormula_basic_left f g l h).symm.trans (GreensFormula_basic_right f g l)

#check L_Bilin
#check (LinearMap.toMatrix stdBasis stdBasis).symm (Q.toMatrix' (n := X) (R₁ := ℝ)) -- I'll have to define this

example (x y : X) :
    Q (𝟙_x) (𝟙_y) = (l_Bilin Q) x y := by rfl

example (x : X) :
    Q (𝟙_x) 1 = ∑ z, (l_Bilin Q) x z := by
  simp [l_Bilin, matrixAssociatedToForm, BilinForm.toMatrix'_apply, ← map_sum,
    Finset.univ_sum_single]
  rfl

#check Q_Op
#check (L.toMatrix stdBasis stdBasis).toBilin' -- I'll probably want to define this too

#check Q_Mat
#check M.toBilin'

example (l : Matrix X X ℝ) (f g : X → ℝ) : (Q_Mat l) f g = ∑ (x : X), ∑ (y : X), (l x y) * f x * g y := by
  simp only [formInducedByMatrix, Matrix.toBilin'_apply]
  grind
