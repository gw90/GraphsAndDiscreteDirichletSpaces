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
abbrev L_Mat (M : Matrix X X ℝ) := opInducedByMatrix M

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

/-
In particular, when Q is symmetric, we get  Q( f + g) = Q( f ) + 2Q( f , g) + Q(g).
-/
example {f g : X → ℝ} (Q : LinearMap.BilinForm ℝ (X → ℝ)) (h : Q.IsSymm) :
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
def matrixAssociatedToForm (Q : LinearMap.BilinForm ℝ (X → ℝ)) :=
  BilinForm.toMatrix' (n := X) (R₁ := ℝ) Q

noncomputable
abbrev l_Bilin (Q : LinearMap.BilinForm ℝ (X → ℝ)) := matrixAssociatedToForm Q

/-
We note that Q(1x, 1y) = l (x, y) for all x, y ∈ X
-/
example (Q : LinearMap.BilinForm ℝ (X → ℝ)) (x y : X) :
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
-- Upstreamed to Mathlib as
--#check LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm

example (Q : LinearMap.BilinForm ℝ (X → ℝ)) : Q.IsSymm ↔ (l_Bilin Q).IsSymm := by
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

/-Equation on page 9-/
-- To-do: upstream as much as possible
variable (l : Matrix X X ℝ) (f g : X → ℝ)

noncomputable
abbrev Q_Mat := formInducedByMatrix l

example : (Q_Mat l) f g = ∑ (x : X), ∑ (y : X), (l x y) * f x * g y := by
  simp only [formInducedByMatrix, Matrix.toBilin'_apply]
  grind

open scoped Matrix

example (h : l.IsSymm) :
    ∑ (x : X), ∑ (y : X), (l x y) * f x * g y
    = ∑ (y : X), ((L_Mat l) f) y * g y := by
  unfold L_Mat
  unfold opInducedByMatrix
  simp only [toMatrix_symm]
  unfold stdBasis
  simp only [Matrix.toLin_apply, Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : f = stdBasis.equivFun.symm f := by rfl
  rw [this, Module.Basis.equivFun_symm_apply stdBasis f]
  simp only [stdBasis, Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum,
    map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul]
  have (x : X) : (((Pi.basisFun ℝ X).repr (𝟙_x)) : X → ℝ) = 𝟙_x := by
    simp_all only [Module.Basis.equivFun_symm_apply]
    rfl
  simp only [this]
  rw [Finset.sum_comm]
  congr
  ext y
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Matrix.mulVec_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_smul,
    Matrix.transpose_apply]
  simp only [mul_comm]
  rw [← Finset.mul_sum]
  congr
  ext x
  rw [Matrix.IsSymm.apply h y x]

example (h : l.IsSymm) :
    ∑ (y : X), ((L_Mat l) f) y * g y = ∑ (x : X), f x * (L_Mat l g) x:= by
  unfold L_Mat
  unfold opInducedByMatrix
  unfold stdBasis
  simp only [toMatrix_eq_toMatrix', toMatrix'_symm, Matrix.toLin'_apply]
  have : f = stdBasis.equivFun.symm f := by rfl
  rw [this, Module.Basis.equivFun_symm_apply stdBasis f]
  have : g = stdBasis.equivFun.symm g := by rfl
  rw [this, Module.Basis.equivFun_symm_apply stdBasis g]
  unfold stdBasis
  simp only [Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.mulVec_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.op_sum,
    MulOpposite.op_mul, Matrix.transpose_apply, MulOpposite.smul_eq_mul_unop, Finset.unop_sum,
    MulOpposite.unop_mul, MulOpposite.unop_op]
  simp only [Finset.mul_sum]
  nth_rw 2 [Finset.sum_comm]
  rw [Finset.sum_comm_cycle]
  nth_rw 1 [Finset.sum_comm]
  congr
  ext a
  congr
  ext b
  simp only [mul_comm, Finset.mul_sum]
  congr
  ext y
  rw [Matrix.IsSymm.apply h b y]
  ring_nf

-- end 4-part eqn from p. 9

noncomputable
abbrev L_Bilin (Q : LinearMap.BilinForm ℝ (X → ℝ)) :=
  (LinearMap.toMatrix stdBasis stdBasis).symm (Q.toMatrix' (n := X) (R₁ := ℝ))

noncomputable
abbrev Q_Op (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := (L.toMatrix stdBasis stdBasis).toBilin'

-- Notational conventions for inducing matrices, operators, and bilinear forms from one another
#check l_Op
#check l_Bilin
#check L_Mat
#check L_Bilin
#check Q_Op
#check Q_Mat

-- Definiton 0.5
@[simp]
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

@[simp]
lemma associatedForm_apply {f g} : G.associatedForm f g = G.associatedFormFun f g := by rfl

-- form associated to graph G, aka "energy form"
noncomputable
abbrev Q_bc := G.associatedForm

#check G.Q_bc

-- resume at p. 10
--@[simp] -- re-work proofs to use singleton membership instead of equality
/-lemma sum_with_cond_eq {M : Type*} [AddCommMonoid M] (X : Type*) [Fintype X] (a : X) (f : X → M) :
    ∑ (x : X) with x = a, f x = f a := calc
  ∑ x with x = a, f x = ∑ x ∈ {a}, f x := by congr; grind [Set.set_compr_eq_eq_singleton]
  _ = f a := sum_singleton (f ·) a-/

@[simp]
lemma no_loop (x : X) : G.b x x = 0 := by linarith [not_imp_not.mpr (G.edgeDef x x).mpr (G.irrefl (v := x))]

lemma b_symm (y z : X) : G.b y z = G.b z y := by simp [G.edgeWeight_symm.symm_op]

@[simp]
lemma sum_killingTerm_weight_sq_eq_support_weighted :
    ∑ i, ↑(G.c i) * (𝟙_x : X → ℝ) i ^ 2 = ↑(G.c x) * (𝟙_x : X → ℝ) x ^ 2 := by
  simp [(Fintype.sum_subset (f := fun (y : X) ↦ G.c y * (𝟙_x : X → ℝ) y ^ 2)
      (s := {x}) (by grind)).symm]
-- maybe the lemma above and the lemma below can be refactored to share another lemma in common
-- to shorten the proofs
@[simp]
lemma neq_basis_vecs_imp_sum_weighted_killingTerm_eq_zero (x y : X) (h : x ≠ y) :
    ∑ z, ↑(G.c z) * (𝟙_x : X → ℝ) z * (𝟙_y : X → ℝ) z = 0 := by
  have : (𝟙_y : X → ℝ) x = 0 := by grind
  rw [Finset.sum_eq_sum_diff_singleton_add (i := x) (by simp), this, mul_zero, add_zero,
    ← Finset.sum_const_zero (s := (_ : Finset X))]
  congr! with y h
  grind

-- We note by direct calculation that
example : G.Q_bc (𝟙_x) (𝟙_x) = G.deg x := by
  simp only [Q_bc, deg, associatedForm_apply, associatedFormFun, one_div, NNReal.coe_add,
    NNReal.coe_sum]
  field_simp
  simp only [sum_killingTerm_weight_sq_eq_support_weighted, Pi.single_eq_same, one_pow, mul_one]
  rw [mul_add]
  congr
  rw [Finset.sum_eq_sum_diff_singleton_add (i := x) (by simp)]
  have : ∑ x_1, ↑((G.b x x_1) : ℝ) * (1 - (𝟙_x : X → ℝ) x_1) ^ 2 = ∑ x_1, ↑(G.b x x_1 : ℝ) := by
    nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := x) (by simp)]
    rw [Finset.sum_eq_sum_diff_singleton_add (i := x) (by simp)]
    congr
    · ext y
      by_cases h : y = x
      · simp_all
      simp_all
    simp_all
  simp only [Pi.single_eq_same, this, two_mul]
  congr 1
  nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := x) (by simp)]
  simp only [no_loop, coe_zero, add_zero]
  congr! with y h
  have : y ≠ x := by grind
  rw [Finset.sum_eq_sum_diff_singleton_add (i := x) (by simp)]
  simp only [ne_eq, this, not_false_eq_true, Pi.single_eq_of_ne, zero_sub, even_two, Even.neg_pow,
    Pi.single_eq_same, one_pow, mul_one, G.b_symm]
  apply add_eq_right.mpr
  rw [← Finset.sum_const_zero]
  congr! with z h'
  grind

-- And
example (x y : X) (h : x ≠ y) : G.Q_bc (𝟙_x) (𝟙_y) = - G.b x y := by
  simp only [associatedForm_apply, associatedFormFun, one_div]
  field_simp
  rw [neq_basis_vecs_imp_sum_weighted_killingTerm_eq_zero (h := h), mul_zero, add_zero]
  nth_rw 1 [Finset.sum_eq_sum_diff_singleton_add (i := x) (by simp)]
  nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := y) (by simp)]
  have : ↑(G.b x y) * ((𝟙_x : X → ℝ) x - (𝟙_x : X → ℝ) y) * ((𝟙_y : X → ℝ) x - (𝟙_y : X → ℝ) y)
    = - ↑(G.b x y) := by grind
  rw [this]
  have : ∑ x_1 ∈ univ \ {y}, ↑(G.b x x_1) * ((𝟙_x : X → ℝ) x - (𝟙_x : X → ℝ) x_1) * ((𝟙_y : X → ℝ) x - (𝟙_y : X → ℝ) x_1) = 0 := by
    suffices ∑ x_1 ∈ univ \ {y}, ↑(G.b x x_1) * ((𝟙_x : X → ℝ) x - (𝟙_x : X → ℝ) x_1) * ((𝟙_y : X → ℝ) x - (𝟙_y : X → ℝ) x_1) = ∑ x_1 ∈ univ \ {y}, 0 by
      simp_all only [Finset.sum_const_zero]
    congr! with z h2
    grind
  rw [this, zero_add]
  have : ∑ x_1 ∈ univ \ {x}, ∑ x_2, ↑(G.b x_1 x_2) * ((𝟙_x : X → ℝ) x_1 - (𝟙_x : X → ℝ) x_2) *
    ((𝟙_y : X → ℝ) x_1 - (𝟙_y : X → ℝ) x_2)
   = ∑ x_1 ∈ univ \ {x},
    ((∑ x_2 ∈ univ \ {x}, ↑(G.b x_1 x_2) * ((𝟙_x : X → ℝ) x_1 - (𝟙_x : X → ℝ) x_2) * ((𝟙_y : X → ℝ) x_1 - (𝟙_y : X → ℝ) x_2)) +
      ↑(G.b x_1 x) * ((𝟙_x : X → ℝ) x_1 - (𝟙_x : X → ℝ) x) * ((𝟙_y : X → ℝ) x_1 - (𝟙_y : X → ℝ) x)) := by
    congr
    ext z
    simp
  rw [this, Finset.sum_add_distrib]
  have : ∑ x_1 ∈ univ \ {x}, ∑ x_2 ∈ univ \ {x}, ↑(G.b x_1 x_2) * ((𝟙_x : X → ℝ) x_1 -
    (𝟙_x : X → ℝ) x_2) * ((𝟙_y : X → ℝ) x_1 - (𝟙_y : X → ℝ) x_2)
      = 0 := by
    suffices ∑ x_1 ∈ univ \ {x}, ∑ x_2 ∈ univ \ {x}, ↑(G.b x_1 x_2) * ((𝟙_x : X → ℝ) x_1 -
    (𝟙_x : X → ℝ) x_2) * ((𝟙_y : X → ℝ) x_1 - (𝟙_y : X → ℝ) x_2) = ∑ x_1 ∈ univ \ {x}, ∑ x_2 ∈ univ \ {x}, 0 by
      simp only [Finset.sum_const_zero] at this
      exact this
    congr! with z h2
    grind
  rw [this, zero_add, Finset.sum_eq_sum_diff_singleton_add (i := y) (by grind)]
  have : ↑(G.b y x) * ((𝟙_x : X → ℝ) y - (𝟙_x : X → ℝ) x) * ((𝟙_y : X → ℝ) y - (𝟙_y : X → ℝ) x)
    = - ↑(G.b y x) := by grind
  rw [this]
  have : ∑ x_1 ∈ (univ \ {x}) \ {y}, ↑(G.b x_1 x) * ((𝟙_x : X → ℝ) x_1 -
      (𝟙_x : X → ℝ) x) * ((𝟙_y : X → ℝ) x_1 - (𝟙_y : X → ℝ) x) = 0 := by
    suffices ∑ x_1 ∈ (univ \ {x}) \ {y}, ↑(G.b x_1 x) * ((𝟙_x : X → ℝ) x_1 -
      (𝟙_x : X → ℝ) x) * ((𝟙_y : X → ℝ) x_1 - (𝟙_y : X → ℝ) x) = ∑ x_1 ∈ (univ \ {x}) \ {y}, 0 by
      simp only [Finset.sum_const_zero] at this
      exact this
    congr! with z h2
    grind
  rw [this, G.b_symm]
  ring

-- Furthermore
example : G.Q_bc (𝟙_x) 1 = G.c x := by
  unfold Q_bc
  simp only [associatedForm_apply, associatedFormFun, one_div, Pi.one_apply, sub_self, mul_zero,
    sum_const_zero, mul_one, zero_add]
  rw [Finset.sum_eq_sum_diff_singleton_add (i := x) (h := by grind)]
  simp only [Pi.single_eq_same, mul_one]
  have : ∑ x_1 ∈ univ \ {x}, ↑(G.c x_1) * (𝟙_x : X → ℝ) x_1 = 0 := by
    suffices ∑ x_1 ∈ univ \ {x}, ↑(G.c x_1) * (𝟙_x : X → ℝ) x_1
           = ∑ x_1 ∈ (univ \ {x}), 0 by
      simp only [Finset.sum_const_zero] at this
      exact this
    congr! with z h2
    grind
  simp [this]

#check G.Q_bc
-- Clearly
example : G.Q_bc.IsSymm := by
  simp only [isSymm_def, associatedForm_apply, associatedFormFun, one_div, Real.ringHom_apply]
  intro f g
  congr 1; swap
  · grind
  grind

-- more conditions will be added later to get regular dirichlet forms

-- Now we define a predicate for Dirichlet forms
structure DirichletProp (Q : (X → ℝ) →ₗ[ℝ] (X → ℝ) →ₗ[ℝ] ℝ) : Prop where
  protected eq : (∀ (f g : X → ℝ), (∀ (x y : X), |f x - f y| ≤ |g x - g y|)
    → (∀ (x : X), (|f x| ≤ |g x|)) -- is this really what they meant?
    → Q f f ≤ Q g g)

#check DirichletProp G.Q_bc

--maybe define this using derivatives or some sobolev/function properties
-- is this like regularity or something?
-- could find a way to express this with Lipschitz continuity, but it's probably not worth it

theorem DirichletProp_def (Q : (X → ℝ) →ₗ[ℝ] (X → ℝ) →ₗ[ℝ] ℝ) : DirichletProp Q ↔
  (∀ (f g : X → ℝ), (∀ (x y : X), |f x - f y| ≤ |g x - g y|) → (∀ (x : X), (|f x| ≤ |g x|)) → Q f f ≤ Q g g) := by
  constructor
  · exact fun a f g a_1 a_2 ↦ a.eq f g a_1 a_2
  exact fun a ↦ { eq := a }

example : DirichletProp G.Q_bc := by
  simp only [DirichletProp_def]
  intro f g h1 h2
  unfold Q_bc
  simp [associatedForm_apply, associatedFormFun]
  field_simp
  gcongr 1
  · gcongr 3 with a ha b hb
    rw [← sq_abs]
    nth_rw 2 [← sq_abs]
    gcongr 1
    simp [h1]
  gcongr 3 with x hx
  rw [← sq_abs]
  nth_rw 2 [← sq_abs]
  gcongr 1
  simp [h2] -- this is where I use the questionable norm thing

structure DirichletForm (Q : (X → ℝ) →ₗ[ℝ] (X → ℝ) →ₗ[ℝ] ℝ) : Prop where
  protected dirichletProp : DirichletProp Q
  protected symm : Q.IsSymm

instance : DirichletForm G.Q_bc where -- the proofs below are copied from example above
  dirichletProp := by
    simp only [DirichletProp_def]
    intro f g h1 h2
    unfold Q_bc
    simp [associatedForm_apply, associatedFormFun]
    field_simp
    gcongr 1
    · gcongr 3 with a ha b hb
      rw [← sq_abs]
      nth_rw 2 [← sq_abs]
      gcongr 1
      simp [h1]
    gcongr 3 with x hx
    rw [← sq_abs]
    nth_rw 2 [← sq_abs]
    gcongr 1
    simp [h2]
  symm := by
    simp only [isSymm_def, associatedForm_apply, associatedFormFun, one_div, Real.ringHom_apply]
    intro f g
    congr 1; swap
    · grind
    grind

-- Definition 0.6 (Laplacian)
def Laplacian (f : X → ℝ) : X → ℝ :=
  fun x ↦ ∑ y, G.b x y * (f x - f y) + G.c x * f x

lemma Laplacian_apply : G.Laplacian f x = ∑ y, G.b x y * (f x - f y) + G.c x * f x := by rfl

#check G.Laplacian

abbrev L_bc := G.Laplacian

#check Finite.Set.finite_range f
#check Finset.max
#check Set.finite_range f
#check Finset.image f
#check Set.Finite.toFinset (Set.finite_range f)
#check Set.Finite.toFinset_range f (Set.finite_range f)
#check Finset.sup
#check Finset.max' (Set.Finite.toFinset (Set.finite_range f))
-- I'm dying here. I think I have to specify X nonempty and do a bunch of nonsense
/-
lemma Laplacian_max_principle
  (max_nonneg : (0 : ℝ) ≤ Finset.max' (Set.Finite.toFinset (Set.finite_range f)))
  (at_max : f x = Finset.max (Set.Finite.toFinset (Set.finite_range f))) :
    0 ≤ G.L_bc f x := by
  unfold L_bc
  unfold Laplacian

  have (y : X) : f y ≤ sSup (Set.range f) := by sorry
  have (y : X) : 0 ≤ (sSup (Set.range f) - f y) := by sorry -- I should be able to exact? this
  sorry
-/

end GraphOver
