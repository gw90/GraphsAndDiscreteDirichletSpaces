import GraphsAndDiscreteDirichletSpaces.Section011'

variable {X R M : Type*} [Fintype X] [DecidableEq X] [CommSemiring R] [AddCommMonoid M] [Module R M]

open LinearMap Module

lemma bilinForm_symm_iff_toMatrix_symm (Q : LinearMap.BilinForm R M) (b : Basis X R M) :
    Q.IsSymm ↔ (LinearMap.BilinForm.toMatrix b Q).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff, LinearMap.isSymm_def, Matrix.IsSymm.ext_iff]
  simp only [RingHom.id_apply, LinearMap.BilinForm.toMatrix_apply]
  constructor
  · simp_all
  intro h f g
  rw [← b.sum_repr f, ← b.sum_repr g]
  rw [map_sum, map_sum, map_sum, map_sum]
  simp only [coe_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp only [map_smul, smul_apply, smul_eq_mul, h]
  congr
  ext x
  congr
  ext y
  ring

lemma bilinForm_symm_iff_toMatrix'_symm (Q : LinearMap.BilinForm ℝ (X → ℝ)) :
    Q.IsSymm ↔ (BilinForm.toMatrix' (n := X) (R₁ := ℝ) Q).IsSymm :=
  bilinForm_symm_iff_toMatrix_symm Q (Pi.basisFun (η := X) (R := ℝ))
