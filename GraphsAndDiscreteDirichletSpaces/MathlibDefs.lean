import Mathlib

open NNReal

@[ext]
structure WeightedGraph (X : Type*) extends SimpleGraph X where
  edgeWeight : X → X → ℝ≥0
  edgeWeight_symm : IsSymmOp edgeWeight
  edgeDef (u v : X) : Adj u v ↔ 0 < edgeWeight u v -- make a lemma for the contrapositive of this

variable {X : Type*}

@[simp]
lemma WeightedGraph.no_loop {x : X} (G : WeightedGraph X) : G.edgeWeight x x = 0 := by
  linarith [not_imp_not.mpr (G.edgeDef x x).mpr (G.irrefl (v := x))]

lemma WeightedGraph.edgeWeight_symm_apply (G : WeightedGraph X) (y z : X) :
    G.edgeWeight y z = G.edgeWeight z y := G.edgeWeight_symm.symm_op y z

@[ext]
structure WeightedGraphWithKillingTerm (X : Type*) extends WeightedGraph X where
  killingTerm : X → ℝ≥0

-- Define predicates to recover simple graphs and produce them
-- Do everything for WeightedGraph, then include special cases

variable (G : WeightedGraphWithKillingTerm X)

-- Maybe let this be a special corollary that uniquely includes decidability hypotheses
-- #check fun x y ↦ if G.Adj x y then 1 else 0

--instance {x y : X} : Decidable (G.Adj x y) := by infer_instance

structure StandardWeights (G : WeightedGraphWithKillingTerm X) : Prop where
  edgeWeight_Adj_iff : G.Adj x y ↔ G.edgeWeight x y = 1
  edgeWeight_NotAdj_iff : ¬ G.Adj x y ↔ G.edgeWeight x y = 0
  killingTerm_zero : G.killingTerm = 0

@[simp]
lemma standardWeights_edgeWeight_neq_zero_iff_eq_one (h : StandardWeights G) :
    G.edgeWeight x y ≠ 0 ↔ G.Adj x y := by
  contrapose
  exact h.edgeWeight_NotAdj_iff.symm

@[simp]
lemma standardWeights_edgeWeight_neq_one_iff_eq_zero (h : StandardWeights G) :
    G.edgeWeight x y ≠ 1 ↔ ¬ G.Adj x y := by
  contrapose
  exact h.edgeWeight_Adj_iff.symm

-- include way to produce graph with standardweights from simpleGraph

-- Example 0.2 (Graphs with standard weights)
lemma standardWeightEdgeSet (h : StandardWeights G) :
    s(v, w) ∈ G.edgeSet ↔ G.edgeWeight v w = 1 := (G.mem_edgeSet).trans h.edgeWeight_Adj_iff

variable [Fintype X]

def WeightedGraphWithKillingTerm.degree (x : X) : ℝ≥0 :=
  ∑ y, (G.edgeWeight x y) + (G.killingTerm x)

noncomputable
instance : Fintype ↑(G.neighborSet x) := Fintype.ofFinite (G.neighborSet x)

lemma degreeWithStandardWeights (h : StandardWeights G) (x : X) :
    G.degree x = G.toSimpleGraph.degree x := by
  simp only [WeightedGraphWithKillingTerm.degree, h.killingTerm_zero, Pi.zero_apply, add_zero,
    ← G.card_neighborFinset_eq_degree, G.neighborFinset_def, SimpleGraph.neighborSet,
    Finset.cast_card]
  rw [← Finset.sum_filter_ne_zero]
  congr! with y hy
  · grind [standardWeights_edgeWeight_neq_zero_iff_eq_one]
  exact h.edgeWeight_Adj_iff.mp ((G.toSimpleGraph.mem_neighborFinset x y).mp hy)


-- Definiton 0.5
@[simp]
noncomputable
def WeightedGraphWithKillingTerm.associatedFormFun (f g : X → ℝ) :=
  (1/2) * ∑ x, ∑ y, (G.edgeWeight x y) * (f x - f y) * (g x - g y) +
    ∑ x, (G.killingTerm x) * f x * g x

open Finset

instance WeightedGraphWithKillingTerm.associatedFormBilinearMap :
    IsBilinearMap (R := ℝ) G.associatedFormFun where
  add_left f g h := by
    apply sub_eq_zero.mp
    simp [sub_add_eq_sub_sub]
    ring_nf
    simp [sum_add_distrib]
    ring
  smul_left c f g := by
    unfold WeightedGraphWithKillingTerm.associatedFormFun
    field_simp
    ring_nf
    simp [sum_add_distrib]
    ring_nf
    simp [mul_sum]
    ring_nf
  add_right f g h := by
    apply sub_eq_zero.mp
    simp [sub_add_eq_sub_sub]
    ring_nf
    simp [sum_add_distrib]
    ring
  smul_right c f g := by
    unfold WeightedGraphWithKillingTerm.associatedFormFun
    ring_nf
    simp [sum_add_distrib]
    ring_nf
    simp [mul_sum]
    ring_nf
    apply sub_eq_zero.mp
    ring_nf

noncomputable
def WeightedGraphWithKillingTerm.associatedForm := G.associatedFormBilinearMap.toLinearMap

lemma WeightedGraphWithKillingTerm.associatedForm_apply {f g} : G.associatedForm f g =
  (1/2) * ∑ x, ∑ y, (G.edgeWeight x y) * (f x - f y) * (g x - g y) +
    ∑ x, (G.killingTerm x) * f x * g x := by rfl
