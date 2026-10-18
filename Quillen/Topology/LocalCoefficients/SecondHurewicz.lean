/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.LocalCoefficients.MarkedSphericalTwoCycle
public import Quillen.Topology.LocalCoefficients.Prism
public import Quillen.Topology.LocalCoefficients.HomotopyInvariance
public import Quillen.Topology.HomotopyGroups.SphericalHomotopyAddition
public import Quillen.Topology.HomotopyGroups.SphericalSimplexMap
public import Quillen.Topology.HomotopyGroups.PathTransportFundamentalGroup
public import Quillen.Topology.Realization.SimplexFaceGluing
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The original marked second Hurewicz homomorphism

A based spherical triangle is sent to its literal sphere-minus-constant
cycle in the original unnormalized integral singular complex. The explicit
stick-breaking quotient identifies this representative with the original
cubical Pi-two class. A three-prism boundary proves relative homotopy
invariance. A concrete barycentric retraction fills the three-face horn;
the accepted signed tetrahedral homotopy formula and the original chain
differential prove additivity with the same increasing-vertex orientation.

The resulting homomorphism is natural for the original based Pi-two maps
and original integral homology maps, and retains every original basepoint
path. No simple-connectedness or homology comparison law is assumed.
The separate injectivity leaf applies the finite-cap descent theorem when
the target is simply connected.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Convexity Topology
open scoped Simplicial Topology unitInterval

namespace Quillen.LocalCoefficients.SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y] {y : Y}

/-- The original unnormalized singular complex with its lifted integral coefficient object. -/
abbrev Chains (Y : Type u) [TopologicalSpace Y] :=
  singularChainComplex (constant Y integralCoefficientModule.{u})

/-- The original integral generator with coefficient exactly the lifted integer one. -/
def simplexChain {n : ℕ} (τ : SingularSimplex Y ⦋n⦌) : (Chains Y).X n :=
  chainInclusion (constant Y integralCoefficientModule.{u}) τ (ULift.up 1)

/-- The original differential of an integral tetrahedron, with all four face signs. -/
theorem tetrahedron_boundary (τ : SingularSimplex Y ⦋3⦌) :
    (Chains Y).d 3 2 (simplexChain τ) =
      simplexChain (restrictSimplex τ (SimplexCategory.δ 0)) -
      simplexChain (restrictSimplex τ (SimplexCategory.δ 1)) +
      simplexChain (restrictSimplex τ (SimplexCategory.δ 2)) -
      simplexChain (restrictSimplex τ (SimplexCategory.δ 3)) := by
  let ev : (integralCoefficientModule.{u} ⟶ (Chains Y).X 2) →+ (Chains Y).X 2 := {
    toFun f := f (ULift.up 1)
    map_zero' := rfl
    map_add' _ _ := rfl }
  have h := congrArg ev (chainInclusion_d (constant Y integralCoefficientModule.{u}) τ)
  change _ = ev _ at h
  simp only [Nat.reduceAdd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, Int.reduceNeg, integralRestrictionTransport,
    Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_smul,
    Fin.val_succ, zero_add, pow_one, Fin.succ_zero_eq_one, neg_smul, add_assoc, even_two,
    Even.neg_pow, one_pow, Fin.succ_one_eq_two, Finset.univ_unique, Fin.default_eq_zero,
    Fin.val_eq_zero, Int.reducePow, Finset.sum_neg_distrib, Finset.sum_singleton, Fin.reduceSucc,
    ModuleCat.hom_add, ModuleCat.hom_id, LinearMap.comp_id, ModuleCat.hom_neg,
    LinearMap.add_apply, LinearMap.neg_apply, ev] at h
  change ((Chains Y).d 3 2).hom
      ((chainInclusion (constant Y integralCoefficientModule.{u}) τ).hom (ULift.up 1)) = _
  convert h using 1
  change _ = simplexChain (restrictSimplex τ (SimplexCategory.δ 0)) +
    (-simplexChain (restrictSimplex τ (SimplexCategory.δ 1)) +
      (simplexChain (restrictSimplex τ (SimplexCategory.δ 2)) +
        -simplexChain (restrictSimplex τ (SimplexCategory.δ 3))))
  abel

/-- The original marked homology class of a spherical triangle. -/
def sphericalClass (a : SphericalSimplex Y y 2) :
    homology (constant Y integralCoefficientModule) 2 :=
  (Chains Y).homologyπ 2 (sphericalTwoCycle a)

/-- An actual differential equality gives equality in the original homology object. -/
theorem homology_eq_of_boundary (a b : (Chains Y).cycles 2) (c : (Chains Y).X 3)
    (hc : (Chains Y).d 3 2 c = (Chains Y).iCycles 2 a - (Chains Y).iCycles 2 b) :
    (Chains Y).homologyπ 2 a = (Chains Y).homologyπ 2 b := by
  have hz : a - b = (Chains Y).toCycles 3 2 c := by
    apply (ModuleCat.mono_iff_injective ((Chains Y).iCycles 2)).mp inferInstance
    rw [map_sub]
    exact hc.symm.trans
      (ConcreteCategory.congr_hom ((Chains Y).toCycles_i 3 2) c).symm
  apply sub_eq_zero.mp
  rw [← map_sub, hz]
  exact ConcreteCategory.congr_hom ((Chains Y).toCycles_comp_homologyπ 3 2) c

/-- The actual constant spherical triangle gives zero under the marked chain convention. -/
theorem sphericalClass_const :
    sphericalClass (SphericalSimplex.const : SphericalSimplex Y y 2) = 0 := by
  have hz : sphericalTwoCycle (SphericalSimplex.const : SphericalSimplex Y y 2) = 0 := by
    apply (ModuleCat.mono_iff_injective ((Chains Y).iCycles 2)).mp inferInstance
    rw [map_zero, iCycles_sphericalTwoCycle, sphericalTwoChain]
    exact sub_self _
  rw [sphericalClass, hz, map_zero]

end Quillen.LocalCoefficients.SecondHurewicz

namespace Quillen.LocalCoefficients.SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y] {y : Y}
  {a b : SphericalSimplex Y y 2}
  (H : a.val.HomotopyRel b.val (simplexBoundary 2))

/-- The original triangle with only its universe lifted. -/
def triangleUp : SingularSimplex (ULift.{u} (StdSimplex ℝ (Fin 3))) ⦋2⦌ :=
  ⟨ULift.up, continuous_uliftUp⟩

/-- The whole relative homotopy with its simplex source lifted
to the coefficient universe. -/
def liftedHomotopy :
    (a.val.comp ⟨ULift.down, continuous_uliftDown⟩).Homotopy
      (b.val.comp ⟨ULift.down, continuous_uliftDown⟩) :=
  H.toHomotopy.compContinuousMap ⟨ULift.down, continuous_uliftDown⟩

/-- The three original standard prism tetrahedra for the full relative homotopy. -/
def prismTriangle (i : Fin 3) : SingularSimplex Y ⦋3⦌ :=
  prismSimplex (liftedHomotopy H) i triangleUp

private theorem sidePrism_const (i : Fin 2) (j : Fin 3) :
    prismSimplex (liftedHomotopy H) i
      (restrictSimplex triangleUp (SimplexCategory.δ j)) = ContinuousMap.const _ y := by
  ext z
  rw [prismSimplex_apply]
  change H (_, (z.map (SimplexCategory.σ i)).map (SimplexCategory.δ j)) = y
  have hz : (z.map (SimplexCategory.σ i)).map (SimplexCategory.δ j) ∈ simplexBoundary 2 :=
    (simplexBoundaryFace 1 j (z.map (SimplexCategory.σ i))).property
  exact (H.eq_fst _ hz).trans (a.boundary _ hz)

private theorem prismTriangle_first :
    restrictSimplex (prismTriangle H 0) (SimplexCategory.δ 0) = b.val :=
  prismSimplex_face_zero (liftedHomotopy H) triangleUp

private theorem prismTriangle_last :
    restrictSimplex (prismTriangle H 2) (SimplexCategory.δ 3) = a.val :=
  prismSimplex_face_last (liftedHomotopy H) triangleUp

private theorem prismTriangle_middle0 :
    restrictSimplex (prismTriangle H 0) (SimplexCategory.δ 1) =
      restrictSimplex (prismTriangle H 1) (SimplexCategory.δ 1) :=
  (prismSimplex_middle_face (liftedHomotopy H) (0 : Fin 2) triangleUp).symm

private theorem prismTriangle_middle1 :
    restrictSimplex (prismTriangle H 1) (SimplexCategory.δ 2) =
      restrictSimplex (prismTriangle H 2) (SimplexCategory.δ 2) :=
  (prismSimplex_middle_face (liftedHomotopy H) (1 : Fin 2) triangleUp).symm

private theorem prismTriangle_side02 :
    restrictSimplex (prismTriangle H 0) (SimplexCategory.δ 2) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_lt (liftedHomotopy H) (1 : Fin 3) (0 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 0 1)

private theorem prismTriangle_side03 :
    restrictSimplex (prismTriangle H 0) (SimplexCategory.δ 3) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_lt (liftedHomotopy H) (2 : Fin 3) (0 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 0 2)

private theorem prismTriangle_side10 :
    restrictSimplex (prismTriangle H 1) (SimplexCategory.δ 0) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_le (liftedHomotopy H) (0 : Fin 3) (0 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 0 0)

private theorem prismTriangle_side13 :
    restrictSimplex (prismTriangle H 1) (SimplexCategory.δ 3) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_lt (liftedHomotopy H) (2 : Fin 3) (1 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 1 2)

private theorem prismTriangle_side20 :
    restrictSimplex (prismTriangle H 2) (SimplexCategory.δ 0) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_le (liftedHomotopy H) (0 : Fin 3) (1 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 1 0)

private theorem prismTriangle_side21 :
    restrictSimplex (prismTriangle H 2) (SimplexCategory.δ 1) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_le (liftedHomotopy H) (1 : Fin 3) (1 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 1 1)

/-- The literal alternating three-prism chain. -/
def prismChain : (Chains Y).X 3 :=
  simplexChain (prismTriangle H 0) - simplexChain (prismTriangle H 1) +
    simplexChain (prismTriangle H 2)

/-- Its original boundary is the terminal spherical generator minus the initial one. -/
theorem prismChain_boundary :
    (Chains Y).d 3 2 (prismChain H) = simplexChain b.val - simplexChain a.val := by
  rw [prismChain, map_add, map_sub, tetrahedron_boundary, tetrahedron_boundary,
    tetrahedron_boundary, prismTriangle_first, prismTriangle_last,
    prismTriangle_middle0, prismTriangle_middle1,
    prismTriangle_side02, prismTriangle_side03, prismTriangle_side10,
    prismTriangle_side13, prismTriangle_side20, prismTriangle_side21]
  abel

include H in
/-- Relative homotopy preserves the original marked absolute homology class. -/
theorem sphericalClass_homotopy : sphericalClass a = sphericalClass b := by
  symm
  apply homology_eq_of_boundary (sphericalTwoCycle b) (sphericalTwoCycle a) (prismChain H)
  rw [prismChain_boundary, iCycles_sphericalTwoCycle, iCycles_sphericalTwoCycle]
  change simplexChain b.val - simplexChain a.val =
    (simplexChain b.val - simplexChain (ContinuousMap.const _ y)) -
      (simplexChain a.val - simplexChain (ContinuousMap.const _ y))
  abel

end Quillen.LocalCoefficients.SecondHurewicz

namespace Quillen.SecondHurewiczHorn

/-- The three included face indices, with the first interior face omitted. -/
def faceIndex (i : Fin 3) : Fin 4 := (1 : Fin 4).succAbove i

/-- The literal geometric horn of the ordered tetrahedron. -/
abbrev Horn := {x : StdSimplex ℝ (Fin 4) // ∃ i : Fin 3, x.weights (faceIndex i) = 0}

/-- Each original included face maps into the actual horn. -/
def face (i : Fin 3) : C(StdSimplex ℝ (Fin 3), Horn) where
  toFun x := ⟨x.map (faceIndex i).succAbove, i,
    (StdSimplex.mem_range_map_iff (faceIndex i).succAbove _).mp ⟨x, rfl⟩ (faceIndex i)
      (by simp [Fin.range_succAbove])⟩
  continuous_toFun := (StdSimplex.continuous_map ℝ _).subtype_mk _

/-- The original finite face cover, retaining all simplex coordinates. -/
def cover : C(Fin 3 × StdSimplex ℝ (Fin 3), Horn) where
  toFun z := face z.1 z.2
  continuous_toFun := continuous_prod_of_discrete_left.mpr (fun i => (face i).continuous)

private theorem cover_surjective : Function.Surjective cover := by
  intro x
  obtain ⟨i, hi⟩ := x.property
  have hm : x.val ∈ Set.range (StdSimplex.map (faceIndex i).succAbove) := by
    rw [StdSimplex.mem_range_map_iff]
    intro j hj
    have hji : j = faceIndex i := by simpa [Fin.range_succAbove] using hj
    simpa only [hji] using hi
  obtain ⟨a, ha⟩ := hm
  exact ⟨(i, a), Subtype.ext ha⟩

/-- The actual finite compact horn cover is a quotient map. -/
theorem cover_quotient : IsQuotientMap cover :=
  IsQuotientMap.of_surjective_continuous cover_surjective cover.continuous

/-- The smallest coordinate among the three included tetrahedron faces. -/
def mass (x : StdSimplex ℝ (Fin 4)) : ℝ :=
  min (x.weights 0) (min (x.weights 2) (x.weights 3))

/-- The smallest coordinate among the three included tetrahedron faces. -/
theorem mass_nonneg (x : StdSimplex ℝ (Fin 4)) : 0 ≤ mass x :=
  le_min (x.weights_nonneg 0) (le_min (x.weights_nonneg 2) (x.weights_nonneg 3))

/-- The smallest coordinate among the three included tetrahedron faces. -/
theorem mass_le (x : StdSimplex ℝ (Fin 4)) (i : Fin 3) :
    mass x ≤ x.weights (faceIndex i) := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- Subtract the smallest included coordinate and transfer the mass to vertex one. -/
def retractPoint (x : StdSimplex ℝ (Fin 4)) : StdSimplex ℝ (Fin 4) where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i => if i = 1 then x.weights i + 3 * mass x else x.weights i - mass x)
  nonneg i := by
    change 0 ≤ if i = 1 then x.weights i + 3 * mass x else x.weights i - mass x
    split_ifs with hi
    · exact add_nonneg (x.weights_nonneg i) (mul_nonneg (by norm_num) (mass_nonneg x))
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      exact sub_nonneg.mpr (mass_le x j)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ i : Fin 4,
      if i = 1 then x.weights i + 3 * mass x else x.weights i - mass x) = 1
    have hx := x.total_of_fintype
    simp only [Fin.sum_univ_succ] at hx ⊢
    norm_num at hx ⊢
    linarith

private theorem retractPoint_weights (x : StdSimplex ℝ (Fin 4)) (i : Fin 4) :
    (retractPoint x).weights i =
      if i = 1 then x.weights i + 3 * mass x else x.weights i - mass x := by
  simp [retractPoint]

/-- The displayed retraction point lies on one of the three included faces. -/
theorem retractPoint_mem (x : StdSimplex ℝ (Fin 4)) :
    ∃ i : Fin 3, (retractPoint x).weights (faceIndex i) = 0 := by
  by_cases h0 : x.weights 0 ≤ min (x.weights 2) (x.weights 3)
  · refine ⟨0, ?_⟩
    change (retractPoint x).weights 0 = 0
    simp [retractPoint_weights, mass, min_eq_left h0]
  · by_cases h2 : x.weights 2 ≤ x.weights 3
    · refine ⟨1, ?_⟩
      change (retractPoint x).weights 2 = 0
      rw [retractPoint_weights]
      norm_num
      rw [mass, min_eq_right (le_of_not_ge h0), min_eq_left h2, sub_self]
    · refine ⟨2, ?_⟩
      change (retractPoint x).weights 3 = 0
      rw [retractPoint_weights]
      norm_num
      rw [mass, min_eq_right (le_of_not_ge h0), min_eq_right (le_of_not_ge h2), sub_self]

/-- The explicit barycentric retraction is continuous in every coordinate. -/
theorem continuous_retractPoint : Continuous retractPoint := by
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 4)).continuous_iff.mpr
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, retractPoint_weights]
  have hm : Continuous mass :=
    (StdSimplex.continuous_weights_apply ℝ 0).min
      ((StdSimplex.continuous_weights_apply ℝ 2).min
        (StdSimplex.continuous_weights_apply ℝ 3))
  split_ifs
  · exact (StdSimplex.continuous_weights_apply ℝ i).add (continuous_const.mul hm)
  · exact (StdSimplex.continuous_weights_apply ℝ i).sub hm

/-- The actual retraction into the included three faces. -/
def retract : C(StdSimplex ℝ (Fin 4), Horn) where
  toFun x := ⟨retractPoint x, retractPoint_mem x⟩
  continuous_toFun := continuous_retractPoint.subtype_mk _

/-- Every point of the original horn is fixed exactly. -/
theorem retract_fixed (x : Horn) : retract x.val = x := by
  have hm : mass x.val = 0 := by
    obtain ⟨i, hi⟩ := x.property
    exact le_antisymm ((mass_le x.val i).trans hi.le) (mass_nonneg x.val)
  apply Subtype.ext
  apply StdSimplex.ext
  ext i
  simp [retract, retractPoint_weights, hm]

variable {Y : Type u} [TopologicalSpace Y] {y : Y}

private theorem face_overlap_based (i j : Fin 3) (hij : i ≠ j)
    (a b : StdSimplex ℝ (Fin 3))
    (hab : a.map (faceIndex i).succAbove = b.map (faceIndex j).succAbove) :
    a ∈ simplexBoundary 2 := by
  have hij' : faceIndex j ≠ faceIndex i := by
    intro h
    exact hij (Fin.succAbove_right_injective h.symm)
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij'
  refine ⟨k, ?_⟩
  have hz := (StdSimplex.mem_range_map_iff (faceIndex j).succAbove _).mp
    ⟨b, rfl⟩ (faceIndex j) (by simp [Fin.range_succAbove])
  rw [← hab, ← hk, StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective] at hz
  exact hz

/-- Evaluate the three original spherical triangles on the finite face cover. -/
def faceValues (a : Fin 3 → SphericalSimplex Y y 2) :
    C(Fin 3 × StdSimplex ℝ (Fin 3), Y) :=
  ⟨fun z => a z.1 z.2,
    continuous_prod_of_discrete_left.mpr (fun i => (a i).val.continuous)⟩

/-- Evaluate the three original spherical triangles on the finite face cover. -/
theorem faceValues_factors (a : Fin 3 → SphericalSimplex Y y 2) :
    Function.FactorsThrough (faceValues a) cover := by
  rintro ⟨i, x⟩ ⟨j, z⟩ h
  have hxz : x.map (faceIndex i).succAbove = z.map (faceIndex j).succAbove :=
    congrArg Subtype.val h
  by_cases hij : i = j
  · subst j
    exact congrArg (a i) (simplex_map_injective Fin.succAbove_right_injective hxz)
  · exact ((a i).boundary x (face_overlap_based i j hij x z hxz)).trans
      ((a j).boundary z (face_overlap_based j i (fun h => hij h.symm) z x hxz.symm)).symm

/-- Based spherical triangles agree on all actual overlaps of the included faces. -/
def desc (a : Fin 3 → SphericalSimplex Y y 2) : C(Horn, Y) :=
  cover_quotient.lift (faceValues a) (faceValues_factors a)

/-- The descended map restricts to exactly each original spherical triangle. -/
theorem desc_face (a : Fin 3 → SphericalSimplex Y y 2) (i : Fin 3)
    (x : StdSimplex ℝ (Fin 3)) : desc a (face i x) = a i x :=
  ContinuousMap.congr_fun (cover_quotient.lift_comp (faceValues a) (faceValues_factors a)) (i, x)

/-- An actual tetrahedron extending the prescribed three spherical faces. -/
def fill (a : Fin 3 → SphericalSimplex Y y 2) : C(StdSimplex ℝ (Fin 4), Y) :=
  (desc a).comp retract

/-- The extension keeps each included standard face pointwise. -/
theorem fill_face (a : Fin 3 → SphericalSimplex Y y 2) (i : Fin 3)
    (x : StdSimplex ℝ (Fin 3)) : fill a (x.map (faceIndex i).succAbove) = a i x := by
  change desc a (retract (face i x).val) = _
  rw [retract_fixed, desc_face]


private theorem skeleton_mem_horn (x : StdSimplex ℝ (Fin 4))
    (hx : x ∈ simplexSkeleton 2 3) : ∃ i : Fin 3, x.weights (faceIndex i) = 0 := by
  classical
  by_contra h
  push Not at h
  have hs : ({0, 2, 3} : Finset (Fin 4)) ⊆ x.weights.support := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact Finsupp.mem_support_iff.mpr (h 0)
    · exact Finsupp.mem_support_iff.mpr (h 1)
    · exact Finsupp.mem_support_iff.mpr (h 2)
  have hc := Finset.card_le_card hs
  norm_num at hc
  change x.weights.support.card ≤ 2 at hx
  omega

/-- Every original edge of the filled tetrahedron remains at the displayed basepoint. -/
theorem fill_skeleton (a : Fin 3 → SphericalSimplex Y y 2)
    (x : StdSimplex ℝ (Fin 4)) (hx : x ∈ simplexSkeleton 2 3) : fill a x = y := by
  obtain ⟨i, hi⟩ := skeleton_mem_horn x hx
  have hm : x ∈ Set.range (StdSimplex.map (faceIndex i).succAbove) := by
    rw [StdSimplex.mem_range_map_iff]
    intro j hj
    have hji : j = faceIndex i := by simpa [Fin.range_succAbove] using hj
    simpa only [hji] using hi
  obtain ⟨z, rfl⟩ := hm
  rw [fill_face]
  apply (a i).boundary
  apply simplexSkeleton_subset_boundary (n := 2) (d := 2) le_rfl
  exact (simplex_map_mem_skeleton_iff (faceIndex i).succAbove
    Fin.succAbove_right_injective z).mp hx

/-- The included spherical faces retain their literal original representatives. -/
theorem sphericalFace_fill (a : Fin 3 → SphericalSimplex Y y 2) (i : Fin 3) :
    sphericalFace (fill a) (fill_skeleton a) (faceIndex i) = a i := by
  ext x
  exact fill_face a i x

end Quillen.SecondHurewiczHorn

namespace Quillen.LocalCoefficients.SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y] {y : Y}

/-- The ordered addition horn consists of the first sphere, second sphere,
and constant sphere. -/
def additionFaces (a b : SphericalSimplex Y y 2) :
    Fin 3 → SphericalSimplex Y y 2 :=
  ![a, b, SphericalSimplex.const]

/-- The actual missing face in the displayed three-spherical-face tetrahedron. -/
def sumSphere (a b : SphericalSimplex Y y 2) : SphericalSimplex Y y 2 :=
  sphericalFace (SecondHurewiczHorn.fill (additionFaces a b))
    (SecondHurewiczHorn.fill_skeleton (additionFaces a b)) 1

private theorem addition_face0 (a b : SphericalSimplex Y y 2) :
    sphericalFace (SecondHurewiczHorn.fill (additionFaces a b))
      (SecondHurewiczHorn.fill_skeleton (additionFaces a b)) 0 = a :=
  SecondHurewiczHorn.sphericalFace_fill (additionFaces a b) 0

private theorem addition_face2 (a b : SphericalSimplex Y y 2) :
    sphericalFace (SecondHurewiczHorn.fill (additionFaces a b))
      (SecondHurewiczHorn.fill_skeleton (additionFaces a b)) 2 = b :=
  SecondHurewiczHorn.sphericalFace_fill (additionFaces a b) 1

private theorem addition_face3 (a b : SphericalSimplex Y y 2) :
    sphericalFace (SecondHurewiczHorn.fill (additionFaces a b))
      (SecondHurewiczHorn.fill_skeleton (additionFaces a b)) 3 = SphericalSimplex.const :=
  SecondHurewiczHorn.sphericalFace_fill (additionFaces a b) 2

/-- The missing face represents the original product in cubical Pi two, with the fixed sign. -/
theorem sumSphere_class (a b : SphericalSimplex Y y 2) :
    (sumSphere a b).homotopyClassStick = a.homotopyClassStick * b.homotopyClassStick := by
  have h := spherical_tetrahedral_homotopy_addition
    (SecondHurewiczHorn.fill (additionFaces a b))
    (SecondHurewiczHorn.fill_skeleton (additionFaces a b))
  rw [addition_face0, addition_face2, addition_face3, SphericalSimplex.homotopyClassStick_const]
    at h
  change Additive.ofMul a.homotopyClassStick - Additive.ofMul (sumSphere a b).homotopyClassStick +
    Additive.ofMul b.homotopyClassStick - 0 = 0 at h
  rw [sub_zero] at h
  have he : Additive.ofMul a.homotopyClassStick + Additive.ofMul b.homotopyClassStick =
      Additive.ofMul (sumSphere a b).homotopyClassStick := by
    apply sub_eq_zero.mp
    calc
      _ = Additive.ofMul a.homotopyClassStick -
          Additive.ofMul (sumSphere a b).homotopyClassStick +
            Additive.ofMul b.homotopyClassStick := by abel
      _ = 0 := h
  exact congrArg Additive.toMul he.symm

/-- The same actual tetrahedron proves addition of the original marked homology classes. -/
theorem sphericalClass_sumSphere (a b : SphericalSimplex Y y 2) :
    sphericalClass (sumSphere a b) = sphericalClass a + sphericalClass b := by
  let τ := SecondHurewiczHorn.fill (additionFaces a b)
  have h0 : restrictSimplex τ (SimplexCategory.δ 0) = a.val :=
    congrArg Subtype.val (addition_face0 a b)
  have h2 : restrictSimplex τ (SimplexCategory.δ 2) = b.val :=
    congrArg Subtype.val (addition_face2 a b)
  have h3 : restrictSimplex τ (SimplexCategory.δ 3) = ContinuousMap.const _ y :=
    congrArg Subtype.val (addition_face3 a b)
  have h := homology_eq_of_boundary (sphericalTwoCycle a + sphericalTwoCycle b)
    (sphericalTwoCycle (sumSphere a b)) (simplexChain τ) (by
      rw [tetrahedron_boundary, h0, h2, h3, map_add,
        iCycles_sphericalTwoCycle, iCycles_sphericalTwoCycle, iCycles_sphericalTwoCycle]
      change simplexChain a.val - simplexChain (sumSphere a b).val + simplexChain b.val -
        simplexChain (ContinuousMap.const _ y) =
          (simplexChain a.val - simplexChain (ContinuousMap.const _ y)) +
          (simplexChain b.val - simplexChain (ContinuousMap.const _ y)) -
          (simplexChain (sumSphere a b).val - simplexChain (ContinuousMap.const _ y))
      abel)
  rw [map_add] at h
  exact h.symm

/-- The original marked class descends through the actual based-cube homotopy quotient. -/
def toHomology (y : Y) :
    HomotopyGroup.Pi 2 Y y → homology (constant Y integralCoefficientModule) 2 :=
  Quotient.lift (fun p => sphericalClass (SphericalSimplex.ofGenLoopStick p)) (by
    intro p q hpq
    have he : (SphericalSimplex.ofGenLoopStick p).homotopyClassStick =
        (SphericalSimplex.ofGenLoopStick q).homotopyClassStick := by
      simp only [SphericalSimplex.homotopyClassStick,
        SphericalSimplex.toGenLoopStick_ofGenLoopStick]
      exact Quotient.sound hpq
    obtain ⟨H⟩ := (SphericalSimplex.homotopyClassStick_eq_iff _ _).mp he
    exact sphericalClass_homotopy H)

/-- Every spherical representative has precisely the specified original cycle class. -/
theorem toHomology_spherical (a : SphericalSimplex Y y 2) :
    toHomology y a.homotopyClassStick = sphericalClass a := by
  change sphericalClass (SphericalSimplex.ofGenLoopStick a.toGenLoopStick) = _
  rw [SphericalSimplex.ofGenLoopStick_toGenLoopStick]

/-- The actual constant cube maps to the zero class. -/
theorem toHomology_one : toHomology y 1 = 0 :=
  (toHomology_spherical (SphericalSimplex.const : SphericalSimplex Y y 2)).trans
    sphericalClass_const

/-- Original cube concatenation is sent to addition of the marked original homology classes. -/
theorem toHomology_mul (a b : HomotopyGroup.Pi 2 Y y) :
    toHomology y (a * b) = toHomology y a + toHomology y b := by
  obtain ⟨a, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective a
  obtain ⟨b, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective b
  rw [← sumSphere_class, toHomology_spherical, toHomology_spherical, toHomology_spherical]
  exact sphericalClass_sumSphere a b

/-- The marked second Hurewicz homomorphism into original integral H-two. -/
def hom (y : Y) : HomotopyGroup.Pi 2 Y y →*
    Multiplicative (homology (constant Y integralCoefficientModule.{u}) 2) where
  toFun a := Multiplicative.ofAdd (toHomology y a)
  map_one' := congrArg Multiplicative.ofAdd toHomology_one
  map_mul' a b := congrArg Multiplicative.ofAdd (toHomology_mul a b)

/-- The homomorphism retains the original sphere-minus-constant cycle and stick orientation. -/
theorem hom_spherical (a : SphericalSimplex Y y 2) :
    hom y a.homotopyClassStick = Multiplicative.ofAdd
      ((Chains Y).homologyπ 2 (sphericalTwoCycle a)) :=
  congrArg Multiplicative.ofAdd (toHomology_spherical a)

end Quillen.LocalCoefficients.SecondHurewicz

namespace Quillen.LocalCoefficients.SecondHurewicz
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y} (f : C(X, Y)) (h : f x = y)

/-- The explicit stick quotient preserves the original based postcomposition map. -/
theorem stickClass_map (a : SphericalSimplex X x 2) :
    (SphericalSimplex.map f h a).homotopyClassStick = piMap 1 f h a.homotopyClassStick := rfl

private theorem pushforward_simplexChain {n : ℕ} (a : SingularSimplex X ⦋n⦌) :
    (pushforwardChainMap f (constant Y integralCoefficientModule.{u})).f n (simplexChain a) =
      simplexChain (f.comp a) :=
  ConcreteCategory.congr_hom
    (chainInclusion_pushforwardModuleMap f (constant Y integralCoefficientModule.{u}) a)
      (ULift.up 1)

/-- The original chain map sends the marked spherical difference to its actual based image. -/
theorem sphericalTwoChain_map (a : SphericalSimplex X x 2) :
    (pushforwardChainMap f (constant Y integralCoefficientModule.{u})).f 2 (sphericalTwoChain a) =
      sphericalTwoChain (SphericalSimplex.map f h a) := by
  change (pushforwardChainMap f (constant Y integralCoefficientModule.{u})).f 2
      (simplexChain a.val - simplexChain (ContinuousMap.const _ x)) = _
  rw [map_sub, pushforward_simplexChain, pushforward_simplexChain]
  have hc : f.comp (ContinuousMap.const (StdSimplex ℝ (Fin 3)) x) =
      ContinuousMap.const _ y := by ext t; exact h
  rw [hc]
  rfl

/-- The original categorical cycle map retains that exact marked spherical cycle. -/
theorem sphericalTwoCycle_map (a : SphericalSimplex X x 2) :
    HomologicalComplex.cyclesMap
      (pushforwardChainMap f (constant Y integralCoefficientModule.{u})) 2 (sphericalTwoCycle a) =
      sphericalTwoCycle (SphericalSimplex.map f h a) := by
  apply (ModuleCat.mono_iff_injective ((Chains Y).iCycles 2)).mp inferInstance
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (pushforwardChainMap f (constant Y integralCoefficientModule.{u})) 2) (sphericalTwoCycle a)
  change (Chains Y).iCycles 2 (HomologicalComplex.cyclesMap
        (pushforwardChainMap f (constant Y integralCoefficientModule.{u})) 2
          (sphericalTwoCycle a)) =
    (pushforwardChainMap f (constant Y integralCoefficientModule.{u})).f 2
      ((Chains X).iCycles 2 (sphericalTwoCycle a)) at hn
  rw [hn, iCycles_sphericalTwoCycle, iCycles_sphericalTwoCycle]
  exact sphericalTwoChain_map f h a

/-- Actual homology-map naturality on the original marked spherical representatives. -/
theorem sphericalClass_map (a : SphericalSimplex X x 2) :
    pushforwardHomologyMap f (constant Y integralCoefficientModule.{u}) 2 (sphericalClass a) =
      sphericalClass (SphericalSimplex.map f h a) := by
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
      (pushforwardChainMap f (constant Y integralCoefficientModule.{u})) 2) (sphericalTwoCycle a)
  change pushforwardHomologyMap f (constant Y integralCoefficientModule.{u}) 2
      (sphericalClass a) = (Chains Y).homologyπ 2
      (HomologicalComplex.cyclesMap
        (pushforwardChainMap f (constant Y integralCoefficientModule.{u})) 2
          (sphericalTwoCycle a)) at hn
  exact hn.trans (congrArg ((Chains Y).homologyπ 2) (sphericalTwoCycle_map f h a))

/-- The marked Hurewicz map is natural for the original based Pi-two and integral H-two maps. -/
theorem toHomology_naturality (a : HomotopyGroup.Pi 2 X x) :
    toHomology y (piMap 1 f h a) =
      pushforwardHomologyMap f (constant Y integralCoefficientModule.{u}) 2 (toHomology x a) := by
  obtain ⟨a, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective a
  rw [← stickClass_map, toHomology_spherical, toHomology_spherical]
  exact (sphericalClass_map f h a).symm

/-- The same naturality statement in the original multiplicative target notation. -/
theorem hom_naturality (a : HomotopyGroup.Pi 2 X x) :
    hom y (piMap 1 f h a) = Multiplicative.ofAdd
      (pushforwardHomologyMap f (constant Y integralCoefficientModule.{u}) 2
        (Multiplicative.toAdd (hom x a))) :=
  congrArg Multiplicative.ofAdd (toHomology_naturality f h a)

private theorem constantHomologyMap_homotopy {f g : C(X, Y)} (H : f.Homotopy g) (n : ℕ) :
    pushforwardHomologyMap f (constant Y integralCoefficientModule.{u}) n =
      pushforwardHomologyMap g (constant Y integralCoefficientModule.{u}) n := by
  have hη : (homotopyPullbackIso H (constant Y integralCoefficientModule.{u})).hom =
      𝟙 (constant X integralCoefficientModule.{u}) := by
    ext z
    rfl
  have ht := pushforwardHomologyMap_homotopy H (constant Y integralCoefficientModule.{u}) n
  change pushforwardHomologyMap f (constant Y integralCoefficientModule.{u}) n =
    coefficientHomologyMap
      (homotopyPullbackIso H (constant Y integralCoefficientModule.{u})).hom n ≫
      pushforwardHomologyMap g (constant Y integralCoefficientModule.{u}) n at ht
  rw [hη] at ht
  erw [coefficientHomologyMap_id] at ht
  exact ht.trans (Category.id_comp _)

/-- The original basepoint transport does not change the marked integral H-two class. -/
theorem toHomology_pathTransport {z : Y} (p : Path y z) (a : HomotopyGroup.Pi 2 Y y) :
    toHomology z (pathTransport p 2 a) = toHomology y a := by
  obtain ⟨b, rfl⟩ := (pathStartEquiv p 2).surjective a
  rw [pathStartEquiv_apply, pathTransport_homotopyGroupMap_start]
  change toHomology z (piMap 1 (freePathEvaluation Y 1) p.target b) =
    toHomology y (piMap 1 (freePathEvaluation Y 0) p.source b)
  rw [toHomology_naturality, toHomology_naturality]
  exact congrArg (fun k => k (toHomology p.toContinuousMap b))
    (constantHomologyMap_homotopy freePathEvaluationHomotopy 2).symm

/-- Path correction is retained exactly by the multiplicative second Hurewicz map. -/
theorem hom_pathTransport {z : Y} (p : Path y z) (a : HomotopyGroup.Pi 2 Y y) :
    hom z (pathTransportMulEquiv p 1 a) = hom y a :=
  congrArg Multiplicative.ofAdd (toHomology_pathTransport p a)

end Quillen.LocalCoefficients.SecondHurewicz

namespace Quillen.LocalCoefficients.SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y] {y : Y}

/-- Every original based two-cube maps to the literal cycle of its stick-descended sphere. -/
theorem hom_genLoop (p : GenLoop (Fin 2) Y y) :
    hom y (Quotient.mk' p) = Multiplicative.ofAdd
      ((Chains Y).homologyπ 2 (sphericalTwoCycle (SphericalSimplex.ofGenLoopStick p))) := by
  have h := hom_spherical (SphericalSimplex.ofGenLoopStick p)
  simpa only [SphericalSimplex.homotopyClassStick,
    SphericalSimplex.toGenLoopStick_ofGenLoopStick] using h

end Quillen.LocalCoefficients.SecondHurewicz
