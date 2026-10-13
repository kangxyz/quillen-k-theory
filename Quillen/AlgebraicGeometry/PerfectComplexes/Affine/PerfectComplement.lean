/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.PerfectVanishing
public import Quillen.AlgebraicGeometry.PerfectComplexes.Single
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectOpenApproximation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.ApproximationTriangle
public import Mathlib.CategoryTheory.Retract

/-! # Actual perfect complements on quasi-compact affine opens

Every original locally-perfect complex E on a compact open W of Spec R is a
derived retract of the actual restriction of a global bounded finite-projective
complex. Genuine uniform derived-Hom vanishing kills the original residual
arrow of an arbitrarily low approximation. Its explicit complement is the
single on the original restricted-cone homology, shifted by -1, and is strict
perfect. The derived isomorphism ends at the localization of the actual
complex biproduct, preserving its original chain projection and the actual
approximation map.

All commutative rings and empty opens are permitted. These endpoints assert
actual original derived splittings. Turning them into a restriction-to-target
weak chain map, or membership in a one-arrow witnessed image category, needs
an additional proved enhancement and is not inferred here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- Zero of the actual residual arrow gives a section of the unchanged original
approximation map and a split with its actual residual single shifted by -1. -/
theorem originalApproximation_splits_of_boundary_zero
    (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    {P K : ModuleComplex R} (f : P ⟶ K) {E : Complex U}
    (eK : (toDerived U).obj ((restrict j).obj ((associatedComplex R).obj K)) ≅ (toDerived U).obj E)
    (n : ℤ)
    (eD : (toDerived U).obj ((restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone
      f))) ≅
      (toDerived U).obj ((CochainComplex.singleFunctor U.Modules n).obj
        (((restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))).homology n)))
    (hzero : originalApproximationBoundary R j f eK = 0) :
    (∃ σ : (toDerived U).obj E ⟶ (toDerived U).obj ((restrict j).obj ((associatedComplex R).obj P)),
      σ ≫ originalApproximationHom R j f eK = 𝟙 _) ∧
    ∃ e : (toDerived U).obj ((restrict j).obj ((associatedComplex R).obj P)) ≅
      ((toDerived U).obj ((CochainComplex.singleFunctor U.Modules n).obj
        (((restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))).homology
          n)))⟦(-1 : ℤ)⟧ ⊞
        (toDerived U).obj E,
      originalApproximationHom R j f eK = e.hom ≫ biprod.snd := by
  let T := originalApproximationSingleTriangle R j f eK n eD
  have hT := originalApproximationSingleTriangle_distinguished R j f eK n eD
  have hz : T.mor₂ = 0 := by
    change originalApproximationBoundary R j f eK ≫ eD.hom = 0
    rw [hzero, zero_comp]
  constructor
  · obtain ⟨σ, hσ⟩ := Triangle.coyoneda_exact₂ T hT (𝟙 ((toDerived U).obj E)) (by simp [hz])
    exact ⟨σ, hσ.symm⟩
  · obtain ⟨e, _, he⟩ := exists_iso_binaryBiproduct_of_distTriang T.invRotate
      (inv_rot_of_distTriang T hT) (by simp [Triangle.invRotate, hz])
    exact ⟨e, he⟩

/-- Every original locally-perfect complex on a compact affine open is a
retract of the actual restriction of a global bounded finite-projective module
complex. The retract projection is the unchanged original approximation map. -/
theorem locallyPerfect_exists_original_strict_derived_retract
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) :
    ∃ (K P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K)
      (eK : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E),
      originalApproximationBoundary R W.ι f eK = 0 ∧
      ∃ σ : (toDerived W.toScheme).obj E ⟶
          (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)),
        σ ≫ originalApproximationHom R W.ι f eK = 𝟙 _ := by
  let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  have hInf : ∀ U V : W.toScheme.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
    fun U V hU hV => (isAffineHom_diagonal_iff (f := W.ι)).mp inferInstance
      ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV
  let : IsAffineHom (pullback.diagonal (terminal.from W.toScheme)) :=
    isAffineHom_diagonal_iff.mpr (fun _ _ U _ V _ hU hV => hInf U V hU hV)
  obtain ⟨c, hc⟩ := locallyPerfect_exists_uniform_low_single_vanishing E hE
  obtain ⟨K, a, b, P, n, f, _, _, hP, hn, ⟨eK⟩, hM, _, _, ⟨eD⟩⟩ :=
    locallyPerfect_exists_original_strict_approximation R W hW E hE c
  let D := (restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
  have : SchemeSheaf.IsFiniteLocallyFree W.toScheme (D.homology n) := hM
  have hz : originalApproximationBoundary R W.ι f eK = 0 := by
    apply (cancel_mono eD.hom).mp
    simpa only [zero_comp] using hc (D.homology n) n hn
      (originalApproximationBoundary R W.ι f eK ≫ eD.hom)
  exact ⟨K, P, hP, f, eK, hz,
    (originalApproximation_splits_of_boundary_zero R W.ι f eK n eD hz).1⟩

/-- The actual original derived object is a literal categorical retract of a
restricted global strict-perfect sheaf complex, for every commutative ring. -/
theorem locallyPerfect_exists_global_strict_retract
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) :
    ∃ Q : Complex (Spec R), strictPerfect (Spec R) Q ∧
      Nonempty (Retract ((toDerived W.toScheme).obj E)
        ((toDerived W.toScheme).obj ((restrict W.ι).obj Q))) := by
  obtain ⟨K, P, hP, f, eK, _, σ, hσ⟩ :=
    locallyPerfect_exists_original_strict_derived_retract R W hW E hE
  exact ⟨(associatedComplex R).obj P, strictPerfect_associated R hP,
    ⟨⟨σ, originalApproximationHom R W.ι f eK, hσ⟩⟩⟩

end Quillen.PerfectComplexes.Affine

namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The actual global finite-projective approximation splits on the compact
open, with its original vector-bundle residual single in any requested low
degree. Both original derived arrows and the original projection are retained. -/
theorem locallyPerfect_exists_arbitrarily_low_original_split
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) (cutoff : ℤ) :
    ∃ (K P : ModuleComplex R) (n : ℤ) (_ : moduleStrictPerfect R P) (f : P ⟶ K)
      (eK : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E),
      n ≤ cutoff ∧
      let D := (restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
      SchemeSheaf.IsFiniteLocallyFree W.toScheme (D.homology n) ∧
      ∃ _eD : (toDerived W.toScheme).obj D ≅
        (toDerived W.toScheme).obj ((CochainComplex.singleFunctor W.toScheme.Modules n).obj
          (D.homology n)),
        originalApproximationBoundary R W.ι f eK = 0 ∧
        (∃ σ : (toDerived W.toScheme).obj E ⟶
            (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)),
          σ ≫ originalApproximationHom R W.ι f eK = 𝟙 _) ∧
        ∃ e : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
          ((toDerived W.toScheme).obj ((CochainComplex.singleFunctor W.toScheme.Modules n).obj
            (D.homology n)))⟦(-1 : ℤ)⟧ ⊞ (toDerived W.toScheme).obj E,
          originalApproximationHom R W.ι f eK = e.hom ≫ biprod.snd := by
  let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  have hInf : ∀ U V : W.toScheme.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
    fun U V hU hV => (isAffineHom_diagonal_iff (f := W.ι)).mp inferInstance
      ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV
  let : IsAffineHom (pullback.diagonal (terminal.from W.toScheme)) :=
    isAffineHom_diagonal_iff.mpr (fun _ _ U _ V _ hU hV => hInf U V hU hV)
  obtain ⟨c, hc⟩ := locallyPerfect_exists_uniform_low_single_vanishing E hE
  obtain ⟨K, a, b, P, n, f, _, _, hP, hn, ⟨eK⟩, hM, _, _, ⟨eD⟩⟩ :=
    locallyPerfect_exists_original_strict_approximation R W hW E hE (min c cutoff)
  let D := (restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
  have : SchemeSheaf.IsFiniteLocallyFree W.toScheme (D.homology n) := hM
  have hz : originalApproximationBoundary R W.ι f eK = 0 := by
    apply (cancel_mono eD.hom).mp
    simpa only [zero_comp] using hc (D.homology n) n (hn.trans (min_le_left _ _))
      (originalApproximationBoundary R W.ι f eK ≫ eD.hom)
  exact ⟨K, P, n, hP, f, eK, hn.trans (min_le_right _ _), hM, eD, hz,
    originalApproximation_splits_of_boundary_zero R W.ι f eK n eD hz⟩

/-- The explicit complement is the original residual vector-bundle single shifted
by -1. The isomorphism ends at the localization of the actual complex biproduct,
and its original chain projection is exactly the original approximation map. -/
theorem locallyPerfect_exists_actual_perfect_complement
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) (cutoff : ℤ) :
    ∃ (K P : ModuleComplex R) (n : ℤ) (_ : moduleStrictPerfect R P) (f : P ⟶ K)
      (eK : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E),
      n ≤ cutoff ∧
      let D := (restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
      let C := ((CochainComplex.singleFunctor W.toScheme.Modules n).obj (D.homology n))⟦(-1 : ℤ)⟧
      SchemeSheaf.IsFiniteLocallyFree W.toScheme (D.homology n) ∧ strictPerfect W.toScheme C ∧
      originalApproximationBoundary R W.ι f eK = 0 ∧
      ∃ e : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
          (toDerived W.toScheme).obj (C ⊞ E),
        originalApproximationHom R W.ι f eK = e.hom ≫
          (toDerived W.toScheme).map (biprod.snd : C ⊞ E ⟶ E) := by
  obtain ⟨K, P, n, hP, f, eK, hn, hM, eD, hz, _, e, he⟩ :=
    locallyPerfect_exists_arbitrarily_low_original_split R W hW E hE cutoff
  let D := (restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
  have : SchemeSheaf.IsFiniteLocallyFree W.toScheme (D.homology n) := hM
  let S := (CochainComplex.singleFunctor W.toScheme.Modules n).obj (D.homology n)
  let C := S⟦(-1 : ℤ)⟧
  let eC := ((toDerived W.toScheme).commShiftIso (-1 : ℤ)).app S
  let : PreservesBinaryBiproducts (toDerived W.toScheme) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let e' := e ≪≫ biprod.mapIso eC.symm (Iso.refl _) ≪≫
    ((toDerived W.toScheme).mapBiprod C E).symm
  refine ⟨K, P, n, hP, f, eK, hn, hM,
    strictPerfect_shift (single_strictPerfect_int (D.homology n) n) (-1), hz, e', ?_⟩
  have hp : ((toDerived W.toScheme).mapBiprod C E).inv ≫
      (toDerived W.toScheme).map (biprod.snd : C ⊞ E ⟶ E) = biprod.snd := by
    apply biprod.hom_ext' <;> simp [← Functor.map_comp]
  dsimp only [e', Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [hp]
  simp only [biprod.mapIso_hom, Iso.refl_hom]
  erw [biprod.map_snd]
  rw [Category.comp_id]
  exact he

end Quillen.PerfectComplexes.Affine
