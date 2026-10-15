/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenGrading
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionKComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.GlobalCofinality

/-!
# Cofinality of the actual supported native coefficient restriction

The original supported evaluation equivalence compares the native fine and
relative-open structures with their actual bounded-flat geometric structures.
The original restriction square then transports the installed supported
perfect cofinality theorem to the same r_Z. Both endpoints are compact, the
ambient endpoint is quasi-separated, and the auxiliary support complement is
compact. No density, image, flatness or localization premise is supplied.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedFlatCoefficientSupportedEvaluation
  boundedFlatCoefficientSupportedSectionEquivalence

/-- The literal forward supported equivalence is exact for the original fine structures. -/
theorem boundedFlatCoefficientSupportedSectionEquivalence_functor_exact
    {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsExact (boundedFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedFlatPerfectSupportedWaldhausen j).cof (boundedFlatPerfectSupportedWaldhausen j).weq
      (boundedFlatCoefficientSupportedSectionEquivalence j).functor := by
  rw [boundedFlatCoefficientSupportedSectionEquivalence_functor]
  exact boundedFlatCoefficientSupportedEvaluation_exact j

/-- Original supported evaluation computes the actual fine supported fiber K-groups. -/
def boundedFlatCoefficientSupportedSectionKEquiv {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] (n : ℕ) :
    (boundedFlatCoefficientSupportedSectionWaldhausen j).K n ≃*
      (boundedFlatPerfectSupportedWaldhausen j).K n :=
  boundedFlatCoefficientEvaluationKEquiv (boundedFlatCoefficientSupportedSectionWaldhausen j)
    (boundedFlatPerfectSupportedWaldhausen j) (boundedFlatCoefficientSupportedSectionEquivalence j)
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact j)
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact j) n

/-- This comparison keeps the original supported evaluated object's honest K-zero class. -/
theorem boundedFlatCoefficientSupportedSectionKEquiv_objectClass
    {i : Index R} {U : Scheme.{u}} (j : U ⟶ space i) [IsOpenImmersion j]
    (S : BoundedFlatCoefficientSupportedSections j) :
    boundedFlatCoefficientSupportedSectionKEquiv j 0
        ((boundedFlatCoefficientSupportedSectionWaldhausen j).kZeroObjectClass S) =
      (boundedFlatPerfectSupportedWaldhausen j).kZeroObjectClass
        ((boundedFlatCoefficientSupportedEvaluation j).obj S) := by
  let W := boundedFlatPerfectSupportedWaldhausen j
  apply (W.smallModelKEquiv 0).injective
  change W.smallModelKEquiv 0 ((W.smallModelKEquiv 0).symm
    (KMap ((boundedFlatCoefficientSupportedSectionEquivalence_functor_exact j).comp
      W.smallModel_up_exact) 0
      ((boundedFlatCoefficientSupportedSectionWaldhausen j).kZeroObjectClass S))) = _
  rw [MulEquiv.apply_symm_apply, Structure.smallModelKEquiv_objectClass]
  rw [← boundedFlatCoefficientSupportedSectionEquivalence_functor j]
  exact KMap_kZeroObjectClass
    ((boundedFlatCoefficientSupportedSectionEquivalence_functor_exact j).comp
      W.smallModel_up_exact) S

private theorem inverse_weq_of_equivalence {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) (V : Structure C) (W : Structure D)
    (h : ∀ {A B : C} (p : A ⟶ B), V.weq p ↔ W.weq (e.functor.map p))
    {A B : D} (p : A ⟶ B) (hp : W.weq p) : V.weq (e.inverse.map p) := by
  apply (h _).mpr
  have hm : e.functor.map (e.inverse.map p) =
      e.counitIso.hom.app _ ≫ p ≫ e.counitIso.inv.app _ := by
    simpa only [Functor.comp_map, Functor.id_map, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id] using
      congrArg (fun k ↦ k ≫ e.counitIso.inv.app _) (e.counitIso.hom.naturality p)
  rw [hm]
  exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance)
    (W.weq.comp_mem _ _ hp (W.weq_iso _ inferInstance))

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Supported coarse evaluation is exact by the proved correspondence of the original weak maps.
-/
theorem boundedFlatCoefficientSupportedOpenEvaluation_coarse_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).cof
      (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).weq
      (boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι)
    where
  zero := (boundedFlatCoefficientSupportedEvaluation_exact
    (boundedFlatCoefficientSupportOpen Q T a).ι).zero
  cofibration := (boundedFlatCoefficientSupportedEvaluation_exact
    (boundedFlatCoefficientSupportOpen Q T a).ι).cofibration
  weak p hp := (boundedFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a p).mp hp
  pushout := (boundedFlatCoefficientSupportedEvaluation_exact
    (boundedFlatCoefficientSupportOpen Q T a).ι).pushout

/-- The inverse of original supported evaluation is exact for the same relative-open structures.
-/
theorem boundedFlatCoefficientSupportedOpenEquivalence_inverse_exact (a : Under R) :
    IsExact
      (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).cof
      (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).weq
      (boundedFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedFlatCoefficientSupportedSectionEquivalence
        (boundedFlatCoefficientSupportOpen Q T a).ι).inverse where
  zero := (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
    (boundedFlatCoefficientSupportOpen Q T a).ι).zero
  cofibration := (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
    (boundedFlatCoefficientSupportOpen Q T a).ι).cofibration
  weak p hp := inverse_weq_of_equivalence
    (boundedFlatCoefficientSupportedSectionEquivalence (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedOpenWaldhausen f T a)
    (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))
    (fun q ↦ by
      rw [boundedFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a q) p hp
  pushout := (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
    (boundedFlatCoefficientSupportOpen Q T a).ι).pushout

/-- The literal forward supported equivalence is exact for the actual coarse structures. -/
theorem boundedFlatCoefficientSupportedOpenEquivalence_functor_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).cof
      (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).weq
      (boundedFlatCoefficientSupportedSectionEquivalence
        (boundedFlatCoefficientSupportOpen Q T a).ι).functor := by
  rw [boundedFlatCoefficientSupportedSectionEquivalence_functor]
  exact boundedFlatCoefficientSupportedOpenEvaluation_coarse_exact f T a

/-- Original supported evaluation computes the actual bounded-flat relative-open K-groups. -/
def boundedFlatCoefficientSupportedOpenKEquiv (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientSupportedOpenWaldhausen f T a).K n ≃*
      (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).K n :=
  boundedFlatCoefficientEvaluationKEquiv (boundedFlatCoefficientSupportedOpenWaldhausen f T a)
    (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))
    (boundedFlatCoefficientSupportedSectionEquivalence (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedOpenEquivalence_functor_exact f T a)
    (boundedFlatCoefficientSupportedOpenEquivalence_inverse_exact f T a) n

/-- The genuine supported evaluation square retains the original geometric restriction K-map. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_KComparison (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedOpenWaldhausen f T a).K n) :
    boundedFlatCoefficientSupportedSectionKEquiv (boundedFlatCoefficientOpenSupportOpen f T a).ι n
        (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a) n x) =
      boundedFlatPerfectSupportedOpenKRestrict (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) n
        (boundedFlatCoefficientSupportedOpenKEquiv f T a n x) :=
  boundedFlatCoefficientEvaluationKEquiv_natural
    (boundedFlatCoefficientSupportedOpenWaldhausen f T a)
    (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))
    (boundedFlatCoefficientSupportedSectionEquivalence (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedOpenEquivalence_functor_exact f T a)
    (boundedFlatCoefficientSupportedOpenEquivalence_inverse_exact f T a)
    (boundedFlatCoefficientSupportedSectionWaldhausen
      (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatPerfectSupportedWaldhausen (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence
      (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact
      (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
      (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedOpenRestriction_exact f T a)
    (boundedFlatPerfectSupportedOpenRestriction_exact (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))
    (by
      simp only [boundedFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedFlatCoefficientSupportedOpenRestrictionEvaluationIso f T a) n x

/-- The native supported open evaluation followed by the genuine supported perfect comparison.
-/
def boundedFlatCoefficientSupportedFullOpenPerfectKEquiv [CompactSpace P.left]
    (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientSupportedSectionWaldhausen
      (boundedFlatCoefficientOpenSupportOpen f T a).ι).K n ≃*
      (perfectSupportedWaldhausen (boundedFlatCoefficientOpenSupportOpen f T a).ι).K n := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  exact (boundedFlatCoefficientSupportedSectionKEquiv
    (boundedFlatCoefficientOpenSupportOpen f T a).ι n).trans
    (boundedFlatPerfectSupportedKEquiv (boundedFlatCoefficientOpenSupportOpen f T a).ι n)

omit [IsOpenImmersion f.left] in
/-- The supported perfect comparison retains the original supported evaluated K-zero class. -/
theorem boundedFlatCoefficientSupportedFullOpenPerfectKEquiv_objectClass [CompactSpace P.left]
    (a : Under R) (S : BoundedFlatCoefficientSupportedOpenSections f T a) :
    boundedFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0
        ((boundedFlatCoefficientSupportedSectionWaldhausen
          (boundedFlatCoefficientOpenSupportOpen f T a).ι).kZeroObjectClass S) =
      (perfectSupportedWaldhausen (boundedFlatCoefficientOpenSupportOpen f T a).ι).kZeroObjectClass
        ((boundedFlatCoefficientSupportedFullOpenPerfectEvaluation f T a).obj S) := by
  change boundedFlatPerfectSupportedToPerfectSupportedKMap
    (boundedFlatCoefficientOpenSupportOpen f T a).ι 0
      (boundedFlatCoefficientSupportedSectionKEquiv
        (boundedFlatCoefficientOpenSupportOpen f T a).ι 0
        ((boundedFlatCoefficientSupportedSectionWaldhausen
          (boundedFlatCoefficientOpenSupportOpen f T a).ι).kZeroObjectClass S)) = _
  rw [boundedFlatCoefficientSupportedSectionKEquiv_objectClass]
  exact KMap_kZeroObjectClass
    (boundedFlatPerfectSupportedInclusion_exact (boundedFlatCoefficientOpenSupportOpen f T a).ι) _

/-- Original supported coarse evaluation followed by the genuine relative supported comparison.
-/
def boundedFlatCoefficientSupportedOpenPerfectKEquiv [CompactSpace Q.left]
    (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientSupportedOpenWaldhausen f T a).K n ≃*
      (perfectSupportedOpenWeakWaldhausen (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).K n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedFlatCoefficientSupportedOpenKEquiv f T a n).trans
    (boundedFlatPerfectSupportedOpenKEquiv (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) n)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The unchanged native r_Z compares with the original supported perfect restriction. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_perfectKComparison
    (a : Under R) (n : ℕ) (x : (boundedFlatCoefficientSupportedOpenWaldhausen f T a).K n) :
    boundedFlatCoefficientSupportedFullOpenPerfectKEquiv f T a n
        (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a) n x) =
      perfectSupportedOpenKRestrict (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) n
        (boundedFlatCoefficientSupportedOpenPerfectKEquiv f T a n x) := by
  change boundedFlatPerfectSupportedToPerfectSupportedKMap
    (boundedFlatCoefficientOpenSupportOpen f T a).ι n
      (boundedFlatCoefficientSupportedSectionKEquiv
        (boundedFlatCoefficientOpenSupportOpen f T a).ι n
        (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a) n x)) =
    perfectSupportedOpenKRestrict (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) n
      (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) n
        (boundedFlatCoefficientSupportedOpenKEquiv f T a n x))
  rw [boundedFlatCoefficientSupportedOpenRestriction_KComparison]
  exact (DFunLike.congr_fun (boundedFlatPerfectSupportedOpenKRestrict_comparison
    (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) n)
    (boundedFlatCoefficientSupportedOpenKEquiv f T a n x)).symm

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- Installed supported qcqs cofinality proves the original native r_Z injective in every degree.
-/
theorem boundedFlatCoefficientSupportedOpenRestriction_KMap_injective (a : Under R) (n : ℕ) :
    Function.Injective (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a) n) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  let : CompactSpace (boundedFlatCoefficientSupportOpen Q T a) :=
    boundedFlatCoefficientSupportOpen_compactSpace Q T a
  have hT : IsCompact (boundedFlatCoefficientSupportOpen Q T a : Set (space (op Q, a))) :=
    isCompact_iff_compactSpace.mpr
      (show CompactSpace (boundedFlatCoefficientSupportOpen Q T a) from inferInstance)
  intro x y hxy
  apply (boundedFlatCoefficientSupportedOpenPerfectKEquiv f T a n).injective
  apply qcqs_perfectSupportedOpenKRestrict_injective (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a)
    hT n
  rw [← boundedFlatCoefficientSupportedOpenRestriction_perfectKComparison f T a n x,
    ← boundedFlatCoefficientSupportedOpenRestriction_perfectKComparison f T a n y, hxy]

/-- Actual supported r_Z is injective on the honest degree-zero endpoint. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_KMap_zero_injective (a : Under R) :
    Function.Injective (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a) 0) :=
  boundedFlatCoefficientSupportedOpenRestriction_KMap_injective f T a 0

/-- Installed supported cofinality proves the same original r_Z bijective in positive degrees. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_KMap_succ_bijective
    (a : Under R) (n : ℕ) :
    Function.Bijective (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a) (n + 1))
    := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  let : CompactSpace (boundedFlatCoefficientSupportOpen Q T a) :=
    boundedFlatCoefficientSupportOpen_compactSpace Q T a
  have hT : IsCompact (boundedFlatCoefficientSupportOpen Q T a : Set (space (op Q, a))) :=
    isCompact_iff_compactSpace.mpr
      (show CompactSpace (boundedFlatCoefficientSupportOpen Q T a) from inferInstance)
  refine ⟨boundedFlatCoefficientSupportedOpenRestriction_KMap_injective f T a (n + 1), ?_⟩
  intro y
  obtain ⟨z, hz⟩ := (qcqs_perfectSupportedOpenKRestrict_succ_bijective (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a) hT
    n).surjective (boundedFlatCoefficientSupportedFullOpenPerfectKEquiv f T a (n + 1) y)
  refine ⟨(boundedFlatCoefficientSupportedOpenPerfectKEquiv f T a (n + 1)).symm z, ?_⟩
  apply (boundedFlatCoefficientSupportedFullOpenPerfectKEquiv f T a (n + 1)).injective
  rw [boundedFlatCoefficientSupportedOpenRestriction_perfectKComparison, MulEquiv.apply_symm_apply]
  exact hz

end Quillen.PerfectComplexes
