/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGradingNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionRestrictionSeed
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramNullIdentityAction
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenDiagramLaurent
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionDiagramLaurent

/-!
# Identity-action interchange for the original section grading null

The actual canonical coefficient-natural null has full interchange with identity actions
that its original composite functor intertwines. The original section restriction supplies
this condition for every original ambient unit and its actual restriction to the open.
The same coefficient equation lifts this interchange to both original Laurent tracks.
Both independent times and all prespectrum levels are retained; Bass-seed compatibility
uses these same whole tracks.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The actual canonical section null has whole interchange for each compatible identity action. -/
theorem boundedFlatAffineFullOpenSectionGradingNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedFlatAffineSectionFullOpenModelTransformation j).app a)
      ((boundedFlatAffineFullOpenSectionGradingModelTransformation j).app a)
      ((boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((boundedFlatAffineSectionFullOpenModelTransformation j).app a)
    ((boundedFlatAffineFullOpenSectionGradingModelTransformation j).app a)
    (boundedFlatAffineFullOpenSectionZeroToGraded j a)
    (boundedFlatAffineFullOpenSectionZeroToGraded_weak j a)

/-- The original restriction and identity changeWeak retain the same forward scalar action. -/
theorem boundedFlatAffineFullOpenSectionGradingComposite_unit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    FunctorIdentityAutomorphism.Preserves
      (((boundedFlatAffineSectionFullOpenModelTransformation j).app a ≫
        (boundedFlatAffineFullOpenSectionGradingModelTransformation j).app a).functor)
      (boundedFlatAffineSectionUnitIso a.right r)
      (boundedFlatAffineFullOpenSectionUnitIso j a (boundedFlatAffineFullOpenUnit j a r)) := by
  change FunctorIdentityAutomorphism.Preserves
    (boundedFlatAffineFullOpenSectionRestriction j a ⋙ 𝟭 _)
    (boundedFlatAffineSectionUnitIso a.right r)
    (boundedFlatAffineFullOpenSectionUnitIso j a (boundedFlatAffineFullOpenUnit j a r))
  simpa only [Functor.comp_id] using
    boundedFlatAffineFullOpenSectionRestriction_unit_preserves j a r

/-- The same canonical null has full interchange with the actual original restricted unit. -/
theorem boundedFlatAffineFullOpenSectionGradingNull_unitInterchange
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedFlatAffineSectionOpenModelFunctor j).obj a)
      (T := (boundedFlatAffineFullOpenGradedSectionModelFunctor j).obj a)
      ((boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy a)
      (boundedFlatAffineSectionUnitIso a.right r)
      (boundedFlatAffineFullOpenSectionUnitIso j a (boundedFlatAffineFullOpenUnit j a r)) :=
  boundedFlatAffineFullOpenSectionGradingNull_unitCompatible j a
    (boundedFlatAffineSectionUnitIso a.right r)
    (boundedFlatAffineFullOpenSectionUnitIso j a (boundedFlatAffineFullOpenUnit j a r))
    (boundedFlatAffineFullOpenSectionGradingComposite_unit_preserves j a r)

/-- The same canonical null transports identity-action interchange along every coefficient. -/
theorem boundedFlatAffineFullOpenSectionGradingNull_coefficientUnitCompatible
    {a b : Under R} (f : a ⟶ b) :
    CoefficientIdentityActionCompatible
      (r := boundedFlatAffineSectionFullOpenModelTransformation j)
      (q := boundedFlatAffineFullOpenSectionGradingModelTransformation j)
      (boundedFlatAffineFullOpenSectionGradingDiagramNull j) f :=
  modelDiagramNull_coefficientCompatible
    (r := boundedFlatAffineSectionFullOpenModelTransformation j)
    (q := boundedFlatAffineFullOpenSectionGradingModelTransformation j)
    (boundedFlatAffineFullOpenSectionGradingDiagramNull j) f

attribute [local irreducible] boundedFlatAffineFullOpenOriginalEvaluation
  boundedFlatAffineOriginalEvaluation boundedFlatPerfectGlobalUnitIso
  boundedFlatPerfectPseudofunctor boundedFlatAffineFullOpenPseudofunctor

/-- The original forward Laurent unit is the accepted original scalar specialization. -/
private theorem gradingNullLaurentUnit_interchange (a : Under R) :
    IdentityActionInterchange
      ((boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy
        ((laurentUnderFunctor R).obj a))
      (boundedFlatAffineSectionLaurentUnitIso a.right)
      (boundedFlatAffineFullOpenSectionLaurentUnitIso j a) :=
  boundedFlatAffineFullOpenSectionGradingNull_unitInterchange j
    ((laurentUnderFunctor R).obj a) (laurentGlobalUnit a.right)

/-- Shared coefficient endpoints keep the original null projections in their given types. -/
private theorem gradingNullCoefficientTrack_interchange {a b : Under R} (f : a ⟶ b)
    (α : 𝟭 ((boundedFlatAffineSectionOpenModelFunctor j).obj b) ≅
      𝟭 ((boundedFlatAffineSectionOpenModelFunctor j).obj b))
    (β : 𝟭 ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).obj b) ≅
      𝟭 ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).obj b))
    (hU : IdentityActionInterchange
      ((boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy b) α β) :
    TrackInterchange
      ((boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy a)
      ((boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy b)
      (prespectrumIsoHomotopy ((boundedFlatAffineSectionOpenModelFunctor j).map f)
        (FunctorIdentityAutomorphism.onFunctor
          ((boundedFlatAffineSectionOpenModelFunctor j).map f).functor α))
      (prespectrumIsoHomotopy ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f)
        (FunctorIdentityAutomorphism.onFunctor
          ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f).functor β)) :=
  boundedFlatAffineFullOpenSectionGradingNull_coefficientUnitCompatible j f α β hU

/-- Both original Laurent tracks commute with the same canonical null at independent times. -/
theorem boundedFlatAffineFullOpenSectionGradingNull_laurentInterchange (a : Under R) :
    TrackInterchange
      ((boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy a)
      ((boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy
        ((laurentUnderFunctor R).obj a))
      (boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a)
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a) :=
  gradingNullCoefficientTrack_interchange (a := a) (b := (laurentUnderFunctor R).obj a)
    j ((laurentUnderCoefficient R).app a)
    (boundedFlatAffineSectionLaurentUnitIso a.right)
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j a)
    (gradingNullLaurentUnit_interchange j a)

/-- The unchanged null and Laurent action retain both times at each original point and level. -/
theorem boundedFlatAffineFullOpenSectionGradingNullHomotopy_laurent_apply
    (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineFullOpenSectionGradingNullHomotopy j
      ((laurentUnderFunctor R).obj a)).level n
        (s, (boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).level n
        (t, (boundedFlatAffineFullOpenSectionGradingNullHomotopy j a).level n (s, x)) :=
  boundedFlatAffineFullOpenSectionGradingNull_laurentInterchange j a n s t x

end Quillen.PerfectComplexes
