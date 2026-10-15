/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.BassNegativeGroups

/-!
# Original K-zero at the bottom of the native ambient Bass family

The original perfect K-zero functor on quasi-compact schemes is naturally the
actual finite stage-zero group. The comparison uses the existing original
normalized evaluation and bounded-flat inclusion, retaining arbitrary coefficient
pullbacks. Polynomial/Laurent geometry and successor comparisons remain separate. This
comparison uses the original perfect K-zero and does not redefine the original
negative groups. Supported comparisons and TT identification remain separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes

/-- Original perfect K-zero computes degree zero of the original localized spectrum. -/
def perfectKZeroLocalizedStableIso (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ) :
    Bass.perfectKZeroFunctor.obj X ≅
      (PerfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor 0).obj X :=
  (originalKStableEquiv (perfectWaldhausen X.unop.obj) 0).toAddCommGrpIso

/-- The comparison preserves every original derived-pullback K-zero map. -/
@[reassoc]
theorem perfectKZeroLocalizedStableIso_naturality
    {X Y : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ} (f : X ⟶ Y) :
    Bass.perfectKZeroFunctor.map f ≫ (perfectKZeroLocalizedStableIso Y).hom =
      (perfectKZeroLocalizedStableIso X).hom ≫
        (PerfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor 0).map f := by
  ext a
  exact perfectLocalizedPullback_originalK_naturality f.unop.hom 0 a.toMul

/-- The unchanged original scheme K-zero functor retains all its original maps. -/
def perfectKZeroLocalizedStableNatIso :
    Bass.perfectKZeroFunctor.{u} ≅
      PerfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor 0 :=
  NatIso.ofComponents perfectKZeroLocalizedStableIso
    (fun f ↦ perfectKZeroLocalizedStableIso_naturality f)

/-- Original perfect K-zero on each compact native fiber is the actual stage-zero bottom. -/
def boundedFlatCoefficientAmbientBassBottomZeroNatIso
    {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] :
    boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.perfectKZeroFunctor ≅
      boundedFlatCoefficientAmbientBassDiagram P 0 ⋙ stableHomotopyFunctor 0 :=
  Functor.isoWhiskerLeft (boundedFlatCoefficientQuasiCompactRow P)
      perfectKZeroLocalizedStableNatIso ≪≫
    (Functor.isoWhiskerRight (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P)
      (localizedStableHomotopyFunctor 0)).symm

/-- The comparison keeps the actual evaluation and original perfect K-zero representative. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientBassBottomZeroNatIso_evaluation
    {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R) :
    (boundedFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a ≫
      (stableHomotopyFunctor 0).map
        (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)) =
    (perfectKZeroLocalizedStableIso ((boundedFlatCoefficientQuasiCompactRow P).obj a)).hom := by
  let A := Functor.isoWhiskerLeft (boundedFlatCoefficientQuasiCompactRow P)
    perfectKZeroLocalizedStableNatIso
  let E := Functor.isoWhiskerRight
    (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P)
    (localizedStableHomotopyFunctor 0)
  have hE : E.hom.app a = (stableHomotopyFunctor 0).map
      (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)) := by
    simp only [E, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso_hom_app,
      localizedStableHomotopyFunctor_original_map]
  change (A.hom.app a ≫ E.inv.app a) ≫ _ = _
  rw [← hE, Category.assoc, ← NatTrans.comp_app, E.inv_hom_id,
    NatTrans.id_app]
  exact Category.comp_id (A.hom.app a)

end Quillen.PerfectComplexes
