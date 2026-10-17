/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveTargetSingleSheet
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetCylinderNative

/-! The literal single-sheet factor of the original positive target action. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveTargetSingleSheet
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassSeedTargetChartAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (polynomialUnderFunctor R).obj a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor)

/-- Inclusion is precisely the existing first simplicial summand. -/
def inclusion : C(targetSpace P f D G ε,
    CoefficientBassSeedTargetCylinderMap.targetSpace P f D G ε ε) :=
  (SSet.toTop.map (left₁ (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G ε) (targetAnchor P f D G ε))).hom

/-- The original two half-clocks agree before any native evaluation. -/
theorem inclusion_nullTrack (t : I) (y : |parameterSSet D|) :
    inclusion P f D G ε (nullTrack P f D G ε false (t, y)) =
      CoefficientBassSeedTargetCylinderMap.nullTrack P f D G ε ε false (t, y) :=
  ContinuousMap.Homotopy.Evaluation.trans_compare
    (chartTrack P f D G ε false) (contraction P f D G ε false)
    (CoefficientBassSeedTargetCylinderMap.chartTrack P f D G ε ε false)
    (CoefficientBassSeedTargetCylinderMap.contraction P f D G ε ε false)
    (inclusion P f D G ε) id y y (fun _ ↦ rfl) (fun _ ↦ rfl) t

private theorem original_firstMap_cylinder (y : |parameterSSet D|) (t : I) :
    CoefficientBassSeedTargetCylinderMap.firstMap P f D G ε ε
      (DoubleCylinder.realizedCylinder
        (attaching D (Ja P (a := a)) G ε) (erase D) (y, ULift.up t)) =
      CoefficientBassSeedTargetCylinderMap.nullTrack P f D G ε ε false (t, y) :=
  DoubleCylinder.homotopyDesc_apply_cylinder
    (SSet.toTop.map (attaching D (Ja P (a := a)) G ε))
    (SSet.toTop.map (erase D)) (first_isPushout D (Ja P (a := a)) G ε)
    (CoefficientBassSeedTargetCylinderMap.laurentMap P f D G ε ε)
    (ContinuousMap.const _ (CoefficientBassSeedTargetCylinderMap.tip P f D G ε ε false))
    (CoefficientBassSeedTargetCylinderMap.nullTrack P f D G ε ε false) t y

/-- The factor equality follows from the actual first pushout, not its native image. -/
theorem inclusion_firstMap (z : |firstSimplicial D (Ja P (a := a)) G ε|) :
    inclusion P f D G ε (firstMap P f D G ε z) =
      CoefficientBassSeedTargetCylinderMap.firstMap P f D G ε ε z := by
  have h : TopCat.ofHom ((inclusion P f D G ε).comp (firstMap P f D G ε)) =
      TopCat.ofHom (CoefficientBassSeedTargetCylinderMap.firstMap P f D G ε ε) := by
    apply (first_isPushout D (Ja P (a := a)) G ε).hom_ext
    · apply ConcreteCategory.hom_ext
      rintro ⟨y, t⟩
      change inclusion P f D G ε (firstMap P f D G ε
        (DoubleCylinder.realizedCylinder (attaching D (Ja P (a := a)) G ε)
          (erase D) (y, ULift.up t.down))) =
        CoefficientBassSeedTargetCylinderMap.firstMap P f D G ε ε
          (DoubleCylinder.realizedCylinder (attaching D (Ja P (a := a)) G ε)
            (erase D) (y, ULift.up t.down))
      rw [firstMap_cylinder, original_firstMap_cylinder]
      exact inclusion_nullTrack P f D G ε t.down y
    · apply ConcreteCategory.hom_ext
      intro y
      have hs := ConcreteCategory.congr_hom
        ((first_isPushout D (Ja P (a := a)) G ε).inr_desc
          (DoubleCylinder.homotopyCylinderMap
            (SSet.toTop.map (attaching D (Ja P (a := a)) G ε))
            (SSet.toTop.map (erase D)) (laurentMap P f D G ε)
            (ContinuousMap.const _ (tip P f D G ε false)) (nullTrack P f D G ε false))
          (DoubleCylinder.homotopyEndMap (laurentMap P f D G ε)
            (ContinuousMap.const _ (tip P f D G ε false)))
          (DoubleCylinder.homotopyDescent_square
            (SSet.toTop.map (attaching D (Ja P (a := a)) G ε))
            (SSet.toTop.map (erase D)) (laurentMap P f D G ε)
            (ContinuousMap.const _ (tip P f D G ε false)) (nullTrack P f D G ε false))) y
      have ht := ConcreteCategory.congr_hom
        ((first_isPushout D (Ja P (a := a)) G ε).inr_desc
          (DoubleCylinder.homotopyCylinderMap
            (SSet.toTop.map (attaching D (Ja P (a := a)) G ε))
            (SSet.toTop.map (erase D))
            (CoefficientBassSeedTargetCylinderMap.laurentMap P f D G ε ε)
            (ContinuousMap.const _ (CoefficientBassSeedTargetCylinderMap.tip P f D G ε ε false))
            (CoefficientBassSeedTargetCylinderMap.nullTrack P f D G ε ε false))
          (DoubleCylinder.homotopyEndMap
            (CoefficientBassSeedTargetCylinderMap.laurentMap P f D G ε ε)
            (ContinuousMap.const _ (CoefficientBassSeedTargetCylinderMap.tip P f D G ε ε false)))
          (DoubleCylinder.homotopyDescent_square
            (SSet.toTop.map (attaching D (Ja P (a := a)) G ε))
            (SSet.toTop.map (erase D))
            (CoefficientBassSeedTargetCylinderMap.laurentMap P f D G ε ε)
            (ContinuousMap.const _ (CoefficientBassSeedTargetCylinderMap.tip P f D G ε ε false))
            (CoefficientBassSeedTargetCylinderMap.nullTrack P f D G ε ε false))) y
      exact (congrArg (inclusion P f D G ε) hs).trans (by cases y <;> exact ht.symm)
  exact ConcreteCategory.congr_hom h z

end Quillen.PerfectComplexes.CoefficientBassPositiveTargetSingleSheet
