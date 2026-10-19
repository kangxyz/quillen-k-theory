/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterSupportedCurrentStageInclusion
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedNegativeBottomComparison

/-!
# Original supported negative classes in the current parameter telescope

The original finite-bottom comparison is transported by the actual finite
section restriction and integral Spec-row isomorphism, then followed by the
independent current-stage inclusion. These maps are natural in coefficient
arrows. Their invertibility uses the proved current inclusion range, not an
inverse telescope comparison. The original Laurent quotient formula is retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSectionChangeIndex.SupportedTelescope SchemeNaturalSeed
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Original finite-bottom classes in the actual parameter finite stage. -/
def finiteNegativeKComparison (i : ℕ) :
    boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ≅
      (specUnder ⋙ (strictDiagramIterate squareFunctor i).obj (parameterDiagram f)) ⋙
        stableHomotopyFunctor (-(i : ℤ)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let v := Functor.whiskerRight (finiteRestriction f i) H
  let : ∀ a, IsIso (v.app a) := fun a =>
    finiteRestriction_isStableEquivalence f i a (-(i : ℤ))
  let : IsIso v := NatIso.isIso_of_isIso_app v
  exact boundedFlatCoefficientSupportedNegativeKComparison f i ≪≫
    (asIso v).symm ≪≫ (Functor.isoWhiskerRight (finiteIso f i) H).symm

/-- The finite comparison retains the original bottom map and both actual inverse maps. -/
theorem finiteNegativeKComparison_hom_app (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (finiteNegativeKComparison f i).hom.app a =
      (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app a ≫
        inv (I := finiteRestriction_isStableEquivalence f i a (-(i : ℤ)))
          ((stableHomotopyFunctor (-(i : ℤ))).map ((finiteRestriction f i).app a)) ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((finiteIso f i).inv.app a) := by
  simp only [finiteNegativeKComparison, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    NatTrans.comp_app, NatIso.isIso_inv_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app]

variable [CompactSpace P.left] [QuasiSeparatedSpace Q.left]

/-- Original negative groups, including degree zero, in the independent current telescope. -/
def currentNegativeKComparison (i : ℕ) :
    boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ≅
      (specUnder ⋙ currentTelescope (ParameterLaurentTrack.supportedTrack f.left)) ⋙
        stableHomotopyFunctor (-(i : ℤ)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let j := Functor.whiskerRight (Functor.whiskerLeft specUnder (currentStageInclusion f i)) H
  let : ∀ a, IsIso (j.app a) := fun a =>
    currentStageInclusion_isIso_of_le f i a (-(i : ℤ)) le_rfl
  let : IsIso j := NatIso.isIso_of_isIso_app j
  exact finiteNegativeKComparison f i ≪≫ asIso j

/-- The current class is the original finite class followed by the literal current inclusion. -/
theorem currentNegativeKComparison_hom_app (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison f i).hom.app a =
      (finiteNegativeKComparison f i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((currentStageInclusion f i).app (specUnder.obj a)) := rfl

/-- The original Laurent quotient formula is preserved before entering the current telescope. -/
@[reassoc]
theorem currentNegativeKComparison_π (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.supportedNegativeKFunctor i).map
        ((boundedFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
        (currentNegativeKComparison f (i + 1)).hom.app a =
    (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor _).obj a) ≫
      (Quillen.Bass.TwoChart.contractionπ (underToLaurent _) (underToLaurentInvert _)
        (boundedFlatCoefficientSupportedBassDiagram f i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
      (boundedFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a ≫
      inv (I := finiteRestriction_isStableEquivalence f (i + 1) a (-((i + 1 : ℕ) : ℤ)))
        ((stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
          ((finiteRestriction f (i + 1)).app a)) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map ((finiteIso f (i + 1)).inv.app a) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((currentStageInclusion f (i + 1)).app (specUnder.obj a)) := by
  rw [currentNegativeKComparison_hom_app, finiteNegativeKComparison_hom_app]
  simpa only [Category.assoc] using
    (boundedFlatCoefficientSupportedNegativeKComparison_π f i a) =≫
      (inv (I := finiteRestriction_isStableEquivalence f (i + 1) a (-((i + 1 : ℕ) : ℤ)))
        ((stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
          ((finiteRestriction f (i + 1)).app a)) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map ((finiteIso f (i + 1)).inv.app a) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((currentStageInclusion f (i + 1)).app (specUnder.obj a)))

end Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
