/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedKZeroForgetComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedContractionForget
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedNegativeBottomComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassOriginalNegativeComparison

/-!
# Original negative support forgetting at every actual finite bottom

The unchanged supported and ambient negative-group comparisons commute with the original
forget-support map. The induction uses actual coefficient contraction transport, its
original group-map naturality and the existing finite-stage forget square. It does not
choose replacement comparisons or assume injectivity of any support-forgetting map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Every original negative support-forgetting map is the existing finite-bottom map. -/
theorem boundedFlatCoefficientSupportedNegativeKComparison_forget (i : ℕ) :
    Functor.whiskerLeft (boundedFlatCoefficientQuasiCompactOpenPairRow f)
        (Bass.supportedNegativeKForgetNat i) ≫
      (boundedFlatCoefficientAmbientNegativeKComparison Q i).hom =
    (boundedFlatCoefficientSupportedNegativeKComparison f i).hom ≫
      Functor.whiskerRight (boundedFlatCoefficientSupportedBassForget f i)
        (stableHomotopyFunctor (-(i : ℤ))) := by
  induction i with
  | zero =>
      apply NatTrans.ext
      funext a
      exact boundedFlatCoefficientSupportedBassBottomZeroIso_forget f a
  | succ i ih =>
      let B := contractionFunctor (underToLaurent R) (underToLaurentInvert R)
      let α := Functor.whiskerLeft (boundedFlatCoefficientQuasiCompactOpenPairRow f)
        (Bass.supportedNegativeKForgetNat i)
      let α' := Functor.whiskerLeft (boundedFlatCoefficientQuasiCompactOpenPairRow f)
        (Bass.supportedNegativeKForgetNat (i + 1))
      let β := Functor.whiskerRight (boundedFlatCoefficientSupportedBassForget f i)
        (stableHomotopyFunctor (-(i : ℤ)))
      let β' := Functor.whiskerRight (boundedFlatCoefficientSupportedBassForget f (i + 1))
        (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)))
      let γS := boundedFlatCoefficientSupportedNegativeKComparison f i
      let γA := boundedFlatCoefficientAmbientNegativeKComparison Q i
      let τS := boundedFlatCoefficientSupportedContractionTransportIso f
        (Bass.supportedNegativeKFunctor i)
      let τA := boundedFlatCoefficientContractionTransportIso Q (Bass.negativeKFunctor i)
      let bS := boundedFlatCoefficientSupportedBassBottomContractionIso f i
      let bA := boundedFlatCoefficientAmbientBassBottomContractionIso Q i
      have hτ : τS.hom ≫ α' = B.map α ≫ τA.hom :=
        boundedFlatCoefficientSupportedContractionTransportIso_negativeForget f i
      have hβ : B.map β ≫ bA.hom = bS.hom ≫ β' := by
        apply NatTrans.ext
        funext a
        exact boundedFlatCoefficientSupportedBassBottomContractionIso_forget f i a
      have hi : α ≫ γA.hom = γS.hom ≫ β := ih
      apply (cancel_epi τS.hom).mp
      change τS.hom ≫ (α' ≫ (τA.inv ≫ B.map γA.hom ≫ bA.hom)) =
        τS.hom ≫ ((τS.inv ≫ B.map γS.hom ≫ bS.hom) ≫ β')
      rw [← Category.assoc τS.hom α', hτ]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ← B.map_comp, hi, B.map_comp]
      simp only [Category.assoc]
      rw [hβ]

/-- The component square retains the actual original finite-stage spectrum inclusion. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedNegativeKComparison_forget_app (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKForgetNat i).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (boundedFlatCoefficientAmbientNegativeKComparison Q i).hom.app a =
    (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedFlatCoefficientSupportedBassForget f i).app a) :=
  NatTrans.congr_app (boundedFlatCoefficientSupportedNegativeKComparison_forget f i) a

/-- Original supported Laurent representatives keep their cone inclusion after forgetting support.
-/
@[reassoc]
theorem boundedFlatCoefficientSupportedNegativeKComparison_π_cone_forget
    (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
        ((boundedFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
      (Bass.supportedNegativeKForgetNat (i + 1)).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (boundedFlatCoefficientAmbientNegativeKComparison Q (i + 1)).hom.app a =
    (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (mappingConeInclusion (StrictSquare.comparison
          ((boundedFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
            (laurentUnderSquare R a)))) ≫
      (Quillen.KTheory.Bass.modelDiagramBottomSuccessorIso
        (boundedFlatCoefficientSupportedModelFunctor f) i).inv.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientSupportedBassForget f (i + 1)).app a) := by
  rw [boundedFlatCoefficientSupportedNegativeKComparison_forget_app]
  exact boundedFlatCoefficientSupportedNegativeKComparison_π_cone_assoc f i a _

end Quillen.PerfectComplexes
