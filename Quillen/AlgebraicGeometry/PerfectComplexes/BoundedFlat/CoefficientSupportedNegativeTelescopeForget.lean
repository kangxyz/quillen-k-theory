/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedNegativeForgetComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFineTelescopeComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassFineTelescopeComparison

/-!
# Original negative support forgetting in the actual fine telescopes

The existing supported and ambient negative-group comparisons commute with the original
forget-support telescope map. The proof retains the finite-bottom square and the literal
stage-inclusion square. Original Laurent quotients and actual telescope inclusions are
unchanged. The ambient scheme is qcqs and the removed open is compact.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The original negative support-forgetting map agrees with the actual fine-telescope map. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app
    (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKForgetNat i).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q i).hom.app a =
    (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a) := by
  rw [boundedFlatCoefficientAmbientNegativeKTelescopeComparison_hom_app,
    boundedFlatCoefficientSupportedNegativeKTelescopeComparison_hom_app,
    ← Category.assoc, boundedFlatCoefficientSupportedNegativeKComparison_forget_app]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun h ↦ (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app a ≫
    (stableHomotopyFunctor (-(i : ℤ))).map h)
    (NatTrans.congr_app (boundedFlatCoefficientSupportedBassTelescopeInclusion_forget f i) a).symm

/-- The same actual forget-support square is natural on the full coefficient category. -/
theorem boundedFlatCoefficientSupportedNegativeKTelescopeComparison_forget (i : ℕ) :
    Functor.whiskerLeft (boundedFlatCoefficientQuasiCompactOpenPairRow f)
        (Bass.supportedNegativeKForgetNat i) ≫
      (boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q i).hom =
    (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom ≫
      Functor.whiskerRight (boundedFlatCoefficientSupportedBassTelescopeForget f)
        (stableHomotopyFunctor (-(i : ℤ))) := by
  apply NatTrans.ext
  funext a
  exact boundedFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app f i a

/-- The unchanged Laurent quotient keeps its actual supported stage inclusion after forgetting. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedNegativeKTelescopeComparison_π_forget
    (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
        ((boundedFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
      (Bass.supportedNegativeKForgetNat (i + 1)).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q (i + 1)).hom.app a =
    (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientSupportedBassDiagram f i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
      (boundedFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f (i + 1)).app a) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a) := by
  rw [boundedFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app]
  exact boundedFlatCoefficientSupportedNegativeKTelescopeComparison_π_assoc f i a _

end Quillen.PerfectComplexes
