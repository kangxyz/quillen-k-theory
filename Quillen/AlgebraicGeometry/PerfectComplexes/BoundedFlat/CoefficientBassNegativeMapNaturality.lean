/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSchemeRestrictionTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassOriginalNegativeNaturality

/-!
# Scheme restriction of the original native telescope class map

For a scheme-over-base arrow with compact source and target, the original Bass
negative-class map commutes with the actual native ambient telescope restriction.
The map retains the unchanged finite comparison and literal stage inclusion;
no seed stabilization, telescope bijectivity or classical TT identification is
asserted.
-/

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)

/-- The literal finite signed-bottom restriction retains the original stage-inclusion face. -/
theorem boundedFlatCoefficientAmbientBassBottomTelescopeInclusion_schemeRestriction (i : ℕ) :
    boundedFlatCoefficientAmbientBassBottomSchemeRestriction f i ≫
      Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeInclusion P i)
        (stableHomotopyFunctor (-(i : ℤ))) =
    Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeInclusion Q i)
        (stableHomotopyFunctor (-(i : ℤ))) ≫
      Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f)
        (stableHomotopyFunctor (-(i : ℤ))) := by
  apply NatTrans.ext
  funext a
  let H := stableHomotopyFunctor (-(i : ℤ))
  change H.map ((boundedFlatCoefficientAmbientBassSchemeRestriction f i).app a) ≫
      H.map ((boundedFlatCoefficientAmbientBassTelescopeInclusion P i).app a) =
    H.map ((boundedFlatCoefficientAmbientBassTelescopeInclusion Q i).app a) ≫
      H.map ((boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f).app a)
  calc
    _ = H.map ((boundedFlatCoefficientAmbientBassSchemeRestriction f i).app a ≫
        (boundedFlatCoefficientAmbientBassTelescopeInclusion P i).app a) :=
      (H.map_comp _ _).symm
    _ = H.map ((boundedFlatCoefficientAmbientBassTelescopeInclusion Q i).app a ≫
        (boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f).app a) :=
      congrArg H.map (congrArg (fun η ↦ η.app a)
        (boundedFlatCoefficientAmbientBassTelescopeInclusion_schemeRestriction f i)).symm
    _ = _ := H.map_comp _ _

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Original negative classes retain actual scheme pullback in the original native telescope. -/
theorem boundedFlatCoefficientAmbientBassNegativeMap_schemeRestriction (i : ℕ) :
    boundedFlatCoefficientOriginalNegativeKRestriction f i ≫
      boundedFlatCoefficientAmbientBassNegativeMap P i =
    boundedFlatCoefficientAmbientBassNegativeMap Q i ≫
      Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f)
        (stableHomotopyFunctor (-(i : ℤ))) := by
  rw [boundedFlatCoefficientAmbientBassNegativeMap,
    boundedFlatCoefficientAmbientBassNegativeMap, ← Category.assoc,
    boundedFlatCoefficientAmbientNegativeKComparison_schemeRestriction,
    Category.assoc, boundedFlatCoefficientAmbientBassBottomTelescopeInclusion_schemeRestriction,
    Category.assoc]

/-- Component form exhibits the original group pullback and the actual telescope map. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientBassNegativeMap_schemeRestriction_app
    (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).map
        (AlgebraicGeometry.Scheme.quasiCompactSchemeProperty.homMk
          (AlgebraicGeometry.Scheme.BaseChange.Coefficients.schemeMap f a)).op ≫
      (boundedFlatCoefficientAmbientBassNegativeMap P i).app a =
    (boundedFlatCoefficientAmbientBassNegativeMap Q i).app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f).app a) :=
  congrArg (fun η ↦ η.app a)
    (boundedFlatCoefficientAmbientBassNegativeMap_schemeRestriction f i)

end Quillen.PerfectComplexes
