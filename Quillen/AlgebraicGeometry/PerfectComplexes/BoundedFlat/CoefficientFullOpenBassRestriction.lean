/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFullOpenBassLocalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeMapNaturality

/-!
# Original restriction in full-open Bass localization

The fine full-open row, its Laurent seed and its telescope are the original
ambient constructions on the open scheme. The constructed ambient-to-full-open
localization map equals the original scheme restriction on every telescope
cylinder. Consequently the unchanged Bass negative-class maps carry original
negative-group pullback to this actual localization map.

Only the final negative-group comparison requires compact source and target.
The localization equality requires just the stated open immersion; the literal row
identities need no such assumption. No comparison
between coarse and fine finite stages is asserted.
-/

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)

/-- The original fine full-open Model row is the original ambient row of the open scheme. -/
theorem boundedFlatCoefficientFullOpenModelFunctor_eq_section :
    boundedFlatCoefficientFullOpenModelFunctor f = boundedFlatCoefficientSectionModelRow P := rfl

/-- The full-open Laurent unit and coefficient naturality are the original ambient action. -/
theorem boundedFlatCoefficientFullOpenLaurentAction_eq_ambient :
    boundedFlatCoefficientFullOpenLaurentAction f = boundedFlatCoefficientAmbientLaurentAction P :=
  rfl

/-- The full-open seed retains the original ambient seed, including its whole scalar track. -/
theorem boundedFlatCoefficientFullOpenBassSeed_eq_ambient :
    boundedFlatCoefficientFullOpenBassSeed f = boundedFlatCoefficientAmbientBassSeed P := rfl

/-- The original fine full-open telescope is the ambient telescope of the open scheme. -/
theorem boundedFlatCoefficientFullOpenBassTelescopeFunctor_eq_ambient :
    boundedFlatCoefficientFullOpenBassTelescopeFunctor f =
      boundedFlatCoefficientAmbientBassTelescopeFunctor P := rfl

variable [IsOpenImmersion f.left]

/-- Every original cylinder identifies the actual localization map with scheme restriction. -/
theorem boundedFlatCoefficientAmbientBassTelescopeFullOpen_eq_schemeRestriction :
    boundedFlatCoefficientAmbientBassTelescopeFullOpen f =
      boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro k i s x
  change Telescope.cylinder
      (fun j ↦ (boundedFlatCoefficientAmbientBassDiagram P j).obj a)
      (fun j ↦ (boundedFlatCoefficientAmbientBassTransition P j).app a) k i
      (s, ((boundedFlatCoefficientOpenBassRestriction f i).app a).map k
        (((boundedFlatCoefficientAmbientBassOpen f i).app a).map k x)) =
    Telescope.cylinder
      (fun j ↦ (boundedFlatCoefficientAmbientBassDiagram P j).obj a)
      (fun j ↦ (boundedFlatCoefficientAmbientBassTransition P j).app a) k i
      (s, (((strictDiagramIterate
        (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor R) i).map
        (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f)).app a).map k x)
  exact congrArg (fun y ↦ Telescope.cylinder
    (fun j ↦ (boundedFlatCoefficientAmbientBassDiagram P j).obj a)
    (fun j ↦ (boundedFlatCoefficientAmbientBassTransition P j).app a) k i (s, y))
      (congrArg (fun η ↦ (η.app a).map k x)
        (boundedFlatCoefficientAmbientBassFullOpen_eq_original f i))

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The original negative pullback square uses the actual full-open localization map. -/
theorem boundedFlatCoefficientAmbientBassNegativeMap_fullOpen (i : ℕ) :
    boundedFlatCoefficientOriginalNegativeKRestriction f i ≫
      boundedFlatCoefficientAmbientBassNegativeMap P i =
    boundedFlatCoefficientAmbientBassNegativeMap Q i ≫
      Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeFullOpen f)
        (stableHomotopyFunctor (-(i : ℤ))) := by
  rw [boundedFlatCoefficientAmbientBassTelescopeFullOpen_eq_schemeRestriction]
  exact boundedFlatCoefficientAmbientBassNegativeMap_schemeRestriction f i

/-- Component form retains the original negative-group pullback and localization arrow. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientBassNegativeMap_fullOpen_app (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).map
        (AlgebraicGeometry.Scheme.quasiCompactSchemeProperty.homMk
          (AlgebraicGeometry.Scheme.BaseChange.Coefficients.schemeMap f a)).op ≫
      (boundedFlatCoefficientAmbientBassNegativeMap P i).app a =
    (boundedFlatCoefficientAmbientBassNegativeMap Q i).app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) :=
  congrArg (fun η ↦ η.app a) (boundedFlatCoefficientAmbientBassNegativeMap_fullOpen f i)

end Quillen.PerfectComplexes
