/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SelfBaseChangeSpan
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasquePhiColumns

/-! # Original source association with the actual positive Phi column before totalization -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints

/-- These two actual model wrappers have the same original flat pullback and chain maps. -/
lemma boundedFlatPullback_eq_native {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    SelfBaseChange.boundedFlatPullback f = FlasqueTwoSummands.boundedPullback f := rfl

/-- Original source association is proved BEFORE the chosen total is applied. -/
def sourcePositiveInputIso (R : CommRingCat.{u}) :
    SelfBaseChange.source R ≅ FlasqueCoefficients.G0 R ⋙ FlasqueTwoSummands.first R :=
  eqToIso (by rfl)

/-- Total is applied only after the actual original source association. -/
def sourcePositiveIso (R : CommRingCat.{u}) :
    SelfBaseChange.spanLeft R ≅ FlasqueCoefficients.G0 R ⋙ FlasquePhiColumns.positive R :=
  Functor.isoWhiskerRight (sourcePositiveInputIso R) (FlasqueBoundedBelow.total (twoChartLine R)) ≪≫
    Functor.associator (FlasqueCoefficients.G0 R) (FlasqueTwoSummands.first R)
      (FlasqueBoundedBelow.total (twoChartLine R))

/-- The actual original map comparison before totalization is the identity chain map. -/
lemma sourcePositiveInputIso_hom_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((sourcePositiveInputIso R).hom.app K).hom = 𝟙 ((SelfBaseChange.source R).obj K).obj := rfl

/-- Original chosen-zero K-map equality for the actual source and positive column. -/
lemma sourcePositive_KMap (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (SelfBaseChange.spanLeft_exact R) n =
      Waldhausen.KMap ((FlasqueCoefficients.G0_exact R).comp
        (FlasquePhiColumns.positive_exact R)) n :=
  Waldhausen.KMap_eq_of_iso (SelfBaseChange.spanLeft_exact R)
    ((FlasqueCoefficients.G0_exact R).comp (FlasquePhiColumns.positive_exact R))
    (sourcePositiveIso R) n

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
