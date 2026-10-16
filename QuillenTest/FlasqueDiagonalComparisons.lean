/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalComparisons

/-! # Original diagonal comparison component and map consumers

The original installed unit/augmentation formula, its naturality on original
source maps, and the literal underlying pushed-total chain map are retained.
-/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
open AlgebraicGeometry.Scheme.Modules.Godement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal

namespace FlasqueDiagonalComparisonConsumers

local instance standardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The derived comparison component is the installed unit and original total augmentation. -/
theorem original_derived_component (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (EDerivedIso R v).hom.app K =
      DerivedCategory.Plus.Q.map ((EPlusIso R v).hom.app K) ≫
      (derivedPushforwardPlusUnit (relativeSecond R)).app
        ((godementTotalPlus (relativeSquare R)).obj
          ((coefficient R v).mapCochainComplexPlus.obj
            ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K))) ≫
      (asIso (godementTotalDerivedAugmentation (relativeSecond R))).inv.app
        ((coefficient R v).mapCochainComplexPlus.obj
          ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K)) :=
  EDerivedIso_hom_app R v K

/-- The literal component formula is natural on every original flasque source map. -/
theorem original_derived_component_naturality (R : CommRingCat.{u}) (v : Vertex)
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    (E R v ⋙ FlasqueCoefficients.toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q).map f ≫
        (EDerivedIso R v).hom.app L =
      DerivedCategory.Plus.Q.map ((EPlusIso R v).hom.app K) ≫
        (derivedPushforwardPlusUnit (relativeSecond R)).app
          ((godementTotalPlus (relativeSquare R)).obj
            ((coefficient R v).mapCochainComplexPlus.obj
              ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K))) ≫
        (asIso (godementTotalDerivedAugmentation (relativeSecond R))).inv.app
          ((coefficient R v).mapCochainComplexPlus.obj
            ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K)) ≫
        (FlasqueCoefficients.toPlus (twoChartLine R) ⋙
          (coefficient R v).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙
          derivedPushforwardPlus (relativeSecond R)).map f := by
  rw [(EDerivedIso R v).hom.naturality f, EDerivedIso_hom_app]
  simp only [Category.assoc]

/-- The whole original chain map uses exactly the first pullback/tensor, total and second image. -/
theorem original_underlying_chain_map (R : CommRingCat.{u}) (v : Vertex)
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    ((E R v).map f).hom =
      ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (relativeSquare R)).map
          (((coefficient R v).mapHomologicalComplex (.up ℤ)).map f.hom)) :=
  E_map R v f

end FlasqueDiagonalComparisonConsumers
