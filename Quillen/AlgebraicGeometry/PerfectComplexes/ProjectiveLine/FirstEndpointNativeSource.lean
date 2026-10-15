/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FirstEndpointCoefficient
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands

/-! # Actual native first/negative source association before totalization -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
open FlasqueCoefficients
variable (R : CommRingCat.{u})

/-- Native and base-change bounded flat pullbacks retain the same original maps. -/
def nativeBoundedPullbackIso :
    FlasqueTwoSummands.boundedPullback (projection R) ≅
      SelfBaseChange.boundedFlatPullback (projection R) :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _ (Iso.refl _)) (fun f => by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom]
    exact Category.comp_id _ |>.trans (Category.id_comp _).symm)

/-- Literal native positive pullback of G0 and original base source S(M), before line tensor. -/
def nativeCoefficientSourceIso :
    G0 R ⋙ FlasqueTwoSummands.first R ≅ SelfBaseChange.source R :=
  Functor.isoWhiskerLeft (G0 R)
    (Functor.isoWhiskerLeft (FlasqueBoundedBelow.inclusion (Spec R))
      (nativeBoundedPullbackIso R))

/-- The actual source coefficient p_* T_P(K RIGHTtensor L), before the BASE shift. -/
def unshiftedCoefficient := resolved R ⋙ G0 R

/-- The actual native LEFT-line negative column with its original outer total. -/
def nativeNegative := FlasqueTwoSummands.second R ⋙
  FlasqueBoundedBelow.total (twoChartLine R)

/-- Exact identity of the original unshifted negative source, before either outer total. -/
def nativeFirstSourceIso :
    unshiftedCoefficient R ⋙ FlasqueTwoSummands.first R ≅
      resolved R ⋙ SelfBaseChange.source R :=
  Functor.associator (resolved R) (G0 R) (FlasqueTwoSummands.first R) ≪≫
    Functor.isoWhiskerLeft (resolved R) (nativeCoefficientSourceIso R)

/-- Original native LEFT tensor then actual T, exactly the negative unshifted column source. -/
def nativeNegativeSourceIso :
    unshiftedCoefficient R ⋙ nativeNegative R ≅
      (resolved R ⋙ SelfBaseChange.source R) ⋙
        (FlasqueTwoSummands.boundedNegativeTwist R ⋙
          FlasqueBoundedBelow.total (twoChartLine R)) :=
  let C := unshiftedCoefficient R
  let F := FlasqueTwoSummands.first R
  let L := FlasqueTwoSummands.boundedNegativeTwist R
  let T := FlasqueBoundedBelow.total (twoChartLine R)
  (Functor.associator C (FlasqueTwoSummands.second R) T).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator C F L).symm T ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (nativeFirstSourceIso R) L) T ≪≫
    Functor.associator (resolved R ⋙ SelfBaseChange.source R) L T

end Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
