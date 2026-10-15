/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.EulerFunctors

/-! # Actual negative Euler coefficients vanish after original Godement projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
open FlasqueCoefficients
variable (R : CommRingCat.{u})

local instance eulerNegativeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

lemma negativeEndpoint_strictPerfect (A : StrictPerfect (Spec R)) :
    strictPerfect (twoChartLine R) ((endpointComplex R (tautologicalLine R)).obj A) :=
  tensor_strictPerfect_of_charts R _ (lineChartIso R) _
    (strictPerfect_pullback (projection R) A.property)

/-- The original negative endpoint with its actual lower-bounded complex. -/
def negativePlus : StrictPerfect (Spec R) ⥤ CochainComplex.Plus (twoChartLine R).Modules :=
  endpointBounded R (tautologicalLine R) (negativeEndpoint_strictPerfect R) ⋙
    boundedToPlus (twoChartLine R)

/-- Literal negative tensor, totalization, and ordinary projection, with no derived replacement. -/
def negativeProjected := projectedEndpoint R (tautologicalLine R) (negativeEndpoint_strictPerfect R)

/-- Reassociation of the original termwise functor retains every actual object and arrow. -/
def negativePlusIso : negativePlus R ≅ strictToPlus (Spec R) ⋙
    (affineNegativePullbackModule R).mapCochainComplexPlus :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    apply ObjectProperty.hom_ext
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

/-- The actual natural derived unit of the original exact negative pullback tensor. -/
def negativeDerivedUnit :
    strictToPlus (Spec R) ⋙ (affineNegativePullbackModule R).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q ⟶
    strictToDerivedPlus (Spec R) ⋙ affineNegativePullbackDerived R :=
  Functor.whiskerLeft (strictToPlus (Spec R))
    (affineNegativePullbackModule R).rightDerivedFunctorPlusUnit

instance negativeDerivedUnit_isIso : IsIso (negativeDerivedUnit R) := by
  have := (affineNegativePullbackModule R).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro A
  exact inferInstanceAs (IsIso ((affineNegativePullbackModule R).rightDerivedFunctorPlusUnit.app
    ((strictToPlus (Spec R)).obj A)))

/-- This comparison is precisely the original exact-functor unit after literal reassociation. -/
def negativeDerivedIso : negativePlus R ⋙ DerivedCategory.Plus.Q ≅
    strictToDerivedPlus (Spec R) ⋙ affineNegativePullbackDerived R :=
  Functor.isoWhiskerRight (negativePlusIso R) DerivedCategory.Plus.Q ≪≫
    asIso (negativeDerivedUnit R)

/-- The native O(-1) vanishing theorem applies to the actual strict-perfect affine coefficient. -/
lemma negativeEndpoint_derived_zero (A : StrictPerfect (Spec R)) :
    IsZero ((derivedPushforwardPlus (projection R)).obj
      (DerivedCategory.Plus.Q.obj ((negativePlus R).obj A))) := by
  have hA : perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj ((strictToDerivedPlus (Spec R)).obj A)) :=
    (perfectDerivedObjects_toDerived_iff (Spec R) A.obj).mpr
      (locallyPerfect_of_strictPerfect A.property)
  have hz := isZero_derivedProjection_negativePullback_perfect R
    ((strictToDerivedPlus (Spec R)).obj A) hA
  exact hz.of_iso ((derivedPushforwardPlus (projection R)).mapIso
    ((negativeDerivedIso R).app A))

/-- Forgetting the proved predicates retains exactly the actual projected total and every map. -/
def negativeProjectedPlusIso : negativeProjected R ⋙ toPlus (Spec R) ≅
    negativePlus R ⋙ godementTotalPlus (twoChartLine R) ⋙
      (Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    apply ObjectProperty.hom_ext
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

/-- Actual installed Godement comparison, restricted naturally to the negative endpoint. -/
def negativeProjectedDerivedIso :
    negativeProjected R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q ≅
      negativePlus R ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R) :=
  Functor.isoWhiskerRight (negativeProjectedPlusIso R) DerivedCategory.Plus.Q ≪≫
    Functor.isoWhiskerLeft (negativePlus R) (godementTotalDerivedPushforwardIso (projection R))

/-- The literal projected total of the negative endpoint is derived-zero. -/
lemma negativeProjected_derived_zero (A : StrictPerfect (Spec R)) :
    IsZero (DerivedCategory.Plus.Q.obj
      ((toPlus (Spec R)).obj ((negativeProjected R).obj A))) :=
  (negativeEndpoint_derived_zero R A).of_iso ((negativeProjectedDerivedIso R).app A)

end Quillen.PerfectComplexes.ProjectiveLine.Euler
