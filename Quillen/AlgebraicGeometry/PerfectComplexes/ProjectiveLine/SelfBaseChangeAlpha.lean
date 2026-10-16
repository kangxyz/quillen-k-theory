/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.GodementUnit
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedSelfBaseChangePerfect
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientZero
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect

/-!
# The actual ordinary self-base-change quasi-isomorphism

The source has original termwise flasque locally perfect complexes. The map is
literal ordinary cartesian base change followed by direct image of the actual
Godement augmentation. Its derived image is the original installed mate through
the original units, so the accepted intrinsic-perfect mate theorem proves the
quasi-isomorphism for every coefficient ring, including the zero ring.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.SelfBaseChange
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance selfBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : CommRingCat.{u})
local instance firstFlat : Flat (relativeFirst R) := by
  dsimp [relativeFirst]
  infer_instance

/-- The literal lower-bounded source p* p_* M. -/
def sourcePlus : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    CochainComplex.Plus (twoChartLine R).Modules :=
  FlasqueCoefficients.toPlus (twoChartLine R) ⋙
    (Scheme.Modules.pushforward (projection R) ⋙
      Scheme.Modules.pullback (projection R)).mapCochainComplexPlus

/-- The literal lower-bounded target p2_* T_Z(p1* M). -/
def targetPlus : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    CochainComplex.Plus (twoChartLine R).Modules :=
  FlasqueCoefficients.toPlus (twoChartLine R) ⋙
    (Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus ⋙
      godementTotalPlus (relativeSquare R) ⋙
        (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus

/-- The actual natural ordinary mate followed by pushforward of the actual total unit. -/
def alphaPlus : sourcePlus R ⟶ targetPlus R :=
  CategoryTheory.Functor.whiskerLeft (FlasqueCoefficients.toPlus (twoChartLine R))
    (godementBaseChangeMap (relativeFirst R) (relativeSecond R)
      (projection R) (projection R) (IsPullback.of_hasPullback (projection R) (projection R)))

/-- Its components are the prescribed original maps, in the prescribed order. -/
lemma alphaPlus_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (alphaPlus R).app K =
      (NatTrans.mapCochainComplexPlus
        (cartesianBaseChangeMap (relativeFirst R) (relativeSecond R)
          (projection R) (projection R)
          (IsPullback.of_hasPullback (projection R) (projection R)))).app
            ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K) ≫
        (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus.map
          ((godementTotalPlusUnit (relativeSquare R)).app
            ((Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus.obj
              ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K))) :=
  godementBaseChangeMap_app _ _ _ _ _ _

/-- The Q-image is identified with the ORIGINAL accepted self-base-change mate. -/
lemma alphaPlus_original_unit (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    DerivedCategory.Plus.Q.map ((alphaPlus R).app K) ≫
        (godementBaseChangeTargetIso (relativeFirst R) (relativeSecond R)).hom.app
          ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K) =
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.pushforward (projection R))
        (Scheme.Modules.pullback (projection R))).app
          ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K) ≫
        (derivedSelfBaseChangeMap R).app
          (DerivedCategory.Plus.Q.obj ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K)) :=
  godementBaseChangeMap_original_unit _ _ _ _ _ _

/-- The ACTUAL original alpha is a genuine quasi-isomorphism, with no supplied replacement. -/
lemma alphaPlus_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((alphaPlus R).app K).hom := by
  let P := (FlasqueCoefficients.toPlus (twoChartLine R)).obj K
  have : IsIso ((Functor.rightDerivedFunctorPlusCompUnit
      (Scheme.Modules.pushforward (projection R))
      (Scheme.Modules.pullback (projection R))).app P) :=
    isIso_baseChangeSourceUnit_of_flasque (projection R) (projection R) P K.property.2
  have hP : perfectDerivedObjects (twoChartLine R)
      (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj P)) :=
    (perfectDerivedObjects_toDerived_iff (twoChartLine R) K.obj).mpr K.property.1.1
  have : IsIso ((derivedSelfBaseChangeMap R).app (DerivedCategory.Plus.Q.obj P)) :=
    isIso_derivedSelfBaseChange_perfect R (DerivedCategory.Plus.Q.obj P) hP
  have : IsIso (DerivedCategory.Plus.Q.map ((alphaPlus R).app K) ≫
      (godementBaseChangeTargetIso (relativeFirst R) (relativeSecond R)).hom.app P) := by
    rw [alphaPlus_original_unit]
    infer_instance
  have : IsIso (DerivedCategory.Plus.Q.map ((alphaPlus R).app K)) :=
    IsIso.of_isIso_comp_right _
      ((godementBaseChangeTargetIso (relativeFirst R) (relativeSecond R)).hom.app P)
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (twoChartLine R).Modules
    ((alphaPlus R).app K).hom).mp
  change IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ((alphaPlus R).app K)))
  infer_instance

end Quillen.PerfectComplexes.ProjectiveLine.SelfBaseChange
