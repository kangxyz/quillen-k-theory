/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.Algebra.Homology.DerivedCategory.Plus.BoundedComparison
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedFlatBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardSection
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.IntrinsicPerfectPushforward

/-! # Original projective-line base-change mate on intrinsic perfect D+

The actual natural derived mate is tested on bounded quasicoherent complexes
by the original single-sheaf base-change theorem and finite brutal layers.
The accepted objectwise global strict producer then proves its invertibility
on intrinsic perfect D+ inputs. No chosen natural strictification is asserted;
the map and its inverse are the original natural mate and canonical inverse.
-/
@[expose] public section

open Quillen.PerfectComplexes

open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance perfectBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- The ORIGINAL mate is invertible on actual bounded quasicoherent complexes. -/
theorem isIso_derivedProjectionBaseChange_bounded_qc
    {W V : Scheme.{u}} (a : W ⟶ twoChartLine R) (b : W ⟶ V) (j : V ⟶ Spec R)
    (h : IsPullback a b (projection R) j) [Flat j]
    (K : CochainComplex.Plus (twoChartLine R).Modules) (l r : ℤ)
    (hl : ∀ n, n < l → IsZero (K.obj.X n))
    (hu : ∀ n, r < n → IsZero (K.obj.X n))
    (hqc : ∀ n, (K.obj.X n).IsQuasicoherent) :
    IsIso ((derivedFlatBaseChangeMap a b (projection R) j h).app
      (DerivedCategory.Plus.Q.obj K)) := by
  let := flat_cartesian_baseChange a b (projection R) j h
  let := derivedFlatBaseChangeMap_commShift a b (projection R) j h
  let : (derivedFlatPullbackPlus j).IsTriangulated := by
    unfold derivedFlatPullbackPlus
    infer_instance
  let : (derivedFlatPullbackPlus a).IsTriangulated := by
    unfold derivedFlatPullbackPlus
    infer_instance
  apply DerivedCategory.Plus.isIso_app_of_term_bounds
    (derivedFlatBaseChangeMap a b (projection R) j h) K l r hl hu
  intro n
  let := hqc n
  exact isIso_derivedProjectionBaseChange_single R a b j h (K.obj.X n)

/-- The ORIGINAL natural base-change mate is invertible on every intrinsic
perfect D+ coefficient over every commutative ring. -/
theorem isIso_derivedProjectionBaseChange_perfect
    {W V : Scheme.{u}} (a : W ⟶ twoChartLine R) (b : W ⟶ V) (j : V ⟶ Spec R)
    (h : IsPullback a b (projection R) j) [Flat j]
    (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((derivedFlatBaseChangeMap a b (projection R) j h).app K) := by
  let := flat_cartesian_baseChange a b (projection R) j h
  obtain ⟨P, ⟨eP⟩⟩ :=
    Quillen.PerfectComplexes.ProjectiveLine.exists_strict_model_of_perfect_plus R K hK
  obtain ⟨⟨l, r, hb⟩, hf⟩ := P.property
  rw [← NatTrans.isIso_app_iff_of_iso (derivedFlatBaseChangeMap a b (projection R) j h) eP]
  exact isIso_derivedProjectionBaseChange_bounded_qc R a b j h
    ((strictToPlus (twoChartLine R)).obj P) l r
    (fun n hn => hb n (Or.inl hn)) (fun n hn => hb n (Or.inr hn))
    (fun n => by
      change (P.obj.X n).IsQuasicoherent
      let := hf n
      infer_instance)

/-- The actual first projection is geometrically flat by base change of the
original flat projective-line projection. -/
local instance perfectBaseChangeFirstFlat : Flat (relativeFirst R) := by
  dsimp [relativeFirst]
  infer_instance

/-- The original self-base-change natural mate, on the actual relative fiber product. -/
def derivedSelfBaseChangeMap :
    derivedPushforwardPlus (projection R) ⋙ derivedFlatPullbackPlus (projection R) ⟶
      derivedFlatPullbackPlus (relativeFirst R) ⋙ derivedPushforwardPlus (relativeSecond R) :=
  derivedFlatBaseChangeMap (relativeFirst R) (relativeSecond R) (projection R) (projection R)
    (IsPullback.of_hasPullback (projection R) (projection R))

/-- Intrinsic perfectness proves invertibility of the original self-base-change component. -/
theorem isIso_derivedSelfBaseChange_perfect
    (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((derivedSelfBaseChangeMap R).app K) :=
  isIso_derivedProjectionBaseChange_perfect R (relativeFirst R) (relativeSecond R)
    (projection R) (IsPullback.of_hasPullback (projection R) (projection R)) K hK
/-- Restricting the ORIGINAL natural mate to the actual full subcategory of
intrinsic perfect D+ objects gives a genuine natural isomorphism. Its inverse is
canonical; strict models enter only the component invertibility proof. -/
def derivedSelfBaseChangePerfectIso :
    ((perfectDerivedObjects (twoChartLine R)).inverseImage
      (DerivedCategory.Plus.ι (C := (twoChartLine R).Modules))).ι ⋙
        (derivedPushforwardPlus (projection R) ⋙ derivedFlatPullbackPlus (projection R)) ≅
      ((perfectDerivedObjects (twoChartLine R)).inverseImage
      (DerivedCategory.Plus.ι (C := (twoChartLine R).Modules))).ι ⋙
        (derivedFlatPullbackPlus (relativeFirst R) ⋙
          derivedPushforwardPlus (relativeSecond R)) := by
  let α := Functor.whiskerLeft
    ((perfectDerivedObjects (twoChartLine R)).inverseImage
      (DerivedCategory.Plus.ι (C := (twoChartLine R).Modules))).ι
    (derivedSelfBaseChangeMap R)
  have hα : IsIso α := by
    apply (NatTrans.isIso_iff_isIso_app α).mpr
    intro K
    change IsIso ((derivedSelfBaseChangeMap R).app K.obj)
    exact isIso_derivedSelfBaseChange_perfect R K.obj K.property
  exact asIso α

/-- The forward natural isomorphism is exactly the original self-base-change
mate on the underlying perfect D+ object. -/
theorem derivedSelfBaseChangePerfectIso_hom_app
    (K : ((perfectDerivedObjects (twoChartLine R)).inverseImage
      (DerivedCategory.Plus.ι (C := (twoChartLine R).Modules))).FullSubcategory) :
    (derivedSelfBaseChangePerfectIso R).hom.app K =
      (derivedSelfBaseChangeMap R).app K.obj := rfl

/-- The original self-base-change comparison retains the ordinary geometric
mate and both installed composite derived units on actual complexes. -/
theorem derivedSelfBaseChangeMap_unit
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit
      (Scheme.Modules.pushforward (projection R))
      (Scheme.Modules.pullback (projection R))).app K ≫
        (derivedSelfBaseChangeMap R).app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus
          (cartesianBaseChangeMap (relativeFirst R) (relativeSecond R)
            (projection R) (projection R)
            (IsPullback.of_hasPullback (projection R) (projection R)))).app K) ≫
        (Functor.rightDerivedFunctorPlusCompUnit
          (Scheme.Modules.pullback (relativeFirst R))
          (Scheme.Modules.pushforward (relativeSecond R))).app K :=
  derivedFlatBaseChangeMap_unit (relativeFirst R) (relativeSecond R)
    (projection R) (projection R)
    (IsPullback.of_hasPullback (projection R) (projection R)) K

end AlgebraicGeometry.Scheme.ProjectiveLine
