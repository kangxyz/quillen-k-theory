/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedFiniteFlatPushforward
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineTensor
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleComplexDirectImage
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatPullbackSingle
public import Quillen.Algebra.Homology.HomotopyCategory.BoundedProperty
public import Quillen.Algebra.Category.ModuleCat.Sheaf.TensorRightUnit

/-! # Affine coefficient projection calculations toward native generation

Over an arbitrary affine base, the original projection takes the pullback of
every intrinsic perfect object back to that object. Its pullback tensored on
the left with the actual tautological O(-1) has zero derived direct image.
Affine strictification is applied only to coefficients on Spec R. These
calculations do not assert strictification or generation of arbitrary perfect
objects on the projective line, or a native projective-line K-equivalence.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine

/-- The standard derived category of module sheaves, used for affine coefficient calculations. -/
local instance affinePerfectGenerationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- The original derived pullback followed by projection recovers an arbitrary perfect
coefficient on the affine base. Only the affine coefficient is strictified. -/
def derivedProjectionPullbackPerfectIso (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (Spec R).Modules)
    (hK : perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj K)) :
    K ≅ (derivedPushforwardPlus (projection R)).obj
      ((derivedFlatPullbackPlus (projection R)).obj K) := Classical.choice (by
  obtain ⟨P, ⟨eP⟩⟩ := Affine.exists_strictToDerivedPlus_iso R K hK
  obtain ⟨a, b, hab⟩ := P.property.1
  have := isIso_derivedFlatPullbackPlusUnit (projection R)
  exact ⟨eP.symm ≪≫ derivedProjectionPullbackBoundedIso R ((strictToPlus (Spec R)).obj P)
      a b (fun i hi => hab i (Or.inl hi)) (fun i hi => hab i (Or.inr hi)) P.property.2 ≪≫
    (derivedPushforwardPlus (projection R)).mapIso
      (asIso ((Scheme.Modules.pullback (projection R)).rightDerivedFunctorPlusUnit.app
        ((strictToPlus (Spec R)).obj P))) ≪≫
    (derivedPushforwardPlus (projection R)).mapIso
      ((derivedFlatPullbackPlus (projection R)).mapIso eP)⟩)

private theorem isZero_on_affinePerfect_of_vectorBundle_single
    (R : CommRingCat.{u}) {Z : Scheme.{u}}
    (F : DerivedCategory.Plus (Spec R).Modules ⥤ DerivedCategory.Plus Z.Modules)
    [F.CommShift ℤ] [F.IsTriangulated]
    (hsingle : ∀ (M : (Spec R).Modules), IsFiniteLocallyFree (Spec R) M →
      IsZero (F.obj ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj M)))
    (K : DerivedCategory.Plus (Spec R).Modules)
    (hK : perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj K)) :
    IsZero (F.obj K) := by
  obtain ⟨P, ⟨eP⟩⟩ := Affine.exists_strictToDerivedPlus_iso R K hK
  obtain ⟨a, b, hab⟩ := P.property.1
  let C := (strictToPlus (Spec R)).obj P
  let J := DerivedCategory.Plus.Qh ⋙ F
  let Q : ObjectProperty (DerivedCategory.Plus Z.Modules) := IsZero
  let : Q.IsClosedUnderIsomorphisms := ⟨fun e h => h.of_iso e.symm⟩
  let : Q.ContainsZero := ⟨0, isZero_zero _, isZero_zero _⟩
  let : Q.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ =>
    T.isZero₂_of_isZero₁₃ hT h₁ h₃)
  have hs (n : ℤ) : Q (J.obj ((HomotopyCategory.Plus.quotient (Spec R).Modules).obj
      (CochainComplex.singlePlus (C.obj.X n) n))) := by
    have hz := hsingle (P.obj.X n) (P.property.2 n)
    let e := ((DerivedCategory.Plus.singleFunctors (Spec R).Modules).shiftIso
      (-n) n 0 (by omega)).app (P.obj.X n)
    let e' := ((F.commShiftIso (-n)).app
      ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj (P.obj.X n))).symm ≪≫
        F.mapIso e
    have hn : IsZero (F.obj
        ((DerivedCategory.Plus.singleFunctor (Spec R).Modules n).obj (P.obj.X n))) :=
      ((shiftFunctor (DerivedCategory.Plus Z.Modules) (-n)).map_isZero hz).of_iso e'.symm
    exact hn.of_iso (F.mapIso
      ((DerivedCategory.Plus.quotientCompQhIso (Spec R).Modules).app
        (CochainComplex.singlePlus (C.obj.X n) n)))
  have h := HomotopyCategory.Plus.property_obj_of_term_bounds J Q C a b
    (fun i hi => hab i (Or.inl hi)) (fun i hi => hab i (Or.inr hi)) hs
  have h' : IsZero (F.obj (DerivedCategory.Plus.Q.obj C)) :=
    h.of_iso (F.mapIso ((DerivedCategory.Plus.quotientCompQhIso (Spec R).Modules).app C)).symm
  exact h'.of_iso (F.mapIso eP).symm

/-- Pullback tensored with the original tautological negative line, in the same left tensor
order as the native second summand. This uses the actual sheaf tensor functor. -/
def affineNegativePullbackModule (R : CommRingCat.{u}) :
    (Spec R).Modules ⥤ (twoChartLine R).Modules :=
  Scheme.Modules.pullback (projection R) ⋙
    moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)

instance affineNegativePullbackModule_additive (R : CommRingCat.{u}) :
    (affineNegativePullbackModule R).Additive := by
  dsimp [affineNegativePullbackModule]
  infer_instance

instance affineNegativePullbackModule_preservesHomology (R : CommRingCat.{u}) :
    (affineNegativePullbackModule R).PreservesHomology := by
  dsimp [affineNegativePullbackModule]
  infer_instance

/-- The exact pullback and actual O(-1) tensor, as its installed derived functor. -/
def affineNegativePullbackDerived (R : CommRingCat.{u}) :
    DerivedCategory.Plus (Spec R).Modules ⥤ DerivedCategory.Plus (twoChartLine R).Modules :=
  (affineNegativePullbackModule R).rightDerivedFunctorPlus

private theorem isZero_derivedProjection_negativePullback_single (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    IsZero ((derivedPushforwardPlus (projection R)).obj
      ((affineNegativePullbackDerived R).obj
        ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj M))) := by
  let H := affineNegativePullbackModule R
  let : (DerivedCategory.Plus.Q (C := (twoChartLine R).Modules)).Additive := by
    dsimp [DerivedCategory.Plus.Q]
    infer_instance
  let : (derivedPushforwardPlus (projection R)).Additive := by
    dsimp [derivedPushforwardPlus]
    infer_instance
  let F := H ⋙ CochainComplex.singleFunctorPlus (twoChartLine R).Modules 0 ⋙
    DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R)
  let e : H.obj (SheafOfModules.unit (Spec R).ringCatSheaf) ≅ tautologicalLine R :=
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).mapIso
      (pullbackUnitIso (projection R)) ≪≫
    (SheafOfModulesOfCommRing.tensorRightUnitIso (twoChartLine R).sheaf).app (tautologicalLine R)
  have hz : IsZero (F.obj M) := by
    apply isZero_obj_affineBundle_of_unit R F _ M
    exact (isZero_derivedProjection_tautologicalLine R).of_iso
      ((derivedPushforwardPlus (projection R)).mapIso
        (DerivedCategory.Plus.Q.mapIso (singleZeroPlusIso e)))
  have := H.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let es : H.mapCochainComplexPlus.obj
        ((CochainComplex.singleFunctorPlus (Spec R).Modules 0).obj M) ≅
      (CochainComplex.singleFunctorPlus (twoChartLine R).Modules 0).obj (H.obj M) :=
    (CochainComplex.plus (twoChartLine R).Modules).isoMk
      ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).app M)
  exact hz.of_iso ((derivedPushforwardPlus (projection R)).mapIso
    ((asIso (H.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus (Spec R).Modules 0).obj M))).symm ≪≫
        DerivedCategory.Plus.Q.mapIso es))

/-- The actual negative-line tensor of a pulled-back perfect affine coefficient has zero
derived projection. No generation or global strict model on the projective line is assumed. -/
theorem isZero_derivedProjection_negativePullback_perfect (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (Spec R).Modules)
    (hK : perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj K)) :
    IsZero ((derivedPushforwardPlus (projection R)).obj
      ((affineNegativePullbackDerived R).obj K)) := by
  exact isZero_on_affinePerfect_of_vectorBundle_single R
    ((affineNegativePullbackModule R).rightDerivedFunctorPlus ⋙
      (Scheme.Modules.pushforward (projection R)).rightDerivedFunctorPlus)
    (fun M hM => isZero_derivedProjection_negativePullback_single R M) K hK

end Quillen.PerfectComplexes.ProjectiveLine
