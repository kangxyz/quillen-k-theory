/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteSourceSheetAction
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeExt
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassReverseFiniteProduct

/-! The finite source action recovers the original first-sheet evaluator at every level. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Convexity
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassFiniteSourceSheetNative
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FiniteSourceSheet
variable {V W T U : Model.{u}} (D : V ⟶ W) (F : W ⟶ T) (J : T ⟶ U)
variable {k : ℕ} (Z : Fin (k + 1) → Node D)

/-- Evaluation is the original two-sheet evaluator restricted to its literal first sheet. -/
def evaluate (n : ℕ) (y : source F J) (x : (prespectrum W).space n) :
    (nativeCone J).space n :=
  nativeEval F J (F ≫ J) (Iso.refl _) (Iso.refl _) n
    (SSet.toTop.map (left₁ F J (F ≫ J) (Iso.refl _) (Iso.refl _)) y) x

theorem evaluate_laurent (n : ℕ) (y : |parameterSSet (F ≫ J)|)
    (x : (prespectrum W).space n) :
    evaluate F J n (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y) x =
      (LoopPrespectrum.mappingConeInclusion (prespectrumMap J)).map n
        (pointwisePrespectrumFamily (F ≫ J) n y x) :=
  nativeEval_laurentInclusion F J (F ≫ J) (Iso.refl _) (Iso.refl _) n y x

theorem evaluate_cylinder (n : ℕ) (y : |parameterSSet F|) (h : I)
    (x : (prespectrum W).space n) :
    evaluate F J n (DoubleCylinder.realizedCylinder
      (attaching F J (F ≫ J) (Iso.refl _)) (erase F) (y, ULift.up h)) x =
      ReducedMappingCone.cylinder ((prespectrum T).point n) ((prespectrum U).point n)
        ((prespectrumMap J).map n) (h, pointwisePrespectrumFamily F n y x) :=
  nativeEval_cylinderMinus F J (F ≫ J) (Iso.refl _) (Iso.refl _) n y h x

theorem evaluate_tip (n : ℕ) (y : |tipSSet.{u}|) (x : (prespectrum W).space n) :
    evaluate F J n (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) y) x =
      (nativeCone J).point n := by
  have hy : y = (default : |tipSSet.{u}|) := Subsingleton.elim _ _
  subst y
  exact nativeEval_tipMinus F J (F ≫ J) (Iso.refl _) (Iso.refl _) n x

/-- Every polynomial parameter has the literal source-first native composition. -/
theorem polynomial_native (n : ℕ) (y : |parameterSSet F|)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (D ≫ F) n (polynomial D F Z (y, z)) x =
      pointwisePrespectrumFamily F n y (prespectrumFamily D Z n (z, x)) :=
  CoefficientBassReverseFiniteProduct.finite_product_native D F (D ≫ F)
    (Iso.refl _) Z n y z x

/-- The Laurent product keeps its displayed associator and unchanged native value. -/
theorem laurent_native (n : ℕ) (y : |parameterSSet (F ≫ J)|)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily ((D ≫ F) ≫ J) n (laurent D F J Z (y, z)) x =
      pointwisePrespectrumFamily (F ≫ J) n y (prespectrumFamily D Z n (z, x)) :=
  CoefficientBassReverseFiniteProduct.finite_product_native D (F ≫ J) ((D ≫ F) ≫ J)
    (Functor.associator D.functor F.functor J.functor) Z n y z x

/-- The original whole first sheet evaluates on the finite source family, including degree zero. -/
theorem action_native (n : ℕ) (y : source F J)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    evaluate (D ≫ F) J n (action D F J Z (y, z)) x =
      evaluate F J n y (prespectrumFamily D Z n (z, x)) := by
  have h : (fun y ↦ evaluate (D ≫ F) J n (action D F J Z (y, z)) x) =
      (fun y ↦ evaluate F J n y (prespectrumFamily D Z n (z, x))) := by
    apply FourEdgeTree.SetDescent.funext (attaching F J (F ≫ J) (Iso.refl _)) (erase F)
    · rintro ⟨y, ⟨t⟩⟩
      rw [action_cylinder]
      change evaluate (D ≫ F) J n (DoubleCylinder.realizedCylinder _ _
        (polynomial D F Z (y, z), ULift.up t)) x = _
      rw [evaluate_cylinder, evaluate_cylinder, polynomial_native]
    · intro y
      change evaluate (D ≫ F) J n
        (action D F J Z (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y, z)) x =
          evaluate F J n (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y)
            (prespectrumFamily D Z n (z, x))
      rw [action_laurent]
      change evaluate (D ≫ F) J n
        (SSet.toTop.map (left₀ (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _))
          (laurent D F J Z (y, z))) x = _
      rw [evaluate_laurent, evaluate_laurent, laurent_native]
    · intro y
      change evaluate (D ≫ F) J n
        (action D F J Z (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) y, z)) x =
          evaluate F J n (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) y)
            (prespectrumFamily D Z n (z, x))
      rw [action_tip]
      change evaluate (D ≫ F) J n
        (SSet.toTop.map (right₀ (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _)) default) x = _
      rw [evaluate_tip, evaluate_tip]
  exact congrFun h y

end Quillen.PerfectComplexes.CoefficientBassFiniteSourceSheetNative
