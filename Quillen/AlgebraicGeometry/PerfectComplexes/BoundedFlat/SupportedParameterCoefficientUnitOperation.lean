/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterCoefficientTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedAction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedParameterDoubleUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedDoubleForwardQuotient

/-!
# The original supported stable unit under the actual coefficient comparison

The complete original parameter track is transported through the specified
Laurent Spec isomorphism, supported row isomorphism, and supported coefficient
restriction. The resulting operation is the original supported coefficient
operation used by its forward-unit quotient. No group-level forgetful
injectivity or replacement of the support pair is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.SupportedParameterCoefficientUnitOperation
open GlobalSectionChangeIndex GlobalSupportedParameterCoefficient
attribute [local irreducible] globalModel

private theorem stableOperation_eq_of_levels {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f f) (J : Homotopy g g) (h : ∀ n, H.level n = J.level n) (d : ℤ) :
    H.stableOperation d = J.stableOperation d := by
  have hf : f = g := by
    apply LoopPrespectrum.Hom.ext
    funext k
    ext x
    exact (H.at_zero k x).symm.trans
      ((congrArg (fun p => p (0, x)) (h k)).trans (J.at_zero k x))
  subst g
  have hH : H = J := by
    apply LoopPrespectrum.Homotopy.ext
    funext k
    exact h k
  subst J
  rfl

/-- The unchanged supported parameter stable operation is natural in every parameter arrow. -/
theorem parameterOperation_naturality {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (d : ℤ) :
    (stableHomotopyFunctor d).map
        (prespectrumMap ((ParameterModels.supported f).map g)) ≫
      ((ParameterLaurentTrack.supportedTrack f).homotopy Y).stableOperation d =
    ((ParameterLaurentTrack.supportedTrack f).homotopy X).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (prespectrumMap ((ParameterModels.supported f).map (laurent.op.map g))) := by
  let A := ParameterLaurentTrack.supportedTrack f
  let i := prespectrumMap ((ParameterModels.supported f).map g)
  let j := prespectrumMap ((ParameterModels.supported f).map (laurent.op.map g))
  have hl (n : ℕ) : ((A.homotopy X).postcomp j).level n =
      ((A.homotopy Y).precomp i).level n := by
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact A.naturality g n t x
  exact ((A.homotopy Y).stableOperation_precomp i d).symm.trans
    ((stableOperation_eq_of_levels _ _ hl d).symm.trans
      ((A.homotopy X).stableOperation_postcomp j d))

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The original supported row isomorphism followed by the actual coefficient restriction. -/
def coefficientModelMap (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.supported f.left).obj (specUnder.obj a) ⟶
      (boundedFlatCoefficientSupportedModelFunctor f).obj a :=
  (parameterSupportedRowIso f).hom.app a ≫ (supportedRowRestriction f).app a

/-- The full Laurent endpoint retains the specified Laurent Spec map and row restriction. -/
def coefficientLaurentModelMap (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.supported f.left).obj (laurent.op.obj (specUnder.obj a)) ⟶
      (boundedFlatCoefficientSupportedModelFunctor f).obj ((laurentUnderFunctor _).obj a) :=
  laurentModelMap f a ≫
    (supportedRowRestriction f).app ((laurentUnderFunctor _).obj a)

private theorem map_comp_apply {V W U : Model.{u}} (i : V ⟶ W) (j : W ⟶ U)
    (n : ℕ) (x : (prespectrum V).space n) :
    (prespectrumMap (i ≫ j)).map n x =
      (prespectrumMap j).map n ((prespectrumMap i).map n x) :=
  congrArg (fun k => k.map n x) (prespectrumFunctor.map_comp i j)

/-- The full original supported coefficient comparison preserves every track level and time. -/
theorem coefficientTrack_square (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((ParameterModels.supported f.left).obj (specUnder.obj a))).space n) :
    (prespectrumMap (coefficientLaurentModelMap f a)).map n
        (((ParameterLaurentTrack.supportedTrack f.left).homotopy
          (specUnder.obj a)).level n (t, x)) =
      (((boundedFlatCoefficientSupportedLaurentAction f).track.homotopy a).level n
        (t, (prespectrumMap (coefficientModelMap f a)).map n x)) := by
  exact (map_comp_apply (laurentModelMap f a)
    ((supportedRowRestriction f).app ((laurentUnderFunctor _).obj a)) n _).trans
    ((congrArg
      ((prespectrumMap ((supportedRowRestriction f).app ((laurentUnderFunctor _).obj a))).map n)
      (GlobalSupportedParameterCoefficient.track_square f a n t x)).trans
      ((supportedRowRestriction_track f a n t
        ((prespectrumMap ((parameterSupportedRowIso f).hom.app a)).map n x)).trans
        (congrArg (fun y =>
          ((boundedFlatCoefficientSupportedLaurentAction f).track.homotopy a).level n (t, y))
          (map_comp_apply ((parameterSupportedRowIso f).hom.app a)
            ((supportedRowRestriction f).app a) n x).symm)))

/-- The unchanged parameter operation gives the actual coefficient operation, with both
specified endpoint comparisons retained. -/
theorem coefficientOperation (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    ((ParameterLaurentTrack.supportedTrack f.left).homotopy
        (specUnder.obj a)).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (prespectrumMap (coefficientLaurentModelMap f a)) =
    (stableHomotopyFunctor d).map (prespectrumMap (coefficientModelMap f a)) ≫
      ((boundedFlatCoefficientSupportedLaurentAction f).track.homotopy a).stableOperation d := by
  let H := (ParameterLaurentTrack.supportedTrack f.left).homotopy (specUnder.obj a)
  let J := (boundedFlatCoefficientSupportedLaurentAction f).track.homotopy a
  let i := prespectrumMap (coefficientModelMap f a)
  let j := prespectrumMap (coefficientLaurentModelMap f a)
  have hl (n : ℕ) : (H.postcomp j).level n = (J.precomp i).level n := by
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact coefficientTrack_square f a n t x
  exact (H.stableOperation_postcomp j d).symm.trans
    ((stableOperation_eq_of_levels _ _ hl d).trans (J.stableOperation_precomp i d))

private theorem quotient_square {C : Type*} [Category C] {A B D E F : C}
    (p : A ⟶ B) (q : B ⟶ D) (i : A ⟶ E) (j : E ⟶ D) (π : D ⟶ F)
    (h : p ≫ q = i ≫ j) : i ≫ (j ≫ π) = p ≫ q ≫ π := by
  rw [← Category.assoc, ← h, Category.assoc]

/-- The original supported forward quotient has the unchanged parameter track representative. -/
theorem forwardQuotient_parameter (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map (prespectrumMap (coefficientModelMap f a)) ≫
      (boundedFlatCoefficientSupportedForwardUnitQuotient f d).app a =
    ((ParameterLaurentTrack.supportedTrack f.left).homotopy
        (specUnder.obj a)).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (prespectrumMap (coefficientLaurentModelMap f a)) ≫
      (Quillen.Bass.TwoChart.contractionπ (underToLaurent _) (underToLaurentInvert _)
        (boundedFlatCoefficientSupportedPrespectrumFunctor f ⋙
          stableHomotopyFunctor (d + 1))).app a := by
  exact quotient_square _ _ _ _ _ (coefficientOperation f a d)

/-- The complete Laurent comparison factors through the specified first Laurent Spec iso. -/
theorem coefficientLaurentModelMap_factor (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    coefficientLaurentModelMap f a =
      (ParameterModels.supported f.left).map (laurentSpecIso a.right).hom.op ≫
        coefficientModelMap f ((laurentUnderFunctor _).obj a) :=
  Category.assoc _ _ _

/-- The actual twice-Laurent endpoint comparison retains both original Laurent Spec maps. -/
def doubleLaurentModelMap (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.supported f.left).obj (laurent.op.obj (laurent.op.obj (specUnder.obj a))) ⟶
      (boundedFlatCoefficientSupportedModelFunctor f).obj
        ((laurentUnderFunctor _).obj ((laurentUnderFunctor _).obj a)) :=
  (ParameterModels.supported f.left).map
      (laurent.op.map (laurentSpecIso a.right).hom.op) ≫
    coefficientLaurentModelMap f ((laurentUnderFunctor _).obj a)

end Quillen.PerfectComplexes.SupportedParameterCoefficientUnitOperation
