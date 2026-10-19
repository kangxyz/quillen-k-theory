/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.OriginalRowSwap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitBassComposite

/-!
# Row interchange on the unchanged raw bounded-flat Bass input tracks

The genuine row transpose commutes with the original geometric pullback, the actual tensor-unit
and unitor tracks, and the prescribed two-half-clock geometric composition homotopy. Therefore
both original Laurent-chart tracks and their specified square homotopy retain the entire row
square. These are the actual finite input identities for a subsequent HPO and cofiber descent;
no cofiber interchange is assumed here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes

/-- The original raw geometric pullback preserves the genuine higher-row transpose. -/
theorem boundedFlatPerfectPrespectrumMap_rowSwap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (k : ℕ) (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen Y))) :
    stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen X))
      ((boundedFlatPerfectPrespectrumMap f).map (k + 3) x) =
    (boundedFlatPerfectPrespectrumMap f).map (k + 3)
      (stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen Y)) x) :=
  exactOriginalPrespectrumMap_rowSwap _ _ (boundedFlatPerfectPullback_exact f) k x

/-- The forward actual tensor-unit track preserves row interchange at every original time. -/
theorem boundedFlatPerfectTensorUnitHomotopy_rowSwap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen Y))) :
    stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen X))
      ((boundedFlatPerfectTensorUnitHomotopy f r).level (k + 3) (t, x)) =
    (boundedFlatPerfectTensorUnitHomotopy f r).level
      (k + 3) (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen Y)) x) :=
  exactOriginalPrespectrumHomotopy_rowSwap _ _ _ _
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom
    (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) k t x

/-- The genuine tensor unitor track retains the entire row-interchange square. -/
theorem boundedFlatPerfectTensorUnitUnitorHomotopy_rowSwap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen Y))) :
    stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen X))
      ((boundedFlatPerfectTensorUnitUnitorHomotopy f).level (k + 3) (t, x)) =
    (boundedFlatPerfectTensorUnitUnitorHomotopy f).level
      (k + 3) (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen Y)) x) :=
  exactOriginalPrespectrumHomotopy_rowSwap _ _ _ _
    (boundedFlatPerfectTensorUnitPullbackIso f).hom
    (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) k t x

/-- Both specified halves of the raw geometric composition track preserve row interchange. -/
theorem boundedFlatPerfectPrespectrumCompHomotopy_rowSwap {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen Z))) :
    stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen X))
      ((boundedFlatPerfectPrespectrumCompHomotopy f g).level (k + 3) (t, x)) =
    (boundedFlatPerfectPrespectrumCompHomotopy f g).level
      (k + 3) (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen Z)) x) := by
  let H := exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackCompIso f g)
  let K := exactOriginalPrespectrumMapCompHomotopy _ _ _
    (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f)
  change stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen X))
    (((H.levelHomotopy (k + 3)).trans (K.levelHomotopy (k + 3))) (t, x)) =
    ((H.levelHomotopy (k + 3)).trans (K.levelHomotopy (k + 3)))
      (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen Z)) x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact exactOriginalPrespectrumHomotopy_rowSwap _ _ _ _
      (boundedFlatPerfectPullbackCompIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) k _ x
  · exact exactOriginalPrespectrumMapCompHomotopy_rowSwap _ _ _
      (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f) k _ x

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The actual positive Laurent-chart track retains its whole row-interchange square. -/
theorem boundedFlatCoefficientLaurentPlusHomotopy_rowSwap (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))) :
    stageRowSwapHomeomorph k
      (modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a))))
      ((boundedFlatCoefficientLaurentPlusHomotopy P a).level (k + 3) (t, x)) =
    (boundedFlatCoefficientLaurentPlusHomotopy P a).level (k + 3)
      (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x)
      :=
  boundedFlatPerfectPrespectrumCompHomotopy_rowSwap (laurentPlus P a)
    (polynomialProjection P a) k t x

/-- The actual inverse Laurent-chart track retains its whole row-interchange square. -/
theorem boundedFlatCoefficientLaurentMinusHomotopy_rowSwap (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))) :
    stageRowSwapHomeomorph k
      (modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a))))
      ((boundedFlatCoefficientLaurentMinusHomotopy P a).level (k + 3) (t, x)) =
    (boundedFlatCoefficientLaurentMinusHomotopy P a).level (k + 3)
      (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x)
      :=
  boundedFlatPerfectPrespectrumCompHomotopy_rowSwap (laurentMinus P a)
    (polynomialProjection P a) k t x

/-- The specified reversed-positive/inverse square keeps both original half-clock pieces. -/
theorem boundedFlatCoefficientBassSquareHomotopy_rowSwap (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))) :
    stageRowSwapHomeomorph k
      (modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a))))
      ((boundedFlatCoefficientBassSquareHomotopy P a).level (k + 3) (t, x)) =
    (boundedFlatCoefficientBassSquareHomotopy P a).level (k + 3)
      (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x)
      := by
  let H := (boundedFlatCoefficientLaurentPlusHomotopy P a).symm
  let K := boundedFlatCoefficientLaurentMinusHomotopy P a
  change stageRowSwapHomeomorph k
    (modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a))))
    (((H.levelHomotopy (k + 3)).trans (K.levelHomotopy (k + 3))) (t, x)) =
    ((H.levelHomotopy (k + 3)).trans (K.levelHomotopy (k + 3)))
      (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact boundedFlatCoefficientLaurentPlusHomotopy_rowSwap P a k _ x
  · exact boundedFlatCoefficientLaurentMinusHomotopy_rowSwap P a k _ x

end Quillen.PerfectComplexes
