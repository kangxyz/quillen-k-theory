/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCoherence
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary

/-!
# Coefficient Transformation Composition

Native coefficient composition for every fixed polynomial/Laurent natural transformation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientTransformationComposition
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {M N : Under R ⥤ Under R} (α : M ⟶ N)
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The actual functor-applied coefficient composition track. -/
def coefficientComposition (M : Under R ⥤ Under R) :=
  (boundedFlatCoefficientCompositionHomotopy P (M.map u) (M.map v)).cast
    (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k))
      (M.map_comp u v)).symm rfl

/-- The original coefficient naturality square for the fixed transformation. -/
def square (u : a ⟶ b) :=
  boundedFlatPerfectPrespectrumSquareHomotopy (coefficientMap P (N.map u))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (M.map u))
    (coefficientTransformation_naturality P α u)

/-- The actual original rectangle, in the coefficient-composition direction. -/
def rectangle :=
  DoubleSquareTrack.originalComparison
    (coefficientMap P (M.map u)) (coefficientMap P (M.map v))
    (coefficientMap P (N.map u)) (coefficientMap P (N.map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientTransformation_naturality P α u).symm
    (coefficientTransformation_naturality P α v).symm

/-- Two successive ORIGINAL transformation squares, with literal associations. -/
def compositeSquare :=
  ((square P α u).postcomp (boundedFlatPerfectPrespectrumMap (coefficientMap P (N.map v)))).trans
    ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P (M.map u)))
      (square P α v)).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)

/-- The original source coefficient composition followed by the original chart map. -/
def sourceComposition :=
  (coefficientComposition P u v M).postcomp (boundedFlatPerfectPrespectrumMap
    (coefficientMap P (α.app c)))

/-- The original target coefficient composition under the original source chart map. -/
def targetComposition :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P (α.app a)))
    (coefficientComposition P u v N)).cast rfl (Category.assoc _ _ _).symm

/-- The rectangle starts at the two complete reversed original transformation tracks. -/
theorem rectangle_source_level (n : ℕ) :
    (compositeSquare P α u v).level n =
      (((rectangle P α u v).symmPath).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  unfold DoubleSquareTrack.originalLeft
  rw [Homotopy.symm_trans]
  apply Homotopy.trans_level_congr
  · rw [← Homotopy.postcomp_symm]
    apply Homotopy.postcomp_level_congr
    exact (boundedFlatGeometricSquareReverse_level
      (coefficientMap P (N.map u)) (coefficientMap P (α.app a))
      (coefficientMap P (α.app b)) (coefficientMap P (M.map u))
      (coefficientTransformation_naturality P α u) n).symm
  · change (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P (M.map u)))
      (square P α v)).level n =
        (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P (M.map u)))
          (boundedFlatPerfectPrespectrumSquareHomotopy
            (coefficientMap P (α.app c)) (coefficientMap P (M.map v))
            (coefficientMap P (N.map v)) (coefficientMap P (α.app b))
            (coefficientTransformation_naturality P α v).symm)).symm.level n
    rw [← Homotopy.precomp_symm]
    apply Homotopy.precomp_level_congr
    exact (boundedFlatGeometricSquareReverse_level
      (coefficientMap P (N.map v)) (coefficientMap P (α.app b))
      (coefficientMap P (α.app c)) (coefficientMap P (M.map v))
      (coefficientTransformation_naturality P α v) n).symm

/-- The whole target is the direct original square and both actual coefficient compositions. -/
theorem rectangle_target_level (n : ℕ) :
    (((targetComposition P α u v).symm.trans (square P α (u ≫ v))).trans
      (sourceComposition P α u v)).level n =
      (((rectangle P α u v).symmPath).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  unfold DoubleSquareTrack.originalRight
  rw [Homotopy.symm_trans, Homotopy.symm_trans, Homotopy.symm_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · apply Homotopy.symm_level_congr
      rfl
    · refine (boundedFlatGeometricSquareReverse_level
        (coefficientMap P (N.map (u ≫ v))) (coefficientMap P (α.app a))
        (coefficientMap P (α.app c)) (coefficientMap P (M.map (u ≫ v)))
        (coefficientTransformation_naturality P α (u ≫ v)) n).symm.trans ?_
      apply Homotopy.symm_level_congr
      exact boundedFlatGeometricSquare_level_congr _ _ rfl
        ((congrArg (coefficientMap P) (M.map_comp u v)).trans
          (coefficientMap_comp P (M.map u) (M.map v)))
        ((congrArg (coefficientMap P) (N.map_comp u v)).trans
          (coefficientMap_comp P (N.map u) (N.map v))) rfl n
  · rfl

/-- Original coefficient-square composition is constructed from the actual rectangle. -/
def comparison :
    (compositeSquare P α u v).RelHomotopy
      (((targetComposition P α u v).symm.trans (square P α (u ≫ v))).trans
        (sourceComposition P α u v)) :=
  Homotopy.RelHomotopy.ofLevels (rectangle P α u v).symmPath _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using rectangle_source_level P α u v n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using rectangle_target_level P α u v n)

/-- Rotate the actual original rectangle to the literal moving-square boundary. -/
def boundary :
    (square P α (u ≫ v)).RelHomotopy
      (((targetComposition P α u v).trans (compositeSquare P α u v)).trans
        (sourceComposition P α u v).symm) := by
  let B := targetComposition P α u v
  let A := sourceComposition P α u v
  let H := square P α (u ≫ v)
  let K := compositeSquare P α u v
  have J := comparison P α u v
  have route : (B.trans K).RelHomotopy (H.trans A) :=
    ((Homotopy.RelHomotopy.refl B).hcomp J).trans
      (((Homotopy.RelHomotopy.transAssoc B (B.symm.trans H) A).symm).trans
        ((((Homotopy.RelHomotopy.transAssoc B B.symm H).symm).hcomp
          (Homotopy.RelHomotopy.refl A)).trans
          ((((Homotopy.RelHomotopy.reflTransSymm B).symm.hcomp
            (Homotopy.RelHomotopy.refl H)).hcomp (Homotopy.RelHomotopy.refl A)).trans
            ((Homotopy.RelHomotopy.reflTrans H).hcomp (Homotopy.RelHomotopy.refl A)))))
  exact (Homotopy.RelHomotopy.transRefl H).symm.trans
    (((Homotopy.RelHomotopy.refl H).hcomp (Homotopy.RelHomotopy.reflTransSymm A)).trans
      (((Homotopy.RelHomotopy.transAssoc H A A.symm).symm).trans
        (route.symm.hcomp (Homotopy.RelHomotopy.refl A.symm))))

/-- Actual composition of the whole original transformation squares with original side tracks. -/
def movingSquare := (boundary P α u v).toSquare

end Quillen.PerfectComplexes.CoefficientTransformationComposition
namespace Quillen.LoopPrespectrum.Homotopy.Square

/-- Add the required terminal pause to one side track while keeping the other three sides exact. -/
def pauseRight {E F : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} (S : H₀.Square H₁ L M) :
    H₀.Square H₁ L (M.trans (Homotopy.refl g₁)) :=
  (S.toBoundary.trans ((Homotopy.RelHomotopy.refl (L.trans H₁)).hcomp
    (Homotopy.RelHomotopy.transRefl M).symm.symmPath)).toSquare

end Quillen.LoopPrespectrum.Homotopy.Square
