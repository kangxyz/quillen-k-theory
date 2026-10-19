/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCoherence

/-!
# Composition of the original global polynomial input squares

The arbitrary-scheme geometric rectangle compares the original direct polynomial square
with the two original successive squares. Both geometric composition tracks and the actual
polynomial functor composition transport are retained. Only generic geometric lemmas are
used from the coefficient coherence owner; no coefficient/global object identification enters.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionPolynomial
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual source geometric composition, in contravariant order. -/
def sourceComposition := boundedFlatPerfectPrespectrumCompHomotopy f g

/-- Polynomial composition uses the original split track and genuine functor composition. -/
def polynomialComposition :
    Homotopy (boundedFlatPerfectPrespectrumMap (polynomial.map (f ≫ g)))
      (boundedFlatPerfectPrespectrumMap (polynomial.map g) ≫
        boundedFlatPerfectPrespectrumMap (polynomial.map f)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (polynomial.map f) (polynomial.map g)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (polynomial.map_comp f g)).symm rfl

/-- The maintained whole geometric rectangle on the actual three polynomial projections. -/
def rectangle :=
  DoubleSquareTrack.originalComparison g f (polynomial.map g) (polynomial.map f)
    (projection.app Z) (projection.app Y) (projection.app X)
    (projection.naturality g).symm (projection.naturality f).symm

/-- The two successive original polynomial squares with their unchanged associations. -/
def compositeSquare :=
  ((polynomialSquareHomotopy g).postcomp
    (boundedFlatPerfectPrespectrumMap (polynomial.map f))).trans
    ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
      (polynomialSquareHomotopy f)).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)

/-- The original source composition followed by the actual target projection. -/
def sourceTrack :=
  (sourceComposition f g).postcomp (boundedFlatPerfectPrespectrumMap (projection.app X))

/-- The actual polynomial composition under the unchanged source projection. -/
def targetTrack :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app Z))
    (polynomialComposition f g)).cast rfl (Category.assoc _ _ _).symm

/-- Every initial rectangle value is the two original successive polynomial squares. -/
theorem rectangle_source_level (n : ℕ) :
    (compositeSquare f g).level n = (((rectangle f g).symmPath).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  unfold DoubleSquareTrack.originalLeft
  rw [Homotopy.symm_trans]
  unfold compositeSquare
  apply Homotopy.trans_level_congr
  · rw [← Homotopy.postcomp_symm]
    apply Homotopy.postcomp_level_congr
    exact (boundedFlatGeometricSquareReverse_level
      (polynomial.map g) (projection.app Z) (projection.app Y) g
      (projection.naturality g) n).symm
  · change (Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
      (polynomialSquareHomotopy f)).level n =
        (Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
          (boundedFlatPerfectPrespectrumSquareHomotopy
            (projection.app X) f (polynomial.map f) (projection.app Y)
            (projection.naturality f).symm)).symm.level n
    rw [← Homotopy.precomp_symm]
    apply Homotopy.precomp_level_congr
    exact (boundedFlatGeometricSquareReverse_level
      (polynomial.map f) (projection.app Y) (projection.app X) f
      (projection.naturality f) n).symm

/-- The full terminal rectangle retains the direct square and both composition tracks. -/
theorem rectangle_target_level (n : ℕ) :
    (((targetTrack f g).symm.trans (polynomialSquareHomotopy (f ≫ g))).trans
      (sourceTrack f g)).level n = (((rectangle f g).symmPath).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  unfold DoubleSquareTrack.originalRight
  rw [Homotopy.symm_trans, Homotopy.symm_trans, Homotopy.symm_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · apply Homotopy.symm_level_congr
      rfl
    · refine (boundedFlatGeometricSquareReverse_level
        (polynomial.map (f ≫ g)) (projection.app Z) (projection.app X) (f ≫ g)
        (projection.naturality (f ≫ g)) n).symm.trans ?_
      apply Homotopy.symm_level_congr
      exact boundedFlatGeometricSquare_level_congr _ _ rfl rfl
        (polynomial.map_comp f g) rfl n
  · rfl

/-- The original geometric rectangle gives the complete polynomial composition comparison. -/
def comparison :
    (compositeSquare f g).RelHomotopy
      (((targetTrack f g).symm.trans (polynomialSquareHomotopy (f ≫ g))).trans
        (sourceTrack f g)) :=
  Homotopy.RelHomotopy.ofLevels (rectangle f g).symmPath _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using rectangle_source_level f g n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using rectangle_target_level f g n)

/-- Rotate the actual rectangle to the direct-to-composite moving-square boundary. -/
def boundary :
    (polynomialSquareHomotopy (f ≫ g)).RelHomotopy
      (((targetTrack f g).trans (compositeSquare f g)).trans (sourceTrack f g).symm) := by
  let B := targetTrack f g
  let A := sourceTrack f g
  let H := polynomialSquareHomotopy (f ≫ g)
  let K := compositeSquare f g
  have J := comparison f g
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

/-- The actual whole polynomial composition square, with both original geometric sides. -/
def square := (boundary f g).toSquare

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionPolynomial
