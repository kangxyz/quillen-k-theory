/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedUnitRoutes
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting
public import Quillen.Topology.Prespectrum.HomotopySquareComposition
public import Quillen.Topology.Prespectrum.ConeSquareMapMovingCoherence

/-! An actual unit square for the original geometric pullback maps, with both split unit tracks. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum (Homotopy coneSquareIdentityTrack)
universe u
namespace Quillen.PerfectComplexes

/-- The right geometric unit route retains both the binary and identity normalizations. -/
def boundedFlatOriginalRightUnitRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedFlatPerfectPrespectrumMap f) (boundedFlatPerfectPrespectrumMap f) :=
  ((boundedFlatPerfectPrespectrumCompHomotopy (𝟙 X) f).cast
    (congrArg boundedFlatPerfectPrespectrumMap (Category.id_comp f)) rfl).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatPerfectPrespectrumIdHomotopy X)).cast rfl (Category.comp_id _))

/-- The left geometric unit route retains both original normalization pieces. -/
def boundedFlatOriginalLeftUnitRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedFlatPerfectPrespectrumMap f) (boundedFlatPerfectPrespectrumMap f) :=
  ((boundedFlatPerfectPrespectrumCompHomotopy f (𝟙 Y)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (Category.comp_id f)) rfl).trans
      (((boundedFlatPerfectPrespectrumIdHomotopy Y).postcomp
        (boundedFlatPerfectPrespectrumMap f)).cast rfl (Category.id_comp _))

/-- The right route's two full composition triangles identify its original split tracks. -/
def boundedFlatNormalizedRightUnitRouteComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatNormalizedRightUnitRoute f).RelHomotopy (boundedFlatOriginalRightUnitRoute f) :=
  ((boundedFlatNormalizedCompTrackComparison (𝟙 X) f).cast
    (congrArg boundedFlatPerfectPrespectrumMap (Category.id_comp f)) rfl).hcomp
      ((Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatNormalizedIdTrackComparison X)).cast rfl (Category.comp_id _))

/-- The left route's two full composition triangles identify its original split tracks. -/
def boundedFlatNormalizedLeftUnitRouteComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatNormalizedLeftUnitRoute f).RelHomotopy (boundedFlatOriginalLeftUnitRoute f) :=
  ((boundedFlatNormalizedCompTrackComparison f (𝟙 Y)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (Category.comp_id f)) rfl).hcomp
      (((boundedFlatNormalizedIdTrackComparison Y).postcomp
        (boundedFlatPerfectPrespectrumMap f)).cast rfl (Category.id_comp _))

/-- Both whole ORIGINAL unit routes agree through their actual normalized unit triangles. -/
def boundedFlatOriginalUnitRoutesComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatOriginalRightUnitRoute f).RelHomotopy (boundedFlatOriginalLeftUnitRoute f) :=
  (boundedFlatNormalizedRightUnitRouteComparison f).symm.trans
    ((boundedFlatNormalizedUnitRoutesComparison f).trans
      (boundedFlatNormalizedLeftUnitRouteComparison f))

/-- The original square is exactly the two composition tracks, with only endpoint transport. -/
theorem boundedFlatPerfectPrespectrumSquareHomotopy_level {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
    (h : p ≫ v = q ≫ w) (n : ℕ) :
    (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).level n =
      ((boundedFlatPerfectPrespectrumCompHomotopy p v).symm.trans
        ((boundedFlatPerfectPrespectrumCompHomotopy q w).cast
          (congrArg boundedFlatPerfectPrespectrumMap h).symm rfl)).level n := by
  have transport_level {E F : Quillen.LoopPrespectrum} {f f' g : E ⟶ F} (e : f = f')
      (p : Homotopy f g = Homotopy f' g) (H : Homotopy f g) :
      (p.mp H).level n = H.level n := by
    subst f'
    rfl
  unfold boundedFlatPerfectPrespectrumSquareHomotopy
  apply Homotopy.trans_level_congr
  · rfl
  · apply transport_level (congrArg boundedFlatPerfectPrespectrumMap h).symm

/-- The original geometric identity square, with the complete geometric and normalization sides. -/
def boundedFlatPerfectPrespectrumUnitSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatPerfectPrespectrumSquareHomotopy (𝟙 X) f f (𝟙 Y) (by simp)).Square
      (coneSquareIdentityTrack (boundedFlatPerfectPrespectrumMap f))
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatPerfectPrespectrumIdHomotopy X))
      ((boundedFlatPerfectPrespectrumIdHomotopy Y).postcomp
        (boundedFlatPerfectPrespectrumMap f)) := by
  let L := (Homotopy.precomp (boundedFlatPerfectPrespectrumMap f)
    (boundedFlatPerfectPrespectrumIdHomotopy X)).cast rfl (Category.comp_id _)
  let M := ((boundedFlatPerfectPrespectrumIdHomotopy Y).postcomp
    (boundedFlatPerfectPrespectrumMap f)).cast rfl (Category.id_comp _)
  have J := Homotopy.RelHomotopy.rotate (boundedFlatOriginalUnitRoutesComparison f)
  have K := J.trans
    ((Homotopy.RelHomotopy.transRefl L).symm.hcomp (Homotopy.RelHomotopy.refl M.symm))
  have S := K.toSquare
  refine S.ofBoundaryLevels _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  rw [boundedFlatPerfectPrespectrumSquareHomotopy_level]
  apply Homotopy.trans_level_congr <;> rfl

end Quillen.PerfectComplexes
