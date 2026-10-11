/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CompositionTrack
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Quillen.Topology.Prespectrum.RelativeHomotopyComposition
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! The original total composition tracks for three genuine bounded-flat pullbacks. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- First decompose the last two scheme arrows and then postcompose their actual track. -/
def boundedFlatNormalizedTripleLeftTrack {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Homotopy (boundedFlatPerfectPrespectrumMap (f ≫ g ≫ h))
      ((boundedFlatPerfectPrespectrumMap h ≫ boundedFlatPerfectPrespectrumMap g) ≫
        boundedFlatPerfectPrespectrumMap f) :=
  (boundedFlatNormalizedCompTrack f (g ≫ h)).trans
    ((boundedFlatNormalizedCompTrack g h).postcomp (boundedFlatPerfectPrespectrumMap f))

/-- The other route retains explicit scheme and prespectrum associativity transports. -/
def boundedFlatNormalizedTripleRightTrack {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Homotopy (boundedFlatPerfectPrespectrumMap (f ≫ g ≫ h))
      ((boundedFlatPerfectPrespectrumMap h ≫ boundedFlatPerfectPrespectrumMap g) ≫
        boundedFlatPerfectPrespectrumMap f) :=
  ((boundedFlatNormalizedCompTrack (f ≫ g) h).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap h)
      (boundedFlatNormalizedCompTrack f g))).cast
    (congrArg boundedFlatPerfectPrespectrumMap (Category.assoc f g h))
    (Category.assoc _ _ _).symm

/-- Endpoint transport in the original composition track does not change its full levels. -/
theorem boundedFlatNormalizedCompTrack_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (boundedFlatNormalizedCompTrack f g).level n =
      (originalPrespectrumTransformationHomotopy (boundedFlatPerfectWaldhausen Z)
        (boundedFlatPerfectWaldhausen X) (boundedFlatNormalizedPullback_exact (f ≫ g))
        ((boundedFlatNormalizedPullback_exact g).comp (boundedFlatNormalizedPullback_exact f))
        (boundedFlatNormalizedPullback_obj_zero _)
        ((congrArg (boundedFlatNormalizedPullback f).obj
          (boundedFlatNormalizedPullback_obj_zero g)).trans
            (boundedFlatNormalizedPullback_obj_zero f))
        (boundedFlatNormalizedPullbackCompIso f g).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)).level n := by
  have homotopy_level_cast {E F : LoopPrespectrum} {a b b' : E ⟶ F} (e : b = b')
      (p : Homotopy a b = Homotopy a b') (H : Homotopy a b) (k : ℕ) :
      (p.mp H).level k = H.level k := by
    subst b'
    rfl
  unfold boundedFlatNormalizedCompTrack
  apply homotopy_level_cast (originalPrespectrumMap_comp _ _ _
    (boundedFlatNormalizedPullback_exact g) (boundedFlatNormalizedPullback_exact f)
    (boundedFlatNormalizedPullback_obj_zero g) (boundedFlatNormalizedPullback_obj_zero f))

/-- The first route of the genuine geometric comparison is the literal postcomposed track. -/
theorem boundedFlatNormalizedTripleLeftTrack_level {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (n : ℕ) :
    (boundedFlatNormalizedTripleLeftTrack f g h).level n =
      ((boundedFlatNormalizedTriplePasting f g h).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x) =
    ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact DFunLike.congr_fun (boundedFlatNormalizedCompTrack_level f (g ≫ h) n) _
  · change (boundedFlatPerfectPrespectrumMap f).map n
      ((boundedFlatNormalizedCompTrack g h).level n _) = _
    rw [boundedFlatNormalizedCompTrack_level]
    symm
    exact DFunLike.congr_fun
      (originalPrespectrumTransformationHomotopy_postcomp_level
        (boundedFlatNormalizedPullback_exact (g ≫ h))
        ((boundedFlatNormalizedPullback_exact h).comp (boundedFlatNormalizedPullback_exact g))
        (boundedFlatNormalizedPullback_exact f)
        (boundedFlatNormalizedPullback_obj_zero _) _ (boundedFlatNormalizedPullback_obj_zero _)
        (boundedFlatNormalizedPullbackCompIso g h).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen Y).weq_iso _ inferInstance) n) _

/-- The second route retains the original precomposed track and both associativity transports. -/
theorem boundedFlatNormalizedTripleRightTrack_level {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (n : ℕ) :
    (boundedFlatNormalizedTripleRightTrack f g h).level n =
      ((boundedFlatNormalizedTriplePasting f g h).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x) =
    ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact DFunLike.congr_fun (boundedFlatNormalizedCompTrack_level (f ≫ g) h n) _
  · change (boundedFlatNormalizedCompTrack f g).level n
      (_, (boundedFlatPerfectPrespectrumMap h).map n x) = _
    rw [boundedFlatNormalizedCompTrack_level]
    symm
    exact DFunLike.congr_fun
      (originalPrespectrumTransformationHomotopy_precomp_level
        (boundedFlatNormalizedPullback_exact h) (boundedFlatNormalizedPullback_exact (f ≫ g))
        ((boundedFlatNormalizedPullback_exact g).comp (boundedFlatNormalizedPullback_exact f))
        (boundedFlatNormalizedPullback_obj_zero _) (boundedFlatNormalizedPullback_obj_zero _) _
        (boundedFlatNormalizedPullbackCompIso f g).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) n) _

/-- Genuine geometric associativity compares the original whole binary tracks, with their
literal pre/postcomposition maps. No geometric coherence is supplied as a hypothesis. -/
def boundedFlatNormalizedTripleTrackComparison {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedFlatNormalizedTripleLeftTrack f g h).RelHomotopy
      (boundedFlatNormalizedTripleRightTrack f g h) where
  level n := {
    toFun := (boundedFlatNormalizedTriplePasting f g h).level n
    continuous_toFun := ((boundedFlatNormalizedTriplePasting f g h).level n).continuous
    map_zero_left z := by
      rw [boundedFlatNormalizedTripleLeftTrack_level]
      rfl
    map_one_left z := by
      rw [boundedFlatNormalizedTripleRightTrack_level]
      rfl
    prop' r z hz := by
      change (boundedFlatNormalizedTriplePasting f g h).level n (r, z) = _
      rw [boundedFlatNormalizedTripleLeftTrack_level, Homotopy.RelHomotopy.at_zero]
      exact ((boundedFlatNormalizedTriplePasting f g h).level n).eq_fst r hz }
  comm n r s x t := (boundedFlatNormalizedTriplePasting f g h).comm n r s x t

/-- The left route uses the existing geometric-plus-binary-normalization tracks verbatim. -/
def boundedFlatTripleLeftTrack {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Homotopy (boundedFlatPerfectPrespectrumMap (f ≫ g ≫ h))
      ((boundedFlatPerfectPrespectrumMap h ≫ boundedFlatPerfectPrespectrumMap g) ≫
        boundedFlatPerfectPrespectrumMap f) :=
  (boundedFlatPerfectPrespectrumCompHomotopy f (g ≫ h)).trans
    ((boundedFlatPerfectPrespectrumCompHomotopy g h).postcomp (boundedFlatPerfectPrespectrumMap f))

/-- The right route uses the existing tracks and explicitly transports both associations. -/
def boundedFlatTripleRightTrack {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Homotopy (boundedFlatPerfectPrespectrumMap (f ≫ g ≫ h))
      ((boundedFlatPerfectPrespectrumMap h ≫ boundedFlatPerfectPrespectrumMap g) ≫
        boundedFlatPerfectPrespectrumMap f) :=
  ((boundedFlatPerfectPrespectrumCompHomotopy (f ≫ g) h).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap h)
      (boundedFlatPerfectPrespectrumCompHomotopy f g))).cast
    (congrArg boundedFlatPerfectPrespectrumMap (Category.assoc f g h))
    (Category.assoc _ _ _).symm

/-- The original geometric and binary normalization tracks satisfy genuine whole associativity.
The only input is the three arbitrary scheme maps; the relative filler is constructed from the
proved geometric pseudofunctor equation and actual normalization triangles. -/
def boundedFlatTripleTrackComparison {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedFlatTripleLeftTrack f g h).RelHomotopy
      (boundedFlatTripleRightTrack f g h) :=
  ((boundedFlatNormalizedCompTrackComparison f (g ≫ h)).hcomp
    ((boundedFlatNormalizedCompTrackComparison g h).postcomp
      (boundedFlatPerfectPrespectrumMap f))).symm.trans
    ((boundedFlatNormalizedTripleTrackComparison f g h).trans
      (((boundedFlatNormalizedCompTrackComparison (f ≫ g) h).hcomp
        (Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap h)
          (boundedFlatNormalizedCompTrackComparison f g))).cast
        (congrArg boundedFlatPerfectPrespectrumMap (Category.assoc f g h))
        (Category.assoc _ _ _).symm))

end Quillen.PerfectComplexes
