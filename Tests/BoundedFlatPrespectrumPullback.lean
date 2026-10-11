/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.DerivedPullback

/-! Raw arbitrary-map pullbacks retain the existing localized morphism and original K-map. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.BoundedFlatPrespectrumPullback

lemma original_localized_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    toStableLocalization.map (boundedFlatPerfectPrespectrumMap f) =
      boundedFlatLocalizedPullback f := rfl

lemma original_k_map {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : BoundedFlatPerfectK Y n) :
    originalZeroSpaceEquiv (boundedFlatPerfectWaldhausen X) n
        (boundedFlatPerfectKPullback f n a) =
      Quillen.homotopyGroupMap ((boundedFlatPerfectPrespectrumMap f).map 0)
        ((boundedFlatPerfectPrespectrumMap f).map_point 0)
        (originalZeroSpaceEquiv (boundedFlatPerfectWaldhausen Y) n a) :=
  exactOriginalZeroSpaceEquiv_naturality _ _ (boundedFlatPerfectPullback_exact f) n a

lemma original_square_source {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z) (h : p ≫ v = q ≫ w)
    (n : ℕ) (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).level n (0, x) =
      (boundedFlatPerfectPrespectrumMap p).map n
        ((boundedFlatPerfectPrespectrumMap v).map n x) :=
  (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).at_zero n x

lemma original_square_target {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z) (h : p ≫ v = q ≫ w)
    (n : ℕ) (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).level n (1, x) =
      (boundedFlatPerfectPrespectrumMap q).map n
        ((boundedFlatPerfectPrespectrumMap w).map n x) :=
  (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).at_one n x

end Quillen.Tests.BoundedFlatPrespectrumPullback
