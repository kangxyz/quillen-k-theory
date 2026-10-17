/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrack
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationIntertwining
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationNaturality

/-!
# Actual global-unit operations under arbitrary bounded-flat pullback

The existing geometric composition tracks and existing unit squares imply the original
K-operation pre/postcomposition laws. These retain the exact original geometric maps and
units, and require no flatness of either scheme morphism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- Arbitrary target pullback preserves the actual original bounded-flat unit operation. -/
theorem boundedFlatPerfectUnitHomotopy_originalKOperation_postcomp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : (Γ(Y, ⊤))ˣ) (n : ℕ) :
    (boundedFlatPerfectKPullback f (n + 1)).comp
      (originalKSelfTrackOperation (boundedFlatPerfectWaldhausen Z)
        (boundedFlatPerfectWaldhausen Y) (boundedFlatPerfectUnitHomotopy g r) n) =
      originalKSelfTrackOperation (boundedFlatPerfectWaldhausen Z)
        (boundedFlatPerfectWaldhausen X)
        (boundedFlatPerfectUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)) n := by
  unfold boundedFlatPerfectKPullback
  rw [← originalKSelfTrackOperation_postcomp]
  exact (originalKSelfTrackOperation_intertwine
    (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r))
    ((boundedFlatPerfectUnitHomotopy g r).postcomp (boundedFlatPerfectPrespectrumMap f))
    (boundedFlatPerfectPrespectrumCompHomotopy f g)
    (boundedFlatPerfectUnitTrackPostcomp f g r).symm n).symm

/-- Arbitrary source pullback preserves the actual original bounded-flat unit operation. -/
theorem boundedFlatPerfectUnitHomotopy_originalKOperation_precomp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : (Γ(X, ⊤))ˣ) (n : ℕ) :
    (originalKSelfTrackOperation (boundedFlatPerfectWaldhausen Y)
      (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectUnitHomotopy f q) n).comp
        (boundedFlatPerfectKPullback g n) =
      originalKSelfTrackOperation (boundedFlatPerfectWaldhausen Z)
        (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectUnitHomotopy (f ≫ g) q) n := by
  unfold boundedFlatPerfectKPullback
  rw [← originalKSelfTrackOperation_precomp]
  exact (originalKSelfTrackOperation_intertwine
    (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectUnitHomotopy (f ≫ g) q)
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap g) (boundedFlatPerfectUnitHomotopy f q))
    (boundedFlatPerfectPrespectrumCompHomotopy f g)
    (boundedFlatPerfectUnitTrackPrecomp f g q).symm n).symm

end Quillen.PerfectComplexes
