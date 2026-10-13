/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Functor
public import Quillen.Waldhausen.SConstruction.Iterated.ExactCoherence
public import Quillen.Topology.Prespectrum.HomotopyLoop

/-!
# Original bounded-flat prespectrum pullback under arbitrary scheme maps

Actual Waldhausen-exact bounded-flat pullback supplies the raw normalized maps, before passing to
stable localization. The original geometric identity, composition and commuting-square tracks are
retained. These data do not assert strict functoriality or coherent Bass transition naturality.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The original prespectrum map induced by genuine bounded-flat pullback, with no flatness
hypothesis on the scheme morphism. -/
def boundedFlatPerfectPrespectrumMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    originalPrespectrum (boundedFlatPerfectWaldhausen Y) ⟶
      originalPrespectrum (boundedFlatPerfectWaldhausen X) :=
  exactOriginalPrespectrumMap _ _ (boundedFlatPerfectPullback_exact f)

/-- The actual geometric identity comparison includes canonical spectrum normalization. -/
def boundedFlatPerfectPrespectrumIdHomotopy (X : Scheme.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (𝟙 X)) (𝟙 _) :=
  (exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectPullback_exact (𝟙 X))
    (Waldhausen.IsExact.id _ _) (boundedFlatPerfectPullbackIdIso X)).trans
      (exactOriginalPrespectrumMapIdHomotopy _)

/-- The actual geometric composition comparison includes canonical spectrum normalization. -/
def boundedFlatPerfectPrespectrumCompHomotopy {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (boundedFlatPerfectPrespectrumMap (f ≫ g))
      (boundedFlatPerfectPrespectrumMap g ≫ boundedFlatPerfectPrespectrumMap f) :=
  (exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackCompIso f g)).trans
      (exactOriginalPrespectrumMapCompHomotopy _ _ _
        (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f))

/-- An actual commuting geometric square induces a whole homotopy between its original raw
bounded-flat prespectrum composites. -/
def boundedFlatPerfectPrespectrumSquareHomotopy {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
    (h : p ≫ v = q ≫ w) :
    Homotopy (boundedFlatPerfectPrespectrumMap v ≫ boundedFlatPerfectPrespectrumMap p)
      (boundedFlatPerfectPrespectrumMap w ≫ boundedFlatPerfectPrespectrumMap q) := by
  have H := boundedFlatPerfectPrespectrumCompHomotopy q w
  have e : boundedFlatPerfectPrespectrumMap (p ≫ v) =
      boundedFlatPerfectPrespectrumMap (q ≫ w) := by congr 1
  rw [← e] at H
  exact (boundedFlatPerfectPrespectrumCompHomotopy p v).symm.trans H

end Quillen.PerfectComplexes
