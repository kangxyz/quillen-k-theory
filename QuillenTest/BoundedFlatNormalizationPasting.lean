/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Functor

/-! Actual geometric inputs to the two binary normalization pastings used in Bass coherence. -/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.BoundedFlatNormalizationPasting

open Quillen

/-- Postwhisker the original composite-pullback comparison by the actual third pullback. -/
def geometric_first_factor {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :=
  exactNormalizationLeftPasting (boundedFlatPerfectPullback_exact (g ≫ h))
    ((boundedFlatPerfectPullback_exact h).comp (boundedFlatPerfectPullback_exact g))
    (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullbackCompIso g h).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen Y).weq_iso _ inferInstance)

/-- Prewhisker the original composite-pullback comparison by the actual third pullback. -/
def geometric_second_factor {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :=
  exactNormalizationRightPasting (boundedFlatPerfectPullback_exact h)
    (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackCompIso f g).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)

end QuillenTest.BoundedFlatNormalizationPasting
