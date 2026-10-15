/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactCompositionHomotopy
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PullbackCoherence

/-! Two actual geometric pullback-comparison tracks after canonical spectrum normalization.
Binary normalization of composites of spectrum maps remains a separate obligation. -/
@[expose] public section

open Quillen.PerfectComplexes


noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.BoundedFlatPullbackCoherence

open Quillen

/-- These are two actual geometric pullback-composition isomorphisms, with all original
normalizations retained and no supplied higher coherence hypothesis. -/
def arbitrary_pullback_composition {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :=
  exactOriginalPrespectrumIsoCompositionHomotopy (boundedFlatPerfectWaldhausen T)
    (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectPullback_exact ((f ≫ g) ≫ h))
    ((boundedFlatPerfectPullback_exact h).comp
      (boundedFlatPerfectPullback_exact (f ≫ g)))
    ((boundedFlatPerfectPullback_exact h).comp
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f)))
    (boundedFlatPerfectPullbackCompIso (f ≫ g) h)
    (Functor.isoWhiskerLeft (boundedFlatPerfectPullback h) (boundedFlatPerfectPullbackCompIso f g))


/-- The original comparison routes agree on the actual underlying complex of every bounded-flat
object; no flatness assumptions on the three scheme morphisms are needed. -/
lemma original_two_routes {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (K : BoundedFlatPerfect T) :
    (((boundedFlatPerfectPullbackCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (boundedFlatPerfectPullbackCompIso g h).hom
        (boundedFlatPerfectPullback f) ≫
      (Functor.associator (boundedFlatPerfectPullback h) (boundedFlatPerfectPullback g)
        (boundedFlatPerfectPullback f)).hom).app K).hom =
    (((eqToHom (by simp) : boundedFlatPerfectPullback (f ≫ g ≫ h) ⟶
      boundedFlatPerfectPullback ((f ≫ g) ≫ h)) ≫
      (boundedFlatPerfectPullbackCompIso (f ≫ g) h).hom ≫
      Functor.whiskerLeft (boundedFlatPerfectPullback h)
        (boundedFlatPerfectPullbackCompIso f g).hom).app K).hom :=
  congrArg (fun η ↦ (η.app K).hom) (boundedFlatPerfectPullbackCompIso_two_routes f g h)

end QuillenTest.BoundedFlatPullbackCoherence
