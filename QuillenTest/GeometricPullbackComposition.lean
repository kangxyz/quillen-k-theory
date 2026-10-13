/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactCompositionHomotopy
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit

/-! Two actual geometric pullback-comparison tracks after canonical spectrum normalization.
Binary normalization of composites of spectrum maps remains a separate obligation. -/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
universe u
namespace QuillenTest.GeometricPullbackComposition

open Quillen

/-- These are two actual geometric pullback-composition isomorphisms, with all original
normalizations retained and no supplied higher coherence hypothesis. -/
def geometric_pullback_composition {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) [Flat f] [Flat g] [Flat h] :=
  exactOriginalPrespectrumIsoCompositionHomotopy (perfectWaldhausen T) (perfectWaldhausen X)
    (perfectFlatPullback_waldhausenExact ((f ≫ g) ≫ h))
    ((perfectFlatPullback_waldhausenExact h).comp
      (perfectFlatPullback_waldhausenExact (f ≫ g)))
    ((perfectFlatPullback_waldhausenExact h).comp
      ((perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f)))
    (perfectFlatPullbackCompIso (f ≫ g) h)
    (Functor.isoWhiskerLeft (perfectFlatPullback h) (perfectFlatPullbackCompIso f g))


end QuillenTest.GeometricPullbackComposition
