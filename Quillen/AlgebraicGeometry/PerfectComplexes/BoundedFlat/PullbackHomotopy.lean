/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PullbackCoherence
public import Quillen.Waldhausen.SConstruction.Iterated.ExactPastingHomotopy

/-!
# Relative comparison of the two original triple-pullback tracks

For arbitrary scheme maps, the actual bounded-flat geometric associativity equation supplies a
whole relative comparison of its two normalized transformation pastings. Both the original
functor associator and the scheme-associativity transport are retained. Comparison with binary
normalization of spectrum-map composition and the final Bass moving-boundary descent are separate.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The two genuine geometric routes for triple bounded-flat pullback have relatively homotopic
normalized spectrum tracks, without flatness hypotheses on the scheme maps. -/
def boundedFlatPerfectTriplePullbackHomotopy {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    let W := boundedFlatPerfectWaldhausen T
    let V := boundedFlatPerfectWaldhausen X
    let hA := boundedFlatPerfectPullback_exact (f ≫ g ≫ h)
    let hB := (boundedFlatPerfectPullback_exact (g ≫ h)).comp
      (boundedFlatPerfectPullback_exact f)
    let hB' := (boundedFlatPerfectPullback_exact h).comp
      (boundedFlatPerfectPullback_exact (f ≫ g))
    let hD := (boundedFlatPerfectPullback_exact h).comp
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    let e := boundedFlatPerfectPullbackCompIso f (g ≫ h)
    let e₂ := Functor.isoWhiskerRight (boundedFlatPerfectPullbackCompIso g h)
      (boundedFlatPerfectPullback f) ≪≫
        Functor.associator (boundedFlatPerfectPullback h) (boundedFlatPerfectPullback g)
          (boundedFlatPerfectPullback f)
    let e' := eqToIso (congrArg boundedFlatPerfectPullback (Category.assoc f g h).symm) ≪≫
      boundedFlatPerfectPullbackCompIso (f ≫ g) h
    let e₂' := Functor.isoWhiskerLeft (boundedFlatPerfectPullback h)
      (boundedFlatPerfectPullbackCompIso f g)
    ((exactOriginalPrespectrumIsoHomotopy W V hA hB e).trans
      (exactOriginalPrespectrumIsoHomotopy W V hB hD e₂)).RelHomotopy
      ((exactOriginalPrespectrumIsoHomotopy W V hA hB' e').trans
        (exactOriginalPrespectrumIsoHomotopy W V hB' hD e₂')) := by
  dsimp only
  apply exactOriginalPrespectrumPastingHomotopy
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    eqToIso.hom, Category.assoc] using boundedFlatPerfectPullbackCompIso_two_routes f g h

end Quillen.PerfectComplexes
