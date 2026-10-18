/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientSeed
public import Quillen.KTheory.Bass.SchemeCoefficientSeedNaturality

/-! # Actual Spec-row compatibility with the original ambient Bass seed -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex

/-- The original null/unit/null seed commutes with the actual integral Spec comparison. -/
theorem seed_square (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)) ≫
        bassComparison Q =
      rowComparison Q ≫ (globalLaurentAction Q).track.seed := by
  apply NatTrans.ext
  funext a
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, bassComparison_app]
  have h := SchemeCoefficientSeedNaturality.seed_naturality
    (ParameterLaurentTrack.ambientTrack Q.left) (globalLaurentAction Q).track
    (specUnder.obj a) a (squareComparison Q a) (squareComparison_track Q a)
  rw [squareComparison_source] at h
  exact h

end Quillen.PerfectComplexes.GlobalParameterCoefficient
