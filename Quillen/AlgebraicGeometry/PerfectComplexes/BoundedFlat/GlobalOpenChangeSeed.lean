/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenAction

/-! # The actual fine-to-coarse identity preserves the original global seed -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Forgetting support retains the original unit component. -/
theorem openRowChangeWeak_unit (a : Under R) :
    Preserves ((openRowChangeWeak f).app ((laurentUnderFunctor R).obj a)).functor
      ((globalLaurentAction Q).unit a) ((openLaurentAction f).unit a) := fun _ => rfl

/-- The fine-to-coarse identity preserves every original Laurent-track value. -/
theorem openRowChangeWeak_track (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((globalRow Q).obj a)).space n) :
    (prespectrumMap ((openRowChangeWeak f).app ((laurentUnderFunctor R).obj a))).map n
      (((globalLaurentAction Q).track.homotopy a).level n (t, x)) =
    ((openLaurentAction f).track.homotopy a).level n
      (t, (prespectrumMap ((openRowChangeWeak f).app a)).map n x) :=
  LaurentSeed.ModelAction.track_square _ _ _ (openRowChangeWeak_unit f) a n t x

/-- The original global seed commutes with the actual fine-to-coarse identity. -/
theorem openRowChangeWeak_seed :
    (globalLaurentAction Q).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor) =
    Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor ≫
      (openLaurentAction f).track.seed :=
  LaurentSeed.Track.seed_square _ _ _ (openRowChangeWeak_track f)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
