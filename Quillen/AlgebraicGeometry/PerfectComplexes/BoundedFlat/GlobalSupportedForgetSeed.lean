/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedAction

/-! # The actual supported inclusion preserves the original global seed -/
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

/-- Forgetting support retains the original lifted unit component. -/
theorem supportedRowForget_unit (a : Under R) :
    Preserves ((supportedRowForget f).app ((laurentUnderFunctor R).obj a)).functor
      ((supportedLaurentAction f).unit a) ((globalLaurentAction Q).unit a) :=
  map_lift_hom (rowSupported f ((laurentUnderFunctor R).obj a)).ι (globalLaurentUnit Q a)

/-- The support inclusion preserves every original Laurent-track value. -/
theorem supportedRowForget_track (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((supportedRow f).obj a)).space n) :
    (prespectrumMap ((supportedRowForget f).app ((laurentUnderFunctor R).obj a))).map n
      (((supportedLaurentAction f).track.homotopy a).level n (t, x)) =
    ((globalLaurentAction Q).track.homotopy a).level n
      (t, (prespectrumMap ((supportedRowForget f).app a)).map n x) :=
  LaurentSeed.ModelAction.track_square _ _ _ (supportedRowForget_unit f) a n t x

/-- The original global seed commutes with the actual supported inclusion. -/
theorem supportedRowForget_seed :
    (supportedLaurentAction f).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (supportedRowForget f) prespectrumFunctor) =
    Functor.whiskerRight (supportedRowForget f) prespectrumFunctor ≫
      (globalLaurentAction Q).track.seed :=
  LaurentSeed.Track.seed_square _ _ _ (supportedRowForget_track f)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
