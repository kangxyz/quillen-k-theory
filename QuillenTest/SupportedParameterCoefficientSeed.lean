/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterCoefficientSeed

/-!
# Original supported Spec seed on arbitrary native inputs

The regression retains the original supported input, every native degree, and the
independent output loop time. It also checks the actual coefficient restriction of the
same complete seed square, rather than a newly chosen loop or source null.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : (parameterDiagram f).obj (specUnder.obj a) |>.space n) (t : unitInterval) :
    (show Path _ _ from ((bassComparison f).app a).map n
        (((SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left)).app
          (specUnder.obj a)).map n x)) t =
      (show Path _ _ from ((supportedLaurentAction f).track.seed.app a).map n
        (((rowComparison f).app a).map n x)) t :=
  congrArg (fun k => (show Path _ _ from k.map n x) t)
    (NatTrans.congr_app (seed_square f) a)

example :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left)) ≫
      bassComparison f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor _)).map
        (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor) =
    rowComparison f ≫ Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor ≫
      (boundedFlatCoefficientSupportedLaurentAction f).track.seed := by
  rw [← Category.assoc]
  erw [seed_square f]
  rw [Category.assoc, supportedRowRestriction_seed]
