/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassSeedChangeWeak

/-!
# Consumers of the actual relative-open Laurent action and Bass seed

The original target scalar, degree-zero full track, cone null cylinder, loop coordinate and
strict fine-to-coarse seed square remain explicit. No stable-equivalence claim is made for the
seed or for the change of weaknesses.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.AffineOpenPair
open Quillen.PerfectComplexes


open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
  AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace QuillenTest.SectionOpenBassSeed

open Quillen
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The target action uses the original Laurent coordinate on the actual coefficient image. -/
theorem originalTargetAction (a : Under R)
    (s : (boundedFlatAffineSectionOpenModelFunctor j).obj a) :
    (boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a).hom.app s =
      (boundedFlatAffineSectionLaurentUnitIso a.right).hom.app
        (((boundedFlatAffineSectionOpenModelFunctor j).map
          ((laurentUnderCoefficient R).app a)).functor.obj s) := rfl

/-- The inverse target action uses the same original inverse Laurent unit. -/
theorem originalInverseTargetAction (a : Under R)
    (s : (boundedFlatAffineSectionOpenModelFunctor j).obj a) :
    (boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a).inv.app s =
      (boundedFlatAffineSectionLaurentUnitIso a.right).inv.app
        (((boundedFlatAffineSectionOpenModelFunctor j).map
          ((laurentUnderCoefficient R).app a)).functor.obj s) := rfl

/-- The entire original degree-zero action is preserved by the actual change of weaknesses. -/
theorem originalDegreeZeroTrack (a : Under R) (t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj a.right).space 0) :
    (boundedFlatAffineSectionOpenPrespectrumMap
        (inclusion j ((laurentUnderFunctor R).obj a))).map 0
        ((boundedFlatAffineSectionLaurentUnitHomotopy a.right).level 0 (t, x)) =
      (boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level 0
        (t, (boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map 0 x) :=
  boundedFlatAffineSectionOpenDiagramLaurentHomotopy_changeWeak_apply j a 0 t x

/-- Every cone null-cylinder value is retained at the original time. -/
theorem originalConeNullTrack (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj a.right).space n) :
    (boundedFlatAffineSectionOpenBassConeChangeWeak j a).map n
        ((boundedFlatAffineSectionBassNullHomotopy a.right).level n (t, x)) =
      (boundedFlatAffineSectionOpenBassNullHomotopy j a).level n
        (t, (boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map n x) :=
  boundedFlatAffineSectionOpenBassNullHomotopy_changeWeak_apply j a n t x

/-- The actual coarse seed loop keeps the original Laurent track and both original null legs. -/
theorem originalSeedLoop (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n)
    (t : unitInterval) :
    Path.toContinuousMap ((boundedFlatAffineSectionOpenBassSeedMap j a).map n x) t =
      (((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineSectionOpenBassSquare j a))))
        |>.conjugateToZero (boundedFlatAffineSectionOpenBassNullHomotopy j a)).level n (t, x) :=
  boundedFlatAffineSectionOpenBassSeedMap_apply j a n x t

/-- The two genuine original seed transformations satisfy the literal fine-to-coarse square. -/
theorem originalSeedSquare :
    boundedFlatAffineSectionBassUnderSeed R ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSectionOpenPrespectrumTransformation j) =
      boundedFlatAffineSectionOpenPrespectrumTransformation j ≫
        boundedFlatAffineSectionOpenBassSeed j :=
  boundedFlatAffineSectionOpenBassSeed_changeWeak j

end QuillenTest.SectionOpenBassSeed
