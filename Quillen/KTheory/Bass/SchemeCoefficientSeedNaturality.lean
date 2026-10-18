/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeNaturalSeed
public import Quillen.KTheory.Bass.StrictLaurentSeed
public import Quillen.Topology.Prespectrum.StrictSquareSeedNaturality

/-!
# Original Scheme and coefficient seeds under a whole square map

The original endpoint casts in the two seed constructions preserve their complete
null/unit/null words. A map between their original strict squares, preserving the
specified scalar track at every time, therefore gives the original seed square.
The scheme point and coefficient object are arbitrary; geometric consumers supply
their actual square map and the same-time scalar compatibility.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum
universe u w
namespace Quillen.KTheory.Bass.SchemeCoefficientSeedNaturality
open NaturalTrack GeometricSeedCospan
variable {R : CommRingCat.{u}} {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    {G : Under R ⥤ LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : LaurentSeed.Track G)
    (X : Scheme.{u}ᵒᵖ) (a : Under R)

/-- Only the original coefficient diagonal endpoints are changed to their square presentation. -/
def coefficientTrack :
    Homotopy ((LaurentSeed.square G a).left.hom ≫ (LaurentSeed.square G a).hom.right)
      ((LaurentSeed.square G a).left.hom ≫ (LaurentSeed.square G a).hom.right) :=
  (B.homotopy a).cast (LaurentSeed.square_source G a).symm
    (LaurentSeed.square_source G a).symm

/-- The original Scheme seed is the strict-square seed with its original endpoint cast. -/
theorem scheme_seed_eq :
    (SchemeNaturalSeed.seed A).app X =
      ((sourceTrack F A.homotopy X).postcomp
        (mappingConeInclusion (StrictSquare.comparison
          (F.mapArrow.mapArrow.obj (square X))))).nullLoopMap
        (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (square X))) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext t
  rfl

/-- The original coefficient seed has the same whole word after its diagonal endpoint cast. -/
theorem coefficient_seed_eq :
    B.seed.app a =
      ((coefficientTrack B a).postcomp
        (mappingConeInclusion (StrictSquare.comparison (LaurentSeed.square G a)))).nullLoopMap
        (StrictSquare.sourceNullHomotopy (LaurentSeed.square G a)) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext t
  rfl

/-- A whole scalar square gives the original Scheme-to-coefficient seed square. -/
theorem seed_naturality
    (e : F.mapArrow.mapArrow.obj (square X) ⟶ LaurentSeed.square G a)
    (hU : ∀ n r x, e.right.right.map n ((A.homotopy X).level n (r, x)) =
      (B.homotopy a).level n (r, e.left.left.map n x)) :
    (SchemeNaturalSeed.seed A).app X ≫ strictSquareLoopedConeFunctor.map e =
      e.left.left ≫ B.seed.app a := by
  rw [scheme_seed_eq A X, coefficient_seed_eq B a]
  exact StrictSquare.sourceSeed_naturality e (sourceTrack F A.homotopy X)
    (coefficientTrack B a) hU

end Quillen.KTheory.Bass.SchemeCoefficientSeedNaturality
