/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.StrictSquareConeInterchangeNaturality

/-!
# Original strict-square cofiber-interchange consumers

These clients retain the actual double target, all three independent interval coordinates,
the unchanged coefficient cube, and the literal quotient inverse. No signed-boundary law
is inferred from the genuine point-set coordinate swap.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.StrictSquareConeInterchange
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T)

/-- The original target corner keeps both literal cone inclusions. -/
theorem originalDoubleTarget (n : ℕ) (x : T.right.right.space n) :
    (StrictSquare.coneInterchangeIso a).hom.map n
      ((mappingConeInclusion (mappingConeMap (strictSquareComparisonFunctor.map a))).map n
        ((mappingConeInclusion (StrictSquare.comparison T)).map n x)) =
      (mappingConeInclusion (StrictSquare.comparison (StrictSquare.coneSquare a))).map n
        ((mappingConeInclusion a.right.right).map n x) :=
  StrictSquare.coneInterchangeIso_inclusion_inclusion a n x

/-- The literal span/cofiber interchange keeps both independent original cylinder times. -/
theorem originalSpanCylinder (n : ℕ) (r s : unitInterval) (x : S.left.left.space n) :
    (StrictSquare.coneSpanIso a).hom.map n
      (ReducedMappingCone.cylinder ((StrictSquare.span S).point n)
        ((StrictSquare.span T).point n) ((StrictSquare.spanMap a).map n)
        (r, HomotopyPushout.cylinder S.left.hom S.hom.left n (s, x))) =
      HomotopyPushout.cylinder (mappingConeMap (StrictSquare.coneTopFace a))
        (mappingConeMap (StrictSquare.coneLeftFace a)) n
        (s, ReducedMappingCone.cylinder (S.left.left.point n) (T.left.left.point n)
          (a.left.left.map n) (r, x)) := rfl

/-- Structure time is independent of the two swapped original cone coordinates. -/
theorem originalThreeTimes (n : ℕ) (r s t : unitInterval) (x : (StrictSquare.span S).space n) :
    (mappingCone (StrictSquare.comparison (StrictSquare.coneSquare a))).structureMap n
      ((StrictSquare.coneInterchangeIso a).hom.map n
        (ReducedMappingCone.cylinder ((mappingCone (StrictSquare.comparison S)).point n)
          ((mappingCone (StrictSquare.comparison T)).point n)
          ((mappingConeMap (strictSquareComparisonFunctor.map a)).map n)
          (r, ReducedMappingCone.cylinder ((StrictSquare.span S).point n)
            (S.right.right.point n) ((StrictSquare.comparison S).map n) (s, x)))) t =
      ReducedMappingCone.cylinder ((StrictSquare.span (StrictSquare.coneSquare a)).point (n + 1))
        ((mappingCone a.right.right).point (n + 1))
        ((StrictSquare.comparison (StrictSquare.coneSquare a)).map (n + 1))
        (s, (StrictSquare.coneSpanIso a).hom.map (n + 1)
          (ReducedMappingCone.cylinder ((StrictSquare.span S).point (n + 1))
            ((StrictSquare.span T).point (n + 1)) ((StrictSquare.spanMap a).map (n + 1))
            (r, (StrictSquare.span S).structureMap n x t))) := by
  exact (congrArg (fun p ↦ p t) ((StrictSquare.coneInterchangeIso a).hom.comm n _)).symm

/-- Every actual coefficient cube commutes on the original quotient, not just on stable classes. -/
theorem originalCoefficientCube {S' T' : Arrow (Arrow LoopPrespectrum.{u})}
    {b : S' ⟶ T'} (k : Arrow.mk a ⟶ Arrow.mk b) (n : ℕ)
    (x : (mappingCone (mappingConeMap (strictSquareComparisonFunctor.map a))).space n) :
    (StrictSquare.coneInterchangeIso b).hom.map n
      ((mappingConeMap
        ((strictSquareComparisonFunctor ⋙ mappingConeFunctor).mapArrow.map k)).map n x) =
      (mappingConeMap
        (strictSquareComparisonFunctor.map (StrictSquare.coneSquareMap k))).map n
          ((StrictSquare.coneInterchangeIso a).hom.map n x) :=
  congrArg (fun f ↦ f.map n x) (StrictSquare.coneInterchangeIso_naturality k)

/-- The actual quotient map has its original strict inverse at every level. -/
theorem originalPointwiseInverse (n : ℕ)
    (x : (mappingCone (mappingConeMap (strictSquareComparisonFunctor.map a))).space n) :
    (StrictSquare.coneInterchangeIso a).inv.map n
      ((StrictSquare.coneInterchangeIso a).hom.map n x) = x :=
  congrArg (fun f ↦ f.map n x) (StrictSquare.coneInterchangeIso a).hom_inv_id

end Quillen.Tests.StrictSquareConeInterchange
