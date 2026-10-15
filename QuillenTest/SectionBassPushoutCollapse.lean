/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassPushoutCollapse

/-!
# Literal original Laurent-span collapse consumers

The actual Laurent evaluation square supplies the original span. Its cone collapse retains B
and the old overlap cylinder, kills every value of the attached C-cylinder, and is weak even at
level zero. The all-signed stable conclusion includes every negative degree.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum
open scoped unitInterval
universe u
namespace QuillenTest.SectionBassPushoutCollapse

open Quillen

/-- The unchanged actual Laurent span has complete cone-collapse weakness even in degree zero. -/
theorem actual_laurent_span_level_zero (i : ℕ) (R : CommRingCat.{u}) :
    IsWeakHomotopyEquivalence ((HomotopyPushout.rightConeCollapse
      ((boundedFlatAffineSectionBassDiagram i).map
        (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.hom)
      ((boundedFlatAffineSectionBassDiagram i).map
        (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).hom.left)).map 0) :=
  boundedFlatAffineSectionBass_rightConeCollapse_level_isWeakHomotopyEquivalence
    i i i (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.left
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.right
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).right.left _ _ 0

/-- The actual original Laurent-span collapse is invertible on every negative stable group. -/
theorem actual_laurent_span_negative_iso (i : ℕ) (R : CommRingCat.{u}) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map (HomotopyPushout.rightConeCollapse
      ((boundedFlatAffineSectionBassDiagram i).map
        (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.hom)
      ((boundedFlatAffineSectionBassDiagram i).map
        (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).hom.left))) :=
  boundedFlatAffineSectionBass_rightConeCollapse_isStableEquivalence
    i i i (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.left
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.right
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).right.left _ _ _

variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- The original B endpoint is exactly preserved, before any passage to stable groups. -/
theorem original_left_endpoint (n : ℕ) (y : B.space n) :
    (HomotopyPushout.rightConeCollapse f g).map n
      ((mappingConeInclusion (HomotopyPushout.inr f g)).map n
        ((HomotopyPushout.inl f g).map n y)) = (mappingConeInclusion f).map n y :=
  HomotopyPushout.rightConeCollapse_left f g n y

/-- The old original A-cylinder is retained at every independent cylinder parameter. -/
theorem original_overlap_cylinder (n : ℕ) (s : unitInterval) (x : A.space n) :
    (HomotopyPushout.rightConeCollapse f g).map n
      ((mappingConeInclusion (HomotopyPushout.inr f g)).map n
        (HomotopyPushout.cylinder f g n (s, x))) =
      ReducedMappingCone.cylinder (A.point n) (B.point n) (f.map n) (s, x) :=
  HomotopyPushout.rightConeCollapse_overlap f g n s x

/-- Every value of the new original C-cylinder is collapsed to the actual point. -/
theorem original_attached_cylinder (n : ℕ) (s : unitInterval) (x : C.space n) :
    (HomotopyPushout.rightConeCollapse f g).map n
      (ReducedMappingCone.cylinder (C.point n) ((HomotopyPushout.prespectrum f g).point n)
        ((HomotopyPushout.inr f g).map n) (s, x)) = (mappingCone f).point n :=
  HomotopyPushout.rightConeCollapse_attachedCylinder f g n s x

end QuillenTest.SectionBassPushoutCollapse
