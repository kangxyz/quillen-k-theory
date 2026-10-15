/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGradingLift

/-!
Consumers of the original section grade's algebraic extension. The zero criterion uses the
actual raw restriction image and original perfect evaluation, without replacing the quotient.
-/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
open Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace QuillenTest.FullOpenSectionGradingLift

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual algebraic class retains the quotient class of the original evaluated object. -/
theorem original_object_grade (a : Under R) (S : BoundedFlatAffineFullOpenSections j a) :
    lift (boundedFlatAffineFullOpenSectionWaldhausen j a)
        (boundedFlatAffineFullOpenSectionGrading j a)
        (objectClass (boundedFlatAffineFullOpenSectionWaldhausen j a) S) =
      QuotientAddGroup.mk'
        (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (inclusion j a))
          (perfectRestrict (inclusion j a))
          (perfectOpenRestrict_waldhausenExact (inclusion j a))).range
        (objectClass (perfectWaldhausen (openSpace j a))
          ((boundedFlatAffineFullOpenPerfectEvaluation j a).obj S)) := by
  rw [boundedFlatAffineFullOpenSectionGrading_lift, AddMonoidHom.comp_apply, map_objectClass]

/-- Vanishing is precisely membership of the evaluated algebraic class in the original image. -/
theorem original_lift_zero_iff (a : Under R)
    (x : AlgebraicGrothendieck.Group (boundedFlatAffineFullOpenSectionWaldhausen j a)) :
    lift (boundedFlatAffineFullOpenSectionWaldhausen j a)
        (boundedFlatAffineFullOpenSectionGrading j a) x = 0 ↔
      AlgebraicGrothendieck.map (boundedFlatAffineFullOpenSectionWaldhausen j a)
          (boundedFlatAffineFullOpenPerfectEvaluation j a)
          (boundedFlatAffineFullOpenPerfectEvaluation_exact j a) x ∈
        (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (inclusion j a))
          (perfectRestrict (inclusion j a))
          (perfectOpenRestrict_waldhausenExact (inclusion j a))).range := by
  rw [boundedFlatAffineFullOpenSectionGrading_lift, AddMonoidHom.comp_apply]
  exact QuotientAddGroup.eq_zero_iff _

/-- A witnessed class in the original raw restriction image has zero original section grade. -/
theorem original_raw_image_vanishes (a : Under R)
    (x : AlgebraicGrothendieck.Group (boundedFlatAffineFullOpenSectionWaldhausen j a))
    (y : AlgebraicGrothendieck.Group (perfectOpenWeakWaldhausen (inclusion j a)))
    (h : AlgebraicGrothendieck.map (boundedFlatAffineFullOpenSectionWaldhausen j a)
        (boundedFlatAffineFullOpenPerfectEvaluation j a)
        (boundedFlatAffineFullOpenPerfectEvaluation_exact j a) x =
      AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (inclusion j a))
        (perfectRestrict (inclusion j a))
        (perfectOpenRestrict_waldhausenExact (inclusion j a)) y) :
    lift (boundedFlatAffineFullOpenSectionWaldhausen j a)
      (boundedFlatAffineFullOpenSectionGrading j a) x = 0 :=
  (original_lift_zero_iff j a x).mpr ⟨y, h.symm⟩

end QuillenTest.FullOpenSectionGradingLift
