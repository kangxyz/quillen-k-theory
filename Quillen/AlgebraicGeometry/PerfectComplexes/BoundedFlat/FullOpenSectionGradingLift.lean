/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGrading

/-!
# Algebraic extension of the original full-open section grading

The universal algebraic extension of the actual section grading is the unchanged raw-perfect
image quotient after the original perfect evaluation map. Object classes prove the formula
across the independent section and raw-perfect hom universes. No connective K-theory comparison
or replacement of the grading is used.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original section grading extends to the original raw quotient after actual evaluation. -/
theorem boundedFlatAffineFullOpenSectionGrading_lift (a : Under R) :
    lift (boundedFlatAffineFullOpenSectionWaldhausen j a)
        (boundedFlatAffineFullOpenSectionGrading j a) =
      (QuotientAddGroup.mk'
        (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (inclusion j a))
          (perfectRestrict (inclusion j a))
          (perfectOpenRestrict_waldhausenExact (inclusion j a))).range).comp
        (AlgebraicGrothendieck.map (boundedFlatAffineFullOpenSectionWaldhausen j a)
          (boundedFlatAffineFullOpenPerfectEvaluation j a)
          (boundedFlatAffineFullOpenPerfectEvaluation_exact j a)) := by
  apply hom_ext (boundedFlatAffineFullOpenSectionWaldhausen j a)
  intro S
  rw [lift_objectClass, AddMonoidHom.comp_apply, map_objectClass]
  rfl

end Quillen.PerfectComplexes
