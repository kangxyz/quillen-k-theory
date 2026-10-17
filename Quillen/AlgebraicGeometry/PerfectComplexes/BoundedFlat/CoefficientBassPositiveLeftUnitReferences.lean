/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH1References
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0ShiftedBridge

/-!
# Actual unit-reference squares for the left-route constituents

The prescribed commonUnit intertwines the actual first and middle H1 anchors with the
original p source unit postcomposed by Laurent q and the original q source unit
precomposed by coefficient p. Laurent pullback preserves the actual forward scalar;
chosen-zero normalization and the accepted small-model lift are retained throughout.
This module supplies no unit path, midpoint seed seam, or terminal seed seam.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftUnitReferences
open LaurentUnitReferenceSpecialization CoefficientBassPositiveJ0ShiftedBridge
variable {R : CommRingCat.{u}} (P : Over (Spec R))

section LaurentCoefficient
variable {a b : Under R} (w : a ⟶ b)

/-- The actual Laurent coefficient pullback preserves the specified forward Laurent scalar. -/
theorem laurent_coefficient_unit :
    Units.map (coefficientMap P ((laurentUnderFunctor R).map w)).appTop.hom.toMonoidHom
      (laurentUnit P a) = laurentUnit P b :=
  boundedFlatCoefficientLaurentUnit_coefficient P w

/-- Its original normalized small-model functor preserves the two actual unit actions. -/
theorem laurent_map_preserves :
    Preserves (BassH1Components.laurentMap P w).functor (smallUnit P a) (smallUnit P b) := by
  have h := GlobalUnitReferenceNaturality.normalizedModel_preserves
    (i := (op P, (laurentUnderFunctor R).obj a))
    (k := (op P, (laurentUnderFunctor R).obj b))
    (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentUnit P a)
  rw [laurent_coefficient_unit] at h
  exact h

end LaurentCoefficient

variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The first full reference intertwines commonUnit with the original right-whiskered p unit. -/
theorem first_unit_reference :
    commonUnit P p q ≪≫ BassH1References.firstIso P p q =
      BassH1References.firstIso P p q ≪≫
        isoWhiskerRight (sourceUnit P p) (BassH1Components.laurentMap P q).functor := by
  rw [commonUnit_eq_action, sourceUnit_action]
  apply Iso.ext
  change (onFunctor (BassOverlap.commonReference P p q).functor (smallUnit P c)).hom ≫
      (BassH1References.firstIso P p q).hom =
    (BassH1References.firstIso P p q).hom ≫
      Functor.whiskerRight (onFunctor (CoefficientLaurentUnitTenNodes.source P p).functor
        (smallUnit P b)).hom (BassH1Components.laurentMap P q).functor
  exact onFunctor_intertwine (BassOverlap.commonReference P p q).functor
    (CoefficientLaurentUnitTenNodes.source P p).functor (BassH1Components.laurentMap P q).functor
    (BassH1References.firstIso P p q).hom (smallUnit P b) (smallUnit P c)
    (laurent_map_preserves P q)

/-- Precomposition retains the original q source action pointwise, with left whiskering. -/
theorem middle_source_action :
    onFunctor (BassH1Components.middleSource P p q).functor (smallUnit P c) =
      isoWhiskerLeft (BassH1Components.coefficientMapModel P p).functor (sourceUnit P q) := by
  rw [sourceUnit_action]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rfl

/-- The middle full reference intertwines commonUnit with the original left-whiskered q unit. -/
theorem middle_unit_reference :
    commonUnit P p q ≪≫ BassH1References.middleIso P p q =
      BassH1References.middleIso P p q ≪≫
        isoWhiskerLeft (BassH1Components.coefficientMapModel P p).functor (sourceUnit P q) := by
  rw [commonUnit_eq_action, ← middle_source_action]
  exact GlobalUnitReferenceNaturality.reference_intertwine
    (op P, (laurentUnderFunctor R).obj c) (laurentUnit P c)
    (BassOverlap.commonReference P p q).functor (BassH1Components.middleSource P p q).functor
    (BassH1References.middleIso P p q)

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftUnitReferences
