/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetReferenceTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.LaurentUnitReferenceCore

/-! Actual coefficient-unit intertwining on complete target sheet references. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetUnitReference
open CommonReferenceNerve LaurentUnitReferenceSpecialization
open CoefficientBassSeedTargetChartAttachment CoefficientBassSeedTargetReferenceTransport
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)

/-- The actual Laurent coefficient map preserves the specified forward inner unit. -/
theorem coefficient_preserves :
    Preserves (L P f).functor (smallUnit P a) (smallUnit P b) := by
  have h := GlobalUnitReferenceNaturality.normalizedModel_preserves
    (i := (op P, (laurentUnderFunctor R).obj a))
    (k := (op P, (laurentUnderFunctor R).obj b))
    (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentUnit P a)
  have hu : Units.map (coefficientMap P ((laurentUnderFunctor R).map f)).appTop.hom.toMonoidHom
      (laurentUnit P a) = laurentUnit P b :=
    boundedFlatCoefficientLaurentUnit_coefficient P f
  rw [hu] at h
  exact h

variable {V : Model.{u + 1}}
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (H : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj b))))
  (ρ : H.functor ≅ (G ≫ L P f).functor)

/-- Full-reference transport intertwines the actual old and new Laurent units. -/
theorem unit_intertwine :
    onFunctor H.functor (smallUnit P b) ≪≫ ρ =
      ρ ≪≫ isoWhiskerRight (onFunctor G.functor (smallUnit P a)) (L P f).functor := by
  apply Iso.ext
  exact onFunctor_intertwine H.functor G.functor (L P f).functor ρ.hom
    (smallUnit P a) (smallUnit P b) (coefficient_preserves P f)

variable (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
  (space (op P, (polynomialUnderFunctor R).obj a))))
  (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor)

/-- The transported shifted anchor is the target unit acting on the full ordinary anchor. -/
theorem shifted_anchor :
    ρ ≪≫ targetAnchor P f D G (onFunctor G.functor (smallUnit P a) ≪≫ ε) =
      onFunctor H.functor (smallUnit P b) ≪≫ (ρ ≪≫ targetAnchor P f D G ε) := by
  rw [targetAnchor_shifted]
  rw [← Iso.trans_assoc, ← unit_intertwine P f G H ρ, Iso.trans_assoc]

/-- This specializes to the actual whole-reference normalization, at every source model. -/
theorem whole_shifted_anchor
    (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (τ : (BassProjectionPath.WholeReference.reference P a E).functor ≅ G.functor) :
    sheetReference P f E G τ D (onFunctor G.functor (smallUnit P a) ≪≫ ε) =
      onFunctor (BassProjectionPath.WholeReference.reference P b
        (targetInput P f E)).functor (smallUnit P b) ≪≫
          sheetReference P f E G τ D ε :=
  shifted_anchor P f G _ (referenceIso P f E G τ) D ε

end Quillen.PerfectComplexes.CoefficientBassSeedTargetUnitReference
