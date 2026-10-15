/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalCokernel
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of the original diagonal short exact sequence and cokernel

The consumers retain both original arrows, their universal properties, the signed affine
kernel and opposite Laurent coordinates, over nonreduced and zero-ring bases as well.
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.Modules
  Quillen.PolynomialDiagonal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace QuillenTest.ProjectiveLineDiagonalCokernel

open Quillen
/-- An arrow annihilating the original incidence factors uniquely through the original quotient. -/
theorem original_quotient_factorization (R : CommRingCat.{u}) {N : (relativeSquare R).Modules}
    (f : (Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R) ⟶ N)
    (hf : diagonalIncidence R ≫ f = 0) :
    ∃! g : (Scheme.Modules.pushforward (relativeDiagonal R)).obj
      (tautologicalQuotientLine R) ⟶ N,
      diagonalQuotientMap R ≫ g = f := by
  let h := diagonalQuotientIsCokernel R
  let c := CokernelCofork.ofπ f hf
  refine ⟨h.desc c, ?_, ?_⟩
  · exact Cofork.IsColimit.π_desc h (t := c)
  · intro g hg
    apply Cofork.IsColimit.hom_ext h
    exact hg.trans (Cofork.IsColimit.π_desc h (t := c)).symm
/-- Every original quotient-kernel arrow has a unique lift through the original incidence. -/
theorem original_kernel_lift (R : CommRingCat.{u}) {N : (relativeSquare R).Modules}
    (f : N ⟶ (Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R))
    (hf : f ≫ diagonalQuotientMap R = 0) :
    ∃! g : N ⟶ (Scheme.Modules.pullback (relativeFirst R)).obj (tautologicalLine R),
      g ≫ diagonalIncidence R = f := by
  have := (diagonalIncidenceSequence_shortExact R).mono_f
  let h := (diagonalIncidenceSequence_shortExact R).exact.fIsKernel
  let c := KernelFork.ofι f hf
  refine ⟨h.lift c, ?_, ?_⟩
  · exact Fork.IsLimit.lift_ι h (t := c)
  · intro g hg
    apply Fork.IsLimit.hom_ext h
    exact hg.trans (Fork.IsLimit.lift_ι h (t := c)).symm
/-- The categorical cokernel is the actual diagonal direct image, with the literal quotient map. -/
theorem original_cokernel_identification (R : CommRingCat.{u}) :
    ∃ e : cokernel (diagonalIncidence R) ≅
      (Scheme.Modules.pushforward (relativeDiagonal R)).obj (tautologicalQuotientLine R),
      cokernel.π (diagonalIncidence R) ≫ e.hom = diagonalQuotientMap R := by
  let h := cokernelIsCokernel (diagonalIncidence R)
  let k := diagonalQuotientIsCokernel R
  refine ⟨h.coconePointUniqueUpToIso k, ?_⟩
  exact h.comp_coconePointUniqueUpToIso_hom k WalkingParallelPair.one
/-- The positive-positive kernel uses the incidence sign C X - X explicitly. -/
theorem original_positive_signed_kernel (R : CommRingCat.{u})
    (p : Polynomial (Polynomial R)) :
    (diagonalEvaluation R).hom p = 0 ↔ ∃ q, q * (C X - X) = p := by
  change p ∈ RingHom.ker (diagonalEvaluation R).hom ↔ _
  rw [diagonalEvaluation_ker, ← neg_sub, Ideal.span_singleton_neg,
    Ideal.mem_span_singleton']
/-- The opposite mixed map sends the original variables to the literal inverse Laurent pair. -/
theorem original_opposite_laurent_coordinates (R : CommRingCat.{u}) :
    (oppositeMixedEvaluation R).hom (C X) = LaurentPolynomial.T (-1) ∧
      (oppositeMixedEvaluation R).hom X = LaurentPolynomial.T 1 := by
  simp [oppositeMixedEvaluation, mixedEvaluation]
/-- Cancellation is through the actual diagonal quotient arrow. -/
theorem original_quotient_cancel (R : CommRingCat.{u}) {N : (relativeSquare R).Modules}
    (f g : (Scheme.Modules.pushforward (relativeDiagonal R)).obj (tautologicalQuotientLine R) ⟶ N)
    (hfg : diagonalQuotientMap R ≫ f = diagonalQuotientMap R ≫ g) : f = g := by
  have : Epi (diagonalQuotientMap R) := (diagonalIncidenceSequence_shortExact R).epi_g
  exact (cancel_epi (diagonalQuotientMap R)).mp hfg
/-- The genuine short exact sequence remains valid over a nonreduced base. -/
theorem nonreduced_original_shortExact :
    (diagonalIncidenceSequence (.of (ZMod 4))).ShortExact :=
  diagonalIncidenceSequence_shortExact _
/-- The original quotient retains its cokernel property over the zero ring. -/
def zeroRingOriginalCokernel :
    IsColimit (CokernelCofork.ofπ (diagonalQuotientMap (.of (ZMod 1)))
      (diagonalIncidence_quotient (.of (ZMod 1)))) := diagonalQuotientIsCokernel _
end QuillenTest.ProjectiveLineDiagonalCokernel
