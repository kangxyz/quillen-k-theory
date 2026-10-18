/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.WeylTransporter
public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.NormalizerMatrix
public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.LiftedWeyl
public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.Normalizer
public import Quillen.Aglib.LinearAlgebra.Matrix.GeneralLinearGroup.SignedSection.Basic
public import Quillen.Aglib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.Weyl
public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.Torus

/-!
# WeylTransporter

Canonical provider for the accepted interfaces described in the sections below.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## WeylTransporterClient -/

section

/-!
# A nontrivial-index client with a variable diagonal ratio

A positive 3-cycle transports root (0,1) to (1,2). Multiplication by H_1(a) changes the
ratio to a squared; the actual transporter must produce W_1(-a squared).
-/

noncomputable section
universe u
namespace Quillen.StableSteinberg.RootCoordinate.WeylTransporterClient
open _root_.Matrix.Bruhat
variable (F : Type u) [Field F]

/-- A positive cycle sending the first adjacent pair to the second. -/
def cycle : Equiv.Perm (Fin 3) := simpleSwap (0 : Fin 2) * simpleSwap (1 : Fin 2)

lemma cycle_prefix (j : Fin 3) :
    _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount cycle j = if j = 2 then 2 else 0 :=
      by
  revert j
  decide

lemma cycle_sign (j : Fin 3) : (-1 : Fˣ) ^
  _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount cycle j = 1 := by
  rw [cycle_prefix]
  split_ifs <;> simp

/-- The actual normalizer element used by the client. -/
def shiftedTorus (a : Fˣ) : LiftedNormalizer F 2 :=
  normalizerTorus F 2 (simple F (1 : Fin 2) a) * pureNormalizerLift F cycle

/-- Literal row-monomial data for the client. -/
def shiftedMonomial (a : Fˣ) : MonomialGroup F 3 :=
  ⟨simpleDiagonal F (1 : Fin 2) a, cycle⟩

lemma shiftedTorus_toGL (a : Fˣ) :
    normalizerToGL F 2 (shiftedTorus F a) = monomialToGL F 3 (shiftedMonomial F a) := by
  have he : normalizerEvaluation F 2 (shiftedTorus F a) = (simple F (1 : Fin 2) a, cycle) := by
    change torusLeft F 2 (simple F (1 : Fin 2) a)
      (normalizerEvaluation F 2 (pureNormalizerLift F cycle)) = _
    rw [normalizerEvaluation_pure]
    change (simple F (1 : Fin 2) a * 1, cycle) = _
    rw [mul_one]
  apply Units.ext
  ext r j
  rw [normalizerToGL_apply, he, stateMatrix_entry, cycle_sign]
  change (if r = cycle j then
      ((diagonalCoordinates F (Pi.mulSingle (1 : Fin 2) a) (cycle j) * 1 : Fˣ) : F) else 0) =
    if r = cycle j then (simpleDiagonal F (1 : Fin 2) a r : F) else 0
  rw [diagonalCoordinates_single]
  by_cases hr : r = cycle j <;> simp [hr]

/-- The full theorem resolves a different source and target index with the negative square. -/
theorem shiftedTorus_conjugate (a : Fˣ) :
    shiftedTorus F a * normalizerW F (0 : Fin 2) (-1) * (shiftedTorus F a)⁻¹ =
      normalizerW F (1 : Fin 2) (-(a * a)) := by
  have h0 : (shiftedMonomial F a).right (0 : Fin 2).castSucc = (1 : Fin 2).castSucc := by
    change cycle (0 : Fin 3) = 1
    decide
  have h1 : (shiftedMonomial F a).right (0 : Fin 2).succ = (1 : Fin 2).succ := by
    change cycle (1 : Fin 3) = 2
    decide
  have he := normalizer_conjugate_W_neg_one F (shiftedTorus F a) (shiftedMonomial F a)
    (shiftedTorus_toGL F a) (1 : Fin 2) (0 : Fin 2) h0 h1
  simpa [shiftedMonomial, simpleDiagonal] using he

/-- The transported signed generator retains the central fourth power. -/
theorem cycle_conjugate_fourth_power :
    (shiftedTorus F 1 * normalizerW F (0 : Fin 2) (-1) * (shiftedTorus F 1)⁻¹) ^ 4 =
      normalizerCoefficient F 2 (Multiplicative.ofAdd (MilnorK.symbol ![-1, -1])) := by
  rw [shiftedTorus_conjugate]
  simp only [one_mul, normalizerW_neg_one_pow_four]

end Quillen.StableSteinberg.RootCoordinate.WeylTransporterClient

end

end
