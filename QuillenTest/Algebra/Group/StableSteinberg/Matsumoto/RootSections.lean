/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.RootSections
public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.FiniteRootLifting
public import Quillen.Aglib.LinearAlgebra.Matrix.Elementary
public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.Weyl
public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.Torus

/-!
# RootSections

Canonical provider for the accepted interfaces described in the sections below.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootSectionClient -/

section

noncomputable section
universe u
namespace Quillen.RootSectionProducer.Client
open StableSteinberg
variable (F : Type u) [Field F]

/-- The client supplies only an original single elementary root, as an additive homomorphism. -/
def elementarySection {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    Multiplicative F →* Matrix.GeneralLinearGroup (Fin m) F where
  toFun z := _root_.Quillen.ElementaryMatrix.unit a b hab z.toAdd
  map_one' := _root_.Quillen.ElementaryMatrix.unit_zero a b hab
  map_mul' z w := (_root_.Quillen.ElementaryMatrix.unit_mul_same a b hab z.toAdd w.toAdd).symm

lemma identity_central_kernel {m : ℕ} :
    (MonoidHom.id (Matrix.GeneralLinearGroup (Fin m) F)).ker ≤
      Subgroup.center (Matrix.GeneralLinearGroup (Fin m) F) := by
  intro x hx
  have hx' : x = 1 := hx
  rw [hx']
  exact Subgroup.one_mem _

lemma identity_det_one_onto (n : ℕ) :
    DetOneOnto F (MonoidHom.id (Matrix.GeneralLinearGroup (Fin (n + 1)) F)) := by
  intro g _
  exact ⟨g, rfl⟩

lemma elementary_base_covariance {n : ℕ} (a b : Fin (n + 1)) (hab : a ≠ b) :
    BaseDiagonalCovariance F (RootCoordinate.torusToGL F n) a b
      (elementarySection F a b hab) := by
  intro t z
  change RootCoordinate.torusToGL F n t * _root_.Quillen.ElementaryMatrix.unit a b hab z *
    (RootCoordinate.torusToGL F n t)⁻¹ = _
  rw [torusToGL_eq_diagonalUnit]
  exact FiniteRootLifting.diagonalUnit_conjugate_unit F
    (RootCoordinate.diagonalCoordinates F t.diagonal) a b hab z

/-- The produced lower root has the literal positive coefficient even across the signed swap. -/
theorem produced_lower_root (z : F) :
    FiniteRootLifting.root
      (rootSections F (MonoidHom.id (Matrix.GeneralLinearGroup (Fin 2) F))
        (identity_det_one_onto F 1) 0 1 (elementarySection F 0 1 (by decide)))
      1 0 (by decide) z = _root_.Quillen.ElementaryMatrix.unit 1 0 (by decide) z :=
  rootSections_projection F (MonoidHom.id (Matrix.GeneralLinearGroup (Fin 2) F))
    (identity_det_one_onto F 1) 0 1 (by decide) (elementarySection F 0 1 (by decide))
    (fun _ => rfl) 1 0 (by decide) z

/-- The existential common-diagonal witness is inhabited by the actual matrix client. -/
theorem produced_common_diagonal :
    FiniteRootLifting.DiagonalCovariance
      (MonoidHom.id (Matrix.GeneralLinearGroup (Fin 2) F))
      (rootSections F (MonoidHom.id (Matrix.GeneralLinearGroup (Fin 2) F))
        (identity_det_one_onto F 1) 0 1 (elementarySection F 0 1 (by decide))) :=
  rootSections_diagonal_covariance F
    (MonoidHom.id (Matrix.GeneralLinearGroup (Fin 2) F)) (identity_central_kernel F)
    (identity_det_one_onto F 1) 0 1 (by decide) (RootCoordinate.torusToGL F 1)
    (elementarySection F 0 1 (by decide)) (fun _ => rfl)
    (elementary_base_covariance F 0 1 (by decide))

/-- A nontrivial lower root is scaled by the inverse square under diag(2,1/2). -/
theorem rational_lower_diagonal :
    let w : Fin 2 → ℚˣ := ![FiniteRootLifting.twoUnit ℚ, (FiniteRootLifting.twoUnit ℚ)⁻¹]
    let t := diagonalTorusLift ℚ w
    RootCoordinate.torusToGL ℚ 1 t * _root_.Quillen.ElementaryMatrix.unit (1 : Fin 2) 0 (by decide)
      3 *
        (RootCoordinate.torusToGL ℚ 1 t)⁻¹ =
      _root_.Quillen.ElementaryMatrix.unit (1 : Fin 2) 0 (by decide) (3 / 4 : ℚ) := by
  dsimp only
  let w : Fin 2 → ℚˣ := ![FiniteRootLifting.twoUnit ℚ, (FiniteRootLifting.twoUnit ℚ)⁻¹]
  have hw : ∏ i, w i = 1 := by simp [w, Fin.prod_univ_two]
  rw [torusToGL_diagonalTorusLift ℚ w hw,
    FiniteRootLifting.diagonalUnit_conjugate_unit]
  congr 1
  norm_num [w, FiniteRootLifting.twoUnit]

end Quillen.RootSectionProducer.Client

end

end
