/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Matrix.RightAutomorphisms
public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveMonoidal

/-!
# Explicit left rank-one stabilization of matrix automorphisms

Reversal of the finite ordered basis converts right matrix stabilization into
left direct-sum stabilization. The basis change is explicit at every rank;
right and left direct-sum identifications are never identified definitionally.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  preservesBinaryBiproducts_of_preservesBiproducts

namespace Quillen.RightMatrix

variable (R : Type u) [Ring R]

/-- The explicit involution reversing the standard ordered basis. -/
def reverseColumns (n : ℕ) : (Fin n → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ) where
  toFun x i := x i.rev
  invFun x i := x i.rev
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Basis reversal as an actual automorphism of the chosen finite free module. -/
def reverseIso (n : ℕ) : freeModule R n ≅ freeModule R n :=
  (reverseColumns R n).toModuleIso

/-- Matrix automorphisms in the reversed basis, adapted to left direct sums. -/
def leftModuleAutEquiv (n : ℕ) : StableGeneralLinear.GL R n ≃* Aut (freeModule R n) :=
  (moduleAutEquiv R n).trans (Aut.autMulEquivOfIso (reverseIso R n))

@[simp] lemma leftModuleAutEquiv_apply (n : ℕ) (g : StableGeneralLinear.GL R n)
    (x : Fin n → Rᵐᵒᵖ) (i : Fin n) :
    (leftModuleAutEquiv R n g).hom x i =
      (moduleAutEquiv R n g).hom (fun j => x j.rev) i.rev := rfl

/-- The added first coordinate is fixed after the explicit reversal. -/
lemma leftModuleAutEquiv_step_zero (n : ℕ) (g : StableGeneralLinear.GL R n)
    (x : Fin (n + 1) → Rᵐᵒᵖ) :
    (leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom x 0 = x 0 := by
  rw [leftModuleAutEquiv_apply, Fin.rev_zero, moduleAutEquiv_step_last, Fin.rev_last]

/-- All later coordinates carry the preceding reversed-basis action. -/
lemma leftModuleAutEquiv_step_succ (n : ℕ) (g : StableGeneralLinear.GL R n)
    (x : Fin (n + 1) → Rᵐᵒᵖ) (i : Fin n) :
    (leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom x i.succ =
      (leftModuleAutEquiv R n g).hom (fun j => x j.succ) i := by
  simp only [leftModuleAutEquiv_apply, Fin.rev_succ, moduleAutEquiv_step_castSucc,
    Fin.rev_castSucc]

/-- The left rank-one module isomorphism used by the projective free sequence. -/
def prependIso (n : ℕ) : freeModule R 1 ⊞ freeModule R n ≅ freeModule R (n + 1) :=
  ModuleCat.biprodIsoProd _ _ ≪≫
    ((LinearEquiv.prodCongr (LinearEquiv.funUnique (Fin 1) Rᵐᵒᵖ Rᵐᵒᵖ)
      (LinearEquiv.refl Rᵐᵒᵖ (Fin n → Rᵐᵒᵖ))).trans
        (Fin.consLinearEquiv Rᵐᵒᵖ (fun _ : Fin (n + 1) => Rᵐᵒᵖ))).toModuleIso

/-- Reversed-basis stabilization is the actual left direct-sum automorphism. -/
lemma leftModuleAutEquiv_stabilization (n : ℕ) (g : StableGeneralLinear.GL R n) :
    (leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom ≫
        (prependIso R n).inv =
      (prependIso R n).inv ≫ biprod.map (𝟙 (freeModule R 1)) (leftModuleAutEquiv R n g).hom := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id,
      prependIso, Iso.trans_inv, Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst]
    ext x
    funext i
    exact leftModuleAutEquiv_step_zero R n g x
  · simp only [Category.assoc, biprod.map_snd]
    simp only [prependIso, Iso.trans_inv, Category.assoc,
      ModuleCat.biprodIsoProd_inv_comp_snd]
    rw [← Category.assoc ((ModuleCat.biprodIsoProd (freeModule R 1) (freeModule R n)).inv),
      ModuleCat.biprodIsoProd_inv_comp_snd]
    ext x
    funext i
    exact leftModuleAutEquiv_step_succ R n g x i

/-- Equality of the complete automorphisms, with the chosen left-sum isomorphism retained. -/
lemma leftModuleAutEquiv_step (n : ℕ) (g : StableGeneralLinear.GL R n) :
    leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (prependIso R n).symm ≪≫
        biprod.mapIso (Iso.refl (freeModule R 1)) (leftModuleAutEquiv R n g) ≪≫
          prependIso R n := by
  apply Iso.ext
  apply (cancel_mono (prependIso R n).inv).1
  simpa only [Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Iso.refl_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] using leftModuleAutEquiv_stabilization R n g

/-- The reversed matrix action in the actual finite projective category. -/
def leftFreeAutEquiv (n : ℕ) : StableGeneralLinear.GL R n ≃*
    Aut (FiniteProjectiveModule.free (R := Rᵐᵒᵖ) n) :=
  let h := Functor.FullyFaithful.ofFullyFaithful (FiniteProjectiveModule.property Rᵐᵒᵖ).ι
  (leftModuleAutEquiv R n).trans
    (h.autMulEquivOfFullyFaithful (FiniteProjectiveModule.free (R := Rᵐᵒᵖ) n)).symm

@[simp] lemma leftFreeAutEquiv_map (n : ℕ) (g : StableGeneralLinear.GL R n) :
    (FiniteProjectiveModule.property Rᵐᵒᵖ).ι.mapIso (leftFreeAutEquiv R n g) =
      leftModuleAutEquiv R n g := by
  let h := Functor.FullyFaithful.ofFullyFaithful (FiniteProjectiveModule.property Rᵐᵒᵖ).ι
  exact (h.autMulEquivOfFullyFaithful
    (FiniteProjectiveModule.free (R := Rᵐᵒᵖ) n)).apply_symm_apply _

/-- The chosen projective left-sum isomorphism is precisely the module-level prepend map. -/
lemma freeSuccIso_map (n : ℕ) :
    (FiniteProjectiveModule.property Rᵐᵒᵖ).ι.mapIso
        (FiniteProjectiveModule.freeSuccIso (R := Rᵐᵒᵖ) n) =
      (FiniteProjectiveModule.property Rᵐᵒᵖ).ι.mapBiprod
        (FiniteProjectiveModule.free 1) (FiniteProjectiveModule.free n) ≪≫ prependIso R n := rfl

private lemma inclusion_biprod_naturality (n : ℕ)
    (a : End (FiniteProjectiveModule.free (R := Rᵐᵒᵖ) n)) :
    (FiniteProjectiveModule.property Rᵐᵒᵖ).ι.map (biprod.map (𝟙 _) a) ≫
        ((FiniteProjectiveModule.property Rᵐᵒᵖ).ι.mapBiprod
          (FiniteProjectiveModule.free 1) (FiniteProjectiveModule.free n)).hom =
      ((FiniteProjectiveModule.property Rᵐᵒᵖ).ι.mapBiprod
          (FiniteProjectiveModule.free 1) (FiniteProjectiveModule.free n)).hom ≫
        biprod.map (𝟙 _) ((FiniteProjectiveModule.property Rᵐᵒᵖ).ι.map a) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id, Functor.mapBiprod_hom,
      biprod.lift_fst]
    exact congrArg (fun k : FiniteProjectiveModule.free (R := Rᵐᵒᵖ) 1 ⊞
        FiniteProjectiveModule.free n ⟶ FiniteProjectiveModule.free 1 => k.hom)
      ((biprod.map_fst (𝟙 _) a).trans (Category.comp_id _))
  · simp only [Category.assoc, biprod.map_snd, Functor.mapBiprod_hom,
      biprod.lift_snd, biprod.lift_snd_assoc]
    exact congrArg (fun k : FiniteProjectiveModule.free (R := Rᵐᵒᵖ) 1 ⊞
        FiniteProjectiveModule.free n ⟶ FiniteProjectiveModule.free n => k.hom)
      (biprod.map_snd (𝟙 _) a)

/-- Reversal intertwines matrix stabilization with the existing projective left-sum diagram. -/
lemma leftFreeAutEquiv_stabilization (n : ℕ) (g : StableGeneralLinear.GL R n) :
    (leftFreeAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom ≫
        (FiniteProjectiveModule.freeSuccIso (R := Rᵐᵒᵖ) n).inv =
      (FiniteProjectiveModule.freeSuccIso (R := Rᵐᵒᵖ) n).inv ≫
        biprod.map (𝟙 _) (leftFreeAutEquiv R n g).hom := by
  let F := (FiniteProjectiveModule.property Rᵐᵒᵖ).ι
  apply F.map_injective
  simp only [Functor.map_comp]
  apply (cancel_mono (F.mapBiprod
    (FiniteProjectiveModule.free 1) (FiniteProjectiveModule.free n)).hom).1
  have hsn := congrArg Iso.inv (freeSuccIso_map R n)
  have hag := congrArg Iso.hom (leftFreeAutEquiv_map R n g)
  have has := congrArg Iso.hom
    (leftFreeAutEquiv_map R (n + 1) (StableGeneralLinear.step R n g))
  change F.map (leftFreeAutEquiv R n g).hom = (leftModuleAutEquiv R n g).hom at hag
  change F.map (leftFreeAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom =
    (leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom at has
  change F.map (FiniteProjectiveModule.freeSuccIso (R := Rᵐᵒᵖ) n).inv =
    (F.mapBiprod (FiniteProjectiveModule.free 1) (FiniteProjectiveModule.free n) ≪≫
      prependIso R n).inv at hsn
  rw [has, hsn]
  simp only [Iso.trans_inv, Category.assoc]
  rw [inclusion_biprod_naturality R n (leftFreeAutEquiv R n g).hom]
  dsimp only [F] at hag ⊢
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, hag]
  exact leftModuleAutEquiv_stabilization R n g

/-- The full projective automorphism identity for the pre-existing left free sequence. -/
lemma leftFreeAutEquiv_step (n : ℕ) (g : StableGeneralLinear.GL R n) :
    leftFreeAutEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (FiniteProjectiveModule.freeSuccIso (R := Rᵐᵒᵖ) n).symm ≪≫
        biprod.mapIso (Iso.refl _) (leftFreeAutEquiv R n g) ≪≫
          FiniteProjectiveModule.freeSuccIso n := by
  apply Iso.ext
  apply (cancel_mono (FiniteProjectiveModule.freeSuccIso (R := Rᵐᵒᵖ) n).inv).1
  simpa only [Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Iso.refl_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] using leftFreeAutEquiv_stabilization R n g

end Quillen.RightMatrix
