/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.ProjectiveCoreCharacter
public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeFree
public import Quillen.CategoryTheory.GroupCompletion.StableFreeDiagram

/-!
# Original finite matrix values of the projective character

The character returns the original stable matrix quotient class, retaining both
the explicit reversed basis and the chosen rank-one-power isomorphism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  Quillen.FiniteProjectiveModule.categoryDirectSumMonoidal
  Quillen.FiniteProjectiveModule.directSumMonoidal
namespace Quillen.RightMatrix
variable (R : Type u) [Ring R]

/-- The actual free-module character takes the original finite matrix value. -/
lemma projectiveAutomorphismClass_freeAutEquiv (n : ℕ) (g : StableGeneralLinear.GL R n) :
    projectiveAutomorphismClass (FiniteProjectiveModule.free (R := Rᵐᵒᵖ) n)
      (freeAutEquiv R n g) = StableGeneralLinear.finiteClass R n g := by
  let e := freeImageIso (R := R) n
  have he : Aut.autMulEquivOfIso e (imageFunctor.mapIso (matrixUnitAut n g)) =
      freeAutEquiv R n g := by
    apply Iso.ext
    change e.inv ≫ imageFunctor.map (matrixUnitAut n g).hom ≫ e.hom = _
    have ha := freeImageIso_matrix_action (R := R) n g
    change imageFunctor.map (matrixUnitAut n g).hom ≫ e.hom =
      e.hom ≫ (freeAutEquiv R n g).hom at ha
    rw [ha]
    simp
  rw [← he, projectiveAutomorphismClass_presentation, automorphismClass_matrixUnitAut]

/-- Basis reversal does not change the original stable class of the matrix action. -/
lemma projectiveAutomorphismClass_leftFreeAutEquiv (n : ℕ) (g : StableGeneralLinear.GL R n) :
    projectiveAutomorphismClass (FiniteProjectiveModule.free (R := Rᵐᵒᵖ) n)
      (leftFreeAutEquiv R n g) = StableGeneralLinear.finiteClass R n g := by
  let e := (FiniteProjectiveModule.property Rᵐᵒᵖ).isoMk (reverseIso R n)
  have he : Aut.autMulEquivOfIso e (freeAutEquiv R n g) = leftFreeAutEquiv R n g := by
    apply Iso.ext
    apply (FiniteProjectiveModule.property Rᵐᵒᵖ).ι.map_injective
    have h₁ := congrArg Iso.hom (freeAutEquiv_map R n g)
    have h₂ := congrArg Iso.hom (leftFreeAutEquiv_map R n g)
    change _ = (FiniteProjectiveModule.property Rᵐᵒᵖ).ι.map (leftFreeAutEquiv R n g).hom
    rw [show (FiniteProjectiveModule.property Rᵐᵒᵖ).ι.map
      (leftFreeAutEquiv R n g).hom = (leftModuleAutEquiv R n g).hom from h₂]
    change (reverseIso R n).inv ≫
      (FiniteProjectiveModule.property Rᵐᵒᵖ).ι.map (freeAutEquiv R n g).hom ≫
        (reverseIso R n).hom = _
    rw [show (FiniteProjectiveModule.property Rᵐᵒᵖ).ι.map
      (freeAutEquiv R n g).hom = (moduleAutEquiv R n g).hom from h₁]
    rfl
  rw [← he, projectiveAutomorphismClass_conjugate, projectiveAutomorphismClass_freeAutEquiv]

end Quillen.RightMatrix

namespace Quillen.FiniteProjectiveModule
variable (R : Type u) [Ring R]

/-- The core character recovers the exact matrix class on the original free action. -/
lemma coreCharacter_freeEndEquiv (n : ℕ) (g : StableGeneralLinear.GL R n) :
    coreCharacter (freeIso Rᵐᵒᵖ n) (StableFree.freeEndEquiv R n g) =
      StableGeneralLinear.finiteClass R n g :=
  RightMatrix.projectiveAutomorphismClass_leftFreeAutEquiv R n g

/-- The original rank-one-power matrix action has precisely its original stable quotient class. -/
lemma coreCharacter_powerEndEquiv (n : ℕ) (g : StableGeneralLinear.GL R n) :
    coreCharacter (rankOnePower Rᵐᵒᵖ n) (StableFree.powerEndEquiv R n g) =
      StableGeneralLinear.finiteClass R n g := by
  change coreCharacter _ ((rankOnePowerIsoFree Rᵐᵒᵖ n).hom ≫
    StableFree.freeEndEquiv R n g ≫ (rankOnePowerIsoFree Rᵐᵒᵖ n).inv) = _
  rw [show (rankOnePowerIsoFree Rᵐᵒᵖ n).hom =
    inv (rankOnePowerIsoFree Rᵐᵒᵖ n).inv from by simp]
  rw [coreCharacter_conjugate, coreCharacter_freeEndEquiv]

end Quillen.FiniteProjectiveModule
