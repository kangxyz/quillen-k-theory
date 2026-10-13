/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal

/-!
# Coherence of the original scalar-extension units

The original identity and composition comparisons preserve the actual
semilinear units. The proof retains the chosen matrix presentations: entrywise
change of rings commutes with compatible matrices, and the image equivalence's
triangle identity cancels the intermediate presentation counit. All three
rings have independent universes and may be noncommutative or trivial.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace Quillen.RightMatrix

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

/-- Entrywise scalar extension along the identity fixes the original image. -/
theorem imageUnit_id (P : ProjectiveMatrices R) (x : (linearMap P.p).range) :
    imageUnit (RingHom.id R) P x = x := by
  apply Subtype.ext
  rfl

/-- Successive image units apply the two ring homomorphisms in their original order. -/
theorem imageUnit_comp (f : R →+* S) (g : S →+* T)
    (P : ProjectiveMatrices R) (x : (linearMap P.p).range) :
    imageUnit g ((baseChange f).obj P) (imageUnit f P x) = imageUnit (g.comp f) P x := by
  apply Subtype.ext
  rfl

end Quillen.RightMatrix

namespace Quillen.FiniteProjectiveModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

/-- The unchanged identity comparison sends the original scalar-extension unit to identity. -/
theorem rightBaseChangeId_hom_unit (P : Category.{u, u} Rᵐᵒᵖ) (x : P.obj) :
    (rightBaseChangeId.hom.app P).hom.hom (rightBaseChangeUnit (RingHom.id R) P x) = x := by
  change rightBaseChangePresentationEquiv P
    (RightMatrix.imageUnit (RingHom.id R) _ ((rightBaseChangePresentationEquiv P).symm x)) = x
  rw [RightMatrix.imageUnit_id, LinearEquiv.apply_symm_apply]

/-- The unchanged composition comparison preserves successive original scalar-extension units. -/
theorem rightBaseChangeComp_hom_unit (f : R →+* S) (g : S →+* T)
    (P : Category.{u, u} Rᵐᵒᵖ) (x : P.obj) :
    ((rightBaseChangeComp f g).hom.app P).hom.hom
        (rightBaseChangeUnit g ((rightBaseChange f).obj P) (rightBaseChangeUnit f P x)) =
      rightBaseChangeUnit (g.comp f) P x := by
  let A := (RightMatrix.baseChange f).obj (RightMatrix.imageEquivalence.inverse.obj P)
  have he : RightMatrix.imageMap ((RightMatrix.imageEquivalence (R := S)).unitIso.inv.app A) =
      (rightBaseChangePresentationEquiv ((rightBaseChange f).obj P)).toLinearMap := by
    exact congrArg
      (fun k : RightMatrix.imageFunctor.obj
          (RightMatrix.imageEquivalence.inverse.obj (RightMatrix.imageFunctor.obj A)) ⟶
          RightMatrix.imageFunctor.obj A ↦ k.hom.hom)
      ((RightMatrix.imageEquivalence (R := S)).counit_app_functor A).symm
  change RightMatrix.imageMap
      ((RightMatrix.baseChange g).map ((RightMatrix.imageEquivalence (R := S)).unitIso.inv.app A))
      (RightMatrix.imageUnit g _
        ((rightBaseChangePresentationEquiv ((rightBaseChange f).obj P)).symm
          (rightBaseChangeUnit f P x))) = _
  rw [← RightMatrix.imageUnit_naturality, he]
  change RightMatrix.imageUnit g A
    (rightBaseChangePresentationEquiv ((rightBaseChange f).obj P)
      ((rightBaseChangePresentationEquiv ((rightBaseChange f).obj P)).symm
        (rightBaseChangeUnit f P x))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact RightMatrix.imageUnit_comp f g _ _

end Quillen.FiniteProjectiveModule
