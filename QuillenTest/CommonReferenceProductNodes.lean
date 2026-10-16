/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceProductNodes

/-! # Consumers of complete product-reference nodes -/
@[expose] public section
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.IteratedS.CommonReferenceProduct
universe u
namespace QuillenTest.CommonReferenceProductNodes

variable {V W T : Model.{u}} (F : V ⟶ T)
variable (H₀ H₁ : V ⟶ W) (G₀ G₁ : W ⟶ T)
variable (θ : H₀.functor ≅ H₁.functor) (κ : G₀.functor ≅ G₁.functor)
variable (η : F.functor ≅ (H₀ ≫ G₀).functor)
variable (N : CommonReferenceNerve.Node H₁) (M : CommonReferenceNerve.Node G₁)

/-- Two independent reference changes retain the entire product node. -/
theorem actual_two_reference_changes :
    node F H₀ G₀ η (reanchor θ N) (reanchor κ M) =
      node F H₁ G₁
        ((η ≪≫ isoWhiskerRight θ G₀.functor) ≪≫
          isoWhiskerLeft H₁.functor κ) N M := by
  rw [node_first_reanchor, node_second_reanchor]

/-- The same two transports keep the original composite input and output functor. -/
theorem actual_two_reference_functor :
    (node F H₀ G₀ η (reanchor θ N) (reanchor κ M)).1 = N.1 ≫ M.1 := rfl

/-- The reference component remembers both transports, even when functors coincide. -/
theorem actual_two_reference_component (X : V) :
    (node F H₀ G₀ η (reanchor θ N) (reanchor κ M)).2.hom.app X =
      (node F H₁ G₁
        ((η ≪≫ isoWhiskerRight θ G₀.functor) ≪≫ isoWhiskerLeft H₁.functor κ)
        N M).2.hom.app X := by
  have h := actual_two_reference_changes F H₀ H₁ G₀ G₁ θ κ η N M
  have he := (Sigma.mk.inj h).2
  exact congrArg (fun e : F.functor ≅ N.1.functor ⋙ M.1.functor => e.hom.app X)
    (eq_of_heq he)

/-- Association of full nodes can be reanchored again without losing its references. -/
theorem actual_reanchored_association {W' : Model.{u}} (H : V ⟶ W)
    (J : W ⟶ W') (G : W' ⟶ T) (F' : V ⟶ T)
    (η' : F'.functor ≅ F.functor) (η : F.functor ≅ ((H ≫ J) ≫ G).functor)
    (N : CommonReferenceNerve.Node H) (M : CommonReferenceNerve.Node G) :
    reanchor η' (node F (H ≫ J) G η (postNode (H ≫ J) J (Iso.refl _) N) M) =
      reanchor η' (node F H (J ≫ G) η N (preNode (J ≫ G) J (Iso.refl _) M)) := by
  exact congrArg (reanchor η') (node_associativity F H J G η N M)

end QuillenTest.CommonReferenceProductNodes
