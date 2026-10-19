/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexLiftPasting
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIntertwiningHomotopy

/-!
# The original intertwining word on four complete reference nodes

The two original composition triangles, their reversal, concatenation and endpoint transport
are retained literally. This lifts the prescribed intertwining comparison, not merely a surface
with the same four boundary paths.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Convexity Quillen.LoopPrespectrum
open Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.SimplexIntertwiningLift

/-- The first original composition triangle follows nodes zero, one and three. -/
def firstFace : ⦋2⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 3], by decide⟩

/-- The second original composition triangle follows nodes zero, two and three. -/
def secondFace : ⦋2⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![0, 2, 3], by decide⟩

/-- The exact two-triangle parameter word of the original intertwining comparison. -/
def parameter : ((edge (k := 3) 0 1).trans (edge 1 3)).Homotopy
    ((edge 0 2).trans (edge 2 3)) :=
  (triangle firstFace).symm.trans (triangle secondFace)

private def pastingTemplate {E D : LoopPrespectrum.{u}} {f g : E ⟶ D}
    {A B C D' : Homotopy f g} (e : A = B)
    (J : A.RelHomotopy C) (K : B.RelHomotopy D') : C.RelHomotopy D' :=
  J.symm.trans ((congrArg (fun H ↦ H.RelHomotopy D') e.symm).mp K)

private theorem template_lift {V W : Model.{u}} (S : ModelSimplex V W 3)
    {f g : prespectrum V ⟶ prespectrum W} {A B C D : Homotopy f g}
    (e : A = B) (J : A.RelHomotopy C) (K : B.RelHomotopy D)
    (hJ : HomotopyLift S (triangle firstFace) J)
    (hK : HomotopyLift S (triangle secondFace) K) :
    HomotopyLift S parameter (pastingTemplate e J K) :=
  HomotopyLift.trans S (HomotopyLift.symm S hJ)
    (HomotopyLift.nativeCast S hK e.symm rfl
      (congrArg (fun H ↦ H.RelHomotopy D) e.symm))

private theorem composite_eq {V W : Model.{u}} {F G G' H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (η' : F.functor ⟶ G'.functor) (θ' : G'.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.waldhausen.weq (η'.app A))
    (hθ' : ∀ A, W.waldhausen.weq (θ'.app A)) (he : η ≫ θ = η' ≫ θ') :
    prespectrumTransformationHomotopy (η ≫ θ)
      (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) =
    prespectrumTransformationHomotopy (η' ≫ θ')
      (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη' A) (hθ' A)) := by
  congr 1

/-- Two exact triangle lifts recover the entire existing pasting, including its stored cast. -/
theorem pasting_lift {V W : Model.{u}} {F G G' H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (η' : F.functor ⟶ G'.functor) (θ' : G'.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.waldhausen.weq (η'.app A))
    (hθ' : ∀ A, W.waldhausen.weq (θ'.app A)) (he : η ≫ θ = η' ≫ θ')
    (S : ModelSimplex V W 3)
    (hfirst : HomotopyLift S (triangle firstFace)
      (prespectrumTransformationCompositionHomotopy η θ hη hθ))
    (hsecond : HomotopyLift S (triangle secondFace)
      (prespectrumTransformationCompositionHomotopy η' θ' hη' hθ')) :
    HomotopyLift S parameter (prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he) := by
  have hform : prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he =
      pastingTemplate (composite_eq η θ η' θ' hη hθ hη' hθ' he)
        (prespectrumTransformationCompositionHomotopy η θ hη hθ)
        (prespectrumTransformationCompositionHomotopy η' θ' hη' hθ') := rfl
  rw [hform]
  exact template_lift S _ _ _ hfirst hsecond

variable {V W T U : Model.{u}}
  (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
  (α : F.functor ≅ F.functor) (i : (F ≫ b).functor ≅ (a ≫ G).functor)

/-- The original four vertices, including the separately anchored repeated vertices. -/
def vertices : Fin 4 → (V ⟶ U) := ![F ≫ b, F ≫ b, a ≫ G, a ≫ G]

/-- All four full reference isomorphisms are the original whiskering and comparison word. -/
def anchors : ∀ n, (F ≫ b).functor ≅ (vertices F G a b n).functor :=
  Fin.cases (Iso.refl _) (Fin.cases (isoWhiskerRight α b.functor)
    (Fin.cases i (Fin.cases (isoWhiskerRight α b.functor ≪≫ i) (fun j ↦ Fin.elim0 j))))

/-- The actual common simplex retains the full original reference nodes. -/
def simplex : ModelSimplex V U 3 :=
  ModelSimplex.ofIsos (F ≫ b) (vertices F G a b) (anchors F G a b α i)

variable (θ : G.functor ⟶ G.functor)
  (hα : ∀ X, W.waldhausen.weq (α.hom.app X))
  (hθ : ∀ X, U.waldhausen.weq (θ.app X))
  (hi : ∀ X, U.waldhausen.weq (i.hom.app X))
  (he : whiskerRight α.hom b.functor ≫ i.hom = i.hom ≫ whiskerLeft a.functor θ)

/-- The first whole triangle is the original postwhiskered unit followed by comparison. -/
theorem first_lift : HomotopyLift (simplex F G a b α i) (triangle firstFace)
    (prespectrumTransformationCompositionHomotopy
      (F := F ≫ b) (G := F ≫ b) (H := a ≫ G) (whiskerRight α.hom b.functor) i.hom
      (fun X ↦ b.exact.weak _ (hα X)) hi) := by
  intro n r s x
  exact prespectrumSimplexFamily_ofIsos_triangle (F ≫ b) (vertices F G a b)
    (anchors F G a b α i) firstFace (whiskerRight α.hom b.functor) i.hom
    (fun X ↦ b.exact.weak _ (hα X)) hi (Category.id_comp _) rfl n r s x

/-- The second whole triangle uses the given actual intertwining equality at its final anchor. -/
theorem second_lift
    (he : whiskerRight α.hom b.functor ≫ i.hom = i.hom ≫ whiskerLeft a.functor θ) :
    HomotopyLift (simplex F G a b α i) (triangle secondFace)
    (prespectrumTransformationCompositionHomotopy
      (F := F ≫ b) (G := a ≫ G) (H := a ≫ G) i.hom (whiskerLeft a.functor θ)
      hi (fun X ↦ hθ (a.functor.obj X))) := by
  intro n r s x
  exact prespectrumSimplexFamily_ofIsos_triangle (F ≫ b) (vertices F G a b)
    (anchors F G a b α i) secondFace i.hom (whiskerLeft a.functor θ)
    hi (fun X ↦ hθ (a.functor.obj X)) (Category.id_comp _) he.symm n r s x

/-- The original ofLevels wrapper preserves an exact two-triangle lift on any given simplex. -/
theorem of_triangle_lifts (S : ModelSimplex V U 3)
    (hfirst : HomotopyLift S (triangle firstFace)
      (prespectrumTransformationCompositionHomotopy
        (F := F ≫ b) (G := F ≫ b) (H := a ≫ G) (whiskerRight α.hom b.functor) i.hom
        (fun X ↦ b.exact.weak _ (hα X)) hi))
    (hsecond : HomotopyLift S (triangle secondFace)
      (prespectrumTransformationCompositionHomotopy
        (F := F ≫ b) (G := a ≫ G) (H := a ≫ G) i.hom (whiskerLeft a.functor θ)
        hi (fun X ↦ hθ (a.functor.obj X)))) :
    HomotopyLift S parameter
      (prespectrumTransformationIntertwiningHomotopy F G a b α.hom θ i.hom hα hθ hi he) := by
  unfold prespectrumTransformationIntertwiningHomotopy
  exact HomotopyLift.ofLevels S
    (pasting_lift (F := F ≫ b) (G := F ≫ b) (G' := a ≫ G) (H := a ≫ G)
      (whiskerRight α.hom b.functor) i.hom i.hom (whiskerLeft a.functor θ)
      (fun X ↦ b.exact.weak _ (hα X)) hi hi (fun X ↦ hθ (a.functor.obj X)) he
      S hfirst hsecond) _ _ _ _

/-- The original full intertwining comparison has exactly the two-triangle parameter word. -/
theorem native : HomotopyLift (simplex F G a b α i) parameter
    (prespectrumTransformationIntertwiningHomotopy F G a b α.hom θ i.hom hα hθ hi he) :=
  of_triangle_lifts F G a b α i θ hα hθ hi he (simplex F G a b α i)
    (first_lift F G a b α i hα hi) (second_lift F G a b α i θ hθ hi he)

end Quillen.Waldhausen.IteratedS.SimplexIntertwiningLift
