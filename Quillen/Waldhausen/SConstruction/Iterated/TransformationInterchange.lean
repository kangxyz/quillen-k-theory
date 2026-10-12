/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.NerveCylinderInterchange
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopy
public import Quillen.Topology.Prespectrum.HomotopyLoop

/-!
# Literal identity-action interchange of the original iterated S cylinders

The actual endpoint functors preserve the specified source and target identity actions.
Their original weak transformation therefore commutes with both original simplicial time
parameters at every iterated S stage. The existing double-cylinder realization theorem retains
those same parameters, including the unchanged degree-zero loop coordinate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS

/-- Every actual iterated S-simplex retains the two independent transformation-cylinder times. -/
theorem stageTransformationFunction_identityAction_interchange (r : ℕ)
    {V W : Model.{u}} {F G : V ⟶ W} (η : F.functor ⟶ G.functor)
    (α : (𝟙 V : V ⟶ V).functor ⟶ (𝟙 V : V ⟶ V).functor)
    (β : (𝟙 W : W ⟶ W).functor ⟶ (𝟙 W : W ⟶ W).functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hα : ∀ X, V.waldhausen.weq (α.app X))
    (hβ : ∀ X, W.waldhausen.weq (β.app X))
    (hF : ∀ X, F.functor.map (α.app X) = β.app (F.functor.obj X))
    (hG : ∀ X, G.functor.map (α.app X) = β.app (G.functor.obj X))
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ θ : (Δ[1]).obj n) :
    stageTransformationFunction r η hη n
        (stageTransformationFunction r α hα n A τ) θ =
      stageTransformationFunction r β hβ n
        (stageTransformationFunction r η hη n A θ) τ := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveCylinderDiagram_identityAction_interchange η α β hF hG A.val τ.down θ.down
  | succ r ih =>
    apply ih (rowsTransformation η n.unop) (rowsTransformation α n.unop)
      (rowsTransformation β n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak α hα n.unop)
      (rowsTransformation_weak β hβ n.unop)
    · intro B
      apply ObjectProperty.hom_ext
      ext p
      exact hF (B.obj.obj p)
    · intro B
      apply ObjectProperty.hom_ext
      ext p
      exact hG (B.obj.obj p)

variable {V W : Model.{u}} {F G : V ⟶ W} (η : F.functor ⟶ G.functor)
    (α : (𝟙 V : V ⟶ V).functor ⟶ (𝟙 V : V ⟶ V).functor)
    (β : (𝟙 W : W ⟶ W).functor ⟶ (𝟙 W : W ⟶ W).functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hα : ∀ X, V.waldhausen.weq (α.app X))
    (hβ : ∀ X, W.waldhausen.weq (β.app X))
    (hF : ∀ X, F.functor.map (α.app X) = β.app (F.functor.obj X))
    (hG : ∀ X, G.functor.map (α.app X) = β.app (G.functor.obj X))

include hF hG

/-- The original double simplicial cylinder retains its specified parameter swap exactly. -/
theorem stageTransformationCylinder_identityAction_interchange (r : ℕ) :
    stageTransformationCylinder r α hα ▷ Δ[1] ≫ stageTransformationCylinder r η hη =
      simplicialCylinderSwap ((stages r).obj V) ≫
        stageTransformationCylinder r η hη ▷ Δ[1] ≫ stageTransformationCylinder r β hβ := by
  ext n z : 4
  exact stageTransformationFunction_identityAction_interchange r η α β hη hα hβ hF hG
    n z.1.1 z.1.2 z.2

/-- Realization preserves the same two original transformation times at every S stage. -/
theorem stageTransformationTopHomotopy_identityAction_interchange
    (r : ℕ) (s t : unitInterval) (x : stageSpace r V) :
    stageTransformationTopHomotopy r η hη (s, stageTransformationTopHomotopy r α hα (t, x)) =
      stageTransformationTopHomotopy r β hβ (t, stageTransformationTopHomotopy r η hη (s, x)) :=
  realizationSimplicialHomotopy_interchange
    (stageTransformationHomotopy r η hη) (stageTransformationHomotopy r α hα)
    (stageTransformationHomotopy r η hη) (stageTransformationHomotopy r β hβ)
    (stageTransformationCylinder_identityAction_interchange η α β hη hα hβ hF hG r) s t x

/-- The full original prespectrum homotopies commute, including actual degree-zero loops. -/
theorem prespectrumTransformationHomotopy_identityAction_interchange
    (n : ℕ) (s t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationHomotopy η hη).level n
        (s, (prespectrumTransformationHomotopy α hα).level n (t, x)) =
      (prespectrumTransformationHomotopy β hβ).level n
        (t, (prespectrumTransformationHomotopy η hη).level n (s, x)) := by
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext q
    exact stageTransformationTopHomotopy_identityAction_interchange η α β hη hα hβ hF hG
      0 s t (x q)
  | succ r =>
    exact stageTransformationTopHomotopy_identityAction_interchange η α β hη hα hβ hF hG
      r s t x

/-- Reversing the original weak transformation retains literally the reversed null-track time. -/
theorem prespectrumTransformationHomotopy_symm_identityAction_interchange
    (n : ℕ) (s t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationHomotopy η hη).symm.level n
        (s, (prespectrumTransformationHomotopy α hα).level n (t, x)) =
      (prespectrumTransformationHomotopy β hβ).level n
        (t, (prespectrumTransformationHomotopy η hη).symm.level n (s, x)) :=
  prespectrumTransformationHomotopy_identityAction_interchange η α β hη hα hβ hF hG
    n (unitInterval.symm s) t x

end Quillen.Waldhausen.IteratedS
