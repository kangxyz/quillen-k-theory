/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RowLoopFunctor
public import Quillen.Topology.Prespectrum.HomotopyPushout

/-!
# Genuine row interchange on an original homotopy pushout

The last two actual Waldhausen rows act on each of the three original homotopy-pushout
cells. The overlap height is unchanged. This gives a based involution and the complete
two-structure identity at positive levels. It is a levelwise construction, not a claim
that the transpose itself is a prespectrum endomorphism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.RowHomotopyPushout
open LoopPrespectrum
variable {A B C : Model.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- The unchanged original homotopy-pushout prespectrum of the two exact model maps. -/
abbrev spectrum := HomotopyPushout.prespectrum (prespectrumMap f) (prespectrumMap g)

/-- The original realized transpose, typed at its actual prespectrum level. -/
def vertex (k : ℕ) (W : Model.{u}) :
    C((prespectrum W).space (k + 3), (prespectrum W).space (k + 3)) :=
  ⟨stageRowSwapHomeomorph k W, (stageRowSwapHomeomorph k W).continuous⟩

/-- The original vertex transpose fixes the specified point. -/
theorem vertex_point (k : ℕ) (W : Model.{u}) :
    vertex k W ((prespectrum W).point (k + 3)) = (prespectrum W).point (k + 3) :=
  stageRowSwapHomeomorph_point k W

/-- Exact model maps commute with the typed vertex transpose. -/
theorem vertex_naturality (k : ℕ) {V W : Model.{u}} (F : V ⟶ W)
    (x : (prespectrum V).space (k + 3)) :
    vertex k W ((prespectrumMap F).map (k + 3) x) =
      (prespectrumMap F).map (k + 3) (vertex k V x) :=
  stageRowSwapHomeomorph_naturality k F x

/-- The two original rows transpose on every vertex and on the whole overlap cylinder. -/
def rowSwap (k : ℕ) : C((spectrum f g).space (k + 3), (spectrum f g).space (k + 3)) where
  toFun := Quot.lift
    (Sum.elim (Sum.elim
      (fun y => HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3) (vertex k B y))
      (fun z => HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3) (vertex k C z)))
      (fun z => HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3)
        (z.1, vertex k A z.2))) (by
    intro x y h
    cases h with
    | left x =>
      dsimp only [Sum.elim]
      rw [HomotopyPushout.cylinder_zero]
      exact congrArg (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3))
        (vertex_naturality k f x).symm
    | right x =>
      dsimp only [Sum.elim]
      rw [HomotopyPushout.cylinder_one]
      exact congrArg (HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3))
        (vertex_naturality k g x).symm
    | base s =>
      change HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3)
        (s, vertex k A ((prespectrum A).point (k + 3))) =
          HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3)
            (vertex k B ((prespectrum B).point (k + 3)))
      rw [vertex_point, vertex_point]
      exact HomotopyPushout.cylinder_point _ _ (k + 3) s)
  continuous_toFun := continuous_quot_lift _
    (((HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3)).continuous.comp
      (vertex k B).continuous).sumElim
      ((HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3)).continuous.comp
        (vertex k C).continuous) |>.sumElim (by fun_prop))

/-- The left original target is acted on by its actual row transpose. -/
theorem rowSwap_left (k : ℕ) (x : (prespectrum B).space (k + 3)) :
    rowSwap f g k (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3) x) =
      HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3) (vertex k B x) := rfl

/-- The right original target is acted on by its actual row transpose. -/
theorem rowSwap_right (k : ℕ) (x : (prespectrum C).space (k + 3)) :
    rowSwap f g k (HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3) x) =
      HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3) (vertex k C x) := rfl

/-- The entire overlap retains its original height. -/
theorem rowSwap_cylinder (k : ℕ) (h : unitInterval)
    (x : (prespectrum A).space (k + 3)) :
    rowSwap f g k (HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3) (h, x)) =
      HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3)
        (h, vertex k A x) := rfl

/-- The actual pushout basepoint is fixed. -/
theorem rowSwap_point (k : ℕ) :
    rowSwap f g k ((spectrum f g).point (k + 3)) = (spectrum f g).point (k + 3) := by
  exact congrArg (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3))
    (vertex_point k B)

private theorem vertex_involutive (k : ℕ) (W : Model.{u})
    (x : (prespectrum W).space (k + 3)) :
    vertex k W (vertex k W x) = x :=
  (stageRowSwapHomeomorph k W).symm_apply_apply x

/-- Applying the genuine quotient row transpose twice is literally the identity. -/
theorem rowSwap_involutive (k : ℕ) : Function.Involutive (rowSwap f g k) := by
  intro q
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl x =>
        exact congrArg (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3))
          (vertex_involutive k B x)
      | inr x =>
        exact congrArg (HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3))
          (vertex_involutive k C x)
    | inr z =>
      exact congrArg (fun y =>
        HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3) (z.1, y))
        (vertex_involutive k A z.2)

/-- The original two structure times interchange, while the overlap height stays fixed. -/
theorem structure_rowSwap (k : ℕ) (x : (spectrum f g).space (k + 1))
    (s t : unitInterval) :
    rowSwap f g k ((spectrum f g).structureMap (k + 2)
      ((spectrum f g).structureMap (k + 1) x s) t) =
        (spectrum f g).structureMap (k + 2)
          ((spectrum f g).structureMap (k + 1) x t) s := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl x =>
        exact congrArg (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3))
          (stageLoopMap_rowSwap k B x s t)
      | inr x =>
        exact congrArg (HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3))
          (stageLoopMap_rowSwap k C x s t)
    | inr z =>
      exact congrArg (fun y =>
        HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3) (z.1, y))
        (stageLoopMap_rowSwap k A z.2 s t)

end Quillen.Waldhausen.IteratedS.RowHomotopyPushout
