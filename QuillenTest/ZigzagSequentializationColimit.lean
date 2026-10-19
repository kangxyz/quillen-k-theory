/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.ZigzagSequentializationColimit

/-!
# Ordinary-colimit and original initial-leg regressions

The constant original sequence tests actual prespectrum colimit descent. The canonical
pushout sequence keeps its initial leg without any closed-embedding assumption on that leg.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Quillen.LoopPrespectrum
universe u
namespace QuillenTest.ZigzagSequentializationColimit

/-- The constant original diagram has its literal identity cocone. -/
def constantCocone (E : Quillen.LoopPrespectrum.{u}) :
    Cocone (Functor.ofSequence (fun _ : ℕ ↦ 𝟙 E)) where
  pt := E
  ι := NatTrans.ofSequence (fun _ ↦ 𝟙 E) (fun _ ↦ by simp)

/-- The actual ordinary colimit admits its expected original constant-sequence collapse. -/
def constantCollapse (E : Quillen.LoopPrespectrum.{u}) :
    SequentialColimit.prespectrum (fun _ ↦ E) (fun _ ↦ 𝟙 E) ⟶ E :=
  SequentialColimit.desc _ _ (constantCocone E)

/-- Every stage retains its literal identity under this actual ordinary-colimit descent. -/
theorem constant_stage (E : Quillen.LoopPrespectrum.{u}) (n : ℕ) :
    SequentialColimit.inclusion (fun _ ↦ E) (fun _ ↦ 𝟙 E) n ≫ constantCollapse E = 𝟙 E :=
  SequentialColimit.inclusion_desc _ _ _ _

/-- Closed identity transitions make the original telescope-to-colimit map stable. -/
theorem constant_telescope_stable (E : Quillen.LoopPrespectrum.{u})
    [∀ k, T1Space (E.space k)] :
    IsStableEquivalence (SequentialColimit.collapse (fun _ ↦ E) (fun _ ↦ 𝟙 E)) := by
  let : ∀ (_ : ℕ) k, T1Space (E.space k) := fun _ k ↦ inferInstance
  exact SequentialColimit.collapse_isStableEquivalence _ _ (fun _ _ ↦ .id)

variable (E V : ℕ → Quillen.LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)

/-- The full ordinary colimit exists with no topology assumption on the first solid arrow. -/
def fullOrdinaryColimit :
    IsColimit (ZigzagSequentialization.ordinaryCocone E V a b) :=
  ZigzagSequentialization.ordinaryIsColimit E V a b

/-- The first solid arrow survives the exact tail-and-collapse bridge unchanged. -/
theorem initial_solid_arrow :
    Telescope.inclusion (ZigzagSequentialization.stage E V a b)
        (ZigzagSequentialization.transition E V a b) 0 ≫
      ZigzagSequentialization.telescopeToOrdinaryColimit E V a b =
        a 0 ≫ SequentialColimit.inclusion (ZigzagSequentialization.positiveStage E V a b)
          (ZigzagSequentialization.positiveTransition E V a b) 0 :=
  ZigzagSequentialization.initial_inclusion_telescopeToOrdinaryColimit E V a b

end QuillenTest.ZigzagSequentializationColimit
