/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramRowInputIdentity
public import Quillen.KTheory.Bass.SchemeModelRowNormalizedInputComposition

/-! # Identity input on the original normalized telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w

private theorem telescopeMap_id_of_eq
    {E V : ℕ → Quillen.LoopPrespectrum.{w}}
    {a : ∀ n, E n ⟶ V n} {b : ∀ n, E (n + 1) ⟶ V n}
    (d : ∀ n, E n ⟶ E n) (v : ∀ n, V n ⟶ V n)
    (ha : ∀ n, a n ≫ v n = d n ≫ a n)
    (hb : ∀ n, b n ≫ v n = d (n + 1) ≫ b n)
    (hd : d = fun n => 𝟙 (E n)) (hv : v = fun n => 𝟙 (V n)) :
    ZigzagSequentialization.inducedTelescopeMap E V a b E V a b d v ha hb = 𝟙 _ := by
  subst d
  subst v
  apply Telescope.hom_ext
  intro k i s x
  change Telescope.cylinder (ZigzagSequentialization.stage E V a b)
      (ZigzagSequentialization.transition E V a b) k i
      (s, (ZigzagSequentialization.stageMap E V a b E V a b _ _ ha hb i).map k x) = _
  rw [ZigzagSequentialization.stageMap_id]
  rfl

namespace Quillen.KTheory.Bass.SchemeModelRowSeed
open GeometricSeedCospan ModelRowZigzagSequentialization
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})

/-- The actual identity input is the identity at every original vertex. -/
theorem stageInput_id (i : ℕ) (X : Scheme.{u}ᵒᵖ) : stageInput M M (𝟙 M) i X = 𝟙 _ := by
  simp only [stageInput, Functor.whiskerRight_id', CategoryTheory.Functor.map_id, NatTrans.id_app]

/-- The actual identity input is the identity at every original proper-row target. -/
theorem targetInput_id (i : ℕ) (X : Scheme.{u}ᵒᵖ) : targetInput M M (𝟙 M) i X = 𝟙 _ :=
  congrArg (fun a => a.app X)
    (ModelDiagramRowStabilizedTarget.inputNatTrans_id squareFunctor i M)

variable
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).functor (unit X) (unit Y))
  (hId : ∀ X, Preserves ((𝟙 M : M ⟶ M).app (laurent.op.obj X)).functor (unit X) (unit X))

/-- Original identity inputs retain every cylinder of the normalized telescope identically. -/
theorem normalizedInputMap_id (X : Scheme.{u}ᵒᵖ) :
    normalizedInputMap M unit hunit M unit hunit (𝟙 M) hId X = 𝟙 _ :=
  telescopeMap_id_of_eq _ _ _ _
    (funext (fun i => stageInput_id M i X)) (funext (fun i => targetInput_id M i X))

end Quillen.KTheory.Bass.SchemeModelRowSeed
