/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramSelfMap
public import Quillen.KTheory.Bass.StrictUnderSuccessor

/-!
# The original telescope self-map square under restriction

A seed-preserving arrow from an Under diagram into a restricted ring diagram induces the
actual telescope map using the specified finite restriction transports. This map commutes
with the original telescope-to-Bass self-maps, on their entire original cylinders. No
separation or stability assumption is needed for this exact square.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u w
namespace Quillen.KTheory.Bass

variable (R : CommRingCat.{u})
    {F : Under R ⥤ LoopPrespectrum.{w}} {G : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (σ : F ⟶ (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).obj F)
    (η : G ⟶ strictRingDiagramFunctor.obj G)
    (a : F ⟶ (strictRingDiagramRestriction R).obj G)
    (h : σ ≫ (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).map a =
      a ≫ strictRingDiagramUnderSeed R η)

include h in
/-- The exact iterated restriction arrows preserve the actual transported original seed. -/
theorem strictRingDiagramRestrictionIterateArrow_shiftedSeed (i : ℕ) :
    strictDiagramShiftedSeed (PolynomialBaseChange.laurentUnderSquareFunctor R) σ i ≫
        (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).map
          (strictRingDiagramRestrictionIterateArrow R i a) =
      strictRingDiagramRestrictionIterateArrow R i a ≫
        strictRingDiagramUnderSeed R
          (strictDiagramShiftedSeed PolynomialBaseChange.laurentSquareFunctor η i) := by
  dsimp only [strictDiagramShiftedSeed]
  rw [Category.assoc, strictRingDiagramRestrictionIterateArrow_successor,
    ← Category.assoc, ← strictRingDiagramRestrictionIterateArrow_transition R i σ η a h,
    Category.assoc]
  rfl

/-- The original finite arrows induce the actual map into the unchanged restricted ring tower. -/
def strictRingDiagramRestrictionTelescopeArrow :
    Telescope.diagramFunctor
        (fun i => (strictDiagramIterate (PolynomialBaseChange.laurentUnderSquareFunctor R) i).obj F)
        (strictDiagramTransition (PolynomialBaseChange.laurentUnderSquareFunctor R) σ) ⟶
      Under.forget R ⋙ Telescope.diagramFunctor
        (fun i => (strictRingDiagramIterate i).obj G)
        (strictDiagramTransition PolynomialBaseChange.laurentSquareFunctor η) :=
  Telescope.diagramMap _ _ _ _ (fun i => strictRingDiagramRestrictionIterateArrow R i a)
    (fun i => strictRingDiagramRestrictionIterateArrow_transition R i σ η a h)

/-- The exact restriction telescope arrow commutes with the whole original Bass self-map. -/
theorem strictRingDiagramRestrictionTelescopeArrow_selfMap :
    strictDiagramTelescopeSelfMap (PolynomialBaseChange.laurentUnderSquareFunctor R) σ ≫
        (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).map
          (strictRingDiagramRestrictionTelescopeArrow R σ η a h) =
      strictRingDiagramRestrictionTelescopeArrow R σ η a h ≫
        strictRingDiagramUnderSeed R
          (strictDiagramTelescopeSelfMap PolynomialBaseChange.laurentSquareFunctor η) := by
  have hc (i : ℕ) :
      strictRingDiagramUnderSeed R
          (strictDiagramShiftedSeed PolynomialBaseChange.laurentSquareFunctor η i) ≫
          (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).map
            ((strictRingDiagramRestriction R).map
              (strictDiagramTransition PolynomialBaseChange.laurentSquareFunctor η i)) =
        (strictRingDiagramRestriction R).map
            (strictDiagramTransition PolynomialBaseChange.laurentSquareFunctor η i) ≫
          strictRingDiagramUnderSeed R
            (strictDiagramShiftedSeed PolynomialBaseChange.laurentSquareFunctor η (i + 1)) := by
    apply NatTrans.ext
    funext X
    exact NatTrans.congr_app
      (strictDiagramShiftedSeed_compatibility PolynomialBaseChange.laurentSquareFunctor η i)
      X.right
  exact strictDiagramTelescopeComparison_square
    (PolynomialBaseChange.laurentUnderSquareFunctor R) _ _ _ _ _
    (fun i => strictRingDiagramRestrictionIterateArrow_transition R i σ η a h)
    (strictDiagramShiftedSeed (PolynomialBaseChange.laurentUnderSquareFunctor R) σ)
    (fun i => strictRingDiagramUnderSeed R
      (strictDiagramShiftedSeed PolynomialBaseChange.laurentSquareFunctor η i))
    (strictDiagramShiftedSeed_compatibility (PolynomialBaseChange.laurentUnderSquareFunctor R) σ)
    hc (strictRingDiagramRestrictionIterateArrow_shiftedSeed R σ η a h)

end Quillen.KTheory.Bass
