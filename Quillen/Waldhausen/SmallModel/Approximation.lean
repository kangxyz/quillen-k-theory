/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Approximation.Basic
public import Quillen.Waldhausen.Fibration.Rows.ReflexiveFactorization
public import Quillen.Waldhausen.SmallModel.Acyclic
public import Quillen.Waldhausen.SmallModel.Joint
public import Quillen.Topology.HomotopyGroups.WeakEquivalenceCancellation

/-! # Actual approximation transport through the existing small model

App1/App2 is transported by the actual up/down functors, retaining the
original factors. The existing joint-cylinder transport specializes to the
reflexive weak pair. Original S-map naturality carries complete weakness
back through the genuine realization homeomorphisms.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}

/-- App1 and App2 are transported through the original actual small-model
functor; each lifted factor is the actual up-map of a base App2 factor. -/
theorem HasApproximationProperty.smallModel (h : HasApproximationProperty W V F) :
    HasApproximationProperty W.smallModel V.smallModel (smallModelFunctor F) where
  reflects f hf := h.reflects (AsSmall.down.map f) hf
  lift f := by
    obtain ⟨X', i, p, hi, hp, he⟩ := h.lift (AsSmall.down.map f)
    exact ⟨(AsSmall.up : C ⥤ SmallModel C).obj X',
      (AsSmall.up : C ⥤ SmallModel C).map i, (AsSmall.up : D ⥤ SmallModel D).map p, hi, hp,
      congrArg (AsSmall.up : D ⥤ SmallModel D).map he⟩

/-- The transported reflexive pair is the literal reflexive small-model pair. -/
@[simp] theorem Fibration.NestedWeakEquivalences.refl_smallModel :
    (Fibration.NestedWeakEquivalences.refl W).smallModel =
      Fibration.NestedWeakEquivalences.refl W.smallModel := rfl

/-- The existing genuine joint transport applies to the exact original weak class. -/
def Fibration.RowFactorization.JointData.reflexiveSmallModel
    (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W)) :
    Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W.smallModel) :=
  J.smallModel

/-- Complete weakness of the actual small-model S-map implies complete weakness
of the unchanged original S-map by its strictly natural homeomorphism square. -/
theorem deloopingMap_isWeakHomotopyEquivalence_of_smallModel
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (h : IsWeakHomotopyEquivalence (deloopingMap hF.smallModel).hom) :
    IsWeakHomotopyEquivalence (deloopingMap hF).hom := by
  have hc := h.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    W.smallModelDeloopingHomeomorph.toHomotopyEquiv)
  rw [← smallModelDeloopingHomeomorph_naturality] at hc
  exact hc.of_comp_right
    (isWeakHomotopyEquivalence_of_homotopyEquiv V.smallModelDeloopingHomeomorph.toHomotopyEquiv)

end Quillen.Waldhausen
