/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Approximation.WeakComma
public import Quillen.Waldhausen.ExtensionCategory.Functoriality

/-!
# Approximation on genuine Reedy cofibration arrows

App1 and App2 transfer to the existing category of cofibration arrows with its
actual source-plus-relative-pushout Waldhausen structure. The App2 construction
first factors the source component, takes the actual relative pushout, descends
the target square using exactness, and factors that descended arrow. Thus the
comparison square is a genuine Reedy cofibration, not just componentwise a
cofibration. Iteration applies to coherent Reedy squares and higher cubes.

This is a finite branching diagram-lifting stage. It does not assert arbitrary
finite-poset replacement, comma contractibility, or a K-theory equivalence.
All postcomposition functors and weak-comma objects are the existing originals.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u v' u'

namespace Quillen.Waldhausen.HasApproximationProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

include h in
/-- Approximation transfers to the actual Reedy cofibration-arrow category.
In particular App2 controls the joint relative map out of the pushout. -/
theorem reedyArrow_approximation :
    HasApproximationProperty (ExtensionCategory.waldhausenStructure W)
      (ExtensionCategory.waldhausenStructure V) (ExtensionCategory.postcompose W V hF) where
  reflects f hf := ⟨h.reflects _ hf.1, h.reflects _ hf.2⟩
  lift {X Y} f := by
    obtain ⟨A, a, p, ha, hp, hap⟩ := h.lift f.hom.left
    obtain ⟨P, i, j, hP⟩ := W.pushout_exists X.obj.hom a X.property
    have comm : F.map X.obj.hom ≫ f.hom.right = F.map a ≫ (p ≫ Y.obj.hom) := by
      rw [← Category.assoc, hap]
      exact f.hom.w.symm
    let hFP := hF.pushout X.property hP
    let q := hFP.desc f.hom.right (p ≫ Y.obj.hom) comm
    obtain ⟨B, b, r, hb, hr, hbr⟩ := h.lift q
    let Z : ExtensionCategory.Obj W :=
      ⟨Arrow.mk (j ≫ b), W.cof.comp_mem _ _ (W.cof_pushout X.property hP) hb⟩
    let inclusion : X ⟶ Z := (ExtensionCategory.objects W).homMk
      (Arrow.homMk a (i ≫ b) (by
        change a ≫ (j ≫ b) = X.obj.hom ≫ (i ≫ b)
        rw [← Category.assoc, ← hP.w, Category.assoc]))
    have hi : F.map (i ≫ b) ≫ r = f.hom.right := by
      rw [F.map_comp, Category.assoc, hbr]
      exact hFP.inl_desc _ _ _
    have hj : F.map (j ≫ b) ≫ r = p ≫ Y.obj.hom := by
      rw [F.map_comp, Category.assoc, hbr]
      exact hFP.inr_desc _ _ _
    let projection : (ExtensionCategory.postcompose W V hF).obj Z ⟶ Y :=
      (ExtensionCategory.objects V).homMk (Arrow.homMk p r hj.symm)
    refine ⟨Z, inclusion, projection, ?_, ⟨hp, hr⟩, ?_⟩
    · exact ExtensionCategory.cof_of_relative W inclusion ha hP b rfl rfl hb
    · apply ObjectProperty.hom_ext
      apply Arrow.hom_ext
      · exact hap
      · exact hi

/-- Target two-out-of-three is inherited by the actual componentwise weak
class on Reedy arrows. No extra saturation assumption is added. -/
theorem reedyArrow_saturated [V.weq.HasTwoOutOfThreeProperty] :
    (ExtensionCategory.waldhausenStructure V).weq.HasTwoOutOfThreeProperty := by
  change (V.weq.inverseImage (ExtensionCategory.source V) ⊓
    V.weq.inverseImage (ExtensionCategory.middle V)).HasTwoOutOfThreeProperty
  infer_instance

include h in
/-- Iterating the actual arrow construction gives approximation on genuine
Reedy commuting squares, including their joint corner cofibration tests. -/
theorem reedySquare_approximation :
    HasApproximationProperty
      (ExtensionCategory.waldhausenStructure (ExtensionCategory.waldhausenStructure W))
      (ExtensionCategory.waldhausenStructure (ExtensionCategory.waldhausenStructure V))
      (ExtensionCategory.postcompose
        (ExtensionCategory.waldhausenStructure W) (ExtensionCategory.waldhausenStructure V)
        (ExtensionCategory.postcompose_exact W V hF)) :=
  reedyArrow_approximation (h.reedyArrow_approximation hF)
    (ExtensionCategory.postcompose_exact W V hF)

include h in
/-- The actual weak-comma category for coherent Reedy squares is nonempty,
by App2 at the unchanged recursively specified zero arrow. -/
theorem reedySquare_weakComma_nonempty
    (Y : WideSubcategory
      (ExtensionCategory.waldhausenStructure (ExtensionCategory.waldhausenStructure V)).weq) :
    Nonempty (WeakComma
      (ExtensionCategory.postcompose_exact
        (ExtensionCategory.waldhausenStructure W) (ExtensionCategory.waldhausenStructure V)
        (ExtensionCategory.postcompose_exact W V hF)) Y) :=
  (h.reedySquare_approximation hF).weakComma_nonempty _ Y

include h in
/-- Common successors for coherent Reedy-square replacements are constructed
inside their original weak comma category, with no contractibility assertion. -/
theorem reedySquare_weakComma_connected [V.weq.HasTwoOutOfThreeProperty]
    (Y : WideSubcategory
      (ExtensionCategory.waldhausenStructure (ExtensionCategory.waldhausenStructure V)).weq) :
    IsConnected (WeakComma
      (ExtensionCategory.postcompose_exact
        (ExtensionCategory.waldhausenStructure W) (ExtensionCategory.waldhausenStructure V)
        (ExtensionCategory.postcompose_exact W V hF)) Y) := by
  let := reedyArrow_saturated (V := V)
  let := reedyArrow_saturated (V := ExtensionCategory.waldhausenStructure V)
  exact (h.reedySquare_approximation hF).weakComma_connected _ Y

end Quillen.Waldhausen.HasApproximationProperty
