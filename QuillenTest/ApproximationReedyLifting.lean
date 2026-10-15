/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Waldhausen.Approximation.ReedyLifting
public import Quillen.Waldhausen.ExtensionCategory.TransposeExact
public import Quillen.Waldhausen.SplitComplexes.Approximation

/-!
# Semantic consumers of branching Reedy approximation

These consumers distinguish a joint latching cofibration from pointwise
cofibrations. They retain the original four component maps, exercise strict
commuting comparison cubes and transposition, and instantiate the construction
for the genuine split-to-ambient complex comparison.
-/
@[expose] public section

open Quillen.Waldhausen


open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Quillen.Waldhausen.HasApproximationProperty
universe v u v' u'

namespace QuillenTest.ApproximationReedyLifting

open Quillen

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

include h in
/-- The App2 comparison square has an actual relative latching cofibration,
not merely cofibrations on its two vertices. Both target faces are strict. -/
theorem arrow_lift_joint_corner
    {X : ExtensionCategory.Obj W} {Y : ExtensionCategory.Obj V}
    (f : (ExtensionCategory.postcompose W V hF).obj X ⟶ Y) :
    ∃ (Z : ExtensionCategory.Obj W) (i : X ⟶ Z)
      (p : (ExtensionCategory.postcompose W V hF).obj Z ⟶ Y),
      W.cof i.hom.left ∧ W.cof (ExtensionCategory.relativeMap W i) ∧
      V.weq p.hom.left ∧ V.weq p.hom.right ∧
      F.map i.hom.left ≫ p.hom.left = f.hom.left ∧
      F.map i.hom.right ≫ p.hom.right = f.hom.right := by
  obtain ⟨Z, i, p, hi, hp, fac⟩ := (h.reedyArrow_approximation hF).lift f
  exact ⟨Z, i, p, hi.1, hi.2, hp.1, hp.2,
    congrArg (fun k ↦ k.hom.left) fac, congrArg (fun k ↦ k.hom.right) fac⟩

/-- The joint-cofibration assertion holds for every genuine presentation of
the relative pushout, independently of any chosen pushout object. -/
theorem arrow_lift_displayed_corner
    {X : ExtensionCategory.Obj W} {Y : ExtensionCategory.Obj V}
    (f : (ExtensionCategory.postcompose W V hF).obj X ⟶ Y)
    {R : C}
    {i : X.obj.right ⟶ R}
    {j : ((h.reedyArrow_approximation hF).chooseStep f).obj.obj.left ⟶ R}
    (hR : IsPushout X.obj.hom
      ((h.reedyArrow_approximation hF).chooseStep f).inclusion.hom.left i j)
    (k : R ⟶ ((h.reedyArrow_approximation hF).chooseStep f).obj.obj.right)
    (hi : i ≫ k = ((h.reedyArrow_approximation hF).chooseStep f).inclusion.hom.right)
    (hj : j ≫ k = ((h.reedyArrow_approximation hF).chooseStep f).obj.obj.hom) :
    W.cof k :=
  ExtensionCategory.cof_relative W
    ((h.reedyArrow_approximation hF).chooseStep f).cofibration hR k hi hj

include h in
/-- A map between genuine Reedy squares factors through a coherent source
cube whose source face and joint relative face are Reedy cofibrations. -/
theorem square_lift_strict_cube
    {X : ExtensionCategory.Obj (ExtensionCategory.waldhausenStructure W)}
    {Y : ExtensionCategory.Obj (ExtensionCategory.waldhausenStructure V)}
    (f : (ExtensionCategory.postcompose
      (ExtensionCategory.waldhausenStructure W) (ExtensionCategory.waldhausenStructure V)
      (ExtensionCategory.postcompose_exact W V hF)).obj X ⟶ Y) :
    ∃ (Z : ExtensionCategory.Obj (ExtensionCategory.waldhausenStructure W))
      (i : X ⟶ Z)
      (p : (ExtensionCategory.postcompose
        (ExtensionCategory.waldhausenStructure W) (ExtensionCategory.waldhausenStructure V)
        (ExtensionCategory.postcompose_exact W V hF)).obj Z ⟶ Y),
      ExtensionCategory.cof W i.hom.left ∧
      ExtensionCategory.cof W
        (ExtensionCategory.relativeMap (ExtensionCategory.waldhausenStructure W) i) ∧
      V.weq p.hom.left.hom.left ∧ V.weq p.hom.left.hom.right ∧
      V.weq p.hom.right.hom.left ∧ V.weq p.hom.right.hom.right ∧
      (ExtensionCategory.postcompose
        (ExtensionCategory.waldhausenStructure W) (ExtensionCategory.waldhausenStructure V)
        (ExtensionCategory.postcompose_exact W V hF)).map i ≫ p = f := by
  obtain ⟨Z, i, p, hi, hp, fac⟩ := (h.reedySquare_approximation hF).lift f
  exact ⟨Z, i, p, hi.1, hi.2, hp.1.1, hp.1.2, hp.2.1, hp.2.2, fac⟩

/-- Every actual input vertex map remains the original F-map after iterated
postcomposition. This is a four-vertex, strict-map check. -/
theorem square_postcomposition_original_maps
    {X Z : ExtensionCategory.Obj (ExtensionCategory.waldhausenStructure W)} (a : X ⟶ Z) :
    let b := (ExtensionCategory.postcompose
      (ExtensionCategory.waldhausenStructure W) (ExtensionCategory.waldhausenStructure V)
      (ExtensionCategory.postcompose_exact W V hF)).map a
    b.hom.left.hom.left = F.map a.hom.left.hom.left ∧
    b.hom.left.hom.right = F.map a.hom.left.hom.right ∧
    b.hom.right.hom.left = F.map a.hom.right.hom.left ∧
    b.hom.right.hom.right = F.map a.hom.right.hom.right :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Swapping the square directions preserves the genuine Reedy cube test of
the constructed App2 inclusion. -/
theorem square_lift_transposed_cofibration
    {X : ExtensionCategory.Obj (ExtensionCategory.waldhausenStructure W)}
    {Y : ExtensionCategory.Obj (ExtensionCategory.waldhausenStructure V)}
    (f : (ExtensionCategory.postcompose
      (ExtensionCategory.waldhausenStructure W) (ExtensionCategory.waldhausenStructure V)
      (ExtensionCategory.postcompose_exact W V hF)).obj X ⟶ Y) :
    ExtensionCategory.cof (ExtensionCategory.waldhausenStructure W)
      ((ExtensionCategory.transpose W).map
        ((h.reedySquare_approximation hF).chooseStep f).inclusion) :=
  ExtensionCategory.transpose_cof W
    ((h.reedySquare_approximation hF).chooseStep f).cofibration

/-- The chosen source zero of the square model is literally the identity of
the identity of the original specified zero. -/
theorem square_source_zero_retained :
    (ExtensionCategory.waldhausenStructure
      (ExtensionCategory.waldhausenStructure W)).zero.obj.left.obj.left = W.zero ∧
    (ExtensionCategory.waldhausenStructure
      (ExtensionCategory.waldhausenStructure W)).zero.obj.hom.hom.left = 𝟙 W.zero :=
  ⟨rfl, rfl⟩

section Complexes
open CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

include hcone in
/-- Actual cone-closed split complexes give coherent Reedy-square
approximation with no additional diagram-lifting hypothesis. -/
theorem split_complex_reedy_square :
    HasApproximationProperty
      (ExtensionCategory.waldhausenStructure
        (ExtensionCategory.waldhausenStructure (splitComplexSubcategory P)))
      (ExtensionCategory.waldhausenStructure
        (ExtensionCategory.waldhausenStructure (complexSubcategory P)))
      (ExtensionCategory.postcompose
        (ExtensionCategory.waldhausenStructure (splitComplexSubcategory P))
        (ExtensionCategory.waldhausenStructure (complexSubcategory P))
        (ExtensionCategory.postcompose_exact _ _
          (splitComplexSubcategory_to_complexSubcategory_exact P))) :=
  (splitComparison_approximation P hcone).reedySquare_approximation
    (splitComplexSubcategory_to_complexSubcategory_exact P)
end Complexes

end QuillenTest.ApproximationReedyLifting
