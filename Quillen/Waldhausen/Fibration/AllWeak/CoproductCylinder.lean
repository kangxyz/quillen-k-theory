/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Fibration.AllWeak.Basic
public import Quillen.Waldhausen.Fibration.Rows.SecondEndpoint
public import Quillen.Waldhausen.ExtensionCategory.Embeddings
public import Quillen.Waldhausen.Additivity.SplitSequence

/-! # A genuine coproduct cylinder for the all-weak model

The middle object is the original source-target coproduct, with projection
`[f,id]`. Its joint arrow is the identity. Exactness into the genuine Reedy
extension category is proved by exact coproduct and identity embeddings.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.AllWeak
variable {C : Type u} [Category.{v} C] (W : Structure C)

section ChosenCoproducts
variable [HasBinaryCoproducts C]

/-- The actual source-target sum functor on arbitrary arrows. -/
def middle : Arrow C ⥤ C := Additivity.sumFunctor Arrow.leftFunc Arrow.rightFunc

/-- The original projection `[f,id]`, natural in every commuting square. -/
def projection : middle (C := C) ⟶ Arrow.rightFunc where
  app f := coprod.desc f.hom (𝟙 f.right)
  naturality f g α := by
    apply coprod.hom_ext
    · simp [middle, Additivity.sumFunctor]
    · simp [middle, Additivity.sumFunctor]

/-- Actual joint cylinder data, retaining the original fine weak maps. -/
def coproductJointData : RowFactorization.JointData (nested W) where
  joint := middle ⋙ ExtensionCategory.identityEmbedding W
  exact := (Additivity.sumFunctor_isExact (ArrowCategory.waldhausenStructure W) W
    (ArrowCategory.source_exact W) (ArrowCategory.target_exact W)).comp
      (ExtensionCategory.identityEmbedding_exact W)
  inl := Additivity.sumInl Arrow.leftFunc Arrow.rightFunc
  inr := Additivity.sumInr Arrow.leftFunc Arrow.rightFunc
  coproduct f := coprodIsCoprod f.left f.right
  projection := projection
  factorization f := by
    change coprod.inl ≫ 𝟙 _ ≫ coprod.desc f.hom (𝟙 f.right) = f.hom
    simp
  weak f := trivial

@[simp] theorem coproductJointData_joint_hom (f : Arrow C) :
    ((coproductJointData W).joint.obj f).obj.hom = 𝟙 (f.left ⨿ f.right) := rfl

@[simp] theorem coproductJointData_projection (f : Arrow C) :
    (coproductJointData W).projection.app f = coprod.desc f.hom (𝟙 f.right) := rfl

/-- The original second endpoint is literally a section of the original projection. -/
theorem coproductJointData_secondEndpointSection :
    RowFactorization.SecondEndpointSection (nested W) (coproductJointData W) := by
  intro f
  change coprod.inr ≫ 𝟙 _ ≫ coprod.desc f.hom (𝟙 f.right) = 𝟙 f.right
  simp

end ChosenCoproducts

/-- The same actual cylinder using coproducts derived from the Waldhausen axioms. -/
def jointData : RowFactorization.JointData (nested W) := by
  letI := Additivity.hasBinaryCoproducts W
  exact coproductJointData W

/-- Its second-endpoint identity requires no additional cylinder hypothesis. -/
theorem jointData_secondEndpointSection :
    RowFactorization.SecondEndpointSection (nested W) (jointData W) := by
  let := Additivity.hasBinaryCoproducts W
  exact coproductJointData_secondEndpointSection W

end Quillen.Waldhausen.Fibration.AllWeak
