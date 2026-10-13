/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OppositeJointData

/-!
Semantic consumers of coherent original opposite-complex cylinders.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes Quillen.Waldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
namespace QuillenTest.PerfectOppositeJointData

open Quillen

/-- The actual opposite structure detects the original admissible epi,
without replacing it by degreewise split epis. -/
theorem actual_strict_fibration_class (X : Scheme.{u}) {A B : StrictPerfect X} (f : A ⟶ B) :
    (strictOppositeWaldhausen X).cof f.op ↔
      (Quillen.ExactSubcategory.exactStructure (Quillen.abelianExactStructure (Complex X))
        (strictPerfect X)).deflation f := Iff.rfl

/-- The constructed perfect cocylinder factors the original map in its
original direction, through a genuine weak map into a perfect middle object. -/
theorem actual_perfect_cocylinder_factorization (X : Scheme.{u})
    {A B : Perfect X} (f : A ⟶ B) :
    ∃ (M : Perfect X) (j : A ⟶ M) (p : M ⟶ B), j ≫ p = f ∧
      ∀ n : ℤ, IsIso (homologyMap j.hom n) := by
  let D := perfectOppositeJointData X
  let a := Arrow.mk f.op
  let M := (D.joint.obj a).obj.right.unop
  let j : A ⟶ M := (D.projection.app a).unop
  let p : M ⟶ B := (D.inl.app a ≫ (D.joint.obj a).obj.hom).unop
  have hj : QuasiIso j.hom := D.weak a
  refine ⟨M, j, p, ?_, fun _ => inferInstance⟩
  have he := congrArg Quiver.Hom.unop (D.factorization a)
  simpa [j, p, a, unop_comp, Category.assoc] using he

/-- The literal strict cocylinder has a strict middle object; its original
projection supplies all actual quasi-isomorphism homology maps. -/
theorem actual_strict_cocylinder_factorization (X : Scheme.{u})
    {A B : StrictPerfect X} (f : A ⟶ B) :
    ∃ (M : StrictPerfect X) (j : A ⟶ M) (p : M ⟶ B), j ≫ p = f ∧
      ∀ n : ℤ, IsIso (homologyMap j.hom n) := by
  let D := strictOppositeJointData X
  let a := Arrow.mk f.op
  let M := (D.joint.obj a).obj.right.unop
  let j : A ⟶ M := (D.projection.app a).unop
  let p : M ⟶ B := (D.inl.app a ≫ (D.joint.obj a).obj.hom).unop
  have hj : QuasiIso j.hom := D.weak a
  refine ⟨M, j, p, ?_, fun _ => inferInstance⟩
  have he := congrArg Quiver.Hom.unop (D.factorization a)
  simpa [j, p, a, unop_comp, Category.assoc] using he

/-- The actual endpoint is a categorical product in the original category,
with a unique original arrow for every pair of endpoint maps. -/
theorem actual_perfect_endpoint_product (X : Scheme.{u}) (f : Arrow (Perfect X)ᵒᵖ)
    (T : Perfect X) (a : T ⟶ f.left.unop) (b : T ⟶ f.right.unop) :
    ∃! l : T ⟶ ((perfectOppositeJointData X).joint.obj f).obj.left.unop,
      l ≫ ((perfectOppositeJointData X).inl.app f).unop = a ∧
      l ≫ ((perfectOppositeJointData X).inr.app f).unop = b := by
  let D := perfectOppositeJointData X
  let hc := D.coproduct f
  refine ⟨(hc.desc (BinaryCofan.mk a.op b.op)).unop, ?_, ?_⟩
  · constructor
    · exact congrArg Quiver.Hom.unop (hc.fac (BinaryCofan.mk a.op b.op) (.mk .left))
    · exact congrArg Quiver.Hom.unop (hc.fac (BinaryCofan.mk a.op b.op) (.mk .right))
  · intro l hl
    apply Quiver.Hom.op_inj
    apply hc.hom_ext
    rintro ⟨j⟩
    cases j
    · change D.inl.app f ≫ l.op = D.inl.app f ≫ hc.desc (BinaryCofan.mk a.op b.op)
      rw [show D.inl.app f ≫ hc.desc (BinaryCofan.mk a.op b.op) = a.op from
        hc.fac _ (.mk .left)]
      exact congrArg Quiver.Hom.op hl.1
    · change D.inr.app f ≫ l.op = D.inr.app f ≫ hc.desc (BinaryCofan.mk a.op b.op)
      rw [show D.inr.app f ≫ hc.desc (BinaryCofan.mk a.op b.op) = b.op from
        hc.fac _ (.mk .right)]
      exact congrArg Quiver.Hom.op hl.2

/-- The common cylinder comparison retains both endpoint maps and the weak
projection, rather than merely identifying unrelated middle objects. -/
theorem actual_inclusion_all_endpoints (X : Scheme.{u}) (f : Arrow (StrictPerfect X)ᵒᵖ) :
    ((perfectOppositeJointData X).inl.app ((strictToPerfect X).op.mapArrow.obj f) ≫
      ((strictToPerfectOpJointIso X).inv.app f).hom.left =
        (strictToPerfect X).op.map ((strictOppositeJointData X).inl.app f)) ∧
    ((perfectOppositeJointData X).inr.app ((strictToPerfect X).op.mapArrow.obj f) ≫
      ((strictToPerfectOpJointIso X).inv.app f).hom.left =
        (strictToPerfect X).op.map ((strictOppositeJointData X).inr.app f)) ∧
    (((strictToPerfectOpJointIso X).inv.app f).hom.right ≫
      (strictToPerfect X).op.map ((strictOppositeJointData X).projection.app f) =
        (perfectOppositeJointData X).projection.app ((strictToPerfect X).op.mapArrow.obj f)) :=
  ⟨strictToPerfectOpJointIso_inv_inl X f, strictToPerfectOpJointIso_inv_inr X f,
    strictToPerfectOpJointIso_inv_projection X f⟩

/-- Degree reversal retains the exact original shift, including negative
indices, over arbitrary independent object and morphism universes. -/
theorem actual_reversed_shift {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex Cᵒᵖ ℤ) :
    Nonempty (((CochainComplex.opEquivalence C).inverse.obj (K⟦(3 : ℤ)⟧)).unop ≅
      ((CochainComplex.opEquivalence C).inverse.obj K).unop⟦(-3 : ℤ)⟧) :=
  ⟨Quillen.CochainComplex.unopShiftIso K 3⟩

/-- The actual component joint cylinder supplies genuine Reedy row
factorizations in every simplicial degree, with the original factorization equation. -/
theorem actual_strict_row_factorization (X : Scheme.{u}) (n : SimplexCategory)
    (a : Arrow (QuotientRows.Obj (strictOppositeWaldhausen X) n)) :
    let W := QuotientRows.waldhausenStructure (strictOppositeWaldhausen X) n
    let F := QuotientRows.factorizationOfJointData (strictOppositeWaldhausen X)
      (strictOppositeJointData X) n
    F.inclusion.app a ≫ F.projection.app a = a.hom ∧
      W.cof (F.inclusion.app a) ∧ W.weq (F.projection.app a) := by
  dsimp only
  exact ⟨(QuotientRows.factorizationOfJointData _ _ n).factorization a,
    (QuotientRows.factorizationOfJointData _ _ n).cofibration a,
    (QuotientRows.factorizationOfJointData _ _ n).weak a⟩

end QuillenTest.PerfectOppositeJointData
