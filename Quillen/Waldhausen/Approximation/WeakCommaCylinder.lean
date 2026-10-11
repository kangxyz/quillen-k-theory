/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Approximation.WeakComma
public import Quillen.Waldhausen.Additivity.CoproductAlgebra
public import Quillen.Topology.ClassifyingSpace.ArrowPaths

/-!
# Coherent cylinder fillings in the original approximation comma category

Factoring the coproduct fold gives an actual joint-endpoint cylinder. For two
parallel original weak-comma arrows, exact pushout descent and App2 attach this
cylinder and produce an actual coherent filling in the same comma category.
Its source endpoint retraction and both filling triangles are strict. Consequently
parallel arrows induce endpoint-fixed homotopic paths on the actual classifying
space. No strict coequalizer, higher contractibility, or approximation comparison
is assumed or asserted.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u v' u' w z

namespace Quillen.Waldhausen
namespace FunctorialFactorization
variable {C : Type u} [Category.{v} C] {W : Structure C}
  [HasBinaryCoproducts C] (T : FunctorialFactorization W) (X : C)

/-- The actual fold arrow on the original object. -/
def foldArrow : Arrow C := Arrow.mk (coprod.desc (𝟙 X) (𝟙 X))

/-- Factor the fold, retaining its actual coproduct as the joint endpoint source. -/
def foldCylinder : C := T.middle.obj (foldArrow X)

/-- The first actual cylinder endpoint. -/
def foldEndpointZero : X ⟶ T.foldCylinder X :=
  coprod.inl ≫ T.inclusion.app (foldArrow X)

/-- The second actual cylinder endpoint. -/
def foldEndpointOne : X ⟶ T.foldCylinder X :=
  coprod.inr ≫ T.inclusion.app (foldArrow X)

/-- The original weak projection of the fold factorization. -/
def foldProjection : T.foldCylinder X ⟶ X := T.projection.app (foldArrow X)

@[reassoc (attr := simp)] theorem foldEndpointZero_projection :
    T.foldEndpointZero X ≫ T.foldProjection X = 𝟙 X := by
  simp [foldEndpointZero, foldProjection, foldArrow]

@[reassoc (attr := simp)] theorem foldEndpointOne_projection :
    T.foldEndpointOne X ≫ T.foldProjection X = 𝟙 X := by
  simp [foldEndpointOne, foldProjection, foldArrow]

/-- The joint map really is a cofibration, by the given factorization. -/
theorem fold_joint_cof : W.cof (T.inclusion.app (foldArrow X)) := T.cofibration _

/-- No extra cylinder axiom is needed for its weak projection. -/
theorem foldProjection_weak : W.weq (T.foldProjection X) := T.weak _

/-- Each endpoint is a genuine cofibration. -/
theorem foldEndpointZero_cof : W.cof (T.foldEndpointZero X) :=
  W.cof.comp_mem _ _ (Additivity.coprod_inl_cof W X X) (T.cofibration _)

/-- Each endpoint is a genuine cofibration. -/
theorem foldEndpointOne_cof : W.cof (T.foldEndpointOne X) :=
  W.cof.comp_mem _ _ (Additivity.coprod_inr_cof W X X) (T.cofibration _)
end FunctorialFactorization

namespace HasApproximationProperty
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]

include h hF in
/-- App1 and exact weak preservation transfer target two-out-of-three to source. -/
theorem source_twoOutOfThree : W.weq.HasTwoOutOfThreeProperty := by
  have hw : W.weq = V.weq.inverseImage F := by
    ext X Y f
    exact ⟨hF.weak f, h.reflects f⟩
  rw [hw]
  infer_instance

variable [HasBinaryCoproducts C] (T : FunctorialFactorization W)
  (Y : WideSubcategory V.weq)

/-- The actual fold cylinder is an object of the original weak comma category. -/
def weakCommaCylinder (A : WeakComma hF Y) : WeakComma hF Y :=
  CostructuredArrow.mk (Y := (⟨T.foldCylinder A.left.obj⟩ : WideSubcategory W.weq))
    ⟨F.map (T.foldProjection A.left.obj) ≫ A.hom.hom,
      V.weq.comp_mem _ _ (hF.weak _ (T.foldProjection_weak _)) A.hom.property⟩

/-- The first cylinder endpoint in the original comma category. -/
def weakCommaEndpointZero (A : WeakComma hF Y) :
    A ⟶ weakCommaCylinder hF T Y A := by
  letI := h.source_twoOutOfThree hF
  refine CostructuredArrow.homMk ⟨T.foldEndpointZero A.left.obj, ?_⟩ ?_
  · apply W.weq.of_postcomp _ (T.foldProjection A.left.obj) (T.foldProjection_weak _)
    simp only [T.foldEndpointZero_projection]
    exact W.weq.id_mem _
  · apply WideSubcategory.hom_ext
    change F.map (T.foldEndpointZero A.left.obj) ≫
      (F.map (T.foldProjection A.left.obj) ≫ A.hom.hom) = A.hom.hom
    rw [← F.map_comp_assoc, T.foldEndpointZero_projection, F.map_id, Category.id_comp]

/-- The second cylinder endpoint in the original comma category. -/
def weakCommaEndpointOne (A : WeakComma hF Y) :
    A ⟶ weakCommaCylinder hF T Y A := by
  letI := h.source_twoOutOfThree hF
  refine CostructuredArrow.homMk ⟨T.foldEndpointOne A.left.obj, ?_⟩ ?_
  · apply W.weq.of_postcomp _ (T.foldProjection A.left.obj) (T.foldProjection_weak _)
    simp only [T.foldEndpointOne_projection]
    exact W.weq.id_mem _
  · apply WideSubcategory.hom_ext
    change F.map (T.foldEndpointOne A.left.obj) ≫
      (F.map (T.foldProjection A.left.obj) ≫ A.hom.hom) = A.hom.hom
    rw [← F.map_comp_assoc, T.foldEndpointOne_projection, F.map_id, Category.id_comp]

/-- The actual cylinder projection, as a weak-comma morphism. -/
def weakCommaCylinderProjection (A : WeakComma hF Y) :
    weakCommaCylinder hF T Y A ⟶ A :=
  CostructuredArrow.homMk ⟨T.foldProjection A.left.obj, T.foldProjection_weak _⟩ rfl

@[reassoc (attr := simp)] theorem weakCommaEndpointZero_projection (A : WeakComma hF Y) :
    weakCommaEndpointZero h hF T Y A ≫ weakCommaCylinderProjection hF T Y A = 𝟙 A := by
  apply CostructuredArrow.hom_ext
  apply WideSubcategory.hom_ext
  exact T.foldEndpointZero_projection _

@[reassoc (attr := simp)] theorem weakCommaEndpointOne_projection (A : WeakComma hF Y) :
    weakCommaEndpointOne h hF T Y A ≫ weakCommaCylinderProjection hF T Y A = 𝟙 A := by
  apply CostructuredArrow.hom_ext
  apply WideSubcategory.hom_ext
  exact T.foldEndpointOne_projection _

/-- A coherent cylinder filling, entirely in the original weak comma category. -/
structure ParallelFilling {A B : WeakComma hF Y} (f g : A ⟶ B) where
  /-- The weak-comma object in which the two cylinder attachment triangles are filled. -/
  target : WeakComma hF Y
  /-- The map from the common target `B` to the filling object, with a cofibration as its
  underlying source-category map. -/
  fromTarget : B ⟶ target
  /-- The map from the chosen cylinder on `A` into the filling object; its endpoint composites
  agree with `f` and `g` followed by `fromTarget`. -/
  fromCylinder : weakCommaCylinder hF T Y A ⟶ target
  fromTarget_cof : W.cof fromTarget.left.hom
  first : weakCommaEndpointZero h hF T Y A ≫ fromCylinder = f ≫ fromTarget
  second : weakCommaEndpointOne h hF T Y A ≫ fromCylinder = g ≫ fromTarget

/-- Attach the actual joint cylinder and apply App2 once. The output fills
both parallel arrows coherently, rather than asserting a strict coequalizer. -/
def parallelFilling {A B : WeakComma hF Y} (f g : A ⟶ B) :
    ParallelFilling h hF T Y f g := Classical.choice (by
  let X := A.left.obj
  let a := T.inclusion.app (FunctorialFactorization.foldArrow X)
  let d := coprod.desc f.left.hom g.left.hom
  obtain ⟨P, i, j, hp⟩ := W.pushout_exists a d (T.cofibration _)
  have comm : F.map a ≫ (weakCommaCylinder hF T Y A).hom.hom =
      F.map d ≫ B.hom.hom := by
    apply (hF.pushout (W.cof_zero X) (Additivity.coprod_isPushout W X X)).hom_ext
    · have hf := congrArg (fun k ↦ k.hom) (CostructuredArrow.w f)
      change F.map f.left.hom ≫ B.hom.hom = A.hom.hom at hf
      have hz := congrArg (fun k ↦ k.hom)
        (CostructuredArrow.w (weakCommaEndpointZero h hF T Y A))
      change F.map (T.foldEndpointZero X) ≫
        (weakCommaCylinder hF T Y A).hom.hom = A.hom.hom at hz
      rw [← F.map_comp_assoc, ← F.map_comp_assoc]
      change F.map (T.foldEndpointZero X) ≫ _ = F.map (coprod.inl ≫ d) ≫ _
      rw [hz]
      simpa only [d, coprod.inl_desc] using hf.symm
    · have hg := congrArg (fun k ↦ k.hom) (CostructuredArrow.w g)
      change F.map g.left.hom ≫ B.hom.hom = A.hom.hom at hg
      have hz := congrArg (fun k ↦ k.hom)
        (CostructuredArrow.w (weakCommaEndpointOne h hF T Y A))
      change F.map (T.foldEndpointOne X) ≫
        (weakCommaCylinder hF T Y A).hom.hom = A.hom.hom at hz
      rw [← F.map_comp_assoc, ← F.map_comp_assoc]
      change F.map (T.foldEndpointOne X) ≫ _ = F.map (coprod.inr ≫ d) ≫ _
      rw [hz]
      simpa only [d, coprod.inr_desc] using hg.symm
  let fp := hF.pushout (T.cofibration _) hp
  let q := fp.desc (weakCommaCylinder hF T Y A).hom.hom B.hom.hom comm
  obtain ⟨Q, k, p, hk, hpweak, hkp⟩ := h.lift q
  have hi : F.map (i ≫ k) ≫ p = (weakCommaCylinder hF T Y A).hom.hom := by
    rw [F.map_comp, Category.assoc, hkp]
    exact fp.inl_desc _ _ _
  have hj : F.map (j ≫ k) ≫ p = B.hom.hom := by
    rw [F.map_comp, Category.assoc, hkp]
    exact fp.inr_desc _ _ _
  have wi : W.weq (i ≫ k) := h.reflects _
    (V.weq.of_postcomp _ p hpweak (hi.symm ▸ (weakCommaCylinder hF T Y A).hom.property))
  have wj : W.weq (j ≫ k) := h.reflects _
    (V.weq.of_postcomp _ p hpweak (hj.symm ▸ B.hom.property))
  let Z : WeakComma hF Y := CostructuredArrow.mk
    (Y := (⟨Q⟩ : WideSubcategory W.weq)) ⟨p, hpweak⟩
  let b : B ⟶ Z := CostructuredArrow.homMk ⟨j ≫ k, wj⟩ (by apply WideSubcategory.hom_ext; exact hj)
  let c : weakCommaCylinder hF T Y A ⟶ Z :=
    CostructuredArrow.homMk ⟨i ≫ k, wi⟩ (by apply WideSubcategory.hom_ext; exact hi)
  refine ⟨⟨Z, b, c, W.cof.comp_mem _ _ (W.cof_pushout (T.cofibration _) hp) hk, ?_, ?_⟩⟩
  · apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    change (coprod.inl ≫ a) ≫ (i ≫ k) = f.left.hom ≫ (j ≫ k)
    rw [Category.assoc, ← Category.assoc a, hp.w]
    rw [Category.assoc d]
    exact coprod.inl_desc_assoc f.left.hom g.left.hom (j ≫ k)
  · apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    change (coprod.inr ≫ a) ≫ (i ≫ k) = g.left.hom ≫ (j ≫ k)
    rw [Category.assoc, ← Category.assoc a, hp.w]
    rw [Category.assoc d]
    exact coprod.inr_desc_assoc f.left.hom g.left.hom (j ≫ k))

include h T in
/-- Every groupoid-valued functor identifies parallel weak-comma arrows. This
is a consequence of the constructed cylinder filler and its strict retraction. -/
theorem parallel_map_eq {G : Type z} [Groupoid.{w} G] (H : WeakComma hF Y ⥤ G)
    {A B : WeakComma hF Y} (f g : A ⟶ B) : H.map f = H.map g := by
  let s := parallelFilling h hF T Y f g
  have he : H.map (weakCommaEndpointZero h hF T Y A) =
      H.map (weakCommaEndpointOne h hF T Y A) := by
    apply (cancel_mono (H.map (weakCommaCylinderProjection hF T Y A))).1
    simp only [← H.map_comp, weakCommaEndpointZero_projection, weakCommaEndpointOne_projection]
  apply (cancel_mono (H.map s.fromTarget)).1
  rw [← H.map_comp, ← H.map_comp, ← s.first, ← s.second, H.map_comp, H.map_comp, he]

include h T in
/-- The original realized paths of any parallel comma arrows are homotopic
relative to both endpoints, in the actual classifying space. -/
theorem parallel_paths_homotopic {A B : WeakComma hF Y} (f g : A ⟶ B) :
    (classifyingSpacePath f).Homotopic (classifyingSpacePath g) :=
  Quotient.exact (parallel_map_eq h hF T Y
    (classifyingFundamentalGroupoidFunctor (WeakComma hF Y)) f g)

include T in
/-- A groupoid-valued functor on the original comma category is naturally
constant. The components are the original common-successor maps, with the
second one inverted in the target groupoid. -/
def groupoidConstantIso {G : Type z} [Groupoid.{w} G]
    (H : WeakComma hF Y ⥤ G) (P : WeakComma hF Y) :
    H ≅ (Functor.const (WeakComma hF Y)).obj (H.obj P) :=
  NatIso.ofComponents (fun A ↦
    asIso (H.map (weakCommaPairLeft h hF Y A P)) ≪≫
      (asIso (H.map (weakCommaPairRight h hF Y A P))).symm) (by
    intro A B f
    let LA := weakCommaPairLeft h hF Y A P
    let RA := weakCommaPairRight h hF Y A P
    let LB := weakCommaPairLeft h hF Y B P
    let RB := weakCommaPairRight h hF Y B P
    let i := weakCommaPairLeft h hF Y (weakCommaPairTarget h hF Y A P)
      (weakCommaPairTarget h hF Y B P)
    let j := weakCommaPairRight h hF Y (weakCommaPairTarget h hF Y A P)
      (weakCommaPairTarget h hF Y B P)
    have hf := parallel_map_eq h hF T Y H (LA ≫ i) (f ≫ LB ≫ j)
    have hp := parallel_map_eq h hF T Y H (RA ≫ i) (RB ≫ j)
    simp only [H.map_comp] at hf hp
    change H.map f ≫ (H.map LB ≫ inv (H.map RB)) =
      (H.map LA ≫ inv (H.map RA)) ≫ 𝟙 _
    rw [Category.comp_id]
    apply (cancel_mono (H.map RB ≫ H.map j)).1
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← hp]
    simp only [IsIso.inv_hom_id_assoc]
    exact hf.symm)

/-- The constant comparison uses exactly the displayed source common successor. -/
@[simp] theorem groupoidConstantIso_hom_app {G : Type z} [Groupoid.{w} G]
    (H : WeakComma hF Y ⥤ G) (P A : WeakComma hF Y) :
    (groupoidConstantIso h hF T Y H P).hom.app A =
      H.map (weakCommaPairLeft h hF Y A P) ≫
        inv (H.map (weakCommaPairRight h hF Y A P)) := rfl

omit [HasBinaryCoproducts C] in
include h T in
/-- The path-homotopy result needs no independently supplied coproducts:
the Waldhausen pushout axiom constructs them. -/
theorem parallel_paths_homotopic_of_factorization {A B : WeakComma hF Y} (f g : A ⟶ B) :
    (classifyingSpacePath f).Homotopic (classifyingSpacePath g) := by
  let := Additivity.hasBinaryCoproducts W
  exact parallel_paths_homotopic h hF T Y f g

omit [HasBinaryCoproducts C] in
/-- The loop made from the two original parallel edges has an actual
nullhomotopy fixing its original vertex throughout. -/
def parallelLoopNullhomotopy {A B : WeakComma hF Y} (f g : A ⟶ B) :
    Path.Homotopy
      ((classifyingSpacePath f).trans (classifyingSpacePath g).symm)
      (Path.refl (classifyingSpacePoint A)) :=
  ((parallel_paths_homotopic_of_factorization h hF T Y f g).hcomp
    (Path.Homotopic.refl (classifyingSpacePath g).symm) |>.trans
      (Path.Homotopic.trans_symm (classifyingSpacePath g))).some

omit [HasBinaryCoproducts C] in
/-- Every time slice retains the original source vertex, including the actual
App2 object obtained from the specified source zero when that object is used. -/
theorem parallelLoopNullhomotopy_source {A B : WeakComma hF Y} (f g : A ⟶ B)
    (t : unitInterval) :
    parallelLoopNullhomotopy h hF T Y f g (t, 0) = classifyingSpacePoint A :=
  Path.Homotopy.source _ _

omit [HasBinaryCoproducts C] in
/-- The nullhomotopy is based at the same original source vertex at both ends. -/
theorem parallelLoopNullhomotopy_target {A B : WeakComma hF Y} (f g : A ⟶ B)
    (t : unitInterval) :
    parallelLoopNullhomotopy h hF T Y f g (t, 1) = classifyingSpacePoint A :=
  Path.Homotopy.target _ _

end HasApproximationProperty
end Quillen.Waldhausen
