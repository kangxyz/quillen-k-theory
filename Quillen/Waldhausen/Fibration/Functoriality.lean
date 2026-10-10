/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.CanonicalFiberMap

/-!
# Actual functors on the original coarse-acyclic categories

A functor exact for the original fine and coarse structures gives a genuine
exact acyclic functor. Identity, composition, natural isomorphisms and both
original inclusion/change-of-weak K-map squares are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

include hFc in
lemma map_acyclic {X : C} (hX : Acyclic N.coarse X) : Acyclic M.coarse (F.obj X) := by
  let e := M.coarse.isZero.iso (hFc.zero N.coarse.isZero)
  have h := M.coarse.weq.comp_mem e.hom (F.map (N.coarse.isZero.to_ X))
    (M.coarse.weq_iso _ inferInstance) (hFc.weak _ hX)
  change M.coarse.weq (M.coarse.isZero.to_ (F.obj X))
  rw [← M.coarse.isZero.eq_of_src (e.hom ≫ F.map (N.coarse.isZero.to_ X))
    (M.coarse.isZero.to_ (F.obj X))]
  exact h

def acyclicFunctor : AcyclicCategory N ⥤ AcyclicCategory M :=
  (acyclicObjects M).lift (acyclicInclusion N ⋙ F) (fun X => map_acyclic N M hFc X.property)

include hF in
lemma acyclicFunctor_exact : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
    (acyclicStructure M).cof (acyclicStructure M).weq (acyclicFunctor N M hFc) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (acyclicObjects M).ι _
    (hF.zero ((acyclicInclusion_exact N).zero hz))
  cofibration f hf := hF.cofibration f.hom hf
  weak f hf := hF.weak f.hom hf
  pushout hi hp := IsPushout.of_map_of_faithful (acyclicObjects M).ι
    (hF.pushout hi (acyclicInclusion_map_pushout N hi hp))

lemma acyclicFunctor_id : acyclicFunctor N N (IsExact.id N.coarse.cof N.coarse.weq) =
    𝟭 (AcyclicCategory N) := rfl

lemma acyclicFunctor_comp {E : Type u} [Category.{v} E] {T : Structure E}
    (L : NestedWeakEquivalences T) {G : D ⥤ E}
    (hGc : IsExact M.coarse.cof M.coarse.weq L.coarse.cof L.coarse.weq G) :
    acyclicFunctor N L (hFc.comp hGc) =
      acyclicFunctor N M hFc ⋙ acyclicFunctor M L hGc := rfl

lemma acyclicFunctor_inclusion : acyclicFunctor N M hFc ⋙ acyclicInclusion M =
    acyclicInclusion N ⋙ F := rfl

lemma changeWeakMap_natural :
    (deloopingMap hFc).hom.comp (changeWeakMap N) =
      (changeWeakMap M).comp (deloopingMap hF).hom := by
  rw [changeWeakMap, changeWeakMap]
  rw [← TopCat.hom_comp, ← TopCat.hom_comp,
    deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]

lemma acyclicInclusionMap_natural :
    (deloopingMap hF).hom.comp (acyclicInclusionMap N) =
      (acyclicInclusionMap M).comp (deloopingMap (acyclicFunctor_exact N M hF hFc)).hom := by
  rw [acyclicInclusionMap, acyclicInclusionMap]
  rw [← TopCat.hom_comp, ← TopCat.hom_comp,
    deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]

lemma changeWeakKMap_natural (n : ℕ) :
    (KMap hFc n).comp (KMap (changeWeak_exact N) n) =
      (KMap (changeWeak_exact M) n).comp (KMap hF n) := by
  rw [KMap_comp_KMap, KMap_comp_KMap]

lemma acyclicInclusionKMap_natural (n : ℕ) :
    (KMap hF n).comp (KMap (acyclicInclusion_exact N) n) =
      (KMap (acyclicInclusion_exact M) n).comp (KMap (acyclicFunctor_exact N M hF hFc) n) := by
  rw [KMap_comp_KMap, KMap_comp_KMap]

lemma acyclicFunctor_zero (h0 : F.obj V.zero = W.zero) :
    (acyclicFunctor N M hFc).obj (acyclicStructure N).zero = (acyclicStructure M).zero := by
  apply ObjectProperty.FullSubcategory.ext
  exact h0


lemma coarse_zero_eq (h0 : F.obj V.zero = W.zero) : F.obj N.coarse.zero = M.coarse.zero := by
  rw [N.zero_eq, M.zero_eq, h0]

def acyclicFunctorIso {G : C ⥤ D}
    (hGc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq G) (e : F ≅ G) :
    acyclicFunctor N M hFc ≅ acyclicFunctor N M hGc :=
  NatIso.ofComponents (fun X => (acyclicObjects M).isoMk (e.app X.obj)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact e.hom.naturality f.hom)

end Quillen.Waldhausen.Fibration
