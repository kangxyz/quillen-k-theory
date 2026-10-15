/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportComparison
public import Quillen.AlgebraicGeometry.Scheme.OpenPairs

/-!
# Actual bounded-flat pullback on arbitrary open-pair squares

The original geometric pullback/restriction comparison preserves supported
objects and relative weak maps using actual bounded-flat acyclicity. Genuine
flat-quotient exactness gives Waldhausen-exact supported and relative functors.
Their original K-maps satisfy identity/composition; support-forgetting and
change-weak maps commute. No qc, flatness or cartesian-square premise is used.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
variable {A B C : AlgebraicGeometry.Scheme.OpenPairs.{u}}

/-- The actual pullback/restriction square for any morphism of open pairs. -/
def pullbackComplexOpenPairIso (f : A ⟶ B) :
    AlgebraicGeometry.Scheme.Modules.Complex.pullback f.hom.right ⋙ restrict A.obj.hom ≅
      restrict B.obj.hom ⋙ AlgebraicGeometry.Scheme.Modules.Complex.pullback f.hom.left :=
  Functor.isoWhiskerLeft _ (restrictIsoPullbackComplex A.obj.hom) ≪≫
    (pullbackComplexCompIso A.obj.hom f.hom.right).symm ≪≫
    eqToIso (congrArg AlgebraicGeometry.Scheme.Modules.Complex.pullback (Arrow.w f.hom).symm) ≪≫
    pullbackComplexCompIso f.hom.left B.obj.hom ≪≫
    Functor.isoWhiskerRight (restrictIsoPullbackComplex B.obj.hom).symm _

theorem boundedFlatPerfectSupported_pairPullback (f : A ⟶ B)
    {K : Complex B.obj.right} (hK : boundedFlatPerfectSupported B.obj.hom K) :
    boundedFlatPerfectSupported A.obj.hom ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
      f.hom.right).obj K) := by
  refine ⟨boundedFlatPerfect_pullback f.hom.right hK.1, ?_⟩
  obtain ⟨b, hb⟩ := boundedAbove_restrict B.obj.hom hK.1.2.1
  have ha := acyclic_pullback_of_boundedAbove_stalkwiseFlat f.hom.left
    ((restrict B.obj.hom).obj K) (fun n => stalkwiseFlat_restrict B.obj.hom (hK.1.2.2 n))
    hK.2 b (fun n hn => ((restrict B.obj.hom).obj K).isZero_of_isStrictlyLE b n hn)
  intro n
  exact (ha n).of_iso ((pullbackComplexOpenPairIso f).app K).symm

/-- The contravariant functor from bounded-flat complexes supported on the complement of `B`'s open
to those supported on the complement of `A`'s open, induced by the commutative open-pair square
`f : A ⟶ B`. -/
def boundedFlatPerfectSupportedPullback (f : A ⟶ B) :
    (boundedFlatPerfectSupported B.obj.hom).FullSubcategory ⥤
      (boundedFlatPerfectSupported A.obj.hom).FullSubcategory :=
  (boundedFlatPerfectSupported A.obj.hom).lift
    ((boundedFlatPerfectSupported B.obj.hom).ι ⋙ AlgebraicGeometry.Scheme.Modules.Complex.pullback
      f.hom.right)
    (fun K => boundedFlatPerfectSupported_pairPullback f K.property)

instance boundedFlatPerfectSupportedPullback_additive (f : A ⟶ B) :
    (boundedFlatPerfectSupportedPullback f).Additive := by
  unfold boundedFlatPerfectSupportedPullback
  infer_instance

/-- Pullback along the open-pair square `f : A ⟶ B` as an exact functor on supported bounded-flat
complexes with their inherited exact structures. -/
def boundedFlatPerfectSupportedExactPullback (f : A ⟶ B) :
    CategoryTheory.ExactCategory.ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (Complex B.obj.right))
        (boundedFlatPerfectSupported B.obj.hom))
      (ExactSubcategory.exactStructure (abelianExactStructure (Complex A.obj.right))
        (boundedFlatPerfectSupported A.obj.hom)) where
  toFunctor := boundedFlatPerfectSupportedPullback f
  map_conflation S hS := by
    apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
    intro n
    exact shortExact_pullback_of_stalkwiseFlat_quotient f.hom.right
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hS n)
      (S.X₃.property.1.2.2 n)

theorem boundedFlatPerfectSupportedPullback_exact (f : A ⟶ B) :
    Waldhausen.IsExact (boundedFlatPerfectSupportedWaldhausen B.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen B.obj.hom).weq
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).weq
      (boundedFlatPerfectSupportedPullback f) where
  zero h := (boundedFlatPerfectSupportedPullback f).map_isZero h
  cofibration p hp := (boundedFlatPerfectSupportedExactPullback f).map_inflation p hp
  weak {K L} p hp := by
    let : QuasiIso p.hom := hp
    obtain ⟨b, hb⟩ := K.property.1.2.1
    obtain ⟨c, hc⟩ := L.property.1.2.1
    exact quasiIso_pullback_of_boundedAbove_stalkwiseFlat f.hom.right
      K.property.1.2.2 L.property.1.2.2 b c
      (fun n hn => K.obj.isZero_of_isStrictlyLE b n hn)
      (fun n hn => L.obj.isZero_of_isStrictlyLE c n hn) p.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (boundedFlatPerfectSupported A.obj.hom).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure (Complex B.obj.right))
      (boundedFlatPerfectSupported B.obj.hom) hi h).map
        (AlgebraicGeometry.Scheme.Modules.Complex.pullback f.hom.right)

theorem boundedFlatPerfect_pairPullback_quasiIso (f : A ⟶ B)
    {K L : Complex B.obj.right} (hK : boundedFlatPerfect B.obj.right K)
    (hL : boundedFlatPerfect B.obj.right L) (p : K ⟶ L)
    [QuasiIso ((restrict B.obj.hom).map p)] :
    QuasiIso ((restrict A.obj.hom).map ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
      f.hom.right).map p)) := by
  obtain ⟨b, hb⟩ := boundedAbove_restrict B.obj.hom hK.2.1
  obtain ⟨c, hc⟩ := boundedAbove_restrict B.obj.hom hL.2.1
  have hKr (n : ℤ) : stalkwiseFlat B.obj.left (((restrict B.obj.hom).obj K).X n) :=
    stalkwiseFlat_restrict B.obj.hom (hK.2.2 n)
  have hLr (n : ℤ) : stalkwiseFlat B.obj.left (((restrict B.obj.hom).obj L).X n) :=
    stalkwiseFlat_restrict B.obj.hom (hL.2.2 n)
  have : QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f.hom.left).map ((restrict
    B.obj.hom).map p)) :=
    quasiIso_pullback_of_boundedAbove_stalkwiseFlat f.hom.left
      (K := (restrict B.obj.hom).obj K) (L := (restrict B.obj.hom).obj L)
      hKr hLr b c
      (fun n hn => ((restrict B.obj.hom).obj K).isZero_of_isStrictlyLE b n hn)
      (fun n hn => ((restrict B.obj.hom).obj L).isZero_of_isStrictlyLE c n hn)
      ((restrict B.obj.hom).map p)
  let e := pullbackComplexOpenPairIso f
  rw [← quasiIso_iff_comp_right _ (e.hom.app L)]
  change QuasiIso (((AlgebraicGeometry.Scheme.Modules.Complex.pullback f.hom.right ⋙ restrict
    A.obj.hom).map p) ≫ e.hom.app L)
  rw [e.hom.naturality p]
  change QuasiIso (e.hom.app K ≫ (AlgebraicGeometry.Scheme.Modules.Complex.pullback f.hom.left).map
    ((restrict B.obj.hom).map p))
  have : QuasiIso (e.hom.app K) := quasiIso_of_isIso _
  infer_instance

/-- Relative weak maps remain weak under every actual commutative open square. -/
theorem boundedFlatPerfectOpenPullback_exact (f : A ⟶ B) :
    Waldhausen.IsExact (boundedFlatPerfectOpenWaldhausen B.obj.hom).cof
      (boundedFlatPerfectOpenWaldhausen B.obj.hom).weq
      (boundedFlatPerfectOpenWaldhausen A.obj.hom).cof
      (boundedFlatPerfectOpenWaldhausen A.obj.hom).weq
      (boundedFlatPerfectPullback f.hom.right) where
  zero := (boundedFlatPerfectPullback_exact f.hom.right).zero
  cofibration := (boundedFlatPerfectPullback_exact f.hom.right).cofibration
  pushout := (boundedFlatPerfectPullback_exact f.hom.right).pushout
  weak {K L} p hp := by
    let : QuasiIso ((restrict B.obj.hom).map p.hom) := hp
    exact boundedFlatPerfect_pairPullback_quasiIso f K.property L.property p.hom

/-- The degree-`n` K-map from the supported bounded-flat model of `B` to that of `A`, induced by
the open-pair morphism `f : A ⟶ B`. -/
def boundedFlatPerfectSupportedKPullback (f : A ⟶ B) (n : ℕ) :
    BoundedFlatPerfectSupportedK B.obj.hom n →* BoundedFlatPerfectSupportedK A.obj.hom n :=
  Waldhausen.KMap (boundedFlatPerfectSupportedPullback_exact f) n

/-- The degree-`n` K-map from the relative-open bounded-flat model of `B` to that of `A`, induced
by the open-pair morphism `f : A ⟶ B`. -/
def boundedFlatPerfectOpenKPullback (f : A ⟶ B) (n : ℕ) :
    BoundedFlatPerfectOpenK B.obj.hom n →* BoundedFlatPerfectOpenK A.obj.hom n :=
  Waldhausen.KMap (boundedFlatPerfectOpenPullback_exact f) n

/-- The natural isomorphism identifying supported bounded-flat pullback along the identity
open-pair morphism with the identity functor. -/
def boundedFlatPerfectSupportedPullbackIdIso (A : AlgebraicGeometry.Scheme.OpenPairs.{u}) :
    boundedFlatPerfectSupportedPullback (𝟙 A) ≅ 𝟭 (boundedFlatPerfectSupported
      A.obj.hom).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfectSupported A.obj.hom).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported A.obj.hom).ι
      (pullbackComplexIdIso A.obj.right))

/-- The natural isomorphism identifying supported bounded-flat pullback along `f ≫ g` with pullback
first along `g` and then along `f`. -/
def boundedFlatPerfectSupportedPullbackCompIso (f : A ⟶ B) (g : B ⟶ C) :
    boundedFlatPerfectSupportedPullback (f ≫ g) ≅
      boundedFlatPerfectSupportedPullback g ⋙ boundedFlatPerfectSupportedPullback f :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfectSupported A.obj.hom).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported C.obj.hom).ι
      (pullbackComplexCompIso f.hom.right g.hom.right))

@[simp] theorem boundedFlatPerfectSupportedKPullback_id (A : AlgebraicGeometry.Scheme.OpenPairs.{u})
  (n : ℕ) :
    boundedFlatPerfectSupportedKPullback (𝟙 A) n = MonoidHom.id _ :=
  (Waldhausen.KMap_eq_of_iso (boundedFlatPerfectSupportedPullback_exact (𝟙 A))
    (Waldhausen.IsExact.id (boundedFlatPerfectSupportedWaldhausen A.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).weq)
    (boundedFlatPerfectSupportedPullbackIdIso A) n).trans (Waldhausen.KMap_id _ n)

@[simp] theorem boundedFlatPerfectSupportedKPullback_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    boundedFlatPerfectSupportedKPullback (f ≫ g) n =
      (boundedFlatPerfectSupportedKPullback f n).comp (boundedFlatPerfectSupportedKPullback g n) :=
  (Waldhausen.KMap_eq_of_iso (boundedFlatPerfectSupportedPullback_exact (f ≫ g))
    ((boundedFlatPerfectSupportedPullback_exact g).comp (boundedFlatPerfectSupportedPullback_exact
      f))
    (boundedFlatPerfectSupportedPullbackCompIso f g) n).trans
      ((Waldhausen.KMap_comp_KMap _ _ n).symm)

@[simp] theorem boundedFlatPerfectOpenKPullback_id (A : AlgebraicGeometry.Scheme.OpenPairs.{u}) (n :
  ℕ) :
    boundedFlatPerfectOpenKPullback (𝟙 A) n = MonoidHom.id _ :=
  (Waldhausen.KMap_eq_of_iso (boundedFlatPerfectOpenPullback_exact (𝟙 A))
    (Waldhausen.IsExact.id (boundedFlatPerfectOpenWaldhausen A.obj.hom).cof
      (boundedFlatPerfectOpenWaldhausen A.obj.hom).weq)
    (boundedFlatPerfectPullbackIdIso A.obj.right) n).trans (Waldhausen.KMap_id _ n)

@[simp] theorem boundedFlatPerfectOpenKPullback_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    boundedFlatPerfectOpenKPullback (f ≫ g) n =
      (boundedFlatPerfectOpenKPullback f n).comp (boundedFlatPerfectOpenKPullback g n) :=
  (Waldhausen.KMap_eq_of_iso (boundedFlatPerfectOpenPullback_exact (f ≫ g))
    ((boundedFlatPerfectOpenPullback_exact g).comp (boundedFlatPerfectOpenPullback_exact f))
    (boundedFlatPerfectPullbackCompIso f.hom.right g.hom.right) n).trans
      ((Waldhausen.KMap_comp_KMap _ _ n).symm)

theorem boundedFlatPerfectSupportedKMap_pullback (f : A ⟶ B) (n : ℕ) :
    (boundedFlatPerfectKPullback f.hom.right n).comp (boundedFlatPerfectSupportedKMap B.obj.hom n) =
      (boundedFlatPerfectSupportedKMap A.obj.hom n).comp (boundedFlatPerfectSupportedKPullback f n)
        := by
  unfold boundedFlatPerfectKPullback boundedFlatPerfectSupportedKMap
    boundedFlatPerfectSupportedKPullback Waldhausen.subcategoryKMap
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]

theorem boundedFlatPerfectOpenKMap_pullback (f : A ⟶ B) (n : ℕ) :
    (boundedFlatPerfectOpenKPullback f n).comp (boundedFlatPerfectOpenKMap B.obj.hom n) =
      (boundedFlatPerfectOpenKMap A.obj.hom n).comp (boundedFlatPerfectKPullback f.hom.right n) :=
        by
  unfold boundedFlatPerfectOpenKPullback boundedFlatPerfectOpenKMap boundedFlatPerfectKPullback
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]

/-- The contravariant degree-`n` K-functor on open pairs, using bounded-flat complexes acyclic on
the specified open and geometric pair pullback. -/
def BoundedFlatPerfectSupportedKFunctor (n : ℕ) : AlgebraicGeometry.Scheme.OpenPairs.{u}ᵒᵖ ⥤
  GrpCat.{u + 1}
  where
  obj X := GrpCat.of (BoundedFlatPerfectSupportedK X.unop.obj.hom n)
  map f := GrpCat.ofHom (boundedFlatPerfectSupportedKPullback f.unop n)
  map_id X := by apply GrpCat.hom_ext; exact boundedFlatPerfectSupportedKPullback_id X.unop n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact boundedFlatPerfectSupportedKPullback_comp g.unop f.unop n

/-- The contravariant degree-`n` K-functor on open pairs for the bounded-flat model whose weak
equivalences are detected on the specified open. -/
def BoundedFlatPerfectOpenKFunctor (n : ℕ) : AlgebraicGeometry.Scheme.OpenPairs.{u}ᵒᵖ ⥤ GrpCat.{u +
  1} where
  obj X := GrpCat.of (BoundedFlatPerfectOpenK X.unop.obj.hom n)
  map f := GrpCat.ofHom (boundedFlatPerfectOpenKPullback f.unop n)
  map_id X := by apply GrpCat.hom_ext; exact boundedFlatPerfectOpenKPullback_id X.unop n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact boundedFlatPerfectOpenKPullback_comp g.unop f.unop n

end Quillen.PerfectComplexes
