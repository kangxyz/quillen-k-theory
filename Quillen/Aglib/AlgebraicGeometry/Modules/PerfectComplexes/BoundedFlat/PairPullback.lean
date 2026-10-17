/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Support
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Pullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PullbackIsomorphisms
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Pullback
public import Quillen.Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Basic
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.BoundedPullback
public import Aglib.AlgebraicGeometry.Modules.Complex.Pullback

/-!
# Supported bounded-flat pullback on open-pair squares

Every actual commuting open-pair square preserves the original support, inherited exact sequences,
and quasi-isomorphisms detected on the open. No flatness, cartesianness or compactness is added.-/
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
    (Complex.pullbackCompIso A.obj.hom f.hom.right).symm ≪≫
    eqToIso (congrArg AlgebraicGeometry.Scheme.Modules.Complex.pullback (Arrow.w f.hom).symm) ≪≫
    Complex.pullbackCompIso f.hom.left B.obj.hom ≪≫
    Functor.isoWhiskerRight (restrictIsoPullbackComplex B.obj.hom).symm _

theorem boundedFlatPerfectSupported_pairPullback (f : A ⟶ B)
    {K : CochainComplex B.obj.right.Modules ℤ} (hK : boundedFlatPerfectSupported B.obj.hom K) :
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
      (ExactSubcategory.exactStructure (abelianExactStructure
        (CochainComplex B.obj.right.Modules ℤ))
        (boundedFlatPerfectSupported B.obj.hom))
      (ExactSubcategory.exactStructure (abelianExactStructure
        (CochainComplex A.obj.right.Modules ℤ))
        (boundedFlatPerfectSupported A.obj.hom)) where
  toFunctor := boundedFlatPerfectSupportedPullback f
  map_conflation S hS := by
    apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
    intro n
    exact shortExact_pullback_of_stalkwiseFlat_quotient f.hom.right
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hS n)
      (S.X₃.property.1.2.2 n)

theorem boundedFlatPerfect_pairPullback_quasiIso (f : A ⟶ B)
    {K L : CochainComplex B.obj.right.Modules ℤ} (hK : boundedFlatPerfect B.obj.right K)
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

/-- The natural isomorphism identifying supported bounded-flat pullback along the identity
open-pair morphism with the identity functor. -/
def boundedFlatPerfectSupportedPullbackIdIso (A : AlgebraicGeometry.Scheme.OpenPairs.{u}) :
    boundedFlatPerfectSupportedPullback (𝟙 A) ≅ 𝟭 (boundedFlatPerfectSupported
      A.obj.hom).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfectSupported A.obj.hom).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported A.obj.hom).ι
      (Complex.pullbackIdIso A.obj.right))

/-- The natural isomorphism identifying supported bounded-flat pullback along `f ≫ g` with pullback
first along `g` and then along `f`. -/
def boundedFlatPerfectSupportedPullbackCompIso (f : A ⟶ B) (g : B ⟶ C) :
    boundedFlatPerfectSupportedPullback (f ≫ g) ≅
      boundedFlatPerfectSupportedPullback g ⋙ boundedFlatPerfectSupportedPullback f :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfectSupported A.obj.hom).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported C.obj.hom).ι
      (Complex.pullbackCompIso f.hom.right g.hom.right))

end Quillen.PerfectComplexes

end

end
