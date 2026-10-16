/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Relative
public import Quillen.AlgebraicGeometry.Scheme.OpenPairs

/-!
Actual polynomial/Laurent products of scheme/open-support pairs, preserving arbitrary commutative
pair squares. The vanishing open is a genuine inverse image, only the ambient scheme is required qc,
and shrinking the open gives the original identity-base pair map.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.Products



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Bass

/-- Base product preserves the original map by an actual pullback square. -/
lemma baseProductFunctor_map_isPullback {S : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    IsPullback ((baseProductFunctor p).map f) (pullback.fst (toIntegerBase X) p)
      (pullback.fst (toIntegerBase Y) p) f := by
  apply IsPullback.of_right (h₁₂ := pullback.snd (toIntegerBase Y) p) (h₂₂ := toIntegerBase Y)
  · simpa [baseProductFunctor] using (IsPullback.of_hasPullback (toIntegerBase X) p).flip
  · simp [baseProductFunctor]
  · exact (IsPullback.of_hasPullback (toIntegerBase Y) p).flip

instance instIsOpenImmersionBaseProductFunctorMap {S : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    IsOpenImmersion ((baseProductFunctor p).map f) :=
  MorphismProperty.of_isPullback (baseProductFunctor_map_isPullback p f).flip inferInstance

/-- Actual products of scheme/open-support pairs; only the ambient scheme is required qc. -/
def pairBaseProductFunctor {S : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) [QuasiCompact p] : QuasiCompactOpenPairs.{u} ⥤ QuasiCompactOpenPairs.{u}
      where
  obj A := ⟨⟨(baseProductFunctor p).mapArrow.obj A.obj.obj,by
    change IsOpenImmersion ((baseProductFunctor p).map A.obj.obj.hom); infer_instance⟩,by
      change CompactSpace (pullback (toIntegerBase A.obj.obj.right) p : AlgebraicGeometry.Scheme);
        infer_instance⟩
  map f := ⟨⟨(baseProductFunctor p).mapArrow.map f.hom.hom⟩⟩
  map_id A := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    exact (baseProductFunctor p).mapArrow.map_id A.obj.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    exact (baseProductFunctor p).mapArrow.map_comp f.hom.hom g.hom.hom

/-- The actual chart map is applied to both entries of the original open pair. -/
def pairBaseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ integerBase) (q : T ⟶ integerBase) [QuasiCompact p] [QuasiCompact q]
    (f : S ⟶ T) (hf : f ≫ q = p) : pairBaseProductFunctor p ⟶ pairBaseProductFunctor q where
  app A := ⟨⟨((Functor.mapArrowFunctor _ _).map (baseProductTransformation p q f hf)).app
    A.obj.obj⟩⟩
  naturality {A B} g := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    exact ((Functor.mapArrowFunctor _ _).map (baseProductTransformation p q f hf)).naturality
      g.hom.hom

/-- Base change of a quasi-compact open pair along the integer polynomial projection. -/
abbrev pairPolynomialFunctor : QuasiCompactOpenPairs.{u} ⥤ QuasiCompactOpenPairs.{u} :=
  pairBaseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)

/-- Base change of a quasi-compact open pair along the integer Laurent projection. -/
abbrev pairLaurentFunctor : QuasiCompactOpenPairs.{u} ⥤ QuasiCompactOpenPairs.{u} :=
  pairBaseProductFunctor (PolynomialLaurent.laurentProjection integerRing)

/-- The transformation of open pairs induced by the usual Laurent chart map. -/
def pairPlus : pairLaurentFunctor.{u} ⟶ pairPolynomialFunctor :=
  pairBaseProductTransformation _ _ (PolynomialLaurent.laurentPlus integerRing)
    (PolynomialLaurent.laurentPlus_projection integerRing)

/-- The transformation of open pairs induced by the inverted Laurent chart map. -/
def pairMinus : pairLaurentFunctor.{u} ⟶ pairPolynomialFunctor :=
  pairBaseProductTransformation _ _ (PolynomialLaurent.laurentMinus integerRing)
    (PolynomialLaurent.laurentMinus_projection integerRing)

@[simp] lemma pairPlus_base (A : QuasiCompactOpenPairs.{u}) :
    quasiCompactOpenPairsBase.map (pairPlus.app A) = plus.app (quasiCompactOpenPairsBase.obj A) :=
      rfl

@[simp] lemma pairMinus_base (A : QuasiCompactOpenPairs.{u}) :
    quasiCompactOpenPairsBase.map (pairMinus.app A) = minus.app (quasiCompactOpenPairsBase.obj A) :=
      rfl

/-- Forgetting the support open preserves the actual polynomial object and every map. -/
def pairPolynomialBaseIso : pairPolynomialFunctor.{u} ⋙ quasiCompactOpenPairsBase ≅
    quasiCompactOpenPairsBase ⋙ polynomialFunctor := Iso.refl _

/-- Forgetting the support open preserves the actual Laurent object and every map. -/
def pairLaurentBaseIso : pairLaurentFunctor.{u} ⋙ quasiCompactOpenPairsBase ≅
    quasiCompactOpenPairsBase ⋙ laurentFunctor := Iso.refl _

/-- The original support pair associated to any open of a qc scheme, with no qc-open premise. -/
def openSupportPair (X : QuasiCompactSchemes.{u}) (U : X.obj.Opens) : QuasiCompactOpenPairs.{u} :=
  ⟨⟨Arrow.mk U.ι,(show IsOpenImmersion U.ι from inferInstance)⟩,(show CompactSpace X.obj from
    inferInstance)⟩

/-- Shrinking the vanishing open is a genuine pair map over the identity ambient scheme. -/
def openSupportPairMap (X : QuasiCompactSchemes.{u}) {U V : X.obj.Opens} (h : U ≤ V) :
    openSupportPair X U ⟶ openSupportPair X V :=
  ⟨⟨Arrow.homMk (X.obj.homOfLE h) (𝟙 X.obj) (by
    change X.obj.homOfLE h ≫ V.ι = U.ι ≫ 𝟙 X.obj
    simp)⟩⟩

@[simp] lemma openSupportPairMap_id (X : QuasiCompactSchemes.{u}) (U : X.obj.Opens) :
    openSupportPairMap X (le_refl U) = 𝟙 _ := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply Arrow.hom_ext
  · exact AlgebraicGeometry.Scheme.homOfLE_rfl X.obj U
  · rfl

@[simp] lemma openSupportPairMap_comp (X : QuasiCompactSchemes.{u}) {U V W : X.obj.Opens}
    (h : U ≤ V) (k : V ≤ W) :
    openSupportPairMap X h ≫ openSupportPairMap X k = openSupportPairMap X (h.trans k) := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply Arrow.hom_ext
  · exact AlgebraicGeometry.Scheme.homOfLE_homOfLE X.obj h k
  · exact Category.id_comp _

@[simp] lemma openSupportPairMap_base (X : QuasiCompactSchemes.{u}) {U V : X.obj.Opens} (h : U ≤ V)
  :
    quasiCompactOpenPairsBase.map (openSupportPairMap X h) = 𝟙 X := rfl

end AlgebraicGeometry.Scheme.Bass

end
