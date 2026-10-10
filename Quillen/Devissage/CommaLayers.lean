/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Devissage.SpanLayers
public import Quillen.Devissage.FullyFaithful
public import Quillen.CategoryTheory.QConstruction.Abelian.Cancellation
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Q-comma categories and the poset of layers

The comparison sends a layer to its quotient-to-ambient admissible span.
All arrows in the target comma category are unique, by monicity of abelian
Q-arrows and faithfulness of the inclusion. The pullback composition law matches
exactly reverse inclusion of the lower endpoint and forward inclusion of the
upper endpoint. Every comma object is represented by its span image and kernel,
yielding the explicit categorical equivalence `layerCommaEquivalence`.
-/
@[expose] public section


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace Quillen.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Passing to quotients by the same subobject gives a monomorphism. -/
lemma quotientMap_mono {A U V : C} (i : A ⟶ U) (g : U ⟶ V) (k : A ⟶ V)
    [Mono g] (w : i ≫ g = k) :
    Mono (cokernel.map i k (𝟙 A) g (by simpa using w)) := by
  apply Abelian.mono_cokernel_map_of_isPullback
  exact IsPullback.of_vert_isIso_mono ⟨by simpa using w⟩

/-- The quotient square of an inclusion of subobjects is a pullback. -/
lemma quotientMap_isPullback {A U V : C} (i : A ⟶ U) (g : U ⟶ V) (k : A ⟶ V)
    [Mono g] (w : i ≫ g = k) :
    IsPullback (cokernel.π i) g
      (cokernel.map i k (𝟙 A) g (by simpa using w)) (cokernel.π k) := by
  let m := cokernel.map i k (𝟙 A) g (by simpa using w)
  let : Mono m := quotientMap_mono i g k w
  have wk : k ≫ cokernel.π g = 0 := by rw [← w, assoc, cokernel.condition, comp_zero]
  let d := cokernel.desc k (cokernel.π g) wk
  have md : m ≫ d = 0 := by
    apply (cancel_epi (cokernel.π i)).mp
    simp [m, d]
  have hz (s : PullbackCone m (cokernel.π k)) : s.snd ≫ cokernel.π g = 0 := by
    rw [← cokernel.π_desc k (cokernel.π g) wk, ← assoc, ← s.condition, assoc, md, comp_zero]
  apply IsPullback.of_isLimit (c := PullbackCone.mk (cokernel.π i) g (by simp))
  apply PullbackCone.IsLimit.mk (by simp [m])
    (fun s => Abelian.monoLift g s.snd (hz s))
  · intro s
    apply (cancel_mono m).mp
    simpa [m] using s.condition.symm
  · intro s
    exact Abelian.monoLift_comp _ _ _
  · intro s a _ ha
    apply (cancel_mono g).mp
    simpa using ha

variable (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts] (M : C)

/-- The inclusion comma category whose objects are Q-arrows from `P` to `M`. -/
abbrev QComma := CostructuredArrow (mapQ P)
  (Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)

instance qComma_thin : Quiver.IsThin (QComma P M) := by
  intro X Y
  constructor
  intro f g
  apply CostructuredArrow.hom_ext
  apply (mapQ P).map_injective
  apply (cancel_mono Y.hom).mp
  exact (CostructuredArrow.w f).trans (CostructuredArrow.w g).symm

/-- Regard an ambient span with source in the smaller category as a comma object. -/
def spanComma {X : Subcategory P} (s : Q.AbelianSpan X.obj M) : QComma P M :=
  CostructuredArrow.mk (Y := Q.of (subcategoryExactStructure P).deflation
    (subcategoryExactStructure P).inflation X) (Q.mkHom _ _ s)

/-- Compatible isomorphisms of the source and apex give an actual comma morphism. -/
def spanCommaHomOfIso {X Y : Subcategory P}
    (s : Q.AbelianSpan X.obj M) (t : Q.AbelianSpan Y.obj M)
    (j : X.obj ≅ Y.obj) (e : s.apex ≅ t.apex)
    (hl : e.hom ≫ t.l = s.l ≫ j.hom) (hr : e.hom ≫ t.r = s.r) :
    spanComma P M s ⟶ spanComma P M t := by
  let c : Q.AbelianSpan X.obj Y.obj :=
    { apex := X.obj
      l := 𝟙 _
      r := j.hom
      wl := (abelianExactStructure_deflation_iff C _).2 inferInstance
      wr := (abelianExactStructure_inflation_iff C _).2 inferInstance }
  refine CostructuredArrow.homMk (Q.mkHom _ _ (liftSpan P c)) ?_
  change Q.mkHom _ _ c ≫ Q.mkHom _ _ t = Q.mkHom _ _ s
  let sq : IsPullback s.l e.hom c.r t.l := IsPullback.of_vert_isIso ⟨hl.symm⟩
  symm
  apply Q.mkHom_eq_of_apexIso _ _ s (Span.comp c t) sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = s.l
    simp
  · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ t.r = s.r
    simpa using hr

/-- Isomorphic presentations of the same subquotient give isomorphic comma objects. -/
def spanCommaIsoOfIso {X Y : Subcategory P}
    (s : Q.AbelianSpan X.obj M) (t : Q.AbelianSpan Y.obj M)
    (j : X.obj ≅ Y.obj) (e : s.apex ≅ t.apex)
    (hl : e.hom ≫ t.l = s.l ≫ j.hom) (hr : e.hom ≫ t.r = s.r) :
    spanComma P M s ≅ spanComma P M t where
  hom := spanCommaHomOfIso P M s t j e hl hr
  inv := spanCommaHomOfIso P M t s j.symm e.symm
    (by rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← assoc, hl]; simp)
    (by simpa only [Iso.symm_hom] using (e.inv_comp_eq.mpr hr.symm))
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

namespace Layer
variable {P M}

/-- The representative Q-span of a layer. -/
def span (L : Layer P M) : Q.AbelianSpan L.quotient M where
  apex := L.upper
  l := cokernel.π (Subobject.ofLE L.lower L.upper L.le)
  r := L.upper.arrow
  wl := (abelianExactStructure_deflation_iff C _).2 inferInstance
  wr := (abelianExactStructure_inflation_iff C _).2 inferInstance

/-- A layer presents its quotient as an object of the Q-comma category. -/
def comma (L : Layer P M) : QComma P M :=
  CostructuredArrow.mk (Y := Q.of (subcategoryExactStructure P).deflation
    (subcategoryExactStructure P).inflation ⟨L.quotient, L.property⟩)
    (Q.mkHom _ _ L.span)

/-- The intermediate quotient for an inclusion of layers. -/
abbrev middle {L K : Layer P M} (h : L ≤ K) : C :=
  cokernel (Subobject.ofLE K.lower L.upper (h.1.trans L.le))

/-- The intermediate quotient embeds in the target quotient. -/
def rightMap {L K : Layer P M} (h : L ≤ K) : middle h ⟶ K.quotient :=
  cokernel.map (Subobject.ofLE K.lower L.upper (h.1.trans L.le))
    (Subobject.ofLE K.lower K.upper K.le) (𝟙 _)
    (Subobject.ofLE L.upper K.upper h.2) (by simp)

instance rightMap_mono {L K : Layer P M} (h : L ≤ K) : Mono (rightMap h) :=
  quotientMap_mono _ _ _ (by simp)

/-- The intermediate quotient surjects onto the source quotient. -/
def leftMap {L K : Layer P M} (h : L ≤ K) : middle h ⟶ L.quotient :=
  cokernel.desc _ (cokernel.π (Subobject.ofLE L.lower L.upper L.le)) (by
    rw [← Subobject.ofLE_comp_ofLE K.lower L.lower L.upper h.1 L.le, assoc]
    simp)

instance leftMap_epi {L K : Layer P M} (h : L ≤ K) : Epi (leftMap h) :=
  epi_of_epi_fac (cokernel.π_desc _ _ _)

/-- The actual Q-span between the two quotient objects. -/
def mapSpan {L K : Layer P M} (h : L ≤ K) : Q.AbelianSpan L.quotient K.quotient where
  apex := middle h
  l := leftMap h
  r := rightMap h
  wl := (abelianExactStructure_deflation_iff C _).2 inferInstance
  wr := (abelianExactStructure_inflation_iff C _).2 inferInstance

omit [P.ContainsZero] [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]
  [P.IsClosedUnderFiniteProducts] in
/-- Its pullback composite is exactly the source layer's Q-span. -/
lemma mapSpan_comp {L K : Layer P M} (h : L ≤ K) :
    Q.mkHom _ _ (mapSpan h) ≫ Q.mkHom _ _ K.span = Q.mkHom _ _ L.span := by
  let sq := quotientMap_isPullback
    (Subobject.ofLE K.lower L.upper (h.1.trans L.le))
    (Subobject.ofLE L.upper K.upper h.2)
    (Subobject.ofLE K.lower K.upper K.le) (by simp)
  symm
  apply Q.mkHom_eq_of_apexIso _ _ L.span (Span.comp (mapSpan h) K.span) sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ leftMap h = _
    simp [leftMap, span]
  · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ K.upper.arrow = _
    simp [span]

/-- The morphism of comma objects associated to an inclusion of layers. -/
def commaMap {L K : Layer P M} (h : L ≤ K) : L.comma ⟶ K.comma :=
  CostructuredArrow.homMk
    (Q.mkHom _ _ (liftSpan P (X := ⟨L.quotient, L.property⟩)
      (Y := ⟨K.quotient, K.property⟩) (mapSpan h))) (mapSpan_comp h)

/-- A morphism between the canonical comma objects forces both endpoint
inequalities in the layer order. -/
lemma le_of_comma_hom {L K : Layer P M} (f : L.comma ⟶ K.comma) : L ≤ K := by
  have w := CostructuredArrow.w f
  obtain ⟨s, hs⟩ := Quotient.exists_rep f.left
  rw [← hs] at w
  change Q.mkHom _ _ ((exactInclusion P).toQCompatibleFunctor.mapSpan s) ≫
    Q.mkHom _ _ K.span = Q.mkHom _ _ L.span at w
  let t : Q.AbelianSpan L.quotient K.quotient :=
    (exactInclusion P).toQCompatibleFunctor.mapSpan s
  obtain ⟨e, el, er⟩ :=
    (Q.mkHom_eq_iff_apexIso _ _ (Span.comp t K.span) L.span).1 w
  have ei : e.inv ≫ pullback.snd t.r K.span.l ≫ K.upper.arrow = L.upper.arrow := by
    exact (e.inv_comp_eq.mpr er.symm)
  refine ⟨?_, Subobject.le_of_comm (e.inv ≫ pullback.snd t.r K.span.l) ((Category.assoc _ _ _).trans
    ei)⟩
  let a : (K.lower : C) ⟶ pullback t.r K.span.l :=
    pullback.lift 0 (Subobject.ofLE K.lower K.upper K.le) (by simpa only [span, zero_comp] using
      (cokernel.condition (Subobject.ofLE K.lower K.upper K.le)).symm)
  let b : (K.lower : C) ⟶ (L.upper : C) := a ≫ e.hom
  have bz : b ≫ cokernel.π (Subobject.ofLE L.lower L.upper L.le) = 0 := by
    change (a ≫ e.hom) ≫ L.span.l = 0
    rw [assoc, el]
    dsimp only [a, Span.comp, span]
    erw [pullback.lift_fst_assoc, zero_comp]
  apply Subobject.le_of_comm
    (Abelian.monoLift (Subobject.ofLE L.lower L.upper L.le) b bz)
  rw [← Subobject.ofLE_arrow L.le, ← assoc, Abelian.monoLift_comp]
  change (a ≫ e.hom) ≫ L.span.r = K.lower.arrow
  rw [assoc, er]
  dsimp only [a, Span.comp, span]
  erw [pullback.lift_snd_assoc]
  exact Subobject.ofLE_arrow K.le

end Layer

/-- The quotient-span comparison from the layer poset to the actual Q-comma category. -/
def layerToComma : Layer P M ⥤ QComma P M where
  obj := Layer.comma
  map h := Layer.commaMap (leOfHom h)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

instance layerToComma_faithful : (layerToComma P M).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance layerToComma_full : (layerToComma P M).Full where
  map_surjective f := ⟨homOfLE (Layer.le_of_comma_hom f), Subsingleton.elim _ _⟩

/-- Every comma object has an actual layer presentation. -/
instance layerToComma_essSurj : (layerToComma P M).EssSurj where
  mem_essImage := by
    rintro ⟨⟨⟨X⟩⟩, ⟨⟨⟩⟩, f⟩
    induction f using Quotient.inductionOn with | _ s =>
    refine ⟨spanLayer P s X.property, ⟨?_⟩⟩
    exact spanCommaIsoOfIso P M
      (X := ⟨(spanLayer P s X.property).quotient, (spanLayer P s X.property).property⟩)
      (Y := X) (spanLayer P s X.property).span s
      (spanLayerQuotientIso P s X.property) (Subobject.underlyingIso s.r)
      (cokernel_π_spanLayerQuotientIso_hom P s X.property).symm
      (Subobject.underlyingIso_hom_comp_eq_mk s.r)

instance layerToComma_isEquivalence : (layerToComma P M).IsEquivalence where

/-- The Q-inclusion comma category is genuinely equivalent to the layer poset.
The forward functor is the explicit quotient-span construction. -/
def layerCommaEquivalence : Layer P M ≌ QComma P M :=
  (layerToComma P M).asEquivalence

end Quillen.Devissage
