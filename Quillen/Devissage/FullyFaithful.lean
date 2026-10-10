/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Devissage.Setup

/-!
# Full faithfulness of the Q-inclusion in dévissage

A Q-arrow between objects of the smaller category is represented by an
admissible span whose apex is a subobject of its target. Subobject closure
therefore puts the apex in the smaller category. The span lifts, and its
isomorphisms lift through the fully faithful ordinary inclusion.

Consequently the dévissage Q-functor is fully faithful. This statement does
not require the finite-filtration hypothesis and does not assert essential
surjectivity of the Q-functor or the homotopical dévissage theorem.
-/
@[expose] public section


noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Quillen.Devissage

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]
  [P.IsClosedUnderFiniteProducts]

omit [P.ContainsZero] [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts] in
/-- An ambient admissible span ending in an object satisfying `P` has its apex
in `P`, by the admissible monomorphism on the right. -/
lemma span_apex_mem {X Y : Subcategory P}
    (s : Span (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X.obj Y.obj) : P s.apex := by
  have : Mono s.r := (abelianExactStructure_inflation_iff C s.r).1 s.wr
  exact P.prop_of_mono s.r Y.property

/-- Lift an actual ambient Q-span between objects of the full subcategory.
The same maps are admissible in the subcategory because the faithful
inclusion reflects monomorphisms and epimorphisms. -/
def liftSpan {X Y : Subcategory P}
    (s : Span (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X.obj Y.obj) :
    Span (subcategoryExactStructure P).deflation
      (subcategoryExactStructure P).inflation X Y where
  apex := ⟨s.apex, span_apex_mem P s⟩
  l := P.homMk s.l
  r := P.homMk s.r
  wl := (abelianExactStructure_deflation_iff (Subcategory P) _).2
    (P.ι.epi_of_epi_map ((abelianExactStructure_deflation_iff C s.l).1 s.wl))
  wr := (abelianExactStructure_inflation_iff (Subcategory P) _).2
    (P.ι.mono_of_mono_map ((abelianExactStructure_inflation_iff C s.r).1 s.wr))

/-- Mapping the lifted span recovers its original ambient representative. -/
@[simp]
lemma mapSpan_liftSpan {X Y : Subcategory P}
    (s : Span (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X.obj Y.obj) :
    (exactInclusion P).toQCompatibleFunctor.mapSpan (liftSpan P s) = s := rfl

/-- Every ambient Q-morphism between objects in the smaller category lifts to
a Q-morphism there. -/
instance mapQ_full : (mapQ P).Full where
  map_surjective := by
    rintro X Y ⟨s⟩
    refine ⟨Q.mkHom _ _ (liftSpan P s), ?_⟩
    rfl

/-- Equality of ambient Q-morphisms is reflected: the commuting apex
isomorphism lifts to an isomorphism in the full subcategory. -/
instance mapQ_faithful : (mapQ P).Faithful where
  map_injective := by
    rintro X Y ⟨s⟩ ⟨t⟩ h
    change Q.mkHom _ _ ((exactInclusion P).toQCompatibleFunctor.mapSpan s) =
      Q.mkHom _ _ ((exactInclusion P).toQCompatibleFunctor.mapSpan t) at h
    obtain ⟨e, hl, hr⟩ := (Q.mkHom_eq_iff_apexIso _ _ _ _).1 h
    apply Q.mkHom_eq_of_apexIso _ _ s t (P.isoMk e)
    · exact P.hom_ext hl
    · exact P.hom_ext hr

/-- The genuine dévissage Q-inclusion is fully faithful, with inverse maps on
hom-sets supplied by lifting admissible spans. -/
def mapQFullyFaithful : (mapQ P).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (mapQ P)

/-- The resulting equivalence of Q-hom sets. -/
def mapQHomEquiv
    (X Y : Q (subcategoryExactStructure P).deflation (subcategoryExactStructure P).inflation) :
    (X ⟶ Y) ≃ ((mapQ P).obj X ⟶ (mapQ P).obj Y) :=
  (mapQFullyFaithful P).homEquiv

end Quillen.Devissage
