/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Complexes
public import Quillen.Waldhausen.ExactCategory
public import Quillen.Waldhausen.Functor
public import Quillen.CategoryTheory.ExactCategory.Abelian
public import Quillen.CategoryTheory.ExactCategory.Subcategory

/-!
# Extension-closed subcategories of complexes

An actual replete, extension-closed full subcategory of complexes containing
zero inherits a Waldhausen structure. Its cofibrations are ambient short
exact sequences whose quotient remains in the subcategory; its weak
equivalences are ambient quasi-isomorphisms. All Waldhausen axioms, including
gluing, are derived. Applications must prove the object-property closure
hypotheses, rather than supplying any K-theory comparison or localization.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Waldhausen

section GeneralSubcategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : Quillen.ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The full exact inclusion preserves pushouts along its admissible
monomorphisms. The pushout object stays inside by extension closure. -/
theorem fullSubcategory_map_pushout {A B D T : P.FullSubcategory}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ T} {j : D ⟶ T}
    (hi : (ExactSubcategory.exactStructure E P).inflation i)
    (h : IsPushout i f g j) : IsPushout i.hom f.hom g.hom j.hom := by
  obtain ⟨Z, hZ, p, hp, hS⟩ := (ExactSubcategory.inflation_iff E P i).1 hi
  let : HasPushout i.hom f.hom := E.inflation.hasPushout f.hom
    (E.inflation_of_conflation hS)
  let T₀ : P.FullSubcategory := ⟨pushout i.hom f.hom,
    E.prop_pushout P hS hZ D.property f.hom⟩
  let g₀ : B ⟶ T₀ := P.homMk (pushout.inl _ _)
  let j₀ : D ⟶ T₀ := P.homMk (pushout.inr _ _)
  have h₀ : IsPushout i f g₀ j₀ :=
    IsPushout.of_map_of_faithful P.ι (IsPushout.of_hasPushout i.hom f.hom)
  let e : T₀ ≅ T := h₀.isoIsPushout _ _ h
  apply (IsPushout.of_hasPushout i.hom f.hom).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (P.ι.mapIso e)
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.id_comp]
    change (g₀ ≫ e.hom).hom = g.hom
    exact congrArg (fun k ↦ k.hom) (h₀.inl_isoIsPushout_hom _ _ h)
  · simp only [Iso.refl_hom, Category.id_comp]
    change (j₀ ≫ e.hom).hom = j.hom
    exact congrArg (fun k ↦ k.hom) (h₀.inr_isoIsPushout_hom _ _ h)

end GeneralSubcategory

section Complexes

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The inherited exact structure is used only for its actual cofibrations. -/
abbrev subcategoryCofibrations : MorphismProperty P.FullSubcategory :=
  (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A ℤ)) P).inflation

/-- Weak equivalences in the full subcategory are genuine quasi-isomorphisms. -/
abbrev subcategoryWeakEquivalences : MorphismProperty P.FullSubcategory :=
  (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι

/-- The full Waldhausen structure is proved from the closure properties of
actual complexes. No K-theory theorem is an input. -/
def complexSubcategory : Structure P.FullSubcategory :=
  { ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P) with
    weq := subcategoryWeakEquivalences P
    weq_multiplicative := inferInstance
    weq_iso := by
      intro X Y f hf
      let : IsIso f := hf
      change QuasiIso f.hom
      infer_instance
    gluing := by
      intro B D E T B' D' E' T' i f g j i' f' g' j' a b d p hi hi' h h' ei ef eg ej ha hb hd
      have hiA := (ExactSubcategory.exactInclusion
        (abelianExactStructure (CochainComplex A ℤ)) P).map_inflation i hi
      have hiA' := (ExactSubcategory.exactInclusion
        (abelianExactStructure (CochainComplex A ℤ)) P).map_inflation i' hi'
      let : Mono i.hom := (abelianExactStructure_inflation_iff _ _).1 hiA
      let : Mono i'.hom := (abelianExactStructure_inflation_iff _ _).1 hiA'
      let : QuasiIso a.hom := ha
      let : QuasiIso b.hom := hb
      let : QuasiIso d.hom := hd
      exact quasiIso_gluing
        (fullSubcategory_map_pushout _ P hi h) (fullSubcategory_map_pushout _ P hi' h')
        a.hom b.hom d.hom p.hom
        (congrArg (fun k ↦ k.hom) ei) (congrArg (fun k ↦ k.hom) ef)
        (congrArg (fun k ↦ k.hom) eg) (congrArg (fun k ↦ k.hom) ej) }

/-- The actual inclusion of complexes is Waldhausen-exact. -/
theorem complexSubcategory_inclusion_exact :
    IsExact (complexSubcategory P).cof (complexSubcategory P).weq
      (complexes A).cof (complexes A).weq P.ι where
  zero h := P.ι.map_isZero h
  cofibration f hf := (abelianExactStructure_inflation_iff _ _).1
    ((ExactSubcategory.exactInclusion _ P).map_inflation f hf)
  weak _ hf := hf
  pushout hi h := fullSubcategory_map_pushout _ P hi h

end Complexes

end Quillen.Waldhausen
