/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.GilletWaldhausen.BoundedTerms
public import Quillen.Waldhausen.ExactFunctor

/-! # The actual acyclic subcategory of bounded termwise-P complexes

The original bounded acyclic category includes exactly into the new ambient
bounded category, and its inherited cofibrations are precisely the ambient
inherited cofibrations between its objects. The genuine quasi-isomorphism
condition from an actual zero object is characterized by actual acyclicity.
No fibration theorem or K-equivalence is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A)

/-- Forgetting acyclicity leaves the original bounded termwise conditions. -/
theorem boundedAcyclic_le_boundedTerms : boundedAcyclic P ≤ boundedTerms P :=
  fun _ hK ↦ ⟨hK.1, hK.2.1⟩

/-- The actual full-subcategory inclusion, with unchanged complexes and chain maps. -/
def boundedAcyclicTermsInclusion :
    (boundedAcyclic P).FullSubcategory ⥤ (boundedTerms P).FullSubcategory :=
  ObjectProperty.ιOfLE (boundedAcyclic_le_boundedTerms P)

@[simp]
theorem boundedAcyclicTermsInclusion_comp_ι :
    boundedAcyclicTermsInclusion P ⋙ (boundedTerms P).ι = (boundedAcyclic P).ι := rfl

instance boundedAcyclicTermsInclusion_additive : (boundedAcyclicTermsInclusion P).Additive where
  map_add := by intros; rfl

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- Exactness of the original inclusion for the actual inherited conflations. -/
def boundedAcyclicTermsExactInclusion :
    ExactFunctor (boundedAcyclicExactStructure P) (boundedTermsExactStructure P) where
  toFunctor := boundedAcyclicTermsInclusion P
  map_conflation _ hS := hS

/-- Between acyclic objects, an inherited ambient quotient is automatically
acyclic, so the actual inclusion reflects inherited inflations. -/
theorem boundedAcyclicTermsInclusion_inflation_iff
    {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    (boundedTermsExactStructure P).inflation ((boundedAcyclicTermsInclusion P).map f) ↔
      (boundedAcyclicExactStructure P).inflation f := by
  constructor
  · intro hf
    obtain ⟨Q, p, w, hS⟩ := hf
    let S := (ShortComplex.mk ((boundedAcyclicTermsInclusion P).map f) p w).map (boundedTerms P).ι
    have hs : S.ShortExact := hS
    have hq : QuasiIso S.f := by
      rw [quasiIso_iff]
      intro n
      exact (quasiIsoAt_iff_exactAt' f.hom n (L.property.2.2 n)).2 (K.property.2.2 n)
    apply (ExactSubcategory.inflation_iff (abelianExactStructure (CochainComplex A ℤ))
      (boundedAcyclic P) f).2
    exact ⟨Q.obj, ⟨Q.property.1, Q.property.2, hs.acyclic_X₃ hq⟩,
      p.hom, congrArg (fun z ↦ z.hom) w, hS⟩
  · exact (boundedAcyclicTermsExactInclusion P).map_inflation f

/-- The same original inclusion is exact with genuine quasi-isomorphisms. -/
theorem boundedAcyclicTermsInclusion_quasiExact :
    IsExact (complexSubcategory (boundedAcyclic P)).cof (complexSubcategory (boundedAcyclic P)).weq
      (complexSubcategory (boundedTerms P)).cof (complexSubcategory (boundedTerms P)).weq
      (boundedAcyclicTermsInclusion P) where
  zero h := (boundedAcyclicTermsInclusion P).map_isZero h
  cofibration f hf := (boundedAcyclicTermsExactInclusion P).map_inflation f hf
  weak _ hf := hf
  pushout hi h := (boundedAcyclicTermsExactInclusion P).map_isPushout hi h

/-- Any map from any actual zero object is a genuine quasi-isomorphism
precisely when its target is actually acyclic. -/
theorem boundedTerms_weq_from_zero_iff
    {Z K : (boundedTerms P).FullSubcategory} (hZ : IsZero Z) (f : Z ⟶ K) :
    (complexSubcategory (boundedTerms P)).weq f ↔ K.obj.Acyclic := by
  have hz := acyclic_of_isZero Z.obj ((boundedTerms P).ι.map_isZero hZ)
  change QuasiIso f.hom ↔ K.obj.Acyclic
  rw [quasiIso_iff]
  exact forall_congr' (fun n ↦ quasiIsoAt_iff_exactAt f.hom n (hz n))

/-- The standard Waldhausen weakly-acyclic predicate is exactly actual
acyclicity of the original bounded complex. -/
theorem boundedTerms_weaklyAcyclic_iff (K : (boundedTerms P).FullSubcategory) :
    (complexSubcategory (boundedTerms P)).weq
      ((complexSubcategory (boundedTerms P)).isZero.to_ K) ↔ boundedAcyclic P K.obj := by
  rw [boundedTerms_weq_from_zero_iff P (complexSubcategory (boundedTerms P)).isZero]
  exact ⟨fun h ↦ ⟨K.property.1, K.property.2, h⟩, fun h ↦ h.2.2⟩

end Quillen.Waldhausen.GilletWaldhausen
