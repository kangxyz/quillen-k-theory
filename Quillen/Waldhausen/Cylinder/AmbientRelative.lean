/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Cylinder.Subcategory
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence
public import Quillen.Waldhausen.SplitComplexes.FunctorialFactorization

/-! # Relative cylinder cofibrations for ambient admissible monomorphisms

The relative map is admissible without a degreewise splitting assumption.
Its genuine quotient is the shifted actual source cokernel. This addresses
the ambient-cofibration model separately from its split-cofibration variant.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
universe u v

namespace Quillen.Waldhausen.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g)
  {R : CochainComplex A ℤ} {i : middle f.hom ⟶ R} {j : g.left ⊞ g.right ⟶ R}
  (h : IsPushout (jointInclusion f.hom) (biprod.map α.left α.right) i j)
  (k : R ⟶ middle g.hom) (hi : i ≫ k = middleFunctor.map α)
  (hj : j ≫ k = jointInclusion g.hom)

include h hi hj in
/-- A monic source map suffices for the actual relative endpoint map to be monic.
No splitting, boundedness, or condition on the target map is used. -/
theorem relative_jointInclusion_mono [Mono α.left] : Mono k := by
  let E := abelianExactStructure (CochainComplex A ℤ)
  let q := pushout.desc (f := jointInclusion f.hom) (g := biprod.map α.left α.right)
    (middleFunctor.map α) (jointInclusion g.hom) (jointInclusion_naturality α)
  have hq : E.inflation q := GilletWaldhausen.relativePushout_inflation E
    (jointSequenceMap α) (jointSequence_shortExact f.hom) (jointSequence_shortExact g.hom)
    ((abelianExactStructure_inflation_iff _ _).2 (by
      change Mono (α.left⟦(1 : ℤ)⟧')
      infer_instance))
  let : Mono q := (abelianExactStructure_inflation_iff _ _).1 hq
  let h₀ := IsPushout.of_hasPushout (jointInclusion f.hom) (biprod.map α.left α.right)
  let e := h₀.isoIsPushout _ _ h
  have he : e.hom ≫ k = q := by
    apply h₀.hom_ext
    · rw [← Category.assoc, h₀.inl_isoIsPushout_hom, hi]
      exact (pushout.inl_desc _ _ _).symm
    · rw [← Category.assoc, h₀.inr_isoIsPushout_hom, hj]
      exact (pushout.inr_desc _ _ _).symm
  have hk : k = e.inv ≫ q := by rw [← he]; simp
  rw [hk]
  infer_instance

include h hi hj in
/-- The original relative quotient sequence is short exact under the ordinary
monomorphism condition, with no degreewise split hypothesis. -/
theorem relativeQuotientSequence_shortExact_of_mono [Mono α.left] :
    (relativeQuotientSequence α h k hi hj).ShortExact where
  mono_f := relative_jointInclusion_mono α h k hi hj
  epi_g := Cofork.IsColimit.epi (relativeQuotientIsCokernel α h k hi hj)
  exact := (relativeQuotientSequence α h k hi hj).exact_of_g_is_cokernel
    (relativeQuotientIsCokernel α h k hi hj)

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
  {f' g' : Arrow P.FullSubcategory} (β : f' ⟶ g') {T : P.FullSubcategory}
  (i' : (subcategoryMiddleFunctor P hcone).obj f' ⟶ T)
  (j' : subcategoryJointSource P g' ⟶ T)
  (h' : IsPushout (jointInclusion f'.hom.hom) (biprod.map β.left.hom β.right.hom) i'.hom j'.hom)
  (k' : T ⟶ (subcategoryMiddleFunctor P hcone).obj g')
  (hi' : i' ≫ k' = (subcategoryMiddleFunctor P hcone).map β)
  (hj' : j' ≫ k' = subcategoryJointInclusion P hcone g')

include hshift h' hi' hj' in
/-- Ordinary inherited admissibility of the source map proves the ordinary
inherited relative-cylinder cofibration, including actual quotient membership. -/
theorem subcategoryRelativeJoint_ambient_cof
    (hβ : (complexSubcategory P).cof β.left) : (complexSubcategory P).cof k' := by
  let γ := P.ι.mapArrow.map β
  let : Mono β.left.hom := (abelianExactStructure_inflation_iff _ _).1
    ((ExactSubcategory.exactInclusion (abelianExactStructure (CochainComplex A ℤ)) P).map_inflation
      β.left hβ)
  let : Mono γ.left := inferInstanceAs (Mono β.left.hom)
  have h₁ : i'.hom ≫ k'.hom = middleFunctor.map γ := congrArg (fun z ↦ z.hom) hi'
  have h₂ : j'.hom ≫ k'.hom = jointInclusion g'.hom.hom := congrArg (fun z ↦ z.hom) hj'
  have hQ : P (cokernel β.left.hom) :=
    ExactSubcategory.cokernel_mem_of_inflation _ P β.left hβ
  apply (ExactSubcategory.inflation_iff (abelianExactStructure (CochainComplex A ℤ)) P k').2
  exact ⟨(cokernel β.left.hom)⟦(1 : ℤ)⟧, hshift _ hQ,
    relativeQuotientProjection γ, relativeQuotient_zero γ h' k'.hom h₁ h₂,
    relativeQuotientSequence_shortExact_of_mono γ h' k'.hom h₁ h₂⟩

end Quillen.Waldhausen.SplitFactorization
