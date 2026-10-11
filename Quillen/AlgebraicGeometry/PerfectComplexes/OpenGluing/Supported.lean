/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.AffineExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Restriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportClosure
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportRestriction

/-! # Actual two-open derived gluing retains an auxiliary support -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open scoped ZeroObject
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard

/-- Perfection and vanishing on an auxiliary open are detected by the same
actual two-open cover. The support need not be termwise zero. -/
theorem perfectSupported_of_two_openImmersions {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) (Z : X.Opens)
    {P : Complex X}
    (hj : perfectSupported (j ⁻¹ᵁ Z).ι ((restrict j).obj P))
    (hk : perfectSupported (k ⁻¹ᵁ Z).ι ((restrict k).obj P)) :
    perfectSupported Z.ι P := by
  refine ⟨locallyPerfect_of_two_openImmersions j k hcover hj.1 hk.1, ?_⟩
  apply (isZero_toDerived_iff_acyclic _).mp
  let Y : Bool → Scheme := fun t ↦ if t then U else V
  let q : ∀ t, Y t ⟶ X := fun t ↦ by
    cases t with
    | false => exact k
    | true => exact j
  have : ∀ t, IsOpenImmersion (q t) := by intro t; cases t <;> dsimp [q] <;> infer_instance
  apply isZero_restrict_of_openImmersionCover P Z Y q
  · intro x
    rcases hcover x with ⟨y,hy⟩ | ⟨y,hy⟩
    · exact ⟨true,y,hy⟩
    · exact ⟨false,y,hy⟩
  · intro t
    cases t
    · exact (isZero_toDerived_iff_acyclic _).mpr hk.2
    · exact (isZero_toDerived_iff_acyclic _).mpr hj.2

/-- A specified original overlap isomorphism glues the original local
supported complexes, with both genuine local quasi-isomorphisms retained. -/
theorem exists_supported_glue_of_openSquare {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : a ≫ j = b ≫ k)
    (ha : ∀ x : U, j x ∈ Set.range k → x ∈ Set.range a)
    (hb : ∀ x : V, k x ∈ Set.range j → x ∈ Set.range b)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    (Z : X.Opens) (A : Complex U) (B : Complex V)
    (hA : perfectSupported (j ⁻¹ᵁ Z).ι A) (hB : perfectSupported (k ⁻¹ᵁ Z).ι B)
    (e : (toDerived W).obj ((restrict a).obj A) ≅
      (toDerived W).obj ((restrict b).obj B)) :
    ∃ P : Complex X, perfectSupported Z.ι P ∧
      ∃ (u : A ⟶ (restrict j).obj P) (v : B ⟶ (restrict k).obj P), QuasiIso u ∧ QuasiIso v := by
  obtain ⟨M,α,β,hα,hβ,_,_⟩ :=
    Quillen.CochainComplex.exists_weak_span_homotopy_of_derived_iso e
      (0 : _ ⟶ (0 : Complex W)) 0 (by simp)
  let P := OpenHomotopyGluing.glued a b j k h α β
  let u := OpenHomotopyGluing.first a b j k h α β
  let v := OpenHomotopyGluing.second a b j k h α β
  have hu : QuasiIso u := OpenHomotopyGluing.first_quasiIso a b j k h α β ha
  have hv : QuasiIso v := OpenHomotopyGluing.second_quasiIso a b j k h α β hb
  refine ⟨P,perfectSupported_of_two_openImmersions j k hcover Z ?_ ?_,u,v,hu,hv⟩
  · exact ⟨(locallyPerfect_iff_of_quasiIso u).mp hA.1,
      (restrictAcyclic_iff_of_quasiIso (j ⁻¹ᵁ Z).ι u).mp hA.2⟩
  · exact ⟨(locallyPerfect_iff_of_quasiIso v).mp hB.1,
      (restrictAcyclic_iff_of_quasiIso (k ⁻¹ᵁ Z).ι v).mp hB.2⟩

end Quillen.PerfectComplexes
