/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenGluing.AffineExtension
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Closure
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.RestrictionVanishing
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Actual two-open derived gluing retains an auxiliary support -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open scoped ZeroObject
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard

/-- Perfection and vanishing on an auxiliary open are detected by the same
actual two-open cover. The support need not be termwise zero. -/
theorem perfectSupported_of_two_openImmersions {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) (Z : X.Opens)
    {P : CochainComplex X.Modules ℤ}
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
    (Z : X.Opens) (A : CochainComplex U.Modules ℤ) (B : CochainComplex V.Modules ℤ)
    (hA : perfectSupported (j ⁻¹ᵁ Z).ι A) (hB : perfectSupported (k ⁻¹ᵁ Z).ι B)
    (e : (DerivedCategory.Q (C := W.Modules)).obj ((restrict a).obj A) ≅
      (DerivedCategory.Q (C := W.Modules)).obj ((restrict b).obj B)) :
    ∃ P : CochainComplex X.Modules ℤ, perfectSupported Z.ι P ∧
      ∃ (u : A ⟶ (restrict j).obj P) (v : B ⟶ (restrict k).obj P), QuasiIso u ∧ QuasiIso v := by
  obtain ⟨M,α,β,hα,hβ,_,_⟩ :=
    Quillen.CochainComplex.exists_weak_span_homotopy_of_derived_iso e
      (0 : _ ⟶ (0 : CochainComplex W.Modules ℤ)) 0 (by simp)
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
