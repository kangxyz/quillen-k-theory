/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.ScalarSupportExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedProjectorExtension

/-!
# Source support in affine roofs and stabilized extension

Regression statements retain additional principal-open source support through
denominators, chain roofs, derived equalities, and stabilized extension from a
retract. The geometric roof statement keeps two support conditions, and the
final statement identifies the split derived cone inclusion after restriction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.SourceSupportRoofs
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] Affine.standardDerivedModules Affine.standardDerivedSheaves

/-- A second, unrelated principal family keeps its original source support. -/
theorem denominator_additional_family (R : CommRingCat.{u}) (s t : Finset R)
    {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hM : ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj M)))
    (hT : ∀ r ∈ t, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      DerivedCategory.Q.map q ≫ α = 0 ∧
      (∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q)) ∧
      ∀ r ∈ t, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  obtain ⟨P', hP', q, hq, hs, ht⟩ :=
    exists_perfect_denominator_preserving_source_support R s hP hM α
  exact ⟨P', hP', q, hq, hs, fun r hr => ht r (hT r hr)⟩

/-- A genuine global homotopy survives while support is kept at an extra principal. -/
theorem actual_numerator_homotopy_with_extra_support (R : CommRingCat.{u}) (s : Finset R)
    {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P) (η : B ⟶ N)
    (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η)) (a : P ⟶ N)
    (r : R) (hr : IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P) (g : P' ⟶ B),
      Nonempty (Homotopy (g ≫ η) (q ≫ a)) ∧
      (∀ z ∈ s, QuasiIso ((localize z (.up ℤ)).map q)) ∧
      IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  obtain ⟨P', hP', q, g, H, hq, hs⟩ :=
    exists_finite_principal_chain_roof_preserving_source_support R s hP η hη a
  exact ⟨P', hP', q, g, H, hq, hs r hr⟩

/-- Equality is obtained for the two original derived arrows, preserving extra support. -/
theorem actual_equality_with_extra_support (R : CommRingCat.{u}) (s : Finset R)
    {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P) (η : B ⟶ N)
    (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η))
    (α β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj B)
    (hαβ : α ≫ DerivedCategory.Q.map η = β ≫ DerivedCategory.Q.map η)
    (r : R) (hr : IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      DerivedCategory.Q.map q ≫ (α - β) = 0 ∧
      (∀ z ∈ s, QuasiIso ((localize z (.up ℤ)).map q)) ∧
      IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  obtain ⟨P', hP', q, he, hq, hs⟩ :=
    exists_finite_principal_derived_equality_preserving_source_support R s hP η hη α β hαβ
  exact ⟨P', hP', q, by rw [Preadditive.comp_sub, he, sub_self], hq, hs r hr⟩

/-- The unconditional original qc-open geometric square has both source-support conditions. -/
theorem original_geometric_roof_with_two_supports (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (hB : moduleStrictPerfect R B)
    (r t : R)
    (hr : IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)))
    (ht : IsZero (DerivedCategory.Q.obj ((localize t (.up ℤ)).obj P)))
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj B))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P) (g : P' ⟶ B),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map q)) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map q)) ≫ α =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ∧
      IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) ∧
      IsZero (DerivedCategory.Q.obj ((localize t (.up ℤ)).obj P')) := by
  obtain ⟨P', hP', q, g, hq, he, hs⟩ :=
    exists_quasiCompact_open_strict_roof_preserving_source_support R W hW hP hB α
  exact ⟨P', hP', q, g, hq, he, hs r hr, hs t ht⟩

/-- An original local retract gives stabilized extension while retaining an
additional support condition absent from the open denominator cover. -/
theorem original_retract_stabilizes_with_support (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E)
    (r : Retract ((toDerived W.toScheme).obj E)
      ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P))))
    (z : R) (hz : IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj P))) :
    ∃ (Q : ModuleComplex R), moduleStrictPerfect R Q ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj Q)) ≅
        (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧)) ∧
      IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj Q)) := by
  obtain ⟨Q, hQ, eQ, hs⟩ :=
    exists_stabilized_extension_preserving_support_of_retract R W hW hP E hE r
  exact ⟨Q, hQ, eQ, hs z hz⟩

/-- The actual original cone inclusion is split after restriction whenever
its preceding original arrow vanishes in the derived category. -/
theorem original_cone_inclusion_split (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] {P B : ModuleComplex R} (f : P ⟶ B)
    (hf : (toDerived U).map ((restrict j).map ((associatedComplex R).map f)) = 0) :
    IsSplitMono ((toDerived U).map ((restrict j).map
      ((associatedComplex R).map (CochainComplex.mappingCone.inr f)))) := by
  obtain ⟨ρ, hρ⟩ := exists_retraction_original_cone_inclusion_of_restrict_zero R j f hf
  exact IsSplitMono.mk' ⟨ρ, hρ⟩

end QuillenTest.SourceSupportRoofs
