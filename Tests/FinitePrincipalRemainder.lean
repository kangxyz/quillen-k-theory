/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FinitePrincipalRemainder
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.StalkFlat

/-! # Original residual homology and genuine cover consumers -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u v w
namespace Tests.FinitePrincipalRemainder

/-- The derived single comparison induces identity on the original homology,
for completely independent category and derived universes. -/
theorem original_homology_identity {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] [K.IsLE n] :
    ((DerivedCategory.homologyFunctorFactors C n).app K).inv ≫
      (DerivedCategory.homologyFunctor C n).map
        (Quillen.CochainComplex.derivedSingleHomologyIso K n).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app (K.homology n) = 𝟙 _ :=
  Quillen.CochainComplex.derivedSingleHomologyIso_homology K n

open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard
variable (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
  (C : ModuleComplex R) (a : ℤ) (s : Finset R)
  (k : ∀ r : s, Spec (.of (Localization.Away r.val)) ⟶ U)
  [∀ r : s, IsOpenImmersion (k r)]
  (hk : ∀ r : s, k r ≫ j = Quillen.CoherentScheme.principalOpen R r.val)
  (hcover : ∀ x : U, ∃ r : s, ∃ y, k r y = x)
  (hlocal : ∀ r : s,
    let L : ModuleComplex (.of (Localization.Away r.val)) := (localize r.val (.up ℤ)).obj C
    L.IsLE a ∧ L.IsGE a ∧ Module.Finite (Localization.Away r.val) (L.homology a) ∧
      Projective (L.homology a))

include hk hcover hlocal in
/-- Local projectivity gives flat stalks of the original restricted homology sheaf. -/
theorem original_remainder_homology_stalkwiseFlat :
    Quillen.SchemeSheaf.stalkwiseFlat U
      (((restrict j).obj ((associatedComplex R).obj C)).homology a) := by
  have hvb := (vectorBundle_single_of_principal_concentration R j C a s k hk hcover hlocal).1
  exact Quillen.SchemeSheaf.stalkwiseFlat_of_finiteLocallyFree _

include hk hcover hlocal in
/-- The same covered original remainder is concentrated in exactly the displayed degree. -/
theorem original_remainder_other_homology_zero (n : ℤ) (hn : n ≠ a) :
    IsZero (((restrict j).obj ((associatedComplex R).obj C)).homology n) := by
  obtain ⟨_, hge, hle, _⟩ := vectorBundle_single_of_principal_concentration R j C a s k hk hcover
    hlocal
  let D := (restrict j).obj ((associatedComplex R).obj C)
  rw [← exactAt_iff_isZero_homology]
  rcases lt_or_gt_of_ne hn with hn | hn
  · exact D.exactAt_of_isGE a n hn
  · exact D.exactAt_of_isLE a n hn

/-- An empty open admits the actual approximation for arbitrary ambient modules,
without requiring the empty principal family to span the ambient unit ideal. -/
theorem empty_family_actual_approximation [IsEmpty U] (K : ModuleComplex R) (a b : ℤ) :
    ∃ (P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K),
      Quillen.SchemeSheaf.IsFiniteLocallyFree U
        (((restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))).homology a)
          := by
  let k : ∀ r : (∅ : Finset R), Spec (.of (Localization.Away r.val)) ⟶ U :=
    fun r => False.elim (Finset.notMem_empty r.val r.property)
  have : ∀ r : (∅ : Finset R), IsOpenImmersion (k r) :=
    fun r => False.elim (Finset.notMem_empty r.val r.property)
  obtain ⟨P, hP, f, hvb, _, _, _⟩ :=
    exists_moduleStrictPerfect_approximation_with_vectorBundle_remainder R j K a b ∅ k
      (fun r => False.elim (Finset.notMem_empty r.val r.property))
      (fun x => isEmptyElim x)
      (fun r => False.elim (Finset.notMem_empty r.val r.property))
      (fun r => False.elim (Finset.notMem_empty r.val r.property))
  exact ⟨P, hP, f, hvb⟩

end Tests.FinitePrincipalRemainder
