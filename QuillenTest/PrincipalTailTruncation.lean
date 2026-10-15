/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalDerivedTruncation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedComparison

/-! Semantic consumers of actual projective locality and lower-tail cutoff. -/
@[expose] public section

open Quillen.CochainComplex
open Quillen.PerfectComplexes


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.ModuleComplex.PrincipalLocalization
open Quillen.PerfectComplexes.Affine
attribute [local instance] HasDerivedCategory.standard
namespace QuillenTest.PrincipalTailTruncation

open Quillen

/-- The splitting really uses the original differential quotient and the
original supplied homotopy component, rather than an abstract projective witness. -/
theorem actual_tail_retract_formula {C : Type u} [Category.{v} C] [Abelian C]
    (P : CochainComplex C ℤ) (n : ℤ) (φ : P ⟶ P)
    (H : Homotopy (𝟙 P) φ) (hφ : φ.f n = 0) :
    P.fromOpcycles n (n+1) ≫ H.hom (n+1) n ≫ P.pOpcycles n = 𝟙 (P.opcycles n) :=
  (opcyclesRetractOfHomotopyAt P n φ H hφ).retract

/-- The patched projectivity supplies actual lifts against every original
module epimorphism, with no finiteness requirement on that epimorphism's source. -/
theorem actual_global_lift_from_local_projectivity {R : Type u} [CommRing R]
    (s : Set R) (hs : Ideal.span s = ⊤) (M : ModuleCat.{u} R)
    (hf : ∀ r : s, Module.Finite (Localization.Away r.val)
      (M.localizedModule (Submonoid.powers r.val)))
    (hp : ∀ r : s, Module.Projective (Localization.Away r.val)
      (M.localizedModule (Submonoid.powers r.val)))
    {N B : ModuleCat.{u} R} (p : N ⟶ B) [Epi p] (a : M ⟶ B) :
    ∃ g : M ⟶ N, g ≫ p = a := by
  let := (finiteProjective_of_localizationSpan s hs M hf hp).2
  have : Projective M := ModuleCat.projective_of_categoryTheory_projective M
  exact ⟨Projective.factorThru a p, Projective.factorThru_comp a p⟩

/-- Actual local models make the literal original truncation projection an
isomorphism on every original module homology object, with unchanged bounds. -/
theorem actual_local_cutoff_homology {R : Type u} [CommRing R]
    (s : Set R) (hs : Ideal.span s = ⊤) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (n b : ℤ) (hb : ∀ i, b < i → IsZero (P.X i))
    (hf : ∀ i, Module.Finite R (P.X i)) (hp : ∀ i, Module.Projective R (P.X i))
    (hlocal : ∀ r : s, ∃ Q : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ,
      (∀ i, i < n+1 → IsZero (Q.X i)) ∧
        Nonempty (HomotopyEquiv ((localize r.val (.up ℤ)).obj P) Q)) :
    (∀ i, i < n ∨ b < i → IsZero ((P.truncGE n).X i)) ∧
      (∀ i, IsIso (homologyMap (P.πTruncGE n) i)) ∧
      Nonempty ((P.truncGE n).X n ≅ P.opcycles n) := by
  obtain ⟨hbound, _, hπ⟩ :=
    bounded_finiteProjective_truncGE_of_principal_homotopy_models s hs P n b hb hf hp hlocal
  let := hπ
  exact ⟨hbound, fun _ => inferInstance, ⟨P.truncGEXIsoOpcycles n⟩⟩

/-- The empty principal cover of a zero ring is allowed, and reversed bounds
produce the literal zero truncation rather than requiring a nonempty interval. -/
theorem actual_empty_cover_reversed_bounds {R : Type u} [CommRing R] [Subsingleton R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hb : ∀ i, -7 < i → IsZero (P.X i))
    (hf : ∀ i, Module.Finite R (P.X i)) (hp : ∀ i, Module.Projective R (P.X i)) :
    IsZero (P.truncGE (-5)) ∧ QuasiIso (P.πTruncGE (-5)) := by
  obtain ⟨hbound, _, hπ⟩ := bounded_finiteProjective_truncGE_of_principal_homotopy_models
    (∅ : Set R) (Subsingleton.elim _ _) P (-5) (-7) hb hf hp
      (fun r => (Set.notMem_empty r.val r.property).elim)
  refine ⟨?_, hπ⟩
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  exact (hbound i (by omega)).eq_of_src _ _

/-- Local derived strict models give a genuine original affine strict sheaf
complex and the actual associated good-truncation quasi-isomorphism. -/
theorem actual_affine_strict_cutoff (R : CommRingCat.{u}) (s : Set R)
    (hs : Ideal.span s = ⊤) (P : ModuleComplex R) (n b : ℤ)
    (hb : ∀ i, b < i → IsZero (P.X i))
    (hf : ∀ i, Module.Finite R (P.X i)) (hp : ∀ i, Module.Projective R (P.X i))
    (hlocal : ∀ r : s, ∃ Q : ModuleComplex (.of (Localization.Away r.val)),
      moduleStrictPerfect _ Q ∧ (∀ i, i < n+1 → IsZero (Q.X i)) ∧
        Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj P) ≅
          DerivedCategory.Q.obj Q)) :
    strictPerfect (Spec R) ((associatedComplex R).obj (P.truncGE n)) ∧
      QuasiIso ((associatedComplex R).map (P.πTruncGE n)) := by
  obtain ⟨hM, _, hπ⟩ :=
    moduleStrictPerfect_truncGE_of_principal_derived_models R s hs P n b hb hf hp hlocal
  exact ⟨strictPerfect_associated R hM, (quasiIso_associated_iff R _).mpr hπ⟩

end QuillenTest.PrincipalTailTruncation
