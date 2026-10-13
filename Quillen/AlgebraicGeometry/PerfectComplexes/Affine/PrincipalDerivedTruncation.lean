/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.ModuleComplex.PrincipalTailTruncation
public import Quillen.Algebra.Homology.KProjectiveDerivedIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedModuleReplacement

/-!
# Actual principal-derived models and global finite-projective cutoff

Original principal-local derived isomorphisms to strict module models lift to
actual chain-homotopy equivalences by the proved K-projective representative
theorems. The genuine local-to-global tail cutoff then makes the literal good
truncation of the supplied bounded-above finite-projective complex a bounded
strict module model. Exact term bounds and the original projection are
retained. Constructing such a bounded-above finite-free complex from arbitrary
local perfection remains a separate theorem.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.ModuleComplex.PrincipalLocalization Quillen.CochainComplex
attribute [local instance] HasDerivedCategory.standard
namespace Quillen.PerfectComplexes.Affine

/-- Actual principal-local derived strict models suffice to cut off the original
bounded-above finite-projective module complex. The local derived isomorphisms
are converted to real homotopy equivalences using proved K-projectivity. -/
theorem moduleStrictPerfect_truncGE_of_principal_derived_models
    (R : CommRingCat.{u}) (s : Set R) (hs : Ideal.span s = ⊤)
    (P : ModuleComplex R) (n b : ℤ)
    (hbound : ∀ i, b < i → IsZero (P.X i))
    (hfinite : ∀ i, Module.Finite R (P.X i))
    (hprojective : ∀ i, Module.Projective R (P.X i))
    (hlocal : ∀ r : s, ∃ Q : ModuleComplex (.of (Localization.Away r.val)),
      moduleStrictPerfect _ Q ∧ (∀ i, i < n+1 → IsZero (Q.X i)) ∧
        Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj P) ≅
          DerivedCategory.Q.obj Q)) :
    moduleStrictPerfect R (P.truncGE n) ∧
      (∀ i, i < n ∨ b < i → IsZero ((P.truncGE n).X i)) ∧ QuasiIso (P.πTruncGE n) := by
  have hmodels : ∀ r : s, ∃ Q : ModuleComplex (.of (Localization.Away r.val)),
      (∀ i, i < n+1 → IsZero (Q.X i)) ∧
        Nonempty (HomotopyEquiv ((localize r.val (.up ℤ)).obj P) Q) := by
    intro r
    obtain ⟨Q, hQ, hbQ, ⟨e⟩⟩ := hlocal r
    let L := (localize r.val (.up ℤ)).obj P
    have : CochainComplex.IsStrictlyLE L b := (CochainComplex.isStrictlyLE_iff L b).mpr
      (fun i hi => (ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)).map_isZero (hbound i
        hi))
    have hproj (i : ℤ) : Projective (L.X i) := by
      let := hprojective i
      have hp : Module.Projective (Localization.Away r.val)
          ((P.X i).localizedModule (Submonoid.powers r.val)) :=
        Module.projective_of_isLocalizedModule (Submonoid.powers r.val)
          ((P.X i).localizedModuleMkLinearMap (Submonoid.powers r.val))
      let : Module.Projective (Localization.Away r.val) (L.X i) := hp
      exact ModuleCat.projective_of_categoryTheory_projective _
    have : CochainComplex.IsKProjective L := CochainComplex.isKProjective_of_projective L b
    have : Q.IsKProjective := isKProjective_of_moduleStrictPerfect _ hQ
    obtain ⟨h, _⟩ := exists_homotopyEquiv_of_derivedIso e
    exact ⟨Q, hbQ, ⟨h⟩⟩
  obtain ⟨hb, hp, hπ⟩ := bounded_finiteProjective_truncGE_of_principal_homotopy_models
    s hs P n b hbound hfinite hprojective hmodels
  exact ⟨⟨⟨n, b, hb⟩, hp⟩, hb, hπ⟩

end Quillen.PerfectComplexes.Affine
