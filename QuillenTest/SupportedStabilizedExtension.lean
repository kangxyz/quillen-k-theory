/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedStabilizedExtension
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

/-!
# Supported stabilized extension regression statements

Records strict-perfect extension of a local complex plus its shift while
retaining vanishing on a specified compact open. Other statements cover an
empty principal support family and a split scalar-cone transition with the
prescribed principal-localization support.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.SupportedStabilizedExtension
open Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] Affine.standardDerivedModules Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The final support endpoint is an actual global strict sheaf complex with
both original restriction statements, not an ambient module substitute. -/
theorem original_strict_extension_with_open_support (R : CommRingCat.{u})
    (W Z : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (hZ : IsCompact (Z : Set (Spec R))) (E : CochainComplex W.toScheme.Modules ℤ)
    (hE : locallyPerfect W.toScheme E)
    (hzero : IsZero ((DerivedCategory.Q (C := (W ⊓ Z).toScheme.Modules)).obj
      ((restrict ((Spec R).homOfLE (inf_le_left : W ⊓ Z ≤ W))).obj E))) :
    ∃ Q : CochainComplex (Spec R).Modules ℤ, strictPerfect (Spec R) Q ∧
      Nonempty ((DerivedCategory.Q (C := W.toScheme.Modules)).obj ((restrict W.ι).obj Q) ≅
        (DerivedCategory.Q (C := W.toScheme.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧)) ∧
      IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj ((restrict Z.ι).obj Q)) := by
  obtain ⟨Q, hQ, eQ, hzQ⟩ :=
    locallyPerfect_exists_stabilized_extension_with_open_support R W Z hW hZ E hE hzero
  exact ⟨(associatedComplex R).obj Q, strictPerfect_associated R hQ, eQ, hzQ⟩

/-- The empty additional support family imposes no acyclicity premise. -/
theorem empty_support_family (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : CochainComplex W.toScheme.Modules ℤ) (hE : locallyPerfect W.toScheme E) :
    ∃ Q : ModuleComplex R, moduleStrictPerfect R Q ∧
      Nonempty ((DerivedCategory.Q (C := W.toScheme.Modules)).obj
        ((restrict W.ι).obj ((associatedComplex R).obj Q)) ≅
        (DerivedCategory.Q (C := W.toScheme.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  obtain ⟨Q, hQ, eQ, _⟩ :=
    locallyPerfect_exists_stabilized_extension_with_principal_support R W hW ∅ E hE (by simp)
  exact ⟨Q, hQ, eQ⟩

/-- The actual composite of scalar-cone inclusions is split after the
original restriction, and its global target has the requested support. -/
theorem original_scalar_cone_transition_split (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (s : Finset R) {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hlocal : ∀ z ∈ s, IsZero ((DerivedCategory.Q (C :=
      (W ⊓ PrimeSpectrum.basicOpen z).toScheme.Modules)).obj
      ((restrict (W ⊓ PrimeSpectrum.basicOpen z).ι).obj ((associatedComplex R).obj P)))) :
    ∃ (Q : ModuleComplex R) (_ : moduleStrictPerfect R Q) (i : P ⟶ Q),
      IsSplitMono ((DerivedCategory.Q (C := W.toScheme.Modules)).map
        ((restrict W.ι).map ((associatedComplex R).map i))) ∧
      ∀ z ∈ s, IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj Q)) := by
  let r : Retract ((DerivedCategory.Q (C := W.toScheme.Modules)).obj
    ((restrict W.ι).obj ((associatedComplex R).obj P)))
      ((DerivedCategory.Q (C := W.toScheme.Modules)).obj
        ((restrict W.ι).obj ((associatedComplex R).obj P))) :=
    { i := 𝟙 _, r := 𝟙 _, retract := Category.id_comp _ }
  obtain ⟨Q, hQ, i, rQ, hi, hs, _, _⟩ := exists_finite_scalar_cone_support R W hW s hP r hlocal
  have he : rQ.i = (DerivedCategory.Q (C := W.toScheme.Modules)).map
    ((restrict W.ι).map ((associatedComplex R).map i)) :=
    by
    simpa only [r, Category.id_comp] using hi
  refine ⟨Q, hQ, i, ?_, hs⟩
  exact IsSplitMono.mk' ⟨rQ.r, by rw [← he]; exact rQ.retract⟩

end QuillenTest.SupportedStabilizedExtension
