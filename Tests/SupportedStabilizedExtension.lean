/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedStabilizedExtension

/-!
# Supported stabilized extension regression statements

Records strict-perfect extension of a local complex plus its shift while
retaining vanishing on a specified compact open. Other statements cover an
empty principal support family and a split scalar-cone transition with the
prescribed principal-localization support.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Tests.SupportedStabilizedExtension
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] Affine.standardDerivedModules Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The final support endpoint is an actual global strict sheaf complex with
both original restriction statements, not an ambient module substitute. -/
theorem original_strict_extension_with_open_support (R : CommRingCat.{u})
    (W Z : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (hZ : IsCompact (Z : Set (Spec R))) (E : Complex W.toScheme)
    (hE : locallyPerfect W.toScheme E)
    (hzero : IsZero ((toDerived (W ⊓ Z).toScheme).obj
      ((restrict ((Spec R).homOfLE (inf_le_left : W ⊓ Z ≤ W))).obj E))) :
    ∃ Q : Complex (Spec R), strictPerfect (Spec R) Q ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj Q) ≅
        (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧)) ∧
      IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj Q)) := by
  obtain ⟨Q, hQ, eQ, hzQ⟩ :=
    locallyPerfect_exists_stabilized_extension_with_open_support R W Z hW hZ E hE hzero
  exact ⟨(associatedComplex R).obj Q, strictPerfect_associated R hQ, eQ, hzQ⟩

/-- The empty additional support family imposes no acyclicity premise. -/
theorem empty_support_family (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) :
    ∃ Q : ModuleComplex R, moduleStrictPerfect R Q ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj Q)) ≅
        (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  obtain ⟨Q, hQ, eQ, _⟩ :=
    locallyPerfect_exists_stabilized_extension_with_principal_support R W hW ∅ E hE (by simp)
  exact ⟨Q, hQ, eQ⟩

/-- The actual composite of scalar-cone inclusions is split after the
original restriction, and its global target has the requested support. -/
theorem original_scalar_cone_transition_split (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (s : Finset R) {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hlocal : ∀ z ∈ s, IsZero ((toDerived (W ⊓ PrimeSpectrum.basicOpen z).toScheme).obj
      ((restrict (W ⊓ PrimeSpectrum.basicOpen z).ι).obj ((associatedComplex R).obj P)))) :
    ∃ (Q : ModuleComplex R) (_ : moduleStrictPerfect R Q) (i : P ⟶ Q),
      IsSplitMono ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map i))) ∧
      ∀ z ∈ s, IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj Q)) := by
  let r : Retract ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)))
      ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P))) :=
    { i := 𝟙 _, r := 𝟙 _, retract := Category.id_comp _ }
  obtain ⟨Q, hQ, i, rQ, hi, hs, _, _⟩ := exists_finite_scalar_cone_support R W hW s hP r hlocal
  have he : rQ.i = (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map i)) :=
    by
    simpa only [r, Category.id_comp] using hi
  refine ⟨Q, hQ, i, ?_, hs⟩
  exact IsSplitMono.mk' ⟨rQ.r, by rw [← he]; exact rQ.retract⟩

end Tests.SupportedStabilizedExtension
