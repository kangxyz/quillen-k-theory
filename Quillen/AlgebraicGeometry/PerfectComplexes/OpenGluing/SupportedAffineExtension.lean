/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedExtensionTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.AffineExtension
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Supported perfect extension across an affine chart

On a quasi-separated scheme covered by a compact open immersion and an affine
open immersion, actual derived-overlap gluing extends the original E plus
E[1] while preserving vanishing on a prescribed compact open Z. The output
retains a literal quasi-isomorphism from the original stabilization into the
restricted glued object. Original inverse-image restrictions detect vanishing
on Z. Quasi-separatedness supplies compact overlaps; no affine-diagonal or
ambient compactness hypothesis is used.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Attach an actual affine chart while preserving vanishing on the original
compact support open and retaining the original weak stabilization arrow. -/
lemma exists_supported_perfect_extension_across_affine_openImmersion {U V X : Scheme.{u}}
    [QuasiSeparatedSpace X] [CompactSpace U] [IsAffine V]
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    (Z : X.Opens) (hZ : IsCompact (Z : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : locallyPerfect U E)
    (hz : IsZero ((DerivedCategory.Q (C := (j ⁻¹ᵁ Z).toScheme.Modules)).obj
      ((restrict (j ⁻¹ᵁ Z).ι).obj E))) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      ∃ u : E ⊞ E⟦(1 : ℤ)⟧ ⟶ (restrict j).obj P, QuasiIso u ∧
        IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj ((restrict Z.ι).obj P)) := by
  let a := pullback.fst j k
  let b := pullback.snd j k
  have hzK : IsZero ((DerivedCategory.Q (C := (b ⁻¹ᵁ (k ⁻¹ᵁ Z)).toScheme.Modules)).obj
      ((restrict (b ⁻¹ᵁ (k ⁻¹ᵁ Z)).ι).obj ((restrict a).obj E))) := by
    have h := isZero_restrict_preimage_of_isZero a (j ⁻¹ᵁ Z) E hz
    have he : b ⁻¹ᵁ (k ⁻¹ᵁ Z) = a ⁻¹ᵁ (j ⁻¹ᵁ Z) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg (fun f => f ⁻¹ᵁ Z) (pullback.condition (f := j) (g := k)).symm
    rw [he]
    exact h
  obtain ⟨B, hB, ⟨eB⟩, hBZ⟩ := exists_strict_supported_stabilized_extension_into_affine b
    (k ⁻¹ᵁ Z) (k.isCompact_preimage hZ) ((restrict a).obj E) (locallyPerfect_restrict a hE) hzK
  have hA : locallyPerfect U (E ⊞ E⟦(1 : ℤ)⟧) :=
    (abelianExactStructure (CochainComplex U.Modules ℤ)).prop_biprod (locallyPerfect U) hE
      (locallyPerfect_shift hE
      1)
  let e := (DerivedCategory.Q (C := (pullback j k).Modules)).mapIso
    (restrictStabilizationIso a E) ≪≫ eB.symm
  obtain ⟨P, hP, u, v, hu, hv⟩ := exists_perfect_glue_of_two_openImmersions j k hcover
    (E ⊞ E⟦(1 : ℤ)⟧) B hA (locallyPerfect_of_strictPerfect hB) e
  refine ⟨P, hP, u, hu, ?_⟩
  let Y : Bool → Scheme := fun t => if t then U else V
  let q : ∀ t, Y t ⟶ X := fun t => by
    cases t with
    | false => exact k
    | true => exact j
  have : ∀ t, IsOpenImmersion (q t) := by intro t; cases t <;> dsimp [q] <;> infer_instance
  apply isZero_restrict_of_openImmersionCover P Z Y q
  · intro x
    rcases hcover x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨true, y, hy⟩
    · exact ⟨false, y, hy⟩
  · intro t
    cases t with
    | false =>
      exact hBZ.of_iso (asIso ((DerivedCategory.Q (C := (k ⁻¹ᵁ Z).toScheme.Modules)).map
        ((restrict (k ⁻¹ᵁ Z).ι).map v))).symm
    | true =>
      have hAZ : IsZero ((DerivedCategory.Q (C := (j ⁻¹ᵁ Z).toScheme.Modules)).obj
          ((restrict (j ⁻¹ᵁ Z).ι).obj (E ⊞ E⟦(1 : ℤ)⟧))) :=
        (isZero_toDerived_stabilization_of_isZero hz).of_iso
          ((DerivedCategory.Q (C := (j ⁻¹ᵁ Z).toScheme.Modules)).mapIso
            (restrictStabilizationIso (j ⁻¹ᵁ Z).ι E))
      exact hAZ.of_iso (asIso ((DerivedCategory.Q (C := (j ⁻¹ᵁ Z).toScheme.Modules)).map
        ((restrict (j ⁻¹ᵁ Z).ι).map u))).symm
end Quillen.PerfectComplexes
