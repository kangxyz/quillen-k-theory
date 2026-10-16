/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StabilizedExtensionTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.Derived
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
/-!
# Actual perfect extension across one affine chart

Original derived overlap isomorphisms glue along arbitrary covering open
immersions to an actual perfect complex with genuine local quasi-isomorphisms.
Combining this with stabilized affine extension enlarges a compact open
immersion across one affine chart in an arbitrary quasi-separated scheme.
The output retains an actual weak arrow from the ORIGINAL local stabilization
into the restriction of the constructed global perfect complex.

Quasi-separatedness supplies compactness of the overlap. The ambient scheme
is not assumed to have affine diagonal or to be quasi-compact.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

lemma locallyPerfect_of_two_openImmersions {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {P : CochainComplex X.Modules ℤ} (hj : locallyPerfect U ((restrict j).obj P))
    (hk : locallyPerfect V ((restrict k).obj P)) : locallyPerfect X P := by
  apply locallyPerfect_of_openImmersion_models
  intro x
  rcases hcover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨O, hy, Q, ⟨eQ⟩⟩ := hj y
    exact ⟨O.toScheme, O.ι ≫ j, inferInstance, ⟨y, hy⟩, rfl,
      ⟨Q, ⟨(DerivedCategory.Q (C := O.toScheme.Modules)).mapIso
        ((restrictCompIso O.ι j).app P).symm ≪≫ eQ⟩⟩⟩
  · obtain ⟨O, hy, Q, ⟨eQ⟩⟩ := hk y
    exact ⟨O.toScheme, O.ι ≫ k, inferInstance, ⟨y, hy⟩, rfl,
      ⟨Q, ⟨(DerivedCategory.Q (C := O.toScheme.Modules)).mapIso
        ((restrictCompIso O.ι k).app P).symm ≪≫ eQ⟩⟩⟩

lemma exists_perfect_glue_of_two_openImmersions {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    (A : CochainComplex U.Modules ℤ) (B : CochainComplex V.Modules ℤ) (hA : locallyPerfect U A)
      (hB : locallyPerfect V B)
    (e : (DerivedCategory.Q (C := (pullback j k).Modules)).obj ((restrict (pullback.fst j k)).obj A)
      ≅
      (DerivedCategory.Q (C := (pullback j k).Modules)).obj ((restrict (pullback.snd j k)).obj B)) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      ∃ (u : A ⟶ (restrict j).obj P) (v : B ⟶ (restrict k).obj P), QuasiIso u ∧ QuasiIso v := by
  let a := pullback.fst j k
  let b := pullback.snd j k
  obtain ⟨M, α, β, hα, hβ, _, _⟩ := Quillen.CochainComplex.exists_weak_span_homotopy_of_derived_iso
    e (0 : _ ⟶ (0 : CochainComplex (pullback j k).Modules ℤ)) 0 (by simp)
  let P := OpenHomotopyGluing.glued a b j k pullback.condition α β
  let u := OpenHomotopyGluing.first a b j k pullback.condition α β
  let v := OpenHomotopyGluing.second a b j k pullback.condition α β
  have hu : QuasiIso u := OpenHomotopyGluing.first_quasiIso a b j k pullback.condition α β
    (by intro x hx; rw [IsOpenImmersion.range_pullbackFst]; exact hx)
  have hv : QuasiIso v := OpenHomotopyGluing.second_quasiIso a b j k pullback.condition α β
    (by intro x hx; rw [IsOpenImmersion.range_pullbackSnd]; exact hx)
  exact ⟨P, locallyPerfect_of_two_openImmersions j k hcover
    ((locallyPerfect_iff_of_quasiIso u).mp hA) ((locallyPerfect_iff_of_quasiIso v).mp hB),
    u, v, hu, hv⟩

/-- An arbitrary compact open immersion can be enlarged across an affine chart
inside any quasi-separated scheme, with an original weak stabilization map. -/
lemma exists_perfect_extension_across_affine_openImmersion {U V X : Scheme.{u}}
    [QuasiSeparatedSpace X] [CompactSpace U] [IsAffine V]
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    (E : CochainComplex U.Modules ℤ) (hE : locallyPerfect U E) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      ∃ u : E ⊞ E⟦(1 : ℤ)⟧ ⟶ (restrict j).obj P, QuasiIso u := by
  let a := pullback.fst j k
  let b := pullback.snd j k
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_strict_stabilized_extension_into_affine b
    ((restrict a).obj E) (locallyPerfect_restrict a hE)
  have hA : locallyPerfect U (E ⊞ E⟦(1 : ℤ)⟧) :=
    (abelianExactStructure (CochainComplex U.Modules ℤ)).prop_biprod (locallyPerfect U) hE
      (locallyPerfect_shift hE
      1)
  let e := (DerivedCategory.Q (C := (pullback j k).Modules)).mapIso
    (restrictStabilizationIso a E) ≪≫ eB.symm
  obtain ⟨P, hP, u, v, hu, hv⟩ := exists_perfect_glue_of_two_openImmersions j k hcover
    (E ⊞ E⟦(1 : ℤ)⟧) B hA (locallyPerfect_of_strictPerfect hB) e
  exact ⟨P, hP, u, hu⟩

end Quillen.PerfectComplexes
