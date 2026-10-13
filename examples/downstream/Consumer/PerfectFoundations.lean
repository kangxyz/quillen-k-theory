/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Basic
public import Quillen.AlgebraicGeometry.Scheme.Comparison.SmallVectorBundleK

/-!
# Perfect-complex K-theory interface examples

Uses restriction, support inclusion, and comparison maps for strict, locally
perfect, and split-cofibration models. The examples retain mapping-cone closure,
split factorizations, canonical forward maps of the model equivalences, and the
factorization of the scheme-to-perfect map through strict-perfect K-theory.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Consumer
open Quillen.PerfectComplexes

/-- Strict-perfect K uses the genuine quasi-isomorphism S-construction. -/
noncomputable def strict_restriction_map {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) : StrictK X n →* StrictK U n := strictKRestrict j n

/-- Strict complexes remain strict under actual mapping cones. -/
theorem strict_mappingCone {X : Scheme.{u}} {P Q : Complex X}
    (hP : strictPerfect X P) (hQ : strictPerfect X Q) (f : P ⟶ Q) :
    strictPerfect X (CochainComplex.mappingCone f) := strictPerfect_mappingCone hP hQ f

/-- Perfectness is geometric and stable under actual open restriction. -/
theorem perfect_open_restriction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {P : Complex X} (hP : locallyPerfect X P) :
    locallyPerfect U ((restrict j).obj P) := locallyPerfect_restrict j hP
/-- Locally-perfect connective K uses actual quasi-isomorphisms. -/
def perfect_restriction_map {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) : PerfectK X n →* PerfectK U n := perfectKRestrict j n

/-- The strict-to-local map is constructed without assuming it invertible. -/
def strict_to_perfect_map (X : Scheme.{u}) (n : ℕ) : StrictK X n →* PerfectK X n :=
  strictToPerfectKMap X n

/-- Supported K is defined by actual acyclicity on the specified open. -/
def perfect_supported_map {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) : PerfectSupportedK j n →* PerfectK X n := perfectSupportedKMap j n
/-- The degreewise-split convention has a canonical actual comparison map. -/
def split_perfect_comparison (X : Scheme.{u}) (n : ℕ) : SplitPerfectK X n →* PerfectK X n :=
  splitPerfectToPerfectKMap X n

/-- Split cofibration/weak-equivalence factorizations stay locally perfect. -/
theorem split_perfect_factorization {X : Scheme.{u}} {K L : Perfect X} (f : K ⟶ L) :
    ∃ (M : Perfect X) (i : K ⟶ M) (p : M ⟶ L),
      (splitPerfectWaldhausen X).cof i ∧ (splitPerfectWaldhausen X).weq p ∧ i ≫ p = f :=
  exists_splitPerfect_factorization f
/-- Public scheme K and the actual vector-bundle Q-model share their realization universe. -/
def scheme_vectorBundle_model (X : Scheme.{u}) (n : ℕ) : Quillen.Scheme.K X n ≃*
    (Quillen.SchemeSheaf.vectorBundleExactStructure X).K n :=
  Quillen.SchemeSheaf.smallVectorBundleKEquiv X n

/-- The model equivalence retains the canonical normalized Q-functor map. -/
theorem scheme_vectorBundle_model_forward (X : Scheme.{u}) (n : ℕ) :
    (scheme_vectorBundle_model X n).toMonoidHom =
      Quillen.SchemeSheaf.smallVectorBundleKMap X n := rfl
/-- The previously constructed locally-perfect map is the equivalence's exact forward map. -/
def split_perfect_equivalence (X : Scheme.{u}) (n : ℕ) : SplitPerfectK X n ≃* PerfectK X n :=
  splitPerfectKEquiv X n

theorem split_perfect_equivalence_forward (X : Scheme.{u}) (n : ℕ) :
    (split_perfect_equivalence X n).toMonoidHom = splitPerfectToPerfectKMap X n := rfl

/-- The same comparison is proved for globally bounded strict-perfect complexes. -/
def split_strict_equivalence (X : Scheme.{u}) (n : ℕ) : SplitStrictK X n ≃* StrictK X n :=
  splitStrictKEquiv X n
/-- The public Q-defined scheme model is now canonically exact vector-bundle S-theory. -/
def vector_bundle_qs (X : Scheme.{u}) (n : ℕ) : Quillen.Scheme.K X n ≃*
    (Quillen.Waldhausen.ofExactCategory (Quillen.SchemeSheaf.vectorBundleExactStructure X)).K n :=
  vectorBundleQSEquiv X n

/-- The genuine Q-to-perfect comparison is constructed without claiming Gillet–Waldhausen. -/
def scheme_to_perfect (X : Scheme.{u}) (n : ℕ) : Quillen.Scheme.K X n →* PerfectK X n :=
  vectorBundleToPerfectKMap X n

theorem scheme_to_perfect_factors_through_strict (X : Scheme.{u}) (n : ℕ) :
    (strictToPerfectKMap X n).comp (vectorBundleToStrictKMap X n) =
      scheme_to_perfect X n := rfl
end Consumer
