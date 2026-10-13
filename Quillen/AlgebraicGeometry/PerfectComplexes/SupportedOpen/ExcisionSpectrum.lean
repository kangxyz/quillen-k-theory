/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Excision
public import Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality

/-!
# Original supported cover excision on the connective prespectra

The original supported restriction is realized by the actual normalized exact
prespectrum map. When the image of the immersion and the auxiliary acyclicity
open cover the scheme, the existing support-excision K-equivalence proves that
this map is stable. Its nonnegative stable maps retain the original restriction
K-maps, including degree zero.

No quasi-compactness or quasi-separatedness is required. The normalization is
the existing `exactOriginalPrespectrumMap` construction, without an additional
chosen-zero hypothesis. These are the original connective supported spectra;
no Bass-telescope or classical nonconnective comparison is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The actual normalized prespectrum map of the original supported restriction. -/
def perfectSupportedExcisionPrespectrumMap :
    originalPrespectrum (perfectSupportedWaldhausen T.ι) ⟶
      originalPrespectrum (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) :=
  exactOriginalPrespectrumMap (perfectSupportedWaldhausen T.ι)
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (perfectSupportedRestrict_exact j T)

/-- The original cover support-excision equivalence makes the same restriction map stable. -/
theorem perfectSupportedExcisionPrespectrumMap_isStableEquivalence
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) :
    IsStableEquivalence (perfectSupportedExcisionPrespectrumMap j T) :=
  (exactOriginalPrespectrumMap_isStableEquivalence_iff
    (perfectSupportedWaldhausen T.ι)
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
    (perfectSupportedRestrict_exact j T)).mpr
      (fun n => (perfectSupportedExcisionKEquiv j T hcover n).bijective)

/-- Every nonnegative stable map is the unchanged original supported restriction K-map. -/
theorem perfectSupportedExcisionPrespectrumMap_originalK_naturality
    (n : ℕ) (x : PerfectSupportedK T.ι n) :
    originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) n
        (Additive.ofMul (perfectSupportedKRestrict j T n x)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedExcisionPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen T.ι) n (Additive.ofMul x)) :=
  originalKStableEquiv_exact_naturality (perfectSupportedWaldhausen T.ι)
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (perfectSupportedRestrict_exact j T) n x

end Quillen.PerfectComplexes
