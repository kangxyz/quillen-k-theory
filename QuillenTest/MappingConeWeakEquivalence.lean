/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ConeComparison

/-! The actual zero-arrow cofiber comparison of bounded-flat inclusion spectra is stable in every
integer degree. Arbitrary original S-spectrum arrows also retain well-based positive cone points. -/
@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum
open Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS hiding zeroHom
universe u v
namespace QuillenTest.MappingConeWeakEquivalence

open Quillen

/-- The zero-arrow cone comparison retains the literal bounded-flat inclusions. -/
theorem boundedFlatZeroCone_isStableEquivalence
    (X Y : Scheme.{u}) [CompactSpace X] [CompactSpace Y] :
    let iX := exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
      (boundedFlatPerfectInclusion_exact X)
    let iY := exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
      (boundedFlatPerfectInclusion_exact Y)
    ∃ w : iX ≫ zeroHom _ _ = zeroHom _ _ ≫ iY,
      IsStableEquivalence (mappingConeMap (Arrow.homMk
        (f := Arrow.mk (zeroHom _ _)) (g := Arrow.mk (zeroHom _ _)) iX iY w)) := by
  dsimp
  have w : exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
      (boundedFlatPerfectInclusion_exact X) ≫ zeroHom _ _ =
      zeroHom _ _ ≫ exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y)
        (perfectWaldhausen Y) (boundedFlatPerfectInclusion_exact Y) := by
    apply Hom.ext
    funext n
    ext x
    exact ((exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
      (boundedFlatPerfectInclusion_exact Y)).map_point n).symm
  exact ⟨w, boundedFlatPerfectConeMap_isStableEquivalence X Y (zeroHom _ _) (zeroHom _ _) w⟩

/-- Every original S-spectrum arrow has well-based positive reduced cone levels. -/
theorem originalMappingCone_positivePoint_homotopyExtensionProperty
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Waldhausen.Structure C) (V : Waldhausen.Structure D)
    (f : originalPrespectrum W ⟶ originalPrespectrum V) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{max u v + 1} ((mappingCone f).point (n + 1)))) :=
  mappingCone_positivePoint_homotopyExtensionProperty f
    (originalPrespectrum_positivePoint_homotopyExtensionProperty W)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty V) n

end QuillenTest.MappingConeWeakEquivalence
