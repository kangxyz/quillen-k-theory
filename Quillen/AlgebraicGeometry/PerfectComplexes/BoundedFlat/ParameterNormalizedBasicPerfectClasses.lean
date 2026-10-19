/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicFineComparison
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterInitialPerfectClasses
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterInitialAmbientPerfectClasses
public import Quillen.KTheory.Bass.SchemeModelRowNormalizedClasses

/-!
# The original perfect classes in the independently normalized basic row

The normalized classes are defined by their actual finite row inclusions. Their
comparison to the original fine objects retains the original perfect K
comparison, including the degree-zero map used by negative K-theory.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
open GlobalSectionChangeIndex ParameterLaurentTrack ParameterFullCurrentNull

/-- Each original supported perfect class has the independently normalized finite image. -/
theorem normalized_fine_originalSupportedClass
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace Q.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ParameterModels.supported f.left).obj (specUnder.obj a)).waldhausen.K n) :
    (normalizedFineSupportComparison f a (n : ℤ)).hom
        (SchemeModelRowSeed.normalizedModelClass (ParameterModels.supported f.left)
          (supportedUnit f.left) (supportedUnit_naturality f.left) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        (boundedFlatCoefficientSupportedKStableEquiv f a n
          (Additive.ofMul (boundedFlatCoefficientSupportedPerfectKEquiv f a n
            (Quillen.Waldhausen.KMap
              (((parameterSupportedRowIso f).hom ≫ supportedRowRestriction f).app a).exact
              n x)))) := by
  have hc := SchemeModelRowSeed.normalizedComparison_modelClass
    (ParameterModels.supported f.left) (supportedUnit f.left) (supportedUnit_naturality f.left)
    (specUnder.obj a) n x
  have ht := ConcreteCategory.congr_hom
    (normalizedFineSupportComparison_triangle f a (n : ℤ))
    (SchemeNaturalSeed.currentModelClass (ParameterModels.supported f.left) (supportedTrack f.left)
      (specUnder.obj a) n x)
  exact (congrArg (normalizedFineSupportComparison f a (n : ℤ)).hom hc).symm.trans
    (ht.trans (current_fine_originalSupportedClass f a n x))

/-- Degree zero retains precisely the original bottom comparison used by the negative groups. -/
theorem normalized_fine_originalSupportedZeroClass
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace Q.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : ((ParameterModels.supported f.left).obj (specUnder.obj a)).waldhausen.K 0) :
    (normalizedFineSupportComparison f a 0).hom
        (SchemeModelRowSeed.normalizedModelClass (ParameterModels.supported f.left)
          (supportedUnit f.left) (supportedUnit_naturality f.left) (specUnder.obj a) 0 x) =
      (stableHomotopyFunctor 0).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        ((boundedFlatCoefficientSupportedBassBottomZeroIso f a).hom
          (Additive.ofMul (boundedFlatCoefficientSupportedPerfectKEquiv f a 0
            (Quillen.Waldhausen.KMap
              (((parameterSupportedRowIso f).hom ≫ supportedRowRestriction f).app a).exact
              0 x)))) :=
  normalized_fine_originalSupportedClass f a 0 x

/-- Both original ambient endpoints retain every perfect class through the finite row inclusion. -/
theorem normalized_fine_ambient_perfectClass
    (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ParameterModels.ambient P.left).obj (specUnder.obj a)).waldhausen.K n) :
    (normalizedFineAmbientComparison P a (n : ℤ)).hom
        (SchemeModelRowSeed.normalizedModelClass (ParameterModels.ambient P.left)
          (ParameterLaurentUnit.ambientUnit P.left)
          (ParameterLaurentUnit.ambientUnit_naturality P.left) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientAmbientBassTelescopeInclusion P 0).app a)
        (boundedFlatCoefficientSectionPerfectKStableEquiv (op P, a) n
          (Additive.ofMul (boundedFlatCoefficientSectionPerfectKEquiv (op P, a) n
            (Quillen.Waldhausen.KMap ((parameterCoefficientRestriction P).app a).exact n x)))) := by
  have hc := SchemeModelRowSeed.normalizedComparison_modelClass
    (ParameterModels.ambient P.left) (ParameterLaurentUnit.ambientUnit P.left)
    (ParameterLaurentUnit.ambientUnit_naturality P.left) (specUnder.obj a) n x
  have ht := ConcreteCategory.congr_hom
    (normalizedFineAmbientComparison_triangle (𝟙 P) a (n : ℤ))
    (SchemeNaturalSeed.currentModelClass (ParameterModels.ambient P.left) (ambientTrack P.left)
      (specUnder.obj a) n x)
  exact (congrArg (normalizedFineAmbientComparison P a (n : ℤ)).hom hc).symm.trans
    (ht.trans (current_fine_ambient_perfectClass P a n x))

/-- Ambient degree zero is the unchanged original map that seeds the negative recursion. -/
theorem normalized_fine_ambient_originalZeroClass
    (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : ((ParameterModels.ambient P.left).obj (specUnder.obj a)).waldhausen.K 0) :
    (normalizedFineAmbientComparison P a 0).hom
        (SchemeModelRowSeed.normalizedModelClass (ParameterModels.ambient P.left)
          (ParameterLaurentUnit.ambientUnit P.left)
          (ParameterLaurentUnit.ambientUnit_naturality P.left) (specUnder.obj a) 0 x) =
      (stableHomotopyFunctor 0).map
        ((boundedFlatCoefficientAmbientBassTelescopeInclusion P 0).app a)
        (((boundedFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a)
          (Additive.ofMul (boundedFlatCoefficientSectionPerfectKEquiv (op P, a) 0
            (Quillen.Waldhausen.KMap ((parameterCoefficientRestriction P).app a).exact 0 x)))) := by
  have hc := SchemeModelRowSeed.normalizedComparison_modelClass
    (ParameterModels.ambient P.left) (ParameterLaurentUnit.ambientUnit P.left)
    (ParameterLaurentUnit.ambientUnit_naturality P.left) (specUnder.obj a) 0 x
  have ht := ConcreteCategory.congr_hom
    (normalizedFineAmbientComparison_triangle (𝟙 P) a 0)
    (SchemeNaturalSeed.currentModelClass (ParameterModels.ambient P.left) (ambientTrack P.left)
      (specUnder.obj a) 0 x)
  exact (congrArg (normalizedFineAmbientComparison P a 0).hom hc).symm.trans
    (ht.trans (current_fine_ambient_originalZeroClass P a x))

end Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
