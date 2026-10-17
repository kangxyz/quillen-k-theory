/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenCofinality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedPolynomialLaurentTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedGroups
public import Quillen.Waldhausen.SConstruction.Iterated.ModelStableHomotopy

/-!
# Original supported K-zero at the actual native stage-zero bottom

Original supported evaluation, bounded-flat inclusion and the actual small-model
K/stable comparison identify the original supported perfect K-zero functor with
the finite stage-zero group. Naturality retains every original coefficient pair
square. The only compactness used here concerns the ambient scheme. Successor
bottoms and invertibility of supported transitions are separate assertions.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Actual supported section evaluation followed by the original perfect inclusion comparison. -/
def boundedFlatCoefficientSupportedPerfectKEquiv (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientSupportedModel f a).waldhausen.K n ≃*
      PerfectSupportedK (schemeMap f a) n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).trans
    (boundedFlatPerfectSupportedKEquiv (schemeMap f a) n)

/-- The original supported evaluation preserves the exact coefficient pullback K-map. -/
theorem boundedFlatCoefficientSupportedPerfectKEquiv_naturality
    {a b : Under R} (g : a ⟶ b) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedModel f a).waldhausen.K n) :
    boundedFlatCoefficientSupportedPerfectKEquiv f b n
        (KMap (boundedFlatCoefficientSupportedModelMap f g).exact n x) =
      perfectSupportedKPullback
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).map g).unop n
          (boundedFlatCoefficientSupportedPerfectKEquiv f a n x) := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : CompactSpace (space (op Q, b)) := compactSpace_space (op Q, b)
  have he := boundedFlatCoefficientEvaluationKEquiv_natural
    (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
    (boundedFlatPerfectSupportedWaldhausen (schemeMap f a))
    (boundedFlatCoefficientSupportedSectionEquivalence (schemeMap f a))
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact (schemeMap f a))
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f a))
    (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f b))
    (boundedFlatPerfectSupportedWaldhausen (schemeMap f b))
    (boundedFlatCoefficientSupportedSectionEquivalence (schemeMap f b))
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact (schemeMap f b))
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f b))
    (boundedFlatCoefficientSupportedModelMap f g).exact
    (boundedFlatPerfectSupportedPullback_exact (boundedFlatCoefficientOpenPairMap f g))
    (by
      simp only [boundedFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedFlatCoefficientSupportedSectionReindexIso
        (schemeMap f a) (schemeMap f b) (𝟙 (op Q), g)
        (coefficientMap P g) (boundedFlatCoefficientOpenSquare f g)) n x
  have hp := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat
    ((boundedFlatCoefficientQuasiCompactOpenPairRow f).map g).unop n)
    (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n x)
  exact (congrArg (boundedFlatPerfectSupportedKEquiv (schemeMap f b) n) he).trans hp.symm

/-- Original supported perfect K-zero is the actual stage-zero stable group. -/
def boundedFlatCoefficientSupportedBassBottomZeroIso (a : Under R) :
    (boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKZeroFunctor).obj a ≅
      (boundedFlatCoefficientSupportedBassDiagram f 0 ⋙ stableHomotopyFunctor 0).obj a :=
  ((boundedFlatCoefficientSupportedPerfectKEquiv f a 0).symm.toAdditive.trans
    (modelKStableEquiv (boundedFlatCoefficientSupportedModel f a) 0)).toAddCommGrpIso

/-- Every original coefficient pair pullback is preserved by the stage-zero comparison. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedBassBottomZeroIso_naturality
    {a b : Under R} (g : a ⟶ b) :
    (boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKZeroFunctor).map g ≫
        (boundedFlatCoefficientSupportedBassBottomZeroIso f b).hom =
      (boundedFlatCoefficientSupportedBassBottomZeroIso f a).hom ≫
        (boundedFlatCoefficientSupportedBassDiagram f 0 ⋙ stableHomotopyFunctor 0).map g := by
  ext x
  let y := (boundedFlatCoefficientSupportedPerfectKEquiv f a 0).symm x.toMul
  have hy : boundedFlatCoefficientSupportedPerfectKEquiv f a 0 y = x.toMul :=
    (boundedFlatCoefficientSupportedPerfectKEquiv f a 0).apply_symm_apply x.toMul
  have hn := boundedFlatCoefficientSupportedPerfectKEquiv_naturality f g 0 y
  rw [hy] at hn
  have hi := congrArg (boundedFlatCoefficientSupportedPerfectKEquiv f b 0).symm hn
  rw [MulEquiv.symm_apply_apply] at hi
  change modelKStableEquiv (boundedFlatCoefficientSupportedModel f b) 0
      (Additive.ofMul ((boundedFlatCoefficientSupportedPerfectKEquiv f b 0).symm
        (perfectSupportedKPullback
          ((boundedFlatCoefficientQuasiCompactOpenPairRow f).map g).unop 0 x.toMul))) =
    (stableHomotopyFunctor 0).map (prespectrumMap (boundedFlatCoefficientSupportedModelMap f g))
      (modelKStableEquiv (boundedFlatCoefficientSupportedModel f a) 0 (Additive.ofMul y))
  rw [← hi]
  exact modelKStableEquiv_naturality (boundedFlatCoefficientSupportedModelMap f g) 0 y

/-- The original supported K-zero functor naturally computes the actual finite bottom. -/
def boundedFlatCoefficientSupportedBassBottomZeroNatIso :
    boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKZeroFunctor ≅
      boundedFlatCoefficientSupportedBassDiagram f 0 ⋙ stableHomotopyFunctor 0 :=
  NatIso.ofComponents (boundedFlatCoefficientSupportedBassBottomZeroIso f)
    (fun g ↦ boundedFlatCoefficientSupportedBassBottomZeroIso_naturality f g)

end Quillen.PerfectComplexes
