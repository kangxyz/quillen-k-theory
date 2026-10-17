/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedKStableComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedKGroups

/-!
# Natural original supported K-group comparison on the actual coefficient pair row

The checked all-degree original evaluation equivalence assembles into a natural isomorphism
between the original supported K-pair functor and the actual fine section stable group functor.
This transports the original common-corner and chart maps, not degree-raising scalar operations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The original supported K-pair functor naturally computes the same fine stable groups. -/
def boundedFlatCoefficientSupportedKStableNatIso (n : ℕ) :
    boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKAddFunctor n ≅
      boundedFlatCoefficientSupportedPrespectrumFunctor f ⋙ stableHomotopyFunctor (n : ℤ) :=
  NatIso.ofComponents
    (fun a => (boundedFlatCoefficientSupportedKStableEquiv f a n).toAddCommGrpIso) (by
      intro a b g
      ext x
      exact boundedFlatCoefficientSupportedKStableEquiv_naturality f g n x.toMul)

end Quillen.PerfectComplexes
