/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenGradedSectionDiagram

/-!
# The original change of full-open section weaknesses on prespectra

The actual identity-on-sections Model transformation is realized by the existing iterated-S
prespectrum functor. Its components retain the original inherited zero and coefficient maps.
Compactness is precisely the hypothesis of the accepted quotient-graded coefficient diagram.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The original change of weakness is realized without changing any section objects or maps. -/
def boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation :
    boundedFlatAffineFullOpenSectionPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j :=
  Functor.whiskerRight (boundedFlatAffineFullOpenSectionGradingModelTransformation j)
    prespectrumFunctor

/-- Each component is the original iterated-S map of the actual changeWeak Model arrow. -/
theorem boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation_app (a : Under R) :
    (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a =
      prespectrumMap (boundedFlatAffineFullOpenSectionGradingModelMap j a) := rfl

end Quillen.PerfectComplexes
