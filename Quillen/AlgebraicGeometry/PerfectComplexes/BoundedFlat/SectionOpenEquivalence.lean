/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenStructure
public import Quillen.Waldhausen.Fibration.InverseImageWeakEquivalence

/-!
# The actual relative-open section evaluation equivalence

The inverse of original evaluation preserves the genuine open-detected weak class by its
actual counit. Both directions are exact for the same original relative-open structures.
The target remains the relative model on the ambient scheme, with no full-open identification.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- The original evaluation inverse is exact for the actual relative-open section weak class. -/
theorem boundedFlatAffineSectionOpenEquivalence_inverse_exact :
    IsExact (boundedFlatPerfectOpenWaldhausen j).cof (boundedFlatPerfectOpenWaldhausen j).weq
      (boundedFlatAffineSectionOpenWaldhausen j).cof
      (boundedFlatAffineSectionOpenWaldhausen j).weq
      (boundedFlatAffineSectionEquivalence R).inverse :=
  Structure.withInverseImageWeak_inverse_exact (boundedFlatAffineSectionEquivalence R)
    (boundedFlatAffineOriginalEvaluation_exact R)
    (boundedFlatAffineSectionEquivalence_inverse_exact R) (boundedFlatPerfectOpenNested j)

end Quillen.PerfectComplexes
