/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Resolution

/-!
# Resolution theorem examples

Uses length-one admissible resolutions and the finite-resolution hypothesis for
an object property with the stated closure conditions. The examples record
bijectivity in every connective degree and identify each equivalence's forward
map with the original inclusion.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Consumer
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : Quillen.ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts] [E.IsKernelClosed P]

/-- Downstream clients obtain the canonical all-degree resolution comparison
from actual short admissible resolutions, without supplying homotopy data. -/
theorem length_one_resolution (h : ∀ X, E.ResolutionLength P 1 X) (n : ℕ) :
    Function.Bijective (Quillen.Resolution.inclusionKMap E P n) :=
  Quillen.Resolution.inclusionKMap_bijective_of_length_one E P h n

/-- The public equivalence has exactly the original inclusion as forward map. -/
theorem length_one_resolution_forward (h : ∀ X, E.ResolutionLength P 1 X) (n : ℕ) :
    (Quillen.Resolution.KEquivOfLengthOne E P h n).toMonoidHom =
      Quillen.Resolution.inclusionKMap E P n := rfl

/-- The actual resolution length may vary with the ambient object. -/
theorem finite_resolution (h : E.ResolutionHypothesis P) (n : ℕ) :
    Function.Bijective (Quillen.Resolution.inclusionKMap E P n) :=
  Quillen.Resolution.inclusionKMap_bijective E P h n

/-- Even the unrestricted equivalence retains the original canonical map. -/
theorem finite_resolution_forward (h : E.ResolutionHypothesis P) (n : ℕ) :
    (Quillen.Resolution.KEquiv E P h n).toMonoidHom =
      Quillen.Resolution.inclusionKMap E P n := rfl
end Consumer
