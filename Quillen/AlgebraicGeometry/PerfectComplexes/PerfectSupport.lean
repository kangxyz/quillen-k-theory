/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Perfect


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory
public import Quillen.AlgebraicGeometry.PerfectComplexes.Support

/-!
# Locally perfect complexes supported away from an open

The support predicate is actual acyclicity after open restriction.
Extension closure is proved from local perfectness and the homology long
exact sequence. This gives genuine supported connective K-groups and their
inclusion map. No homotopy-fiber or localization-sequence theorem is assumed.
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

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual Waldhausen structure on supported locally perfect complexes. -/
def perfectSupportedWaldhausen := Waldhausen.complexSubcategory (perfectSupported j)

/-- Connective S-construction K-groups of locally perfect complexes acyclic on U. -/
abbrev PerfectSupportedK (n : ℕ) := (perfectSupportedWaldhausen j).K n

/-- The canonical homomorphism forgetting the support condition. -/
def perfectSupportedKMap (n : ℕ) : PerfectSupportedK j n →* PerfectK X n :=
  Waldhausen.subcategoryKMap (perfectSupported j) (locallyPerfect X) (fun _ h ↦ h.1) n

/-- The canonical supported strict-to-local comparison, with no equivalence claim. -/
def strictSupportedToPerfectKMap (n : ℕ) : StrictSupportedK j n →* PerfectSupportedK j n :=
  Waldhausen.subcategoryKMap (strictSupported j) (perfectSupported j)
    (fun _ h ↦ ⟨locallyPerfect_of_strictPerfect h.1, h.2⟩) n

end Quillen.PerfectComplexes
