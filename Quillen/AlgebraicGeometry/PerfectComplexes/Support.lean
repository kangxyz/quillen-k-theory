/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Strict


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.Restriction
public import Quillen.Waldhausen.SubcategoryInclusion

/-!
# Strict perfect complexes supported away from an open

Support is expressed as actual acyclicity after open restriction. Extension
closure follows from the homology long exact sequence, giving genuine
supported S-construction K-groups and their inclusion map. No localization
sequence is asserted; the all-perfect nonconnective theorem is separate.
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

/-- The genuine Waldhausen structure on supported strict perfect complexes. -/
def strictSupportedWaldhausen := Waldhausen.complexSubcategory (strictSupported j)

/-- Connective K-groups of strict perfect complexes acyclic on the open. -/
abbrev StrictSupportedK (n : ℕ) := (strictSupportedWaldhausen j).K n

/-- Forgetting the support condition gives its canonical K-map. -/
def strictSupportedKMap (n : ℕ) : StrictSupportedK j n →* StrictK X n :=
  Waldhausen.subcategoryKMap (strictSupported j) (strictPerfect X) (fun _ h ↦ h.1) n

end Quillen.PerfectComplexes
