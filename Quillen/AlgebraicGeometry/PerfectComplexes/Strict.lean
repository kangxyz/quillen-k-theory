/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Strict
public import Quillen.Waldhausen.ComplexSubcategory

/-! # Waldhausen structure and K-groups of native strict perfect complexes

The bounded finite-locally-free predicate and its full chain category come from
Aglib. This file supplies the application Waldhausen structure and K-groups.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules.Complex

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- The genuine quasi-isomorphism Waldhausen structure on strict perfect
complexes, with all axioms derived from the preceding closure proofs. -/
def strictWaldhausen (X : Scheme.{u}) : Waldhausen.Structure (StrictPerfect X) :=
  Waldhausen.complexSubcategory (strictPerfect X)

/-- Connective S-construction K-groups of strict perfect complexes.
These are not defined using the ordinary Q-category of complexes. -/
abbrev StrictK (X : Scheme.{u}) (n : ℕ) := (strictWaldhausen X).K n

end Quillen.PerfectComplexes
