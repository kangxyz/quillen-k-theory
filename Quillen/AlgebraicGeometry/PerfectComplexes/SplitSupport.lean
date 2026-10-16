/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SplitKTheory
public import Quillen.AlgebraicGeometry.PerfectComplexes.PerfectSupport

/-!
# Supported perfect K-theory with degreewise split cofibrations

The support predicate remains actual acyclicity on the specified open.
Only the cofibration convention changes. The supported structures,
forget-support maps, strict-to-local maps and change-of-cofibrations maps
are constructed without asserting a localization or equivalence theorem.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Strict-perfect supported complexes with termwise split cofibrations. -/
def splitStrictSupportedWaldhausen :=
  Waldhausen.splitComplexSubcategory (strictSupported j)

/-- Locally-perfect supported complexes with termwise split cofibrations. -/
def splitPerfectSupportedWaldhausen :=
  Waldhausen.splitComplexSubcategory (perfectSupported j)

/-- Actual supported connective strict-perfect K-groups in the split convention. -/
abbrev SplitStrictSupportedK (n : ℕ) := (splitStrictSupportedWaldhausen j).K n

/-- Actual supported connective locally-perfect K-groups in the split convention. -/
abbrev SplitPerfectSupportedK (n : ℕ) := (splitPerfectSupportedWaldhausen j).K n

/-- The strict-perfect supported change-of-cofibrations map. -/
def splitStrictSupportedToStrictSupportedKMap (n : ℕ) :
    SplitStrictSupportedK j n →* StrictSupportedK j n :=
  Waldhausen.splitComplexSubcategoryKMap (strictSupported j) n

/-- The locally-perfect supported change-of-cofibrations map. -/
def splitPerfectSupportedToPerfectSupportedKMap (n : ℕ) :
    SplitPerfectSupportedK j n →* PerfectSupportedK j n :=
  Waldhausen.splitComplexSubcategoryKMap (perfectSupported j) n

/-- Forgetting support in strict-perfect split K-theory. -/
def splitStrictSupportedKMap (n : ℕ) : SplitStrictSupportedK j n →* SplitStrictK X n :=
  Waldhausen.splitSubcategoryKMap (strictSupported j) (strictPerfect X) (fun _ h ↦ h.1) n

/-- Forgetting support in locally-perfect split K-theory. -/
def splitPerfectSupportedKMap (n : ℕ) : SplitPerfectSupportedK j n →* SplitPerfectK X n :=
  Waldhausen.splitSubcategoryKMap (perfectSupported j) (locallyPerfect X) (fun _ h ↦ h.1) n

/-- The actual supported strict-to-locally-perfect comparison in the split convention. -/
def splitStrictSupportedToPerfectKMap (n : ℕ) :
    SplitStrictSupportedK j n →* SplitPerfectSupportedK j n :=
  Waldhausen.splitSubcategoryKMap (strictSupported j) (perfectSupported j)
    (fun _ h ↦ ⟨locallyPerfect_of_strictPerfect h.1, h.2⟩) n

end Quillen.PerfectComplexes
