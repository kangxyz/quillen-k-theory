/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Waldhausen.SplitComplexes.Subcategory
public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory

/-!
# Degreewise split K-theory of strict and locally perfect complexes

These are the actual full categories of sheaf complexes used by the
ambient-monomorphism model, with cofibrations now required to split globally
in every degree and have a quotient in the indicated category. The
splittings need not be chain maps. Weak equivalences are actual
quasi-isomorphisms. The axioms and comparison homomorphisms are proved,
without assuming any comparison equivalence.

This addresses the cofibration-convention distinction with Thomason–Trobaugh.
It does not impose a uniform global Tor-amplitude condition on non-quasi-compact
schemes, and does not assert an identification with all of TT's conventions.
Ordinary vector-bundle short exact sequences may fail to split globally,
so their degree-zero inclusion is not asserted to be exact for this model.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- Strict-perfect complexes with degreewise split cofibrations. -/
def splitStrictWaldhausen (X : Scheme.{u}) : Waldhausen.Structure (StrictPerfect X) :=
  Waldhausen.splitComplexSubcategory (strictPerfect X)

/-- Locally perfect complexes with degreewise split cofibrations. -/
def splitPerfectWaldhausen (X : Scheme.{u}) : Waldhausen.Structure (Perfect X) :=
  Waldhausen.splitComplexSubcategory (locallyPerfect X)

/-- Genuine connective K-groups of the split-cofibration strict-perfect model. -/
abbrev SplitStrictK (X : Scheme.{u}) (n : ℕ) := (splitStrictWaldhausen X).K n

/-- Genuine connective K-groups of the split-cofibration locally-perfect model. -/
abbrev SplitPerfectK (X : Scheme.{u}) (n : ℕ) := (splitPerfectWaldhausen X).K n

/-- The canonical change-of-cofibrations comparison for strict perfect complexes. -/
def splitStrictToStrictKMap (X : Scheme.{u}) (n : ℕ) : SplitStrictK X n →* StrictK X n :=
  Waldhausen.splitComplexSubcategoryKMap (strictPerfect X) n

/-- The canonical change-of-cofibrations comparison for locally perfect complexes. -/
def splitPerfectToPerfectKMap (X : Scheme.{u}) (n : ℕ) : SplitPerfectK X n →* PerfectK X n :=
  Waldhausen.splitComplexSubcategoryKMap (locallyPerfect X) n

/-- The strict-to-locally-perfect comparison in the degreewise split convention. -/
def splitStrictToPerfectKMap (X : Scheme.{u}) (n : ℕ) :
    SplitStrictK X n →* SplitPerfectK X n :=
  Waldhausen.splitSubcategoryKMap (strictPerfect X) (locallyPerfect X)
    (fun _ h ↦ locallyPerfect_of_strictPerfect h) n

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Open restriction preserves the degreewise splittings themselves. -/
theorem degreewiseSplitMono_restrict {K L : Complex X} {f : K ⟶ L}
    (hf : CochainComplex.degreewiseSplitMono f) :
    CochainComplex.degreewiseSplitMono ((restrict j).map f) := by
  intro n
  let : IsSplitMono (f.f n) := hf n
  change IsSplitMono ((Scheme.Modules.restrictFunctor j).map (f.f n))
  infer_instance

/-- Actual strict-perfect restriction is exact with split cofibrations. -/
theorem splitStrictRestrict_waldhausenExact :
    Waldhausen.IsExact (splitStrictWaldhausen X).cof (splitStrictWaldhausen X).weq
      (splitStrictWaldhausen U).cof (splitStrictWaldhausen U).weq (strictRestrict j) where
  zero h := (strictRestrict j).map_isZero h
  cofibration f hf := ⟨(strictRestrict_waldhausenExact j).cofibration f hf.1,
    degreewiseSplitMono_restrict j hf.2⟩
  weak f hf := (strictRestrict_waldhausenExact j).weak f hf
  pushout hi h := (strictRestrict_waldhausenExact j).pushout hi.1 h

/-- Actual locally-perfect restriction is exact with split cofibrations. -/
theorem splitPerfectRestrict_waldhausenExact :
    Waldhausen.IsExact (splitPerfectWaldhausen X).cof (splitPerfectWaldhausen X).weq
      (splitPerfectWaldhausen U).cof (splitPerfectWaldhausen U).weq (perfectRestrict j) where
  zero h := (perfectRestrict j).map_isZero h
  cofibration f hf := ⟨(perfectRestrict_waldhausenExact j).cofibration f hf.1,
    degreewiseSplitMono_restrict j hf.2⟩
  weak f hf := (perfectRestrict_waldhausenExact j).weak f hf
  pushout hi h := (perfectRestrict_waldhausenExact j).pushout hi.1 h

/-- The genuine open-restriction homomorphism for split strict-perfect K-theory. -/
def splitStrictKRestrict (n : ℕ) : SplitStrictK X n →* SplitStrictK U n :=
  Waldhausen.KMap (splitStrictRestrict_waldhausenExact j) n

/-- The genuine open-restriction homomorphism for split locally-perfect K-theory. -/
def splitPerfectKRestrict (n : ℕ) : SplitPerfectK X n →* SplitPerfectK U n :=
  Waldhausen.KMap (splitPerfectRestrict_waldhausenExact j) n

end Quillen.PerfectComplexes
