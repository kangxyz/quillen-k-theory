/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

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

/-- A strict perfect complex has support outside the open when its actual
restriction is acyclic in every degree. -/
def strictSupported : ObjectProperty (Complex X) := fun K ↦
  strictPerfect X K ∧ ((restrict j).obj K).Acyclic

instance strictSupported_containsZero : (strictSupported j).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, strictPerfect_of_isZero (isZero_zero _),
    HomologicalComplex.acyclic_of_isZero _ ((restrict j).map_isZero (isZero_zero _))⟩

instance strictSupported_closedUnderIsomorphisms :
    (strictSupported j).IsClosedUnderIsomorphisms where
  of_iso e hK := ⟨strictPerfect_of_iso e hK.1,
    fun n ↦ (hK.2 n).of_iso ((restrict j).mapIso e)⟩

/-- Supported strict perfect complexes are closed under actual extensions. -/
theorem strictSupported_of_shortExact {S : ShortComplex (Complex X)}
    (hS : S.ShortExact) (h₁ : strictSupported j S.X₁) (h₃ : strictSupported j S.X₃) :
    strictSupported j S.X₂ :=
  ⟨strictPerfect_of_shortExact hS h₁.1 h₃.1,
    (hS.map_of_exact (restrict j)).acyclic_X₂ h₁.2 h₃.2⟩

instance strictSupported_extensionClosed :
    (abelianExactStructure (Complex X)).IsExtensionClosed (strictSupported j) where
  prop_middle := strictSupported_of_shortExact j

instance strictSupported_closedUnderFiniteProducts :
    (strictSupported j).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (Complex X)).extensionClosed_finiteProducts (strictSupported j)

/-- Restriction of a supported object is linked to zero by an actual
quasi-isomorphism. This is the input for a future nullhomotopy theorem. -/
theorem strictSupported_restrict_quasiIso_zero {K : Complex X} (hK : strictSupported j K) :
    QuasiIso (0 : (restrict j).obj K ⟶ (0 : Complex U)) := by
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt' _ n
    (HomologicalComplex.acyclic_of_isZero _ (isZero_zero _) n)).2 (hK.2 n)

/-- The genuine Waldhausen structure on supported strict perfect complexes. -/
def strictSupportedWaldhausen := Waldhausen.complexSubcategory (strictSupported j)

/-- Connective K-groups of strict perfect complexes acyclic on the open. -/
abbrev StrictSupportedK (n : ℕ) := (strictSupportedWaldhausen j).K n

/-- Forgetting the support condition gives its canonical K-map. -/
def strictSupportedKMap (n : ℕ) : StrictSupportedK j n →* StrictK X n :=
  Waldhausen.subcategoryKMap (strictSupported j) (strictPerfect X) (fun _ h ↦ h.1) n

end Quillen.PerfectComplexes
