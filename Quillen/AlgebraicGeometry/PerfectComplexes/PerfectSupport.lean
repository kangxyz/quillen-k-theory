/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

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

/-- Actual locally perfect complexes with cohomological support away from U. -/
def perfectSupported : ObjectProperty (CochainComplex X.Modules ℤ) := fun K ↦
  locallyPerfect X K ∧ ((restrict j).obj K).Acyclic

instance perfectSupported_containsZero : (perfectSupported j).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, locallyPerfect_of_strictPerfect
    (strictPerfect_of_isZero (isZero_zero _)),
    HomologicalComplex.acyclic_of_isZero _ ((restrict j).map_isZero (isZero_zero _))⟩

instance perfectSupported_closedUnderIsomorphisms :
    (perfectSupported j).IsClosedUnderIsomorphisms where
  of_iso e hK := ⟨locallyPerfect_of_iso e hK.1,
    fun n ↦ (hK.2 n).of_iso ((restrict j).mapIso e)⟩

/-- The support condition is stable under actual short exact extensions. -/
theorem perfectSupported_of_shortExact {S : ShortComplex (CochainComplex X.Modules ℤ)}
    (hS : S.ShortExact) (h₁ : perfectSupported j S.X₁) (h₃ : perfectSupported j S.X₃) :
    perfectSupported j S.X₂ :=
  ⟨locallyPerfect_of_shortExact hS h₁.1 h₃.1,
    (hS.map_of_exact (restrict j)).acyclic_X₂ h₁.2 h₃.2⟩

instance perfectSupported_extensionClosed :
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed
      (perfectSupported j) where
  prop_middle := perfectSupported_of_shortExact j

instance perfectSupported_closedUnderFiniteProducts :
    (perfectSupported j).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts
    (perfectSupported j)

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

/-- Every supported object restricts to a complex quasi-isomorphic to zero. -/
theorem perfectSupported_restrict_quasiIso_zero {K : CochainComplex X.Modules ℤ}
    (hK : perfectSupported j K) :
    QuasiIso (0 : (restrict j).obj K ⟶ (0 : CochainComplex U.Modules ℤ)) := by
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt' _ n
    (HomologicalComplex.acyclic_of_isZero _ (isZero_zero _) n)).2 (hK.2 n)

end Quillen.PerfectComplexes
