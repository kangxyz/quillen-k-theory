/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.SplitKTheory
public import Quillen.Waldhausen.SplitComplexes.FactorizationSubcategory
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
/-!
# Actual split-cofibration factorizations of perfect complexes

Local perfectness is closed under the actual mapping cone by the proved
local strict-model theorem for distinguished triangles. Consequently the
explicit factorization `K → Cone(id K) ⊞ L → L`, including its quotient
`Cone(-f)`, stays in both strict-perfect and locally-perfect complexes.
This establishes factorization input for future approximation arguments,
without assuming or asserting a K-theory comparison equivalence.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex

universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- Every map of strict-perfect complexes has the actual split-cofibration
factorization, with strict-perfect middle object and quotient. -/
theorem exists_splitStrict_factorization {X : Scheme.{u}} {K L : StrictPerfect X}
    (f : K ⟶ L) :
    ∃ (M : StrictPerfect X) (i : K ⟶ M) (p : M ⟶ L),
      (splitStrictWaldhausen X).cof i ∧ (splitStrictWaldhausen X).weq p ∧ i ≫ p = f :=
  Waldhausen.SplitFactorization.exists_subcategory_factorization (strictPerfect X)
    (fun hK hL f ↦ strictPerfect_mappingCone hK hL f) f

/-- Every map of locally-perfect complexes has the actual split-cofibration
factorization, with locally-perfect middle object and quotient. -/
theorem exists_splitPerfect_factorization {X : Scheme.{u}} {K L : Perfect X}
    (f : K ⟶ L) :
    ∃ (M : Perfect X) (i : K ⟶ M) (p : M ⟶ L),
      (splitPerfectWaldhausen X).cof i ∧ (splitPerfectWaldhausen X).weq p ∧ i ≫ p = f :=
  Waldhausen.SplitFactorization.exists_subcategory_factorization (locallyPerfect X)
    (fun hK hL f ↦ locallyPerfect_mappingCone hK hL f) f

end Quillen.PerfectComplexes
