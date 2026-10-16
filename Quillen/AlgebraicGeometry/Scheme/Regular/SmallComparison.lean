/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.SmallModel

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.Affine
public import Quillen.Resolution.LengthOne
public import Quillen.KTheory.Equivalence
public import Quillen.AlgebraicGeometry.Scheme.Comparison.KToG

/-! # Applying the resolution theorem to the canonical scheme comparison -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules
variable (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]

instance vectorBundleSmallLiftExact_mapQ_isEquivalence :
    (vectorBundleSmallLiftExact X).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro A B i hi
    rw [← vectorBundleSmallLift_ofEquivalence X]
    exact (CategoryTheory.ExactCategory.ExactStructure.ofEquivalence_inflation_iff _ _ i).mpr hi
  · intro A B p hp
    rw [← vectorBundleSmallLift_ofEquivalence X]
    exact (CategoryTheory.ExactCategory.ExactStructure.ofEquivalence_deflation_iff _ _ p).mpr hp

/-- Quillen's proved length-one theorem applies to the original canonical
scheme K-to-G map. The only hypothesis is the actual algebraic resolution
condition, with the exact subcategory's kernel closure. -/
theorem schemeKToG_bijective_of_length_one
    [(AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).IsKernelClosed
      (coherentVectorBundle X)]
    (h : ∀ M, (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).ResolutionLength
      (coherentVectorBundle X) 1 M) (n : ℕ) :
    Function.Bijective (schemeKToG X n) := by
  have h₁ := (vectorBundleSmallLiftExact X).KMap_bijective_of_mapQ_isEquivalence n
  have h₂ := Resolution.inclusionKMap_bijective_of_length_one
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel
      (coherentSmallVectorBundle X)
    (coherentSmallResolutionLength X 1 h) n
  change Function.Bijective ((vectorBundleToCoherentExact X).smallModel.KMap n)
  rw [← vectorBundleSmall_factor X, CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  exact h₂.comp h₁

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme
variable (R : CommRingCat.{u}) [IsDomain R] [IsPrincipalIdealRing R]

/-- Over the spectrum of a principal ideal domain, the canonical inclusion
of vector bundles into coherent sheaves induces an isomorphism on every
nonnegative K-group. All resolution hypotheses are proved from the PID
submodule theorem. -/
theorem KToG_pid_bijective (n : ℕ) : Function.Bijective (KToG (Spec R) n) :=
  AlgebraicGeometry.Scheme.Modules.schemeKToG_bijective_of_length_one (Spec R)
    (AlgebraicGeometry.Scheme.Modules.coherentResolution_length_le_one_of_pid R) n

/-- The actual canonical K-to-G equivalence for a principal ideal domain. -/
def KToGPIDEquiv (n : ℕ) : K (Spec R) n ≃* G (Spec R) n :=
  MulEquiv.ofBijective (KToG (Spec R) n) (KToG_pid_bijective R n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KToGPIDEquiv_coe (n : ℕ) :
    ↑(KToGPIDEquiv R n) = KToG (Spec R) n := rfl

end AlgebraicGeometry.Scheme
