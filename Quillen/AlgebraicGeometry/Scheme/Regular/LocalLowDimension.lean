/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Regular.SmallComparison
public import Quillen.Algebra.RegularLocal.LowDimension

/-!
# Canonical K-to-G comparison from low-dimensional local regularity

The algebra-layer low-dimensional regular-local results derive the required
field and principal ideal domain structures from mathlib's actual regularity
definition. The dimension-one domain step uses a principal maximal ideal and
Krull intersection. No projective-dimension or resolution hypothesis is imposed.
The endpoints here use the original canonical scheme K-to-G homomorphism.
-/
@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry IsLocalRing

namespace Quillen.Scheme

/-- The canonical comparison for a zero-dimensional regular local ring.
The required field structure is derived from regularity. -/
theorem KToG_regularLocal_dimension_zero_bijective (R : CommRingCat.{u})
    [IsRegularLocalRing R] (h : ringKrullDim R = 0) (n : ℕ) :
    Function.Bijective (KToG (Spec R) n) := by
  let := (RegularLocal.isField_of_regularLocal_dimension_zero R h).toField
  exact KToG_field_bijective R n

/-- The canonical comparison for a regular local ring of dimension at
most one. Both its domain property and finite resolutions are derived. -/
theorem KToG_regularLocal_dimension_le_one_bijective (R : CommRingCat.{u})
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) (n : ℕ) :
    Function.Bijective (KToG (Spec R) n) := by
  have := RegularLocal.isDomain_of_dimension_le_one R h
  have := RegularLocal.isPrincipalIdealRing_of_dimension_le_one R h
  exact KToG_pid_bijective R n

/-- The low-dimensional regular-local comparison, with the original
canonical K-to-G homomorphism as its forward map. -/
def KToGRegularLocalDimOneEquiv (R : CommRingCat.{u})
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) (n : ℕ) :
    K (Spec R) n ≃* G (Spec R) n :=
  MulEquiv.ofBijective (KToG (Spec R) n) (KToG_regularLocal_dimension_le_one_bijective R h n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KToGRegularLocalDimOneEquiv_coe (R : CommRingCat.{u})
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) (n : ℕ) :
    ↑(KToGRegularLocalDimOneEquiv R h n) = KToG (Spec R) n := rfl

end Quillen.Scheme
