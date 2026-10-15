/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Algebra.RegularLocal.Parameters
public import Quillen.Algebra.RegularLocal.QuotientLifting

/-!
# Finite projective dimension over regular local rings

The dimension bound is proved from mathlib's embedding-dimension definition
of regularity. A genuine regular parameter reduces dimension; quotient
exactness and Nakayama lift finite-free syzygies. No finite-projective-
dimension or resolution hypothesis on the original regular ring is assumed.
-/
@[expose] public section

open ModuleCat

open AlgebraicGeometry.Scheme

noncomputable section
universe u
open CategoryTheory IsLocalRing
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.RegularLocal

/-- Every finite module over a regular local ring of dimension `d` has
projective dimension at most `d`, proved by regular-parameter induction. -/
theorem hasProjectiveDimensionLE_of_regularLocal_dimension
    (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = (d : ℕ)) (M : ModuleCat.{u} R) [Module.Finite R M] :
    HasProjectiveDimensionLE M d := by
  induction d generalizing R with
  | zero =>
    have hf := isField_of_regularLocal_dimension_zero R (by simpa using hd)
    let := hf.toField
    infer_instance
  | succ d ih =>
    obtain ⟨x, hx, hxR, hq, hdim⟩ := exists_regular_parameter R d hd
    have := hq
    apply hasProjectiveDimensionLE_of_quotientRingBound R x hx hxR d _ M
    intro N hN
    have := hN
    exact ih (R ⧸ Ideal.span {x}) hdim N

/-- Finite modules over an actual regular local ring have finite projective
dimension, with a bound furnished by its maximal-ideal generator count. -/
theorem projectiveDimension_ne_top_of_regularLocal
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : projectiveDimension M ≠ ⊤ := by
  apply (projectiveDimension_ne_top_iff M).mpr
  exact ⟨(maximalIdeal R).spanFinrank,
    hasProjectiveDimensionLE_of_regularLocal_dimension (maximalIdeal R).spanFinrank R
      IsRegularLocalRing.spanFinrank_maximalIdeal.symm M⟩

/-- The regular-local bound can be enlarged to any stated bound on its
Krull dimension. -/
theorem hasProjectiveDimensionLE_of_regularLocal_dimension_le
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ) (hd : ringKrullDim R ≤ (d : ℕ))
    (M : ModuleCat.{u} R) [Module.Finite R M] : HasProjectiveDimensionLE M d := by
  have he := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have hn : (maximalIdeal R).spanFinrank ≤ d := by exact_mod_cast he.trans_le hd
  have := hasProjectiveDimensionLE_of_regularLocal_dimension (maximalIdeal R).spanFinrank R
    he.symm M
  exact hasProjectiveDimensionLT_of_ge M ((maximalIdeal R).spanFinrank + 1) (d + 1)
    (Nat.succ_le_succ hn)

/-- The resulting finite projective resolution is an actual admissible conflation
tower, extracted from the proved projective-dimension theorem. -/
theorem finiteProjectiveResolution_of_regularLocal
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.FiniteModule.{u, u} R) :
    Nonempty ((ModuleCat.finiteModuleExactStructure R).FiniteResolution
      (AlgebraicGeometry.Scheme.Modules.Coherent.finiteProjective R) M) :=
  Modules.Coherent.nonempty_finiteProjectiveResolution_of_projectiveDimension_ne_top R M
    (projectiveDimension_ne_top_of_regularLocal R M.obj)

end Quillen.RegularLocal
