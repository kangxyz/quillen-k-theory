/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Quillen.Aglib.RingTheory.RegularLocalRing.LowDimension
public import Quillen.Aglib.RingTheory.RegularLocalRing.ProjectiveDimension
public import Quillen.Aglib.Algebra.Homology.ModuleCat.FiniteProjectiveResolution

/-!
# Finite-module bounds on regular rings

Finite modules over a PID have projective dimension at most one; localization gives the same
bound on dimension-one regular rings and a stated dimension bound on finite-dimensional
regular rings.
-/
@[expose] public section

open ModuleCat

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- The finite-free syzygy theorem over a PID gives the independent
Ext-vanishing bound, without assuming projective dimension. -/
theorem hasProjectiveDimensionLE_one_of_pid (R : Type u) [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] (M : ModuleCat.{u} R) [Module.Finite R M] :
    HasProjectiveDimensionLE M 1 := by
  let N : FiniteModule.{u, u} R := ⟨M, (show Module.Finite R M from inferInstance)⟩
  obtain ⟨K, P, i, p, w, hfree, hS⟩ := exists_finiteFree_shortExact R N
  have : Module.Free R P.obj := hfree
  have : Module.Free R K.obj := free_syzygy_of_pid R (ShortComplex.mk i p w) hS
  let S := (ShortComplex.mk i p w).map (finiteModule R).ι
  have hS' : S.ShortExact := (finiteModule_shortExact_iff R _).mp hS
  have hP : Projective S.X₂ := by
    change Projective P.obj
    infer_instance
  have hK : HasProjectiveDimensionLT S.X₁ 1 := by
    change HasProjectiveDimensionLT K.obj 1
    infer_instance
  exact (hS'.hasProjectiveDimensionLT_X₃_iff 0 hP).mpr hK

/-- Every finite module over an actual regular ring of dimension at most one
has projective dimension at most one. No regularity-to-resolution implication
is left as a hypothesis. -/
theorem hasProjectiveDimensionLE_one_of_regular_dim_le_one
    (R : Type u) [CommRing R] [IsRegularRing R] (hd : ringKrullDim R ≤ 1)
    (M : ModuleCat.{u} R) [Module.Finite R M] : HasProjectiveDimensionLE M 1 := by
  apply (ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum 1 M).mpr
  intro p
  have hd' : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans hd
  have := Quillen.RegularLocal.isDomain_of_dimension_le_one (Localization.AtPrime p.asIdeal) hd'
  have := Quillen.RegularLocal.isPrincipalIdealRing_of_dimension_le_one
    (Localization.AtPrime p.asIdeal) hd'
  have : Module.Finite (Localization.AtPrime p.asIdeal) (M.localizedModule p.asIdeal.primeCompl) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
  exact hasProjectiveDimensionLE_one_of_pid (Localization.AtPrime p.asIdeal)
    (M.localizedModule p.asIdeal.primeCompl)

end AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- A uniform dimension bound on an actual regular ring bounds the projective
dimension of all finite modules, by the proved regular-local theorem. -/
theorem hasProjectiveDimensionLE_of_regular_dimension_le
    (R : Type u) [CommRing R] [IsRegularRing R] (d : ℕ) (hd : ringKrullDim R ≤ (d : ℕ))
    (M : ModuleCat.{u} R) [Module.Finite R M] : HasProjectiveDimensionLE M d := by
  apply (ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum d M).mpr
  intro p
  have hd' : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ (d : ℕ) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans hd
  have : Module.Finite (Localization.AtPrime p.asIdeal) (M.localizedModule p.asIdeal.primeCompl) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
  exact Quillen.RegularLocal.hasProjectiveDimensionLE_of_regularLocal_dimension_le
    (Localization.AtPrime p.asIdeal) d hd' (M.localizedModule p.asIdeal.primeCompl)

end AlgebraicGeometry.Scheme.Modules.Coherent
