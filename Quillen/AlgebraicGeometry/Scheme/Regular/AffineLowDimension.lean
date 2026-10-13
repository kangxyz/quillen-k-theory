/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Regular.LocalLowDimension
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Canonical K-to-G comparison for regular affine schemes of dimension at most one

Every prime localization of a regular ring of dimension at most one is a
regular local ring of dimension at most one, hence a PID by the proved local
argument. Actual finite-module projective dimension is at most one locally,
therefore globally. This gives actual finite vector-bundle resolutions and
the canonical Quillen comparison.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

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
  have := RegularLocal.isDomain_of_dimension_le_one (Localization.AtPrime p.asIdeal) hd'
  have := RegularLocal.isPrincipalIdealRing_of_dimension_le_one (Localization.AtPrime p.asIdeal) hd'
  have : Module.Finite (Localization.AtPrime p.asIdeal) (M.localizedModule p.asIdeal.primeCompl) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
  exact hasProjectiveDimensionLE_one_of_pid (Localization.AtPrime p.asIdeal)
    (M.localizedModule p.asIdeal.primeCompl)

end Quillen.CoherentScheme

namespace Quillen.Scheme

/-- For a regular Noetherian ring of dimension at most one, the existing
canonical vector-bundle K-to-coherent G comparison is bijective in every
nonnegative degree. -/
theorem KToG_regular_dimension_le_one_bijective (R : CommRingCat.{u}) [IsRegularRing R]
    (hd : ringKrullDim R ≤ 1) (n : ℕ) : Function.Bijective (KToG (Spec R) n) := by
  apply SchemeSheaf.schemeKToG_bijective_of_length_one (Spec R) _ n
  intro M
  have := CoherentScheme.hasProjectiveDimensionLE_one_of_regular_dim_le_one R hd
    ((CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R).functor.obj M).obj
  exact SchemeSheaf.coherentResolution_length_le_of_projectiveDimensionLE R 1 M

/-- The actual canonical equivalence for a regular affine ring of dimension
at most one. The forward homomorphism is the existing `Scheme.KToG`. -/
def KToGRegularDimOneEquiv (R : CommRingCat.{u}) [IsRegularRing R]
    (hd : ringKrullDim R ≤ 1) (n : ℕ) : K (Spec R) n ≃* G (Spec R) n :=
  MulEquiv.ofBijective (KToG (Spec R) n) (KToG_regular_dimension_le_one_bijective R hd n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KToGRegularDimOneEquiv_coe (R : CommRingCat.{u}) [IsRegularRing R]
    (hd : ringKrullDim R ≤ 1) (n : ℕ) :
    ↑(KToGRegularDimOneEquiv R hd n) = KToG (Spec R) n := rfl

end Quillen.Scheme
