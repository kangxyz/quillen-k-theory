/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Regular.AffineProjective
public import Quillen.AlgebraicGeometry.Scheme.Regular.FiniteProjectiveResolution
public import Quillen.Resolution.Transport

/-!
# Actual finite locally free resolutions on principal-ideal affine schemes

The module resolutions are carried by the genuine tilde equivalence to
short exact coherent sheaf sequences. The augmentation is transported along
the equivalence's unit, so the resolved object is the original coherent
sheaf. All terms are actual finite locally free sheaves.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

variable (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]

/-- The actual vector-bundle condition on an object of the coherent category. -/
def coherentVectorBundle : ObjectProperty (CoherentScheme.FiniteTypeSheaves X) :=
  fun M => IsFiniteLocallyFree X M.obj

instance coherentVectorBundle_isoClosed : (coherentVectorBundle X).IsClosedUnderIsomorphisms where
  of_iso e h := (finiteLocallyFree X).prop_of_iso
    ((CoherentScheme.finiteTypeSheavesToModules X).mapIso e) h

instance coherentVectorBundle_extensionClosed :
    (CoherentScheme.coherentExactStructure X).IsExtensionClosed (coherentVectorBundle X) where
  prop_middle {S} hS h₁ h₃ := by
    have : IsFiniteLocallyFree X (S.map (CoherentScheme.finiteTypeSheavesToModules X)).X₁ := h₁
    have : IsFiniteLocallyFree X (S.map (CoherentScheme.finiteTypeSheavesToModules X)).X₃ := h₃
    exact finiteLocallyFree_of_shortExact
      ((CoherentScheme.coherent_shortExact_iff X S).mp hS)

instance coherentVectorBundle_containsZero : (coherentVectorBundle X).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    exact finiteLocallyFree_of_isZero
      ((CoherentScheme.finiteTypeSheavesToModules X).map_isZero (isZero_zero _))

instance coherentVectorBundle_closedUnderFiniteProducts :
    (coherentVectorBundle X).IsClosedUnderFiniteProducts :=
  (CoherentScheme.coherentExactStructure X).extensionClosed_finiteProducts (coherentVectorBundle X)

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- The actual affine coherent/module equivalence identifies vector bundles
with finite projective modules, with no homological or K-theory assumption. -/
theorem coherentVectorBundle_iff_projective (M : CoherentScheme.FiniteTypeSheaves (Spec R)) :
    coherentVectorBundle (Spec R) M ↔ CoherentScheme.finiteProjective R
      ((CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R).functor.obj M) := by
  have h := (CoherentScheme.affineLocallyFiniteType_spec_iff R M.obj).mp M.property
  have : M.obj.IsQuasicoherent := h.1
  have : Module.Finite R (moduleSpecΓFunctor.obj M.obj) := h.2
  have : IsIso M.obj.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M.obj
  let e : tilde (moduleSpecΓFunctor.obj M.obj) ≅ M.obj := asIso M.obj.fromTildeΓ
  change IsFiniteLocallyFree (Spec R) M.obj ↔ Module.Projective R (moduleSpecΓFunctor.obj M.obj)
  exact (finiteLocallyFree_iff_of_iso e).symm.trans
    (finiteLocallyFree_tilde_iff_projective R (moduleSpecΓFunctor.obj M.obj))

/-- Kernels of epimorphisms between vector bundles are vector bundles on an
actual affine noetherian scheme, by the projective-module characterization. -/
instance coherentVectorBundle_kernelClosed_affine :
    (CoherentScheme.coherentExactStructure (Spec R)).IsKernelClosed
      (coherentVectorBundle (Spec R)) where
  prop_kernel {S} hS h₂ h₃ := by
    let E := CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R
    let T := S.map E.functor
    have hT : T.ShortExact := hS.map_of_exact E.functor
    have h₂' : CoherentScheme.finiteProjective R T.X₂ :=
      (coherentVectorBundle_iff_projective R S.X₂).mp h₂
    have h₃' : CoherentScheme.finiteProjective R T.X₃ :=
      (coherentVectorBundle_iff_projective R S.X₃).mp h₃
    exact (coherentVectorBundle_iff_projective R S.X₁).mpr
      (ExactStructure.IsKernelClosed.prop_kernel
        (E := CoherentScheme.finiteModuleExactStructure R) hT h₂' h₃')

instance finiteTypeSheavesSpecModuleEquivalence_inverse_additive :
    (CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R).inverse.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Associated sheaves of finite modules, landing in the genuine global
coherent category and retaining actual short exact sequences. -/
def finiteModuleTildeExact :
    ExactFunctor (CoherentScheme.finiteModuleExactStructure.{u, u} R)
      (CoherentScheme.coherentExactStructure (Spec R)) where
  toFunctor := (CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R).inverse
  map_conflation _ h := h.map_of_exact _

/-- Tilde carries finite free modules to actual coherent vector bundles. -/
theorem finiteModuleTilde_finiteFree (M : CoherentScheme.FiniteModule.{u, u} R)
    (hM : Module.Free R M.obj) :
    coherentVectorBundle (Spec R) ((finiteModuleTildeExact R).toFunctor.obj M) := by
  change IsFiniteLocallyFree (Spec R) (tilde M.obj)
  have := hM
  exact finiteLocallyFree_tilde_of_finite_free R M.obj

/-- Tilde carries finite projective modules to actual coherent vector bundles. -/
theorem finiteModuleTilde_finiteProjective (M : CoherentScheme.FiniteModule.{u, u} R)
    (hM : CoherentScheme.finiteProjective R M) :
    coherentVectorBundle (Spec R) ((finiteModuleTildeExact R).toFunctor.obj M) := by
  change IsFiniteLocallyFree (Spec R) (tilde M.obj)
  have : Module.Projective R M.obj := hM
  exact finiteLocallyFree_tilde_of_finite_projective R M.obj

/-- An actual projective-dimension bound on a coherent sheaf's module of
global sections produces a genuine finite locally free resolution of that
same sheaf, with that bound. -/
theorem coherentResolution_length_le_of_projectiveDimensionLE (n : ℕ)
    (M : CoherentScheme.FiniteTypeSheaves (Spec R))
    [HasProjectiveDimensionLE
      ((CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R).functor.obj M).obj n] :
    ∃ T : (CoherentScheme.coherentExactStructure (Spec R)).FiniteResolution
        (coherentVectorBundle (Spec R)) M, T.length ≤ n := by
  let E := CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R
  obtain ⟨T, hT⟩ := CoherentScheme.finiteProjectiveResolution_length_le R n (E.functor.obj M)
  let T' := (finiteModuleTildeExact R).mapFiniteResolution
    (finiteModuleTilde_finiteProjective R) T
  let T'' := T'.ofIso (E.unitIso.app M).symm
  refine ⟨T'', ?_⟩
  simpa [T'', T'] using hT

/-- Every coherent sheaf on the spectrum of a PID has an actual admissible
finite locally free resolution of length at most one. -/
theorem coherentResolution_length_le_one_of_pid [IsDomain R] [IsPrincipalIdealRing R]
    (M : CoherentScheme.FiniteTypeSheaves (Spec R)) :
    ∃ T : (CoherentScheme.coherentExactStructure (Spec R)).FiniteResolution
        (coherentVectorBundle (Spec R)) M, T.length ≤ 1 := by
  let E := CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R
  obtain ⟨T, hT⟩ := CoherentScheme.finiteFreeResolution_length_le_one_of_pid R (E.functor.obj M)
  let T' := (finiteModuleTildeExact R).mapFiniteResolution
    (finiteModuleTilde_finiteFree R) T
  let T'' := T'.ofIso (E.unitIso.app M).symm
  refine ⟨T'', ?_⟩
  simpa [T'', T'] using hT

/-- The genuine geometric finite-vector-bundle-resolution hypothesis is
fully discharged for the spectrum of a principal ideal domain. -/
theorem coherentResolutionHypothesis_of_pid [IsDomain R] [IsPrincipalIdealRing R] :
    (CoherentScheme.coherentExactStructure (Spec R)).ResolutionHypothesis
      (coherentVectorBundle (Spec R)) := by
  intro M
  obtain ⟨T, _⟩ := coherentResolution_length_le_one_of_pid R M
  exact ⟨T⟩

end Quillen.SchemeSheaf
