/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Field
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases
public import Quillen.Aglib.Algebra.Homology.ModuleCat.FiniteProjectiveResolution
public import Quillen.Aglib.CategoryTheory.ExactCategory.Resolution.Transport

/-!
# Actual finite locally free resolutions on principal-ideal affine schemes

The module resolutions are carried by the genuine tilde equivalence to
short exact coherent sheaf sequences. The augmentation is transported along
the equivalence's unit, so the resolved object is the original coherent
sheaf. All terms are actual finite locally free sheaves.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.ExactCategory

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]

/-- The actual vector-bundle condition on an object of the coherent category. -/
def coherentVectorBundle : ObjectProperty
  (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X) :=
  fun M => IsFiniteLocallyFree X M.obj

instance coherentVectorBundle_isoClosed : (coherentVectorBundle X).IsClosedUnderIsomorphisms where
  of_iso e h := (finiteLocallyFree X).prop_of_iso
    ((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesToModules X).mapIso e) h

instance coherentVectorBundle_extensionClosed :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).IsExtensionClosed
      (coherentVectorBundle X) where
  prop_middle {S} hS h₁ h₃ := by
    have : IsFiniteLocallyFree X (S.map
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesToModules X)).X₁ := h₁
    have : IsFiniteLocallyFree X (S.map
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesToModules X)).X₃ := h₃
    exact finiteLocallyFree_of_shortExact
      ((AlgebraicGeometry.Scheme.Modules.Coherent.coherent_shortExact_iff X S).mp hS)

instance coherentVectorBundle_containsZero : (coherentVectorBundle X).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    exact finiteLocallyFree_of_isZero
      ((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesToModules X).map_isZero
        (isZero_zero _))

instance coherentVectorBundle_closedUnderFiniteProducts :
    (coherentVectorBundle X).IsClosedUnderFiniteProducts :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
    X).extensionClosed_finiteProducts (coherentVectorBundle X)

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- The actual affine coherent/module equivalence identifies vector bundles
with finite projective modules, with no homological or K-theory assumption. -/
theorem coherentVectorBundle_iff_projective (M :
  AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves (Spec R)) :
    coherentVectorBundle (Spec R) M ↔ AlgebraicGeometry.Scheme.Modules.Coherent.finiteProjective R
      ((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
        R).functor.obj M) := by
  have h := (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_spec_iff R
    M.obj).mp M.property
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
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec R)).IsKernelClosed
      (coherentVectorBundle (Spec R)) where
  prop_kernel {S} hS h₂ h₃ := by
    let E := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence R
    let T := S.map E.functor
    have hT : T.ShortExact := hS.map_of_exact E.functor
    have h₂' : AlgebraicGeometry.Scheme.Modules.Coherent.finiteProjective R T.X₂ :=
      (coherentVectorBundle_iff_projective R S.X₂).mp h₂
    have h₃' : AlgebraicGeometry.Scheme.Modules.Coherent.finiteProjective R T.X₃ :=
      (coherentVectorBundle_iff_projective R S.X₃).mp h₃
    exact (coherentVectorBundle_iff_projective R S.X₁).mpr
      (CategoryTheory.ExactCategory.ExactStructure.IsKernelClosed.prop_kernel
        (E := ModuleCat.finiteModuleExactStructure R) hT h₂' h₃')

/-- Associated sheaves of finite modules, landing in the genuine global
coherent category and retaining actual short exact sequences. -/
def finiteModuleTildeExact :
    ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} R)
      (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec R)) where
  toFunctor :=
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
    R).inverse
  map_conflation _ h := h.map_of_exact _

/-- Tilde carries finite free modules to actual coherent vector bundles. -/
theorem finiteModuleTilde_finiteFree (M : ModuleCat.FiniteModule.{u, u} R)
    (hM : Module.Free R M.obj) :
    coherentVectorBundle (Spec R) ((finiteModuleTildeExact R).toFunctor.obj M) := by
  change IsFiniteLocallyFree (Spec R) (tilde M.obj)
  have := hM
  exact finiteLocallyFree_tilde_of_finite_free R M.obj

/-- Tilde carries finite projective modules to actual coherent vector bundles. -/
theorem finiteModuleTilde_finiteProjective (M : ModuleCat.FiniteModule.{u, u} R)
    (hM : AlgebraicGeometry.Scheme.Modules.Coherent.finiteProjective R M) :
    coherentVectorBundle (Spec R) ((finiteModuleTildeExact R).toFunctor.obj M) := by
  change IsFiniteLocallyFree (Spec R) (tilde M.obj)
  have : Module.Projective R M.obj := hM
  exact finiteLocallyFree_tilde_of_finite_projective R M.obj

/-- An actual projective-dimension bound on a coherent sheaf's module of
global sections produces a genuine finite locally free resolution of that
same sheaf, with that bound. -/
theorem coherentResolution_length_le_of_projectiveDimensionLE (n : ℕ)
    (M : AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves (Spec R))
    [HasProjectiveDimensionLE
      ((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
        R).functor.obj M).obj n] :
    ∃ T : (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec
      R)).FiniteResolution
        (coherentVectorBundle (Spec R)) M, T.length ≤ n := by
  let E := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence R
  obtain ⟨T, hT⟩ := AlgebraicGeometry.Scheme.Modules.Coherent.finiteProjectiveResolution_length_le R
    n (E.functor.obj M)
  let T' := (finiteModuleTildeExact R).mapFiniteResolution
    (finiteModuleTilde_finiteProjective R) T
  let T'' := T'.ofIso (E.unitIso.app M).symm
  refine ⟨T'', ?_⟩
  simpa [T'', T'] using hT

/-- Every coherent sheaf on the spectrum of a PID has an actual admissible
finite locally free resolution of length at most one. -/
theorem coherentResolution_length_le_one_of_pid [IsDomain R] [IsPrincipalIdealRing R]
    (M : AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves (Spec R)) :
    ∃ T : (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec
      R)).FiniteResolution
        (coherentVectorBundle (Spec R)) M, T.length ≤ 1 := by
  let E := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence R
  obtain ⟨T, hT⟩ :=
    AlgebraicGeometry.Scheme.Modules.Coherent.finiteFreeResolution_length_le_one_of_pid R
    (E.functor.obj M)
  let T' := (finiteModuleTildeExact R).mapFiniteResolution
    (finiteModuleTilde_finiteFree R) T
  let T'' := T'.ofIso (E.unitIso.app M).symm
  refine ⟨T'', ?_⟩
  simpa [T'', T'] using hT

/-- The genuine geometric finite-vector-bundle-resolution hypothesis is
fully discharged for the spectrum of a principal ideal domain. -/
theorem coherentResolutionHypothesis_of_pid [IsDomain R] [IsPrincipalIdealRing R] :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec R)).ResolutionHypothesis
      (coherentVectorBundle (Spec R)) := by
  intro M
  obtain ⟨T, _⟩ := coherentResolution_length_le_one_of_pid R M
  exact ⟨T⟩

end AlgebraicGeometry.Scheme.Modules
