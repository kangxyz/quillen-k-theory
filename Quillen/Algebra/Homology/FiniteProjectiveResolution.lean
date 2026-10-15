/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.Finite
public import Quillen.Resolution.Finite
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Actual finite-projective syzygies of finite modules

Finite projective dimension here is mathlib's Ext-vanishing condition, not
an assumption about K-theory. A finite free cover has a finite kernel over
a noetherian ring, and the projective dimension of the kernel drops by one.
This is the algebraic input to finite admissible projective resolutions.

The general regular-local-ring theorem giving finite projective dimension
is not yet in the pinned mathlib. The PID specialization below has no such
extra hypothesis: its first syzygy is free by the submodule theorem.
-/
@[expose] public section

open ModuleCat
open Quillen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- The projective objects used to resolve finite modules are genuinely
projective as modules in the ambient module category. -/
def finiteProjective : ObjectProperty (FiniteModule.{u, u} R) :=
  fun M => Module.Projective R M.obj

instance finiteModuleForget_preservesFiniteLimits :
    PreservesFiniteLimits (finiteModule.{u, u} R).ι := by
  have := (finiteModule.{u, u} R).preservesKernels_ι
  exact Functor.preservesFiniteLimits_of_preservesKernels _

instance finiteModuleForget_preservesFiniteColimits :
    PreservesFiniteColimits (finiteModule.{u, u} R).ι := by
  have := (finiteModule.{u, u} R).preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

/-- Short exactness among finite modules is the actual ambient module
short exactness. -/
theorem finiteModule_shortExact_iff (S : ShortComplex (FiniteModule.{u, u} R)) :
    S.ShortExact ↔ (S.map (finiteModule R).ι).ShortExact := by
  constructor
  · exact fun h => h.map_of_exact _
  · intro h
    exact { exact := Functor.reflects_exact_of_faithful (finiteModule R).ι S h.exact
            mono_f := Functor.mono_of_mono_map (finiteModule R).ι h.mono_f
            epi_g := Functor.epi_of_epi_map (finiteModule R).ι h.epi_g }

/-- Every finite module has a finite free cover with a genuinely finite
kernel, as a short exact sequence in the category of finite modules. -/
theorem exists_finiteFree_shortExact (M : FiniteModule.{u, u} R) :
    ∃ (K P : FiniteModule.{u, u} R) (i : K ⟶ P) (p : P ⟶ M) (w : i ≫ p = 0),
      Module.Free R P.obj ∧ (ShortComplex.mk i p w).ShortExact := by
  obtain ⟨P, hP, hPR, hfree, hfinite, f, hf⟩ :=
    Module.exists_finite_presentation R M.obj
  let K : FiniteModule R := ⟨ModuleCat.of R (LinearMap.ker f), (show Module.Finite R (LinearMap.ker
    f) from inferInstance)⟩
  let F : FiniteModule R := ⟨ModuleCat.of R P, (show Module.Finite R P from inferInstance)⟩
  let i : K ⟶ F := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.ker f).subtype)
  let p : F ⟶ M := ObjectProperty.homMk (ModuleCat.ofHom f)
  have w : i ≫ p = 0 := by
    ext x
    exact x.property
  refine ⟨K, F, i, p, w, hfree, ?_⟩
  apply (finiteModule_shortExact_iff R _).mpr
  exact LinearMap.shortExact_shortComplexKer hf

/-- A finite free cover decreases the actual projective-dimension bound of
its target by one. -/
theorem hasProjectiveDimensionLE_syzygy
    (S : ShortComplex (FiniteModule.{u, u} R)) (hS : S.ShortExact)
    [Module.Free R S.X₂.obj] (n : ℕ)
    [HasProjectiveDimensionLE S.X₃.obj (n + 1)] :
    HasProjectiveDimensionLE S.X₁.obj n := by
  have h := (finiteModule_shortExact_iff R S).mp hS
  have hproj : Projective (S.map (finiteModule R).ι).X₂ := by
    change Projective S.X₂.obj
    exact (IsProjective.iff_projective _).mp inferInstance
  have hdim : HasProjectiveDimensionLT (S.map (finiteModule R).ι).X₃ (n + 2) := by
    change HasProjectiveDimensionLE S.X₃.obj (n + 1)
    infer_instance
  exact (h.hasProjectiveDimensionLT_X₃_iff n hproj).mp hdim

/-- Ext-defined projective dimension at most `n` produces an actual finite
admissible resolution of length at most `n`, all of whose terms are finite
projective modules. No resolution or K-equivalence is assumed. -/
theorem finiteProjectiveResolution_length_le (n : ℕ) (M : FiniteModule.{u, u} R)
    [HasProjectiveDimensionLE M.obj n] :
    ∃ T : (finiteModuleExactStructure R).FiniteResolution (finiteProjective R) M,
      T.length ≤ n := by
  induction n generalizing M with
  | zero =>
    have hproj : Projective M.obj :=
      (projective_iff_hasProjectiveDimensionLE_zero M.obj).mpr inferInstance
    have hM : finiteProjective R M :=
      (IsProjective.iff_projective M.obj).mpr hproj
    exact ⟨.of_mem hM, le_rfl⟩
  | succ n ih =>
    obtain ⟨K, P, i, p, w, hfree, hS⟩ := exists_finiteFree_shortExact R M
    have : Module.Free R P.obj := hfree
    have : HasProjectiveDimensionLE K.obj n :=
      hasProjectiveDimensionLE_syzygy R (ShortComplex.mk i p w) hS n
    obtain ⟨T, hT⟩ := ih K
    have hP : finiteProjective R P := (show Module.Projective R P.obj from inferInstance)
    exact ⟨.step (ShortComplex.mk i p w) hS hP T, Nat.succ_le_succ hT⟩

/-- Every finite module of non-infinite projective dimension has an actual
finite admissible projective resolution, with an object-dependent length. -/
theorem nonempty_finiteProjectiveResolution_of_projectiveDimension_ne_top
    (M : FiniteModule.{u, u} R) (hM : projectiveDimension M.obj ≠ ⊤) :
    Nonempty ((finiteModuleExactStructure R).FiniteResolution (finiteProjective R) M) := by
  obtain ⟨n, hn⟩ := (projectiveDimension_ne_top_iff M.obj).mp hM
  have := hn
  obtain ⟨T, _⟩ := finiteProjectiveResolution_length_le R n M
  exact ⟨T⟩

instance finiteProjective_isoClosed : (finiteProjective R).IsClosedUnderIsomorphisms where
  of_iso {M N} e h := by
    have : Module.Projective R M.obj := h
    let e' : M.obj ≅ N.obj := ((finiteModule R).ι).mapIso e
    exact Module.Projective.of_equiv e'.toLinearEquiv

instance finiteProjective_containsZero : (finiteProjective R).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    have h : IsZero (((finiteModule R).ι).obj (0 : FiniteModule.{u, u} R)) :=
      ((finiteModule R).ι).map_isZero (isZero_zero _)
    exact (IsProjective.iff_projective _).mpr h.projective

instance finiteProjective_extensionClosed :
    (finiteModuleExactStructure R).IsExtensionClosed (finiteProjective R) where
  prop_middle {S} hS h₁ h₃ := by
    have : Module.Projective R S.X₁.obj := h₁
    have : Module.Projective R S.X₃.obj := h₃
    let T := S.map (finiteModule R).ι
    have hT : T.ShortExact := (finiteModule_shortExact_iff R S).mp hS
    have h₁' : HasProjectiveDimensionLT T.X₁ 1 :=
      (projective_iff_hasProjectiveDimensionLT_one (X := S.X₁.obj)).mp inferInstance
    have h₃' : HasProjectiveDimensionLT T.X₃ 1 :=
      (projective_iff_hasProjectiveDimensionLT_one (X := S.X₃.obj)).mp inferInstance
    have h₂ := hT.hasProjectiveDimensionLT_X₂ 1 h₁' h₃'
    exact (IsProjective.iff_projective S.X₂.obj).mpr
      ((projective_iff_hasProjectiveDimensionLT_one (X := S.X₂.obj)).mpr h₂)

instance finiteProjective_kernelClosed :
    (finiteModuleExactStructure R).IsKernelClosed (finiteProjective R) where
  prop_kernel {S} hS h₂ h₃ := by
    have : Module.Projective R S.X₂.obj := h₂
    have : Module.Projective R S.X₃.obj := h₃
    let T := S.map (finiteModule R).ι
    have hT : T.ShortExact := (finiteModule_shortExact_iff R S).mp hS
    have h₂' : HasProjectiveDimensionLT T.X₂ 1 :=
      (projective_iff_hasProjectiveDimensionLT_one (X := S.X₂.obj)).mp inferInstance
    have h₃' : HasProjectiveDimensionLT T.X₃ 2 := by
      change HasProjectiveDimensionLT S.X₃.obj 2
      infer_instance
    have h₁ := hT.hasProjectiveDimensionLT_X₁ 1 h₂' h₃'
    exact (IsProjective.iff_projective S.X₁.obj).mpr
      ((projective_iff_hasProjectiveDimensionLT_one (X := S.X₁.obj)).mpr h₁)

/-- The first syzygy of a finite free cover over a PID is free: it embeds
into a torsion-free finite module. -/
theorem free_syzygy_of_pid [IsDomain R] [IsPrincipalIdealRing R]
    (S : ShortComplex (FiniteModule.{u, u} R)) (hS : S.ShortExact)
    [Module.Free R S.X₂.obj] : Module.Free R S.X₁.obj := by
  have h := (finiteModule_shortExact_iff R S).mp hS
  have hinj : Function.Injective S.f.hom.hom := h.moduleCat_injective_f
  have : Module.IsTorsionFree R S.X₁.obj :=
    Function.Injective.moduleIsTorsionFree S.f.hom.hom hinj S.f.hom.hom.map_smul
  exact Module.free_of_finite_type_torsion_free'

/-- Over a PID every finite module has an actual finite-free resolution of
length at most one. This theorem has no projective-dimension assumption. -/
theorem finiteFreeResolution_length_le_one_of_pid [IsDomain R] [IsPrincipalIdealRing R]
    (M : FiniteModule.{u, u} R) :
    ∃ T : (finiteModuleExactStructure R).FiniteResolution
      (fun N => Module.Free R N.obj) M, T.length ≤ 1 := by
  obtain ⟨K, P, i, p, w, hfree, hS⟩ := exists_finiteFree_shortExact R M
  have : Module.Free R P.obj := hfree
  have hK := free_syzygy_of_pid R (ShortComplex.mk i p w) hS
  exact ⟨.step (ShortComplex.mk i p w) hS hfree (.of_mem hK), le_rfl⟩

/-- Principal ideal domains satisfy the algebraic finite-projective
resolution hypothesis, without assuming its conclusion. -/
theorem finiteProjectiveResolutionHypothesis_of_pid [IsDomain R] [IsPrincipalIdealRing R] :
    (finiteModuleExactStructure R).ResolutionHypothesis (finiteProjective R) := by
  intro M
  obtain ⟨T, _⟩ := finiteFreeResolution_length_le_one_of_pid R M
  exact ⟨T.mono (fun N hN => by
    have : Module.Free R N.obj := hN
    exact (show Module.Projective R N.obj from inferInstance))⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
