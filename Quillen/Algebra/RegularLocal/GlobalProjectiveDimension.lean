/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Quillen.Algebra.RegularLocal.ProjectiveDimension
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Objectwise globalization of finite projective dimension

Finite-free syzygies give an increasing sequence of open free loci. If every
prime localization of a finite module has finite projective dimension, these
opens cover the spectrum. Quasi-compactness supplies a bound for that module,
without imposing a uniform dimension bound on the ring.
-/
@[expose] public section

open ModuleCat
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- A selected actual finite-free presentation with its finite syzygy. -/
structure FiniteFreeCover (M : FiniteModule.{u, u} R) where
  /-- The finite syzygy, identified as the kernel of the cover by `shortExact`. -/
  K : FiniteModule.{u, u} R
  /-- The finite free module surjecting onto `M`. -/
  P : FiniteModule.{u, u} R
  /-- The inclusion of the finite syzygy into the finite free module. -/
  i : K ⟶ P
  /-- The cover map from the finite free module onto `M`. -/
  p : P ⟶ M
  zero : i ≫ p = 0
  free : Module.Free R P.obj
  shortExact : (ShortComplex.mk i p zero).ShortExact

/-- Choose a short exact presentation of the finite module `M` by a finite free module and its
finite syzygy over the noetherian ring `R`. -/
def finiteFreeCover (M : FiniteModule.{u, u} R) : FiniteFreeCover R M :=
  Classical.choice (by
    obtain ⟨K, P, i, p, w, hf, hs⟩ := exists_finiteFree_shortExact R M
    exact ⟨⟨K, P, i, p, w, hf, hs⟩⟩)

/-- Iterated actual finite-free syzygies. -/
def finiteFreeSyzygy : ℕ → FiniteModule.{u, u} R → FiniteModule.{u, u} R
  | 0, M => M
  | n + 1, M => finiteFreeSyzygy n (finiteFreeCover R M).K

/-- A projective terminal syzygy gives a genuine finite-projective resolution
of the original module. -/
theorem finiteProjectiveResolution_of_projective_syzygy (n : ℕ) (M : FiniteModule.{u, u} R)
    (hn : finiteProjective R (finiteFreeSyzygy R n M)) :
    Nonempty ((finiteModuleExactStructure R).FiniteResolution (finiteProjective R) M) := by
  induction n generalizing M with
  | zero => exact ⟨.of_mem hn⟩
  | succ n ih =>
    let C := finiteFreeCover R M
    obtain ⟨T⟩ := ih C.K hn
    have : Module.Free R C.P.obj := C.free
    exact ⟨.step (ShortComplex.mk C.i C.p C.zero) C.shortExact
      (show Module.Projective R C.P.obj from inferInstance) T⟩

instance finite_localizedModule (M : FiniteModule.{u, u} R) (S : Submonoid R) :
    Module.Finite (Localization S) (M.obj.localizedModule S) :=
  Module.Finite.of_isLocalizedModule S (M.obj.localizedModuleMkLinearMap S)

/-- The exact projective-dimension meaning of a localized finite-free syzygy. -/
theorem localized_projectiveDimension_iff_syzygy (n : ℕ) (M : FiniteModule.{u, u} R)
    (p : PrimeSpectrum R) :
    HasProjectiveDimensionLE (M.obj.localizedModule p.asIdeal.primeCompl) n ↔
      Projective ((finiteFreeSyzygy R n M).obj.localizedModule p.asIdeal.primeCompl) := by
  induction n generalizing M with
  | zero => exact (projective_iff_hasProjectiveDimensionLE_zero _).symm
  | succ n ih =>
    let C := finiteFreeCover R M
    have : Module.Free R C.P.obj := C.free
    let S := (ShortComplex.mk C.i C.p C.zero).map (finiteModule R).ι
    have hS : S.ShortExact := (finiteModule_shortExact_iff R _).mp C.shortExact
    let L := ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl
    have hSL : (S.map L).ShortExact := hS.map_of_exact L
    have hP : Projective (S.map L).X₂ := by
      have : Projective C.P.obj := inferInstance
      exact L.projective_obj C.P.obj
    exact (hSL.hasProjectiveDimensionLT_X₃_iff n hP).trans (ih C.K)

omit [IsNoetherianRing R] in
/-- Membership of the actual open free locus agrees with projectivity of
mathlib's chosen localized-module model at the prime. -/
theorem mem_freeLocus_iff_projective_localized (M : FiniteModule.{u, u} R) (p : PrimeSpectrum R) :
    p ∈ Module.freeLocus R M.obj ↔ Projective (M.obj.localizedModule p.asIdeal.primeCompl) := by
  let e : M.obj.localizedModule p.asIdeal.primeCompl ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M.obj :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (M.obj.localizedModuleMkLinearMap p.asIdeal.primeCompl)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M.obj)).extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  constructor
  · intro h
    have : Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M.obj) := h
    have : Module.Free (Localization.AtPrime p.asIdeal)
        (M.obj.localizedModule p.asIdeal.primeCompl) := Module.Free.of_equiv e.symm
    infer_instance
  · intro h
    have := h
    have : Module.Free (Localization.AtPrime p.asIdeal)
        (M.obj.localizedModule p.asIdeal.primeCompl) := Module.free_of_flat_of_isLocalRing
    exact Module.Free.of_equiv e

/-- Stalkwise finite projective dimension globalizes for each finite module.
The compactness argument introduces a bound for this module alone. -/
theorem projectiveDimension_ne_top_of_localized
    (M : FiniteModule.{u, u} R)
    (h : ∀ p : PrimeSpectrum R,
      projectiveDimension (M.obj.localizedModule p.asIdeal.primeCompl) ≠ ⊤) :
    projectiveDimension M.obj ≠ ⊤ := by
  let U : ℕ → Set (PrimeSpectrum R) :=
    fun n => Module.freeLocus R (finiteFreeSyzygy R n M).obj
  have hU (n : ℕ) : IsOpen (U n) := by
    have : Module.FinitePresentation R (finiteFreeSyzygy R n M).obj :=
      Module.finitePresentation_of_finite R _
    exact Module.isOpen_freeLocus
  have hmem (n : ℕ) (p : PrimeSpectrum R) : p ∈ U n ↔
      HasProjectiveDimensionLE (M.obj.localizedModule p.asIdeal.primeCompl) n :=
    (mem_freeLocus_iff_projective_localized R (finiteFreeSyzygy R n M) p).trans
      (localized_projectiveDimension_iff_syzygy R n M p).symm
  have hmono : Monotone U := by
    intro a b hab p hp
    have := (hmem a p).mp hp
    apply (hmem b p).mpr
    exact hasProjectiveDimensionLT_of_ge (M.obj.localizedModule p.asIdeal.primeCompl)
      (a + 1) (b + 1) (Nat.succ_le_succ hab)
  have hcover : Set.univ ⊆ ⋃ n, U n := by
    intro p _
    obtain ⟨n, hn⟩ := (projectiveDimension_ne_top_iff _).mp (h p)
    exact Set.mem_iUnion.mpr ⟨n, (hmem n p).mpr hn⟩
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover U hU hcover
    (fun a b => ⟨max a b, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
  have hpd : HasProjectiveDimensionLE M.obj n :=
    (ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum n M.obj).mpr
      (fun p => (hmem n p).mp (hn (Set.mem_univ p)))
  exact (projectiveDimension_ne_top_iff M.obj).mpr ⟨n, hpd⟩

end AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Every finite module over an actual regular Noetherian ring has finite
projective dimension. The ring need not have finite Krull dimension, and no
common bound over all finite modules is assumed or produced. -/
theorem projectiveDimension_ne_top_of_regular (R : Type u) [CommRing R] [IsRegularRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : projectiveDimension M ≠ ⊤ := by
  let N : FiniteModule.{u, u} R := ⟨M, (show Module.Finite R M from inferInstance)⟩
  apply projectiveDimension_ne_top_of_localized R N
  intro p
  have : Module.Finite (Localization.AtPrime p.asIdeal) (M.localizedModule p.asIdeal.primeCompl) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
  exact RegularLocal.projectiveDimension_ne_top_of_regularLocal (Localization.AtPrime p.asIdeal)
    (M.localizedModule p.asIdeal.primeCompl)

/-- Actual finite-projective resolutions of every finite module over a
regular ring, with object-dependent finite lengths. -/
theorem finiteProjectiveResolutionHypothesis_of_regular (R : Type u) [CommRing R]
    [IsRegularRing R] : (finiteModuleExactStructure.{u, u} R).ResolutionHypothesis
      (finiteProjective R) := by
  intro M
  exact nonempty_finiteProjectiveResolution_of_projectiveDimension_ne_top R M
    (projectiveDimension_ne_top_of_regular R M.obj)

end AlgebraicGeometry.Scheme.Modules.Coherent
