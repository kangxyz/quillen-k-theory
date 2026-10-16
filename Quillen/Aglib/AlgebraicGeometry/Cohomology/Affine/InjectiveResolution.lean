/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Actual affine global sections of injective resolutions

The original affine global-sections functor preserves injective objects:
its left adjoint, the associated-sheaf functor, preserves monomorphisms.
For a quasicoherent sheaf `M` over any commutative ring, applying original
Γ to any ambient injective resolution gives an actual injective module
resolution of Γ(M). Its terms and differentials are the original mapped
ones; its augmentation is the original Γ-map in degree zero.

Positive-degree exactness uses higher affine quasicoherent cohomology.
Degree-zero exactness uses preservation of the actual augmentation kernel.
No resolution term or successive kernel is assumed quasicoherent.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.AffineDerived

/-- Exact tilde makes its right adjoint preserve injective objects. -/

instance globalSections_preservesInjectiveObjects (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms tilde.adjunction

variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (I : CategoryTheory.InjectiveResolution M)

/-- The augmentation of the original Γ-complex, with its literal degree-zero map. -/

def globalSectionsResolutionAugmentation :
    (CochainComplex.single₀ (ModuleCat.{u} R)).obj (moduleSpecΓFunctor.obj M) ⟶
      (moduleSpecΓFunctor.mapHomologicalComplex _).obj I.cocomplex :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨moduleSpecΓFunctor.map (I.ι.f 0), by
      change moduleSpecΓFunctor.map (I.ι.f 0) ≫
        moduleSpecΓFunctor.map (I.cocomplex.d 0 1) = 0
      rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero]⟩

omit [M.IsQuasicoherent] in

lemma globalSectionsResolutionAugmentation_f_zero :
    (globalSectionsResolutionAugmentation M I).f 0 = moduleSpecΓFunctor.map (I.ι.f 0) := rfl

instance globalSectionsResolutionAugmentation_quasiIso :
    QuasiIso (globalSectionsResolutionAugmentation M I) := by
  constructor
  intro n
  cases n with
  | zero =>
    let S := ShortComplex.mk (moduleSpecΓFunctor.map (I.ι.f 0))
      (moduleSpecΓFunctor.map (I.cocomplex.d 0 1)) (by
        rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero])
    have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S
      (KernelFork.mapIsLimit _ I.isLimitKernelFork moduleSpecΓFunctor)
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨hS,
          (inferInstance : Mono (moduleSpecΓFunctor.map (I.ι.f 0)))⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by rfl) (by rfl)
    all_goals simp [HomologicalComplex.shortComplexFunctor']
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact globalSections_injectiveResolution_exact_succ M I n
    · exact CochainComplex.exactAt_succ_single_obj _ _

/-- Original Γ of any ambient injective resolution of a QC sheaf is an injective
module resolution. No alternative complex is chosen. -/

def globalSectionsInjectiveResolution :
    CategoryTheory.InjectiveResolution (moduleSpecΓFunctor.obj M) where
  cocomplex := (moduleSpecΓFunctor.mapHomologicalComplex _).obj I.cocomplex
  ι := globalSectionsResolutionAugmentation M I
  injective n := by
    change Injective (moduleSpecΓFunctor.obj (I.cocomplex.X n))
    infer_instance

end AlgebraicGeometry.Scheme.Modules.AffineDerived
