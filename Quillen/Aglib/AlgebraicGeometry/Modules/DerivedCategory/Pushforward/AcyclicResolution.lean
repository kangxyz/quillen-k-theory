/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Quillen.Aglib.Algebra.Homology.Embedding.ExtendFunctor

/-! # Actual direct image of an acyclic injective resolution

The original augmentation remains a quasi-isomorphism whenever the actual direct-image
resolution is exact in positive degrees. No affine or quasicoherence hypothesis is required.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Positive-degree exactness of the actual direct-image resolution preserves its augmentation. -/
theorem quasiIso_pushforward_injectiveResolution_of_exact {Z X : Scheme.{u}}
    (f : Z ⟶ X) (M : Z.Modules)
    (I : InjectiveResolution M)
    (hI : ∀ n : ℕ, (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).ExactAt (n + 1)) :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).map I.ι) := by
  let F := Scheme.Modules.pushforward f
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · constructor
      · exact ShortComplex.exact_of_f_is_kernel _
          (KernelFork.mapIsLimit _ I.isLimitKernelFork F)
      · change Mono (F.map (I.ι.f 0))
        infer_instance
    all_goals simp
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact hI n
    · apply ShortComplex.exact_of_isZero_X₂
      exact F.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))

/-- The original integer-indexed injective augmentation remains a quasi-isomorphism. -/
theorem quasiIso_pushforward_injectiveResolution_int_of_quasiIso {Z X : Scheme.{u}}
    (f : Z ⟶ X) (M : Z.Modules)
    (I : InjectiveResolution M)
    (hI : QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).map I.ι)) :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map I.ι') := by
  let F := Scheme.Modules.pushforward f
  let := hI
  dsimp only [InjectiveResolution.ι']
  rw [Functor.map_comp, quasiIso_iff_comp_left]
  let e := F.mapHomologicalComplexExtendIso ComplexShape.embeddingUpNat
  apply (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality I.ι).symm)).mpr
  change QuasiIso (HomologicalComplex.extendMap
    ((F.mapHomologicalComplex (.up ℕ)).map I.ι) ComplexShape.embeddingUpNat)
  infer_instance

end AlgebraicGeometry.Scheme.Modules
