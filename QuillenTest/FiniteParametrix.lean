/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Algebra.ModuleComplex.FiniteParametrix
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of the original finite-parametrix replacement

The tests retain the split kernel, both signed chain maps, actual cone homotopies,
and the precise two-term support. The ring may be nonreduced or the zero ring.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Quillen.Module Quillen.ModuleComplex

namespace QuillenTest.FiniteParametrix

open Quillen

variable {R : Type u} [CommRing R]
  {A B F G : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
  (d : A →ₗ[R] B) (s : B →ₗ[R] A) (t : F →ₗ[R] B) (r : B →ₗ[R] F)
  (hr : d.comp s + t.comp r = LinearMap.id)

/-- The projector fixes each actual kernel element, rather than an abstract copy. -/
theorem original_kernel_fixed (x : LinearMap.ker (parametrixTotal d t)) :
    parametrixKernelRetraction d s t r hr x.val = x :=
  LinearMap.congr_fun (parametrixKernelRetraction_subtype d s t r hr) x

/-- The replacement differential on the forward image is the negative right defect factor. -/
theorem original_forward_sign (x : A) :
    parametrixReplacementDifferential d t (parametrixForwardSource d s t r hr x) =
      -r (d x) :=
  LinearMap.congr_fun (parametrixForward_chain d s t r hr) x

/-- The backward chain map retains the negative added column. -/
theorem original_backward_sign (x : LinearMap.ker (parametrixTotal d t)) :
    d (parametrixBackwardSource d t x) = -t (parametrixReplacementDifferential d t x) :=
  LinearMap.congr_fun (parametrixBackward_chain d t) x

/-- The actual cone forward map retains the signed target component
through the original inclusion. -/
theorem original_cone_target_sign :
    CochainComplex.mappingCone.inr
        ((single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d)) ≫
      (parametrixConeHomotopyEquiv d s t r hr).hom =
    (single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom (-r)) ≫
      CochainComplex.mappingCone.inr
        ((single (ModuleCat.{v} R) (.up ℤ) 0).map
          (ModuleCat.ofHom (parametrixReplacementDifferential d t))) := by
  dsimp only [parametrixConeHomotopyEquiv,
    CochainComplex.mappingCone.homotopyEquivOfParametrices,
    CochainComplex.mappingCone.map]
  exact CochainComplex.mappingCone.inr_desc _ _ _ _

/-- The actual cone maps are mutually inverse up to the supplied cochain homotopy. -/
theorem original_cochain_homotopy :
    Nonempty (Homotopy
      ((parametrixConeHomotopyEquiv d s t r hr).hom ≫
        (parametrixConeHomotopyEquiv d s t r hr).inv)
      (𝟙 (linearMapCone d))) :=
  ⟨(parametrixConeHomotopyEquiv d s t r hr).homotopyHomInvId⟩

/-- The actual replacement has no degree-one term: its degrees are minus one and zero. -/
theorem replacement_degree_one :
    IsZero ((linearMapCone (parametrixReplacementDifferential d t)).X 1) :=
  linearMapCone_isZero_X _ 1 (by decide) (by decide)

include hr in
/-- Both factored defects yield a finite-projective model with the actual cone equivalence. -/
theorem finite_replacement
    [Module.Projective R A] [Module.Projective R F] [Module.Finite R F] [Module.Finite R G]
    (u : G →ₗ[R] A) (v : A →ₗ[R] G) (hl : s.comp d + u.comp v = LinearMap.id) :
    Module.Finite R (LinearMap.ker (parametrixTotal d t)) ∧
      Module.Projective R (LinearMap.ker (parametrixTotal d t)) ∧
      Nonempty (HomotopyEquiv (linearMapCone d)
        (linearMapCone (parametrixReplacementDifferential d t))) := by
  obtain ⟨hf, hp⟩ := finite_projective_parametrixKernel d s t r hr u v hl
  exact ⟨hf, hp, ⟨parametrixConeHomotopyEquiv d s t r hr⟩⟩

/-- The original cone criterion includes nonreduced coefficient rings. -/
theorem nonreduced_terms (n : ℤ) :
    Module.Finite (ZMod 4) ((linearMapCone (LinearMap.id : ZMod 4 →ₗ[ZMod 4] ZMod 4)).X n) ∧
    Module.Projective (ZMod 4)
      ((linearMapCone (LinearMap.id : ZMod 4 →ₗ[ZMod 4] ZMod 4)).X n) :=
  linearMapCone_finite_projective _ n

/-- The same actual finite-projective cone terms include the zero ring. -/
theorem zero_ring_terms (n : ℤ) :
    Module.Finite (ZMod 1) ((linearMapCone (LinearMap.id : ZMod 1 →ₗ[ZMod 1] ZMod 1)).X n) ∧
    Module.Projective (ZMod 1)
      ((linearMapCone (LinearMap.id : ZMod 1 →ₗ[ZMod 1] ZMod 1)).X n) :=
  linearMapCone_finite_projective _ n

end QuillenTest.FiniteParametrix
