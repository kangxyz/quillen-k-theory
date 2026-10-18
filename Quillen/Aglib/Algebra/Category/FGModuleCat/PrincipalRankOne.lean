/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Aglib.Algebra.Category.FGModuleCat.Localization
public import Aglib.Algebra.Category.FGModuleCat.IdealClosedSupport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.Localization.Away.Basic
public import Quillen.Aglib.Algebra.Category.FGModuleCat.ScalarMatrices

/-!
# Original rank-one multiplication, principal quotient, and localization

The actual free finite module uses Fin 1 coordinates. Multiplication by r and
the original quotient projection form a literal short complex whose categorical
cokernel is the existing quotient-ring rank-one restriction. For a regular r
over a noetherian commutative ring, this same complex is short exact and is a
conflation for the standard exact structure.

The actual finite-module localization is identified with the original localized
rank-one module by the module-localization universal property. Its R-linear
comparison is explicitly upgraded to localization-linearity. Under this actual
isomorphism, the original mapped multiplication is the scalar GL(Fin 1) action
at the unit with value algebraMap r. The quotient, localization and map equations
work for every commutative ring; regularity is used only for monicity, and
noetherianity only for the short-exact and conflation statements.

Intended upstream module: `Aglib.Algebra.Category.FGModuleCat.PrincipalRankOne`.
Current consumer: the principal-open object-boundary calibration in Quillen K-theory.
This leaf contains only ordinary module algebra and category comparisons.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
open scoped nonZeroDivisors
universe u
namespace FGModuleCat.PrincipalRankOne
variable (R : Type u) [CommRing R]

/-- The original free rank-one finite module, with Fin 1 coordinates. -/
abbrev rankOne : FGModuleCat.{u} R := FGModuleCat.of R (Fin 1 → R)

/-- The original multiplication-by-r endomorphism is the scalar identity. -/
def multiply (r : R) : rankOne R ⟶ rankOne R := r • 𝟙 _

/-- Multiplication retains the original coordinatewise ring multiplication. -/
@[simp] theorem multiply_apply (r : R) (x : Fin 1 → R) (i : Fin 1) :
    multiply R r x i = r * x i := rfl

/-- The original principal quotient ring. -/
abbrev quotientRing (r : R) := R ⧸ Ideal.span {r}

/-- The existing quotient-ring restriction applied to its original free rank-one module. -/
def quotientObject (r : R) : FGModuleCat.{u} R :=
  (ModuleCat.FiniteLocalization.IdealClosedSupport.closedRestriction (Ideal.span {r})).obj
    (rankOne (quotientRing R r))

/-- The original quotient ring map on every rank-one coordinate, with its restricted R-action. -/
def quotientMap (r : R) : rankOne R ⟶ quotientObject R r :=
  ⟨ModuleCat.ofHom (X := (rankOne R).obj) (Y := (quotientObject R r).obj) {
    toFun := fun x i => Ideal.Quotient.mk (Ideal.span {r}) (x i)
    map_add' := by
      intro x y
      change (fun i => Ideal.Quotient.mk (Ideal.span {r}) (x i + y i)) =
        fun i => Ideal.Quotient.mk (Ideal.span {r}) (x i) +
          Ideal.Quotient.mk (Ideal.span {r}) (y i)
      ext i
      exact map_add _ _ _
    map_smul' := by
      intro a x
      change (fun i => Ideal.Quotient.mk (Ideal.span {r}) (a * x i)) =
        fun i => Ideal.Quotient.mk (Ideal.span {r}) a *
          Ideal.Quotient.mk (Ideal.span {r}) (x i)
      ext i
      exact map_mul _ _ _ }⟩

/-- The projection retains the original ring quotient map. -/
@[simp] theorem quotientMap_apply (r : R) (x : Fin 1 → R) (i : Fin 1) :
    quotientMap R r x i = Ideal.Quotient.mk (Ideal.span {r}) (x i) := rfl

/-- Multiplication followed by the original quotient projection is zero. -/
theorem multiply_quotientMap (r : R) : multiply R r ≫ quotientMap R r = 0 := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (fun i => Ideal.Quotient.mk (Ideal.span {r}) (r * x i)) = 0
  ext i
  change Ideal.Quotient.mk (Ideal.span {r}) (r * x i) = 0
  rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), zero_mul]

/-- The original coefficient localization map in Fin 1 coordinates; this map is R-linear. -/
abbrev coordinates (r : R) : (Fin 1 → R) →ₗ[R] (Fin 1 → Localization.Away r) :=
  LinearMap.pi fun i => (Algebra.linearMap R (Localization.Away r)).comp (LinearMap.proj i)

/-- The original coordinate map is a module-localization map by the finite-product supplier. -/
theorem coordinates_isLocalizedModule (r : R) :
    IsLocalizedModule (Submonoid.powers r) (coordinates R r) := by
  dsimp only [coordinates]
  infer_instance

attribute [local instance] coordinates_isLocalizedModule

/-- The canonical R-linear localization comparison, upgraded to localization-linearity. -/
def localizationLinearEquiv (r : R) :
    ((rankOne R).obj.localizedModule (Submonoid.powers r)) ≃ₗ[Localization.Away r]
      (Fin 1 → Localization.Away r) := by
  letI := ModuleCat.localizedModule_isLocalizedModule (rankOne R).obj (Submonoid.powers r)
  exact (IsLocalizedModule.linearEquiv (Submonoid.powers r)
    ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r))
      (coordinates R r)).extendScalarsOfIsLocalization (Submonoid.powers r) (Localization.Away r)

/-- The actual finite-module localization is isomorphic to the original localized rank-one
  module -/
def localizationIso (r : R) :
    (ModuleCat.FiniteLocalization.functor (Submonoid.powers r)).obj (rankOne R) ≅
      rankOne (Localization.Away r) :=
  ObjectProperty.isoMk _ (localizationLinearEquiv R r).toModuleIso

/-- On original numerators, the comparison is exactly the coefficient algebra map. -/
theorem localizationIso_hom_mk (r : R) (x : Fin 1 → R) :
    (localizationIso R r).hom
      ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r) x) =
      fun i => algebraMap R (Localization.Away r) (x i) := by
  have := ModuleCat.localizedModule_isLocalizedModule (rankOne R).obj (Submonoid.powers r)
  exact IsLocalizedModule.linearEquiv_apply (Submonoid.powers r)
    ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r)) (coordinates R r) x

/-- The original image of r, bundled as a unit by the localization-away supplier. -/
def localizationUnit (r : R) : (Localization.Away r)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).unit

/-- The localized unit has exactly the original coefficient image as its value. -/
@[simp] theorem localizationUnit_val (r : R) :
    (localizationUnit R r : Localization.Away r) = algebraMap R (Localization.Away r) r :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).unit_spec

/-- The actual scalar GL(Fin 1) automorphism at the original localized unit. -/
def localizationAut (r : R) : Aut (rankOne (Localization.Away r)) :=
  FGModuleCat.matrixToAut (Localization.Away r) 1
    (Matrix.GeneralLinearGroup.scalar (Fin 1) (localizationUnit R r))

/-- The localized scalar automorphism has the original multiplication map as its forward map. -/
theorem localizationAut_hom (r : R) :
    (localizationAut R r).hom = multiply (Localization.Away r)
      (algebraMap R (Localization.Away r) r) := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (FGModuleCat.matrixToAut (Localization.Away r) 1
    (Matrix.GeneralLinearGroup.scalar (Fin 1) (localizationUnit R r))).hom x = _
  rw [FGModuleCat.matrixToAut_apply]
  change (Matrix.scalar (Fin 1) (localizationUnit R r : Localization.Away r)).mulVec x =
    fun i => algebraMap R (Localization.Away r) r * x i
  ext i
  simp only [Matrix.scalar_apply, Matrix.mulVec_diagonal, localizationUnit_val]

/-- A non-zero-divisor acts injectively on the actual free rank-one module. -/
theorem multiply_injective (r : R) (hr : r ∈ nonZeroDivisors R) :
    Function.Injective (multiply R r) := by
  intro x y h
  change (fun i => r * x i) = (fun i => r * y i) at h
  funext i
  apply sub_eq_zero.mp
  apply (mul_left_mem_nonZeroDivisors_eq_zero_iff hr).mp
  rw [mul_sub]
  exact sub_eq_zero.mpr (congrFun h i)

/-- Regularity of r makes its original rank-one multiplication a monomorphism. -/
theorem multiply_mono (r : R) (hr : r ∈ nonZeroDivisors R) : Mono (multiply R r) :=
  ConcreteCategory.mono_of_injective _ (multiply_injective R r hr)

/-- The original coordinate quotient projection is surjective. -/
theorem quotientMap_surjective (r : R) : Function.Surjective (quotientMap R r) := by
  intro x
  change Fin 1 → quotientRing R r at x
  choose y hy using fun i : Fin 1 => Ideal.Quotient.mk_surjective (x i)
  exact ⟨y, funext hy⟩

/-- The actual quotient projection is an epimorphism, over every commutative ring. -/
instance quotientMap_epi (r : R) : Epi (quotientMap R r) :=
  ConcreteCategory.epi_of_surjective _ (quotientMap_surjective R r)

/-- The literal multiplication and quotient maps are exact as maps of the original modules. -/
theorem function_exact (r : R) : Function.Exact (multiply R r) (quotientMap R r) := by
  intro x
  change (fun i => Ideal.Quotient.mk (Ideal.span {r}) (x i)) = 0 ↔
    ∃ y : Fin 1 → R, (fun i => r * y i) = x
  constructor
  · intro hx
    have h (i : Fin 1) : r ∣ x i := Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hx i))
    choose y hy using h
    exact ⟨y, funext fun i => (hy i).symm⟩
  · rintro ⟨y, rfl⟩
    funext i
    rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), zero_mul]
    rfl

/-- The literal multiplication-to-quotient short complex. -/
def shortComplex (r : R) : ShortComplex (FGModuleCat.{u} R) :=
  ShortComplex.mk (multiply R r) (quotientMap R r) (multiply_quotientMap R r)

/-- The original quotient projection is a categorical cokernel, via the module supplier. -/
def cokernelCoforkIsColimit (r : R) :
    IsColimit (CokernelCofork.ofπ (quotientMap R r) (multiply_quotientMap R r)) := by
  apply isColimitOfReflects (forget₂ (FGModuleCat R) (ModuleCat R))
  refine (isColimitMapCoconeCoforkEquiv' (forget₂ (FGModuleCat R) (ModuleCat R))
    (multiply_quotientMap R r)).symm ?_
  exact ModuleCat.isColimitCokernelCofork (multiply R r).hom (quotientMap R r).hom
    (function_exact R r) (quotientMap_surjective R r)

/-- The actual categorical cokernel is canonically the original quotient-ring rank-one
  restriction -/
def cokernelIso (r : R) : cokernel (multiply R r) ≅ quotientObject R r :=
  colimit.isoColimitCocone ⟨_, cokernelCoforkIsColimit R r⟩

/-- The cokernel comparison retains the original quotient projection. -/
@[reassoc (attr := simp)] theorem cokernelIso_π_hom (r : R) :
    cokernel.π (multiply R r) ≫ (cokernelIso R r).hom = quotientMap R r :=
  colimit.isoColimitCocone_ι_hom _ _

/-- The inverse comparison carries the original quotient projection to the categorical one. -/
@[reassoc (attr := simp)] theorem quotientMap_cokernelIso_inv (r : R) :
    quotientMap R r ≫ (cokernelIso R r).inv = cokernel.π (multiply R r) := by
  rw [← cokernelIso_π_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original quotient-ring restriction is annihilated by r. -/
theorem quotientObject_killed (r : R) (x : quotientObject R r) : r • x = 0 :=
  ModuleCat.FiniteLocalization.IdealClosedSupport.closedRestriction_killed
    (Ideal.span {r}) (rankOne (quotientRing R r)) r (Ideal.subset_span (by simp)) x

/-- The actual quotient object lies in the kernel of localization away from r. -/
theorem quotientObject_torsion (r : R) :
    ModuleCat.FiniteLocalization.torsion (Submonoid.powers r) (quotientObject R r) := by
  apply (ModuleCat.FiniteLocalization.torsion_powers_iff_uniform r (quotientObject R r)).2
  exact ⟨1, by simpa only [pow_one] using quotientObject_killed R r⟩

/-- The actual localization comparison intertwines original multiplication with its
  coefficient image -/
theorem localization_multiply (r : R) :
    (ModuleCat.FiniteLocalization.functor (Submonoid.powers r)).map (multiply R r) ≫
        (localizationIso R r).hom =
      (localizationIso R r).hom ≫
        multiply (Localization.Away r) (algebraMap R (Localization.Away r) r) := by
  have := ModuleCat.localizedModule_isLocalizedModule (rankOne R).obj (Submonoid.powers r)
  apply FGModuleCat.hom_ext
  change (localizationLinearEquiv R r).toLinearMap.comp
      (IsLocalizedModule.mapExtendScalars (Submonoid.powers r)
        ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r))
        ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r))
        (Localization.Away r) (multiply R r).hom.hom) =
    (algebraMap R (Localization.Away r) r • LinearMap.id).comp
      (localizationLinearEquiv R r).toLinearMap
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers r)
    ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r)) (coordinates R r)
  apply LinearMap.ext
  intro x
  change (localizationIso R r).hom
    (IsLocalizedModule.map (Submonoid.powers r)
      ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r))
      ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r))
      (multiply R r).hom.hom
      ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r) x)) =
    multiply (Localization.Away r) (algebraMap R (Localization.Away r) r)
      ((localizationIso R r).hom
        ((rankOne R).obj.localizedModuleMkLinearMap (Submonoid.powers r) x))
  rw [IsLocalizedModule.map_apply, localizationIso_hom_mk, localizationIso_hom_mk]
  funext i
  exact map_mul (algebraMap R (Localization.Away r)) r (x i)

/-- The original mapped multiplication intertwines with the actual localized scalar automorphism. -/
theorem localization_multiply_aut (r : R) :
    (ModuleCat.FiniteLocalization.functor (Submonoid.powers r)).map (multiply R r) ≫
        (localizationIso R r).hom =
      (localizationIso R r).hom ≫ (localizationAut R r).hom := by
  rw [localizationAut_hom]
  exact localization_multiply R r

/-- The actual mapped multiplication is conjugation of the original localized scalar
  automorphism -/
theorem localization_map_multiply_eq (r : R) :
    (ModuleCat.FiniteLocalization.functor (Submonoid.powers r)).map (multiply R r) =
      (localizationIso R r).hom ≫ (localizationAut R r).hom ≫ (localizationIso R r).inv := by
  apply (cancel_mono (localizationIso R r).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact localization_multiply_aut R r

/-- The original multiplication map becomes invertible under the actual finite-module
  localization -/
instance localization_multiply_isIso (r : R) :
    IsIso ((ModuleCat.FiniteLocalization.functor (Submonoid.powers r)).map (multiply R r)) := by
  rw [localization_map_multiply_eq]
  infer_instance

/-- The actual mapped automorphism is the original scalar GL(Fin 1) action in the supplied
  coordinates -/
theorem localization_conjugate (r : R) :
    Aut.autMulEquivOfIso (localizationIso R r)
      (asIso ((ModuleCat.FiniteLocalization.functor (Submonoid.powers r)).map (multiply R r))) =
        localizationAut R r := by
  apply Iso.ext
  change (localizationIso R r).inv ≫
    ((ModuleCat.FiniteLocalization.functor (Submonoid.powers r)).map (multiply R r) ≫
      (localizationIso R r).hom) = (localizationAut R r).hom
  rw [localization_multiply_aut, Iso.inv_hom_id_assoc]

variable [IsNoetherianRing R]

/-- A regular element gives the literal short exact multiplication-to-quotient sequence. -/
theorem shortExact (r : R) (hr : r ∈ nonZeroDivisors R) : (shortComplex R r).ShortExact := by
  exact {
    exact := (shortComplex R r).exact_of_g_is_cokernel (cokernelCoforkIsColimit R r)
    mono_f := multiply_mono R r hr
    epi_g := quotientMap_epi R r }

/-- The same literal short complex is a conflation in the standard finite-module exact structure. -/
theorem conflation (r : R) (hr : r ∈ nonZeroDivisors R) :
    (ModuleCat.finiteModuleExactStructure.{u, u} R).conflation (shortComplex R r) :=
  shortExact R r hr

end FGModuleCat.PrincipalRankOne
