/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Regular.AffineResolution
public import Quillen.Resolution.LengthOne

/-! # Applying the resolution theorem to the canonical scheme comparison -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.SchemeSheaf


open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules
variable (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]

/-- The actual vector-bundle property on the chosen small coherent category. -/
def coherentSmallVectorBundle :
    ObjectProperty (SmallModel.{u+1}
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X)) :=
  fun M => coherentVectorBundle X ((equivSmallModel.{u+1}
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves
    X)).inverse.obj M)

instance coherentSmallVectorBundle_isoClosed :
    (coherentSmallVectorBundle X).IsClosedUnderIsomorphisms where
  of_iso e h := (coherentVectorBundle X).prop_of_iso
    ((equivSmallModel.{u+1} (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves
      X)).inverse.mapIso e) h

instance coherentSmallVectorBundle_containsZero : (coherentSmallVectorBundle X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, (coherentVectorBundle X).prop_of_isZero
    ((equivSmallModel.{u+1} (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves
      X)).inverse.map_isZero
      (isZero_zero _))⟩

instance coherentSmallVectorBundle_extensionClosed :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
      X).smallModel.IsExtensionClosed
      (coherentSmallVectorBundle X) where
  prop_middle hS h₁ h₃ := CategoryTheory.ExactCategory.ExactStructure.IsExtensionClosed.prop_middle
    (E := AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X) hS h₁ h₃

instance coherentSmallVectorBundle_finiteProducts :
    (coherentSmallVectorBundle X).IsClosedUnderFiniteProducts :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
    X).smallModel.extensionClosed_finiteProducts
    (coherentSmallVectorBundle X)

instance coherentSmallVectorBundle_kernelClosed
    [(AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).IsKernelClosed
      (coherentVectorBundle X)] :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel.IsKernelClosed
      (coherentSmallVectorBundle X) where
  prop_kernel hS h₂ h₃ := CategoryTheory.ExactCategory.ExactStructure.IsKernelClosed.prop_kernel
    (E := AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X) hS h₂ h₃

/-- Actual coherent resolutions descend to the actual chosen small model,
without changing their length or forgetting any admissible sequence. -/
theorem coherentSmallResolutionLength (n : ℕ)
    (h : ∀ M, (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).ResolutionLength
      (coherentVectorBundle X) n M) :
    ∀ M, (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
      X).smallModel.ResolutionLength
      (coherentSmallVectorBundle X) n M := by
  intro M
  let E := equivSmallModel.{u+1} (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves
    X)
  obtain ⟨T, hT⟩ := h (E.inverse.obj M)
  let T' := (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
    X).originalToSmallModel.mapFiniteResolution
    (P' := coherentSmallVectorBundle X)
    (fun N hN => (coherentVectorBundle X).prop_of_iso (E.unitIso.app N) hN) T
  exact ⟨T'.ofIso (E.counitIso.app M), by simpa [T'] using hT⟩

/-- The canonical small comparison, with its target restricted to vector
bundles inside the small coherent category. -/
def vectorBundleSmallLift : SmallModel.{u+1} (FiniteLocallyFree X) ⥤
    (coherentSmallVectorBundle X).FullSubcategory :=
  (coherentSmallVectorBundle X).lift (vectorBundleToCoherentExact X).smallModel.toFunctor
    (fun M => (coherentVectorBundle X).prop_of_iso
      ((equivSmallModel.{u+1} (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves
        X)).unitIso.app
        ((vectorBundleToCoherent X).obj ((equivSmallModel.{u+1} (FiniteLocallyFree
          X)).inverse.obj M)))
      (((equivSmallModel.{u+1} (FiniteLocallyFree X)).inverse.obj M).property))

instance vectorBundleSmallLift_full : (vectorBundleSmallLift X).Full := by
  dsimp [vectorBundleSmallLift, CategoryTheory.ExactCategory.ExactFunctor.smallModel,
    CategoryTheory.ExactCategory.ExactFunctor.comp,
    CategoryTheory.ExactCategory.ExactStructure.smallModelToOriginal,
      CategoryTheory.ExactCategory.ExactStructure.originalToSmallModel,
    CategoryTheory.ExactCategory.ExactStructure.equivalenceExactFunctor,
      CategoryTheory.ExactCategory.ExactStructure.equivalenceInverseExactFunctor,
    vectorBundleToCoherentExact]
  infer_instance

instance vectorBundleSmallLift_faithful : (vectorBundleSmallLift X).Faithful := by
  dsimp [vectorBundleSmallLift, CategoryTheory.ExactCategory.ExactFunctor.smallModel,
    CategoryTheory.ExactCategory.ExactFunctor.comp,
    CategoryTheory.ExactCategory.ExactStructure.smallModelToOriginal,
      CategoryTheory.ExactCategory.ExactStructure.originalToSmallModel,
    CategoryTheory.ExactCategory.ExactStructure.equivalenceExactFunctor,
      CategoryTheory.ExactCategory.ExactStructure.equivalenceInverseExactFunctor,
    vectorBundleToCoherentExact]
  infer_instance

instance vectorBundleSmallLift_additive : (vectorBundleSmallLift X).Additive := by
  dsimp [vectorBundleSmallLift]
  infer_instance

instance vectorBundleSmallLift_essSurj : (vectorBundleSmallLift X).EssSurj where
  mem_essImage Z := by
    let EV := equivSmallModel.{u+1} (FiniteLocallyFree X)
    let EC := equivSmallModel.{u+1}
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X)
    let V : FiniteLocallyFree X := ⟨(EC.inverse.obj Z.obj).obj, Z.property⟩
    let e : ((vectorBundleToCoherentExact X).smallModel.toFunctor).obj (EV.functor.obj V) ≅
        Z.obj :=
      EC.functor.mapIso ((vectorBundleToCoherent X).mapIso (EV.unitIso.app V).symm) ≪≫
        EC.counitIso.app Z.obj
    exact ⟨EV.functor.obj V, ⟨ObjectProperty.isoMk _ e⟩⟩

instance vectorBundleSmallLift_isEquivalence : (vectorBundleSmallLift X).IsEquivalence :=
  { }

/-- Restricting the codomain does not alter the actual exact comparison. -/
def vectorBundleSmallLiftExact :
    ExactFunctor (vectorBundleExactStructure X).smallModel
      (ExactSubcategory.exactStructure
        (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel
        (coherentSmallVectorBundle X)) where
  toFunctor := vectorBundleSmallLift X
  map_conflation S hS := (vectorBundleToCoherentExact X).smallModel.map_conflation S hS

/-- The lifted equivalence reflects the actual inherited exact structure. -/
theorem vectorBundleSmallLift_conflation_iff
    (S : ShortComplex (SmallModel.{u + 1} (FiniteLocallyFree X))) :
    (ExactSubcategory.exactStructure
      (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel
      (coherentSmallVectorBundle X)).conflation (S.map (vectorBundleSmallLift X)) ↔
      (vectorBundleExactStructure X).smallModel.conflation S := by
  let EV := equivSmallModel.{u+1} (FiniteLocallyFree X)
  let EC := equivSmallModel.{u+1} (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves
    X)
  let T := (S.map EV.inverse).map (vectorBundleToCoherent X)
  change (T.map (EC.functor ⋙ EC.inverse)).ShortExact ↔
    (vectorBundleExactStructure X).conflation (S.map EV.inverse)
  rw [vectorBundleToCoherent_shortExact_iff]
  exact (ShortComplex.shortExact_iff_of_iso (T.mapNatIso EC.unitIso)).symm

instance vectorBundleSmallLift_asEquivalence_additive :
    (vectorBundleSmallLift X).asEquivalence.functor.Additive :=
  inferInstanceAs (vectorBundleSmallLift X).Additive

instance vectorBundleSmallLiftExact_isEquivalence :
    (vectorBundleSmallLiftExact X).toFunctor.IsEquivalence :=
  inferInstanceAs (vectorBundleSmallLift X).IsEquivalence

/-- Pullback along the genuine lifted equivalence gives exactly the existing
small vector-bundle exact structure. -/
theorem vectorBundleSmallLift_ofEquivalence :
    (ExactSubcategory.exactStructure
      (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel
      (coherentSmallVectorBundle X)).ofEquivalence (vectorBundleSmallLift X).asEquivalence =
      (vectorBundleExactStructure X).smallModel := by
  apply CategoryTheory.ExactCategory.ExactStructure.ext_conflation
  funext S
  exact propext (vectorBundleSmallLift_conflation_iff X S)

instance vectorBundleSmallLiftExact_mapQ_isEquivalence :
    (vectorBundleSmallLiftExact X).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro A B i hi
    rw [← vectorBundleSmallLift_ofEquivalence X]
    exact (CategoryTheory.ExactCategory.ExactStructure.ofEquivalence_inflation_iff _ _ i).mpr hi
  · intro A B p hp
    rw [← vectorBundleSmallLift_ofEquivalence X]
    exact (CategoryTheory.ExactCategory.ExactStructure.ofEquivalence_deflation_iff _ _ p).mpr hp

/-- The actual canonical small comparison factors through the inherited
small vector-bundle subcategory, with identical underlying map. -/
theorem vectorBundleSmall_factor :
    (vectorBundleSmallLiftExact X).comp
      (Resolution.exactInclusion (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
        X).smallModel
        (coherentSmallVectorBundle X)) = (vectorBundleToCoherentExact X).smallModel := rfl

/-- Quillen's proved length-one theorem applies to the original canonical
scheme K-to-G map. The only hypothesis is the actual algebraic resolution
condition, with the exact subcategory's kernel closure. -/
theorem schemeKToG_bijective_of_length_one
    [(AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).IsKernelClosed
      (coherentVectorBundle X)]
    (h : ∀ M, (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).ResolutionLength
      (coherentVectorBundle X) 1 M) (n : ℕ) :
    Function.Bijective (schemeKToG X n) := by
  have h₁ := (vectorBundleSmallLiftExact X).KMap_bijective_of_mapQ_isEquivalence n
  have h₂ := Resolution.inclusionKMap_bijective_of_length_one
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel
      (coherentSmallVectorBundle X)
    (coherentSmallResolutionLength X 1 h) n
  change Function.Bijective ((vectorBundleToCoherentExact X).smallModel.KMap n)
  rw [← vectorBundleSmall_factor X, CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  exact h₂.comp h₁

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme
variable (R : CommRingCat.{u}) [IsDomain R] [IsPrincipalIdealRing R]

/-- Over the spectrum of a principal ideal domain, the canonical inclusion
of vector bundles into coherent sheaves induces an isomorphism on every
nonnegative K-group. All resolution hypotheses are proved from the PID
submodule theorem. -/
theorem KToG_pid_bijective (n : ℕ) : Function.Bijective (KToG (Spec R) n) :=
  AlgebraicGeometry.Scheme.Modules.schemeKToG_bijective_of_length_one (Spec R)
    (AlgebraicGeometry.Scheme.Modules.coherentResolution_length_le_one_of_pid R) n

/-- The actual canonical K-to-G equivalence for a principal ideal domain. -/
def KToGPIDEquiv (n : ℕ) : K (Spec R) n ≃* G (Spec R) n :=
  MulEquiv.ofBijective (KToG (Spec R) n) (KToG_pid_bijective R n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KToGPIDEquiv_coe (n : ℕ) :
    ↑(KToGPIDEquiv R n) = KToG (Spec R) n := rfl

end AlgebraicGeometry.Scheme
