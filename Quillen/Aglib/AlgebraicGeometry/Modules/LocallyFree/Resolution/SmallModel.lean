/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Exact
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.Affine
public import Quillen.Aglib.CategoryTheory.ExactCategory.Resolution.Closure
public import Quillen.Aglib.CategoryTheory.ExactCategory.Resolution.Transport

/-!
# Vector-bundle resolutions in small coherent models

The actual vector-bundle property and finite resolutions descend to the chosen coherent
small model. The lifted bundle inclusion is an exact equivalence onto its full subcategory.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

open Quillen

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
      X).smallModel.{u+1}.IsExtensionClosed
      (coherentSmallVectorBundle X) where
  prop_middle hS h₁ h₃ := CategoryTheory.ExactCategory.ExactStructure.IsExtensionClosed.prop_middle
    (E := AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X) hS h₁ h₃

instance coherentSmallVectorBundle_finiteProducts :
    (coherentSmallVectorBundle X).IsClosedUnderFiniteProducts :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
    X).smallModel.{u+1}.extensionClosed_finiteProducts
    (coherentSmallVectorBundle X)

instance coherentSmallVectorBundle_kernelClosed
    [(AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).IsKernelClosed
      (coherentVectorBundle X)] :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
      X).smallModel.{u+1}.IsKernelClosed
      (coherentSmallVectorBundle X) where
  prop_kernel hS h₂ h₃ := CategoryTheory.ExactCategory.ExactStructure.IsKernelClosed.prop_kernel
    (E := AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X) hS h₂ h₃

/-- Actual coherent resolutions descend to the actual chosen small model,
without changing their length or forgetting any admissible sequence. -/
theorem coherentSmallResolutionLength (n : ℕ)
    (h : ∀ M, (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).ResolutionLength
      (coherentVectorBundle X) n M) :
    ∀ M, (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
      X).smallModel.{u+1}.ResolutionLength
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
  (coherentSmallVectorBundle X).lift (vectorBundleToCoherentExact X).smallModel.{u+1}.toFunctor
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
    let e : ((vectorBundleToCoherentExact X).smallModel.{u+1}.toFunctor).obj (EV.functor.obj V) ≅
        Z.obj :=
      EC.functor.mapIso ((vectorBundleToCoherent X).mapIso (EV.unitIso.app V).symm) ≪≫
        EC.counitIso.app Z.obj
    exact ⟨EV.functor.obj V, ⟨ObjectProperty.isoMk _ e⟩⟩

instance vectorBundleSmallLift_isEquivalence : (vectorBundleSmallLift X).IsEquivalence :=
  { }

/-- Restricting the codomain does not alter the actual exact comparison. -/
def vectorBundleSmallLiftExact :
    ExactFunctor (vectorBundleExactStructure X).smallModel.{u+1}
      (ExactSubcategory.exactStructure
        (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel.{u+1}
        (coherentSmallVectorBundle X)) where
  toFunctor := vectorBundleSmallLift X
  map_conflation S hS := (vectorBundleToCoherentExact X).smallModel.{u+1}.map_conflation S hS

/-- The lifted equivalence reflects the actual inherited exact structure. -/
theorem vectorBundleSmallLift_conflation_iff
    (S : ShortComplex (SmallModel.{u + 1} (FiniteLocallyFree X))) :
    (ExactSubcategory.exactStructure
      (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel.{u+1}
      (coherentSmallVectorBundle X)).conflation (S.map (vectorBundleSmallLift X)) ↔
      (vectorBundleExactStructure X).smallModel.{u+1}.conflation S := by
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
      (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel.{u+1}
      (coherentSmallVectorBundle X)).ofEquivalence (vectorBundleSmallLift X).asEquivalence =
      (vectorBundleExactStructure X).smallModel.{u+1} := by
  apply CategoryTheory.ExactCategory.ExactStructure.ext_conflation
  funext S
  exact propext (vectorBundleSmallLift_conflation_iff X S)

/-- The actual canonical small comparison factors through the inherited
small vector-bundle subcategory, with identical underlying map. -/
theorem vectorBundleSmall_factor :
    (vectorBundleSmallLiftExact X).comp
      (Resolution.exactInclusion (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
        X).smallModel.{u+1}
        (coherentSmallVectorBundle X)) = (vectorBundleToCoherentExact X).smallModel.{u+1} := rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]

/-- Objectwise actual finite resolutions pass to the chosen small model;
no uniform bound is introduced. -/
theorem coherentSmallResolutionHypothesis
    (h : (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).ResolutionHypothesis
      (coherentVectorBundle X)) :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
      X).smallModel.{u+1}.ResolutionHypothesis
      (coherentSmallVectorBundle X) := by
  intro M
  let E := equivSmallModel.{u+1} (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves
    X)
  obtain ⟨T⟩ := h (E.inverse.obj M)
  let T' := (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure
    X).originalToSmallModel.mapFiniteResolution
    (P' := coherentSmallVectorBundle X)
    (fun N hN => (coherentVectorBundle X).prop_of_iso (E.unitIso.app N) hN) T
  exact ⟨T'.ofIso (E.counitIso.app M)⟩

end AlgebraicGeometry.Scheme.Modules
