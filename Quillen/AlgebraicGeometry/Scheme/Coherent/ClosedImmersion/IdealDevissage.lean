/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealSmallModel

public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealPushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealSupportDevissage

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Equivalence
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel
/-!
# Geometric affine closed-support dévissage

Actual closed sheaf pushforward factors through the annihilated objects in
the compatible small supported category. It is an exact equivalence only
onto those annihilated objects. Genuine finite-image dévissage then gives
the supported G-equivalence, with the original canonical pushforward map.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent
open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

local instance : PreservesFiniteLimits (coherentRestrictionExact (openMap R I)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (openMap R I)

local instance : PreservesFiniteColimits (coherentRestrictionExact (openMap R I)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (openMap R I)

local instance : (coherentRestrictionExact (openMap R I)).toFunctor.IsLocalization
    (coherentRestrictionExact (openMap R I)).toFunctor.kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel (openMap R I)

instance smallPushforwardToKilledExact_mapQ_isEquivalence :
    (smallPushforwardToKilledExact R I).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N a ha
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves (Spec
        (Pushforward.ClosedImmersion.Ideal.closedRing R I))))).inflation a
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff]
    have : Mono ((smallPushforwardToKilled R I).map a) :=
      (abelianExactStructure_inflation_iff _ _).mp ha
    exact Functor.mono_of_mono_map (smallPushforwardToKilled R I) this
  · intro M N a ha
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves (Spec
        (Pushforward.ClosedImmersion.Ideal.closedRing R I))))).deflation a
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff]
    have : Epi ((smallPushforwardToKilled R I).map a) :=
      (abelianExactStructure_deflation_iff _ _).mp ha
    exact Functor.epi_of_epi_map (smallPushforwardToKilled R I) this

/-- Public scheme G-theory of the affine closed subscheme is equivalent
to the actual compatible supported G-term by geometric dévissage. -/
def closedSupportGEquiv (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R I)) n ≃*
      CoherentGlobalSupportedG (openMap R I) n :=
  ((smallPushforwardToKilledExact R I).KEquivOfMapQIsEquivalence n).trans
    (supportDevissageKEquiv R I n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem closedSupportGEquiv_coe (n : ℕ) :
    (↑(closedSupportGEquiv R I n) :
      AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec
        (Pushforward.ClosedImmersion.Ideal.closedRing R I)) n →*
        CoherentGlobalSupportedG (openMap R I) n) =
      (smallPushforwardToSupportExact R I).KMap n := by
  rw [smallPushforwardToSupportExact, CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  rfl

/-- The geometric dévissage comparison preserves exactly the canonical G-map
of actual sheaf pushforward, including small-model and zero normalizations. -/
theorem closedSupportGEquiv_pushforward (n : ℕ) :
    (SmallModelGLocalization.inclusionKMap.{u+1}
      (coherentRestrictionExact (openMap R I)) n).comp
        (closedSupportGEquiv R I n).toMonoidHom = coherentPushforwardGMap R I n := by
  have h : ((smallPushforwardToKilledExact R I).comp
      (CategoryTheory.ObjectProperty.exactInclusion (supportKilled R I))).comp
      (CategoryTheory.ObjectProperty.exactInclusion (coherentGlobalSmallSupport (openMap R I))) =
    (CategoryTheory.ExactCategory.ExactFunctor.smallModel.{u+1} (coherentPushforwardExact R I)).comp
      (CategoryTheory.SmallModel.abelianExactComparison.{u+1} (FiniteTypeSheaves (Spec R))) :=
        by rfl
  have hk := congrArg (fun F ↦ F.KMap n) h
  simp only [CategoryTheory.ExactCategory.ExactFunctor.KMap_comp] at hk
  ext x
  apply (SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves (Spec R)) n).injective
  change SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves (Spec R)) n
      ((SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves (Spec R)) n).symm
        (Devissage.KMap (coherentGlobalSmallSupport (openMap R I)) n
          (Devissage.KMap (supportKilled R I) n
            ((smallPushforwardToKilledExact R I).KMap n x)))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun hk x

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
