/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralPushforward

public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.SmallModel

public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralSupportDevissage
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Equivalence
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel

/-!
# Geometric closed-support dévissage

Actual closed sheaf pushforward factors through the annihilated objects in
the compatible small supported category. It is an exact equivalence only
onto those annihilated objects. Genuine ideal-kernel dévissage then gives
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

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

local instance : PreservesFiniteLimits (coherentRestrictionExact (openMap i)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (openMap i)

local instance : PreservesFiniteColimits (coherentRestrictionExact (openMap i)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (openMap i)

local instance : (coherentRestrictionExact (openMap i)).toFunctor.IsLocalization
    (coherentRestrictionExact (openMap i)).toFunctor.kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel (openMap i)

instance smallPushforwardToKilledExact_mapQ_isEquivalence :
    (smallPushforwardToKilledExact i).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N a ha
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves Z))).inflation a
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff]
    have : Mono ((smallPushforwardToKilled i).map a) :=
      (abelianExactStructure_inflation_iff _ _).mp ha
    exact Functor.mono_of_mono_map (smallPushforwardToKilled i) this
  · intro M N a ha
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves Z))).deflation a
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff]
    have : Epi ((smallPushforwardToKilled i).map a) :=
      (abelianExactStructure_deflation_iff _ _).mp ha
    exact Functor.epi_of_epi_map (smallPushforwardToKilled i) this

/-- Public scheme G-theory of the closed subscheme is equivalent
to the actual compatible supported G-term by geometric dévissage. -/
def closedSupportGEquiv (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G Z n ≃* CoherentGlobalSupportedG (openMap i) n :=
  ((smallPushforwardToKilledExact i).KEquivOfMapQIsEquivalence n).trans
    (supportDevissageKEquiv i n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem closedSupportGEquiv_coe (n : ℕ) :
    (↑(closedSupportGEquiv i n) :
      AlgebraicGeometry.Scheme.Modules.Coherent.G Z n →* CoherentGlobalSupportedG (openMap i) n) =
      (smallPushforwardToSupportExact i).KMap n := by
  rw [smallPushforwardToSupportExact, CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  rfl

/-- The geometric dévissage comparison preserves exactly the canonical G-map
of actual sheaf pushforward, including small-model and zero normalizations. -/
theorem closedSupportGEquiv_pushforward (n : ℕ) :
    (SmallModelGLocalization.inclusionKMap.{u+1}
      (coherentRestrictionExact (openMap i)) n).comp
        (closedSupportGEquiv i n).toMonoidHom = coherentPushforwardGMap i n := by
  have h : ((smallPushforwardToKilledExact i).comp
      (CategoryTheory.ObjectProperty.exactInclusion (supportKilled i))).comp
      (CategoryTheory.ObjectProperty.exactInclusion (coherentGlobalSmallSupport (openMap i))) =
    (CategoryTheory.ExactCategory.ExactFunctor.smallModel.{u+1} (coherentPushforwardExact i)).comp
      (CategoryTheory.SmallModel.abelianExactComparison.{u+1} (FiniteTypeSheaves X)) := by rfl
  have hk := congrArg (fun F ↦ F.KMap n) h
  simp only [CategoryTheory.ExactCategory.ExactFunctor.KMap_comp] at hk
  ext x
  apply (SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves X) n).injective
  change SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves X) n
      ((SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves X) n).symm
        (Devissage.KMap (coherentGlobalSmallSupport (openMap i)) n
          (Devissage.KMap (supportKilled i) n
            ((smallPushforwardToKilledExact i).KMap n x)))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun hk x

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
