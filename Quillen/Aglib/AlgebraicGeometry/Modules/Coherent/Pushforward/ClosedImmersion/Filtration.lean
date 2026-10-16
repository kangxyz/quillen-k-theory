/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.Nilpotence
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Subcategory
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Functor
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Refinement
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis

/-!
# Finite coherent closed-support filtrations

Under the original noetherian hypotheses, genuine closed support produces finite filtrations whose factors are annihilated by the defining ideal. The actual supported categorical presentations and their universes are retained.
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

open Quillen

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The genuine finite coherent filtration by actual closed-image factors. -/

theorem coherentClosedFiltration (M : FiniteTypeSheaves X)
    (hM : finiteTypeSheavesSupportedAway (openMap i) M) :
    Nonempty ((coherentExactStructure X).Filtration (coherentKilled i) M) :=
  ReflectorDevissage.exists_filtration_of_eventually_zero (coherentAdjunction i).unit
    (coherentKilled i) (fun _ ↦ (coherentPushforward i).obj_mem_essImage _)
      M (kernelIterate_eventually_zero i M hM)

/-- The full subcategory of the global small coherent model consisting of objects supported on the
closed image of `i`. -/

abbrev SmallSupport := (coherentGlobalSmallSupport (openMap i)).FullSubcategory

/-- The actual coherent object represented by the compatible small support category. -/

abbrev supportRepresentation : SmallSupport i ⥤ FiniteTypeSheaves X :=
  (coherentGlobalSmallSupport (openMap i)).ι ⋙ (equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse

/-- The actual annihilated property in that genuine support presentation. -/

abbrev supportKilled : ObjectProperty (SmallSupport i) :=
  (coherentKilled i).inverseImage (supportRepresentation i)

instance supportRepresentation_preservesFiniteLimits : PreservesFiniteLimits (supportRepresentation
  i) := by
  let : PreservesFiniteLimits (coherentGlobalSmallSupport (openMap i)).ι :=
    CategoryTheory.ObjectProperty.inclusion_preservesFiniteLimits _
  exact comp_preservesFiniteLimits _ _

instance supportRepresentation_preservesFiniteColimits : PreservesFiniteColimits
  (supportRepresentation i) := by
  let : PreservesFiniteColimits (coherentGlobalSmallSupport (openMap i)).ι :=
    CategoryTheory.ObjectProperty.inclusion_preservesFiniteColimits _
  exact comp_preservesFiniteColimits _ _

instance supportKilled_containsZero : (supportKilled i).ContainsZero := by
  dsimp [supportKilled]
  infer_instance

instance supportKilled_subobjects : (supportKilled i).IsClosedUnderSubobjects := by
  dsimp [supportKilled]
  infer_instance

instance supportKilled_quotients : (supportKilled i).IsClosedUnderQuotients := by
  dsimp [supportKilled]
  infer_instance

instance supportKilled_finiteProducts : (supportKilled i).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := {
    limitsOfShape_le := by
      rintro M ⟨p⟩
      exact (coherentKilled i).prop_of_isLimit
        (isLimitOfPreserves (supportRepresentation i) p.isLimit)
        (fun j ↦ p.prop_diag_obj j) }

instance supportPresentationInverse_additive :
    (coherentGlobalSmallSupportEquivalence (openMap i)).inverse.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (coherentGlobalSmallSupportEquivalence (openMap i)).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The inverse of the canonical support presentation, as an exact functor. -/

def supportPresentationExact :
    ExactFunctor (supportedCoherentExactStructure (openMap i))
      (abelianExactStructure (SmallSupport i)) where
  toFunctor := (coherentGlobalSmallSupportEquivalence (openMap i)).inverse
  map_conflation _ h := h.map_of_exact _

/-- Genuine geometric finite filtrations give the small dévissage hypothesis. -/

theorem supportFiltrationHypothesis : Devissage.FiltrationHypothesis (supportKilled i) := by
  intro M
  let E := coherentGlobalSmallSupportEquivalence (openMap i)
  let N := E.functor.obj M
  obtain ⟨F⟩ := coherentClosedFiltration i N.obj N.property
  let F' := F.toFullSubcategory (finiteTypeSheavesSupportedAway (openMap i)) N.property
  have hp (Q : SupportedFiniteTypeSheaves (openMap i)) (hQ : coherentKilled i Q.obj) :
      supportKilled i (E.inverse.obj Q) :=
    (coherentKilled i).prop_of_iso
      ((finiteTypeSheavesSupportedAway (openMap i)).ι.mapIso (E.counitIso.app Q)).symm hQ
  let F'' := (supportPresentationExact i).mapFiltration hp F'
  exact ⟨F''.ofIso (E.unitIso.app M).symm⟩

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
