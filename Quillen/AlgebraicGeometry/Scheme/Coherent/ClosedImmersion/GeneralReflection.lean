/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AffineDetection
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.AffineReflection
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralUnitBaseChange
public import Quillen.Devissage.ReflectorFiltration

/-!
# The genuine coherent closed reflector

Affine epimorphic units and canonical open base change prove the global
unit is epic. Full faithfulness and subquotient closure of the actual
closed essential image are then consequences of the proved adjunction.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The actual coherent pullback unit is an epimorphism globally. -/
instance coherentAdjunction_unit_epi (M : FiniteTypeSheaves X) :
    Epi ((coherentAdjunction i).unit.app M) := by
  apply Preadditive.epi_of_isZero_cokernel
  apply coherent_isZero_of_affineRestrictions
  intro R _ a _
  have : Epi ((coherentAdjunction (pullback.snd i a)).unit.app
      ((finiteTypeSheavesRestriction a).obj M)) :=
    coherentAdjunction_affine_unit_epi R (pullback.snd i a) _
  have : Epi ((finiteTypeSheavesRestriction a).map ((coherentAdjunction i).unit.app M)) := by
    rw [← epi_comp_iff_of_isIso _ (coherentUnitTargetOpenBaseChange i a M).hom,
      coherentUnit_comp_target]
    infer_instance
  exact (isZero_cokernel_of_epi
    ((finiteTypeSheavesRestriction a).map ((coherentAdjunction i).unit.app M))).of_iso
      (PreservesCokernel.iso (finiteTypeSheavesRestriction a) ((coherentAdjunction i).unit.app M))

/-- Genuine global closed pushforward is fully faithful. -/
def fullyFaithfulCoherentPushforward : (coherentPushforward i).FullyFaithful :=
  ReflectorDevissage.fullyFaithfulRight (coherentAdjunction i)

instance coherentPushforward_full : (coherentPushforward i).Full :=
  (fullyFaithfulCoherentPushforward i).full

/-- The actual coherent-adjunction counit is an isomorphism. -/
instance coherentAdjunction_counit_isIso : IsIso (coherentAdjunction i).counit :=
  NatIso.isIso_of_isIso_app _

/-- The actual annihilated coherent objects, as the proved closed direct-image
essential image. It is smaller than the category of all supported objects. -/
abbrev coherentKilled : ObjectProperty (FiniteTypeSheaves X) := (finiteTypePushforward i).essImage

instance coherentKilled_containsZero : (coherentKilled i).ContainsZero :=
  ⟨⟨(finiteTypePushforward i).obj 0, (finiteTypePushforward i).map_isZero (isZero_zero _),
    (finiteTypePushforward i).obj_mem_essImage _⟩⟩

instance coherentKilled_subobjects : (coherentKilled i).IsClosedUnderSubobjects where
  prop_of_mono f _ h := ReflectorDevissage.essImage_of_mono (coherentAdjunction i) f h

instance coherentKilled_quotients : (coherentKilled i).IsClosedUnderQuotients where
  prop_of_epi {M N} p hp hM := by
    have hK : coherentKilled i (kernel p) :=
      (coherentKilled i).prop_of_mono (kernel.ι p) hM
    have hS : (ShortComplex.kernelSequence p).ShortExact :=
      { exact := ShortComplex.kernelSequence_exact p, epi_g := hp }
    apply (coherentKilled i).prop_of_isColimit hS.gIsCokernel
    rintro (_ | _)
    · exact hK
    · exact hM

instance coherentKilled_finiteProducts : (coherentKilled i).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    dsimp [coherentKilled]
    infer_instance

/-- The actual closed essential image is equivalently recognized by the
actual adjunction unit being an isomorphism. -/
theorem coherentKilled_iff_unit_isIso (M : FiniteTypeSheaves X) :
    coherentKilled i M ↔ IsIso ((coherentAdjunction i).unit.app M) :=
  (coherentAdjunction i).isIso_unit_app_iff_mem_essImage.symm

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
