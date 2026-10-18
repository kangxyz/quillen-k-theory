/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.GTheory.SmallModelBoundaryNaturality
public import Quillen.AlgebraicGeometry.Scheme.PrincipalClosedGTheory
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.LocalizationNaturality
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ClosedDevissage

/-!
# The original public principal-closed boundary under affine global sections

For a noetherian ring and an arbitrary element, the original public
`Scheme.PrincipalClosed.boundaryG` agrees with the native finite-module
`closedConnectingHom` under the canonical `publicSpecGRingEquiv` comparisons.

The ordinary closed-pushforward/global-sections isomorphism is lifted through
the fully faithful category inclusion of the actual module-localization
kernel. The same-universe localization square and the original SmallModel
boundary universe comparison then commute before either supported equivalence
is inverted. No ambient K-group inclusion is cancelled.

This is the principal-open boundary used by the literal local-DVR construction.
The separate fraction-field and residue-field coordinate isomorphisms are not
changed or identified merely from an abstract equivalence of groups.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe w₁ w₂ u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry
open Quillen ModuleCat AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : Type u) [Category.{v} C] [Abelian C]
  [EssentiallySmall.{w₁} C] [EssentiallySmall.{w₂} C]

private def modelRoundTripIso :
    (Quillen.SmallModelBoundaryNaturality.Universe.standardComparison.{w₁,w₂} C).toFunctor ⋙
      (Quillen.SmallModelBoundaryNaturality.Universe.standardComparison.{w₂,w₁} C).toFunctor ≅
    𝟭 (SmallModel.{w₁} C) :=
  Functor.isoWhiskerLeft (equivSmallModel.{w₁} C).inverse
    (Functor.isoWhiskerRight (equivSmallModel.{w₂} C).unitIso.symm
      (equivSmallModel.{w₁} C).functor) ≪≫
    Functor.isoWhiskerLeft (equivSmallModel.{w₁} C).inverse
      (Functor.leftUnitor (equivSmallModel.{w₁} C).functor) ≪≫
        (equivSmallModel.{w₁} C).counitIso

private theorem smallKUniverseEquiv_roundTrip (n : ℕ) :
    ((abelianExactStructure C).smallKUniverseEquiv.{w₂,w₁} n).toMonoidHom.comp
      ((abelianExactStructure C).smallKUniverseEquiv.{w₁,w₂} n).toMonoidHom =
    MonoidHom.id _ := by
  change (((abelianExactStructure C).smallModelUniverseComparison.{w₂,w₁}).universalKMap n).comp
    (((abelianExactStructure C).smallModelUniverseComparison.{w₁,w₂}).universalKMap n) = _
  rw [← ExactFunctor.universalKMap_comp]
  have h := ExactFunctor.universalKMap_eq_of_natIso
    (F := ((abelianExactStructure C).smallModelUniverseComparison.{w₁,w₂}).comp
      ((abelianExactStructure C).smallModelUniverseComparison.{w₂,w₁}))
    (G := ExactFunctor.id (abelianExactStructure C).smallModel.{w₁})
    (modelRoundTripIso.{w₁,w₂} C) n
  rw [ExactFunctor.universalKMap_eq_KMap
    (ExactFunctor.id (abelianExactStructure C).smallModel.{w₁}), ExactFunctor.KMap_id] at h
  exact h

end AlgebraicGeometry.Scheme.Modules.Coherent


namespace AlgebraicGeometry.Scheme.Modules.Coherent
attribute [local instance] Abelian.hasFiniteBiproducts
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

local instance : PreservesFiniteLimits (coherentRestrictionExact (principalOpen R f)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (principalOpen R f)
local instance : PreservesFiniteColimits (coherentRestrictionExact (principalOpen R f)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (principalOpen R f)
local instance : (coherentRestrictionExact (principalOpen R f)).toFunctor.IsLocalization
    (coherentRestrictionExact (principalOpen R f)).toFunctor.kernel.isoModSerre :=
  coherentPrincipalRestriction_isLocalization_kernel R f

private def upperLocalizationSquare :
    ((coherentRestrictionExact (principalOpen R f)).comp
      (globalSectionsExact (CommRingCat.of (Localization.Away f)))).toFunctor ≅
    ((globalSectionsExact R).comp
      (FiniteModuleLocalization.exactFunctor (Submonoid.powers f))).toFunctor :=
  Functor.isoWhiskerRight (coherentRestrictionIsoPullback (principalOpen R f))
    (globalSectionsExact (CommRingCat.of (Localization.Away f))).toFunctor ≪≫
      coherentLocalizationGlobalSectionsIso (Submonoid.powers f)

local instance : PreservesFiniteLimits
    (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)).toFunctor :=
  inferInstanceAs
    (PreservesFiniteLimits (ModuleCat.FiniteLocalization.functor (Submonoid.powers f)))
local instance : PreservesFiniteColimits
    (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)).toFunctor :=
  inferInstanceAs
    (PreservesFiniteColimits (ModuleCat.FiniteLocalization.functor (Submonoid.powers f)))
local instance :
    (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)).toFunctor.IsLocalization
    (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)).toFunctor.kernel.isoModSerre :=
  inferInstanceAs ((ModuleCat.FiniteLocalization.functor (Submonoid.powers f)).IsLocalization
    (ModuleCat.FiniteLocalization.torsion (Submonoid.powers f)).isoModSerre)

private def upperSupportExact := Quillen.SmallModelBoundaryNaturality.Square.supportExact.{u+1}
  (coherentRestrictionExact (principalOpen R f))
  (FiniteModuleLocalization.exactFunctor (Submonoid.powers f))
  (globalSectionsExact R) (globalSectionsExact (CommRingCat.of (Localization.Away f)))
  (upperLocalizationSquare R f)

open AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal

private theorem closedBoundary_into_upperKernel (n : ℕ)
    (a : Scheme.G (Spec (CommRingCat.of (Localization.Away f))) (n + 1)) :
    (upperSupportExact R f).KMap n
      (closedSupportGEquiv R f n (Scheme.PrincipalClosed.boundaryG R f n a)) =
    SmallModelGLocalization.connectingHom.{u+1}
      (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)) n
        ((globalSectionsExact (CommRingCat.of (Localization.Away f))).smallKMap.{u+1}
          (n + 1) a) := by
  have hc : closedSupportGEquiv R f n (Scheme.PrincipalClosed.boundaryG R f n a) =
      SmallModelGLocalization.connectingHom.{u+1}
        (coherentRestrictionExact (principalOpen R f)) n a := by
    change closedSupportGEquiv R f n
      ((closedSupportGEquiv R f n).symm
        (coherentPrincipalSupportedGEquiv R f n
          ((coherentPrincipalSupportedGEquiv R f n).symm
            (SmallModelGLocalization.connectingHom.{u+1}
              (coherentRestrictionExact (principalOpen R f)) n a)))) = _
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rw [hc]
  exact DFunLike.congr_fun
    (Quillen.SmallModelBoundaryNaturality.Square.connecting_naturality.{u+1}
      (coherentRestrictionExact (principalOpen R f))
      (FiniteModuleLocalization.exactFunctor (Submonoid.powers f))
      (globalSectionsExact R) (globalSectionsExact (CommRingCat.of (Localization.Away f)))
      (upperLocalizationSquare R f) n) a

private abbrev closedRing := Pushforward.ClosedImmersion.Ideal.closedRing R (Ideal.span {f})

private def publicGlobalSectionsExact (T : CommRingCat.{u}) [IsNoetherianRing T] :
    ExactFunctor (coherentExactStructure (Spec T)).smallModel.{u+1}
      (ModuleCat.finiteModuleExactStructure.{u,u} T).smallModel.{u} :=
  ((coherentExactStructure (Spec T)).smallModelUniverseComparison.{u+1,u}).comp
    (globalSectionsExact T).smallModel.{u}

private def ordinaryClosedSquare :
    ((Pushforward.ClosedImmersion.Ideal.coherentPushforwardExact R (Ideal.span {f})).comp
      (globalSectionsExact R)).toFunctor ≅
    ((globalSectionsExact (closedRing R f)).comp
      (FiniteModuleLocalization.closedRestrictionExact f)).toFunctor :=
  Pushforward.ClosedImmersion.Ideal.coherentPushforwardSquare R (Ideal.span {f})

private def supportedLowerRoute : ExactFunctor
    (coherentExactStructure (Spec (closedRing R f))).smallModel.{u+1}
    (ObjectProperty.subcategoryExactStructure
      (SmallModelGLocalization.supported.{u+1}
        (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)))) :=
  ((publicGlobalSectionsExact (closedRing R f)).comp
    (FiniteModuleLocalization.smallClosedToSupportExact f)).comp
      (Quillen.SmallModelBoundaryNaturality.Universe.supportExact.{u,u+1}
        (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)))

private def supportedUpperRoute : ExactFunctor
    (coherentExactStructure (Spec (closedRing R f))).smallModel.{u+1}
    (ObjectProperty.subcategoryExactStructure
      (SmallModelGLocalization.supported.{u+1}
        (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)))) :=
  (Pushforward.ClosedImmersion.Principal.smallPushforwardToSupportExact R f).comp
    (upperSupportExact R f)

private def supportedGlobalSectionsIso :
    (supportedLowerRoute R f).toFunctor ≅ (supportedUpperRoute R f).toFunctor := by
  apply Functor.fullyFaithfulCancelRight
    (SmallModelGLocalization.supported.{u+1}
      (FiniteModuleLocalization.exactFunctor (Submonoid.powers f))).ι
  let H := (Pushforward.ClosedImmersion.Ideal.coherentPushforwardExact R (Ideal.span {f})).comp
    (globalSectionsExact R)
  let Cmp := (coherentExactStructure (Spec (closedRing R f))).smallModelUniverseComparison.{u+1,u}
  let U := (ModuleCat.finiteModuleExactStructure.{u,u} R).smallModelUniverseComparison.{u,u+1}
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft Cmp.toFunctor
        ((ExactFunctor.smallModelCompIso.{u} (globalSectionsExact (closedRing R f))
          (FiniteModuleLocalization.closedRestrictionExact f)).symm ≪≫
          ExactFunctor.smallModelNatIso.{u} (ordinaryClosedSquare R f).symm)) U.toFunctor ≪≫
    Functor.isoWhiskerRight
      (ExactFunctor.smallModelUniverseComparisonNaturalityIso.{u+1,u} H) U.toFunctor ≪≫
    Functor.isoWhiskerLeft H.smallModel.{u+1}.toFunctor
      (modelRoundTripIso.{u+1,u} (FGModuleCat.{u} R)) ≪≫
    Functor.rightUnitor H.smallModel.{u+1}.toFunctor ≪≫
      ExactFunctor.smallModelCompIso.{u+1}
        (Pushforward.ClosedImmersion.Ideal.coherentPushforwardExact R (Ideal.span {f}))
        (globalSectionsExact R)


private theorem publicGlobalSectionsExact_universalKMap (T : CommRingCat.{u}) [IsNoetherianRing T]
    (n : ℕ) :
    (publicGlobalSectionsExact T).universalKMap n = (publicSpecGRingEquiv T n).toMonoidHom := by
  rw [publicSpecGRingEquiv_toMonoidHom]
  unfold publicGlobalSectionsExact
  rw [ExactFunctor.universalKMap_comp,
    ExactFunctor.universalKMap_eq_KMap (globalSectionsExact T).smallModel.{u}]
  rfl

private theorem publicGlobalSections_up (T : CommRingCat.{u}) [IsNoetherianRing T] (n : ℕ)
    (a : Scheme.G (Spec T) n) :
    (ModuleCat.finiteModuleExactStructure.{u,u} T).smallKUniverseEquiv.{u,u+1} n
      (publicSpecGRingEquiv T n a) = (globalSectionsExact T).smallKMap.{u+1} n a := by
  have hn := DFunLike.congr_fun
    (ExactFunctor.smallKUniverseEquiv_naturality.{u+1,u} (globalSectionsExact T) n) a
  have hs := DFunLike.congr_fun (publicSpecGRingEquiv_toMonoidHom T n) a
  change publicSpecGRingEquiv T n a =
    (globalSectionsExact T).smallKMap.{u} n
      ((coherentExactStructure (Spec T)).smallKUniverseEquiv.{u+1,u} n a) at hs
  change (globalSectionsExact T).smallKMap.{u} n
      ((coherentExactStructure (Spec T)).smallKUniverseEquiv.{u+1,u} n a) =
    (ModuleCat.finiteModuleExactStructure.{u,u} T).smallKUniverseEquiv.{u+1,u} n
      ((globalSectionsExact T).smallKMap.{u+1} n a) at hn
  rw [hs, hn]
  exact DFunLike.congr_fun (smallKUniverseEquiv_roundTrip.{u+1,u}
    (FGModuleCat.{u} T) n) ((globalSectionsExact T).smallKMap.{u+1} n a)

set_option maxHeartbeats 800000 in
-- The exact support routes retain the full sheaf and model-comparison expressions.
private theorem supportedGlobalSectionsKMap (n : ℕ) (a : Scheme.G (Spec (closedRing R f)) n) :
    (Quillen.SmallModelBoundaryNaturality.Universe.supportExact.{u,u+1}
      (FiniteModuleLocalization.exactFunctor (Submonoid.powers f))).universalKMap n
        (FiniteModuleLocalization.closedSupportGEquiv f n
          (publicSpecGRingEquiv (closedRing R f) n a)) =
    (upperSupportExact R f).KMap n
      (Pushforward.ClosedImmersion.Principal.closedSupportGEquiv R f n a) := by
  let A := publicGlobalSectionsExact (closedRing R f)
  let B := FiniteModuleLocalization.smallClosedToSupportExact f
  let C := Quillen.SmallModelBoundaryNaturality.Universe.supportExact.{u,u+1}
    (FiniteModuleLocalization.exactFunctor (Submonoid.powers f))
  let D := Pushforward.ClosedImmersion.Principal.smallPushforwardToSupportExact R f
  let E := upperSupportExact R f
  have h := ExactFunctor.universalKMap_eq_of_natIso (supportedGlobalSectionsIso R f) n
  have hL : (supportedLowerRoute R f).universalKMap n =
      (C.universalKMap n).comp ((B.KMap n).comp (A.universalKMap n)) :=
    (ExactFunctor.universalKMap_comp (A.comp B) C n).trans
      (congrArg (fun k => (C.universalKMap n).comp k)
        ((ExactFunctor.universalKMap_comp A B n).trans
          (congrArg (fun k => k.comp (A.universalKMap n))
            (ExactFunctor.universalKMap_eq_KMap B n))))
  have hR : (supportedUpperRoute R f).universalKMap n = (E.KMap n).comp (D.KMap n) :=
    (ExactFunctor.universalKMap_comp D E n).trans
      ((congrArg (fun k => k.comp (D.universalKMap n))
        (ExactFunctor.universalKMap_eq_KMap E n)).trans
        (congrArg (fun k => (E.KMap n).comp k) (ExactFunctor.universalKMap_eq_KMap D n)))
  have hm := DFunLike.congr_fun (hL.symm.trans (h.trans hR)) a
  have hp := DFunLike.congr_fun
    (publicGlobalSectionsExact_universalKMap (closedRing R f) n) a
  have hl := DFunLike.congr_fun (FiniteModuleLocalization.closedSupportGEquiv_coe f n)
    (publicSpecGRingEquiv (closedRing R f) n a)
  have hr := DFunLike.congr_fun
    (Pushforward.ClosedImmersion.Principal.closedSupportGEquiv_coe R f n) a
  change FiniteModuleLocalization.closedSupportGEquiv f n
      (publicSpecGRingEquiv (closedRing R f) n a) =
    (FiniteModuleLocalization.smallClosedToSupportExact f).KMap n
      (publicSpecGRingEquiv (closedRing R f) n a) at hl
  change Pushforward.ClosedImmersion.Principal.closedSupportGEquiv R f n a = D.KMap n a at hr
  exact (congrArg (C.universalKMap n) hl).trans
    ((congrArg (fun x => C.universalKMap n (B.KMap n x)) hp.symm).trans
      (hm.trans (congrArg (E.KMap n) hr.symm)))


set_option maxHeartbeats 800000 in
-- Compare the original supported-equivalence and SmallModel boundary expressions.
/-- The literal public principal-closed boundary equals the original native module boundary
under the canonical affine comparisons, in every nonnegative degree. -/
theorem publicSpecGRingEquiv_principalClosed_boundaryG (n : ℕ) :
    (publicSpecGRingEquiv
      (Pushforward.ClosedImmersion.Ideal.closedRing R (Ideal.span {f})) n).toMonoidHom.comp
      (Scheme.PrincipalClosed.boundaryG R f n) =
    (FiniteModuleLocalization.closedConnectingHom f n).comp
      (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1)).toMonoidHom := by
  apply MonoidHom.ext
  intro a
  apply (FiniteModuleLocalization.closedSupportGEquiv f n).injective
  apply ((Quillen.SmallModelBoundaryNaturality.Universe.supportExact.{u,u+1}
    (FiniteModuleLocalization.exactFunctor (Submonoid.powers f))).universalKEquivOfMapQIsEquivalence
      n).injective
  change (Quillen.SmallModelBoundaryNaturality.Universe.supportExact.{u,u+1}
      (FiniteModuleLocalization.exactFunctor (Submonoid.powers f))).universalKMap n
        (FiniteModuleLocalization.closedSupportGEquiv f n
          (publicSpecGRingEquiv (closedRing R f) n (Scheme.PrincipalClosed.boundaryG R f n a))) =
    (Quillen.SmallModelBoundaryNaturality.Universe.supportExact.{u,u+1}
      (FiniteModuleLocalization.exactFunctor (Submonoid.powers f))).universalKMap n
        (FiniteModuleLocalization.closedSupportGEquiv f n
          (FiniteModuleLocalization.closedConnectingHom f n
            (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1) a)))
  have hc : FiniteModuleLocalization.closedSupportGEquiv f n
      (FiniteModuleLocalization.closedConnectingHom f n
        (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1) a)) =
    FiniteModuleLocalization.connectingHom (Submonoid.powers f) n
      (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1) a) :=
    (FiniteModuleLocalization.closedSupportGEquiv f n).apply_symm_apply _
  rw [hc, supportedGlobalSectionsKMap, closedBoundary_into_upperKernel]
  have hn := DFunLike.congr_fun
    (Quillen.SmallModelBoundaryNaturality.Universe.connectingHom_universe.{u+1,u}
    (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)) n)
      (publicSpecGRingEquiv (CommRingCat.of (Localization.Away f)) (n + 1) a)
  have hu := publicGlobalSections_up (CommRingCat.of (Localization.Away f)) (n + 1) a
  exact (congrArg (SmallModelGLocalization.connectingHom.{u+1}
    (FiniteModuleLocalization.exactFunctor (Submonoid.powers f)) n) hu.symm).trans hn.symm

end AlgebraicGeometry.Scheme.Modules.Coherent
