/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.GeneralPushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealPushforward
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Coherent.AffineDetection
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.PushforwardIso

/-!
# Actual coherent pushforward along arbitrary closed immersions

Open base change and the quotient description of a closed immersion with
affine target prove coherence of the genuine module-sheaf pushforward.
Neither an assumed coherent pushforward nor an assumed localization theorem
is used in this construction.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme.ClosedImmersion.General
export AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
  (affineLocallyFiniteType_pushforward affineLocallyFiniteType_pushforward_affine
  affineLocallyFiniteType_pushforward_iso affinePresentationComparison coherentOpenBaseChange
  coherentPushforward coherentPushforwardExact coherentPushforward_comp_inclusion
  coherentPushforward_faithful coherentPushforward_quotient pushforwardFaithful)
end Quillen.CoherentScheme.ClosedImmersion.General

end



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
open Scheme.Modules

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The genuine covariant closed-immersion map on public scheme G-theory. -/
def coherentPushforwardGMap (n : ℕ) : G Z n →* G X n :=
  (coherentPushforwardExact i).smallKMap n

/-- The global canonical map agrees with the established affine closed map. -/
@[simp] theorem coherentPushforwardGMap_quotient (R : CommRingCat.{u}) [IsNoetherianRing R]
    (I : Ideal R) (n : ℕ) :
    coherentPushforwardGMap (Ideal.closedMap R I) n = Ideal.coherentPushforwardGMap R I n := rfl

/-- Actual open base change commutes with canonical global G-theory maps. -/
theorem coherentPushforwardGMap_openBaseChange {V : Scheme.{u}} [IsLocallyNoetherian V]
    (a : V ⟶ X) [IsOpenImmersion a] (n : ℕ) :
    (restrictionGMap a n).comp (coherentPushforwardGMap i n) =
      (coherentPushforwardGMap (pullback.snd i a) n).comp
        (restrictionGMap (pullback.fst i a) n) := by
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (coherentPushforwardExact i).comp (coherentRestrictionExact a))
    (G := (coherentRestrictionExact (pullback.fst i a)).comp
      (coherentPushforwardExact (pullback.snd i a)))
    (coherentOpenBaseChange i a) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, coherentPushforwardGMap,
    restrictionGMap] using h

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
