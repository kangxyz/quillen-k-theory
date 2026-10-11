/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.FinitePushforward

/-! Independent consumers of the original finite coherent G-pushforward:
open base change on elements and inverse scheme-isomorphism transport. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CoherentScheme
universe u
namespace Consumer.FinitePushforward

/-- Restricting an original pushforward class agrees with pushing forward
its restriction to the actual cartesian inverse-image open. -/
theorem original_open_base_change {Z X U : Scheme.{u}}
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) (x : G Z n) :
    Finite.coherentPushforwardGMap (pullback.snd f j) n
        (restrictionGMap (pullback.fst f j) n x) =
      restrictionGMap j n (Finite.coherentPushforwardGMap f n x) :=
  congrArg (fun h ↦ h x) (Finite.coherentPushforwardGMap_openBaseChange f j n).symm

/-- The actual direct images along inverse scheme isomorphisms cancel on G-classes. -/
theorem original_isomorphism_transport {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (e : X ≅ Y) (n : ℕ) (x : G X n) :
    Finite.coherentPushforwardGMap e.inv n (Finite.coherentPushforwardGMap e.hom n x) = x :=
  congrArg (fun h ↦ h x) (Finite.coherentPushforwardGMap_iso_inv_comp e n)

end Consumer.FinitePushforward
