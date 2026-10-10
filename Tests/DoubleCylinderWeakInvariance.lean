/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.DoubleMappingCylinder.WeakInvariance

/-!
# Original weak double-cylinder map consumers

The actual map preserves the entire cylinder parameter, the literal overlap
restriction needs only the attaching weak map, and the whole cylinder needs
only objectwise weak maps. No cofibration or lifting hypotheses are present.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open Quillen Quillen.DoubleCylinder CubicalSubdivision
universe u
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

example (x : A) (t : TopCat.I) :
    map sq sq' a b c wf wg (l (x,t)) = l' (a x,t) :=
  map_cylinder_apply sq sq' a b c wf wg x t

example (lo hi : unitInterval) (z : A × Band lo hi) :
    (overlapBandHomeomorph sq lo hi z).val = l (z.1,ULift.up z.2.val) := rfl

example (lo hi : unitInterval) (ha : IsWeakHomotopyEquivalence a.hom) :
    IsWeakHomotopyEquivalence (restriction (map sq sq' a b c wf wg).hom
      (leftCollarSet f' g' sq' hi ∩ rightCollarSet f' g' sq' lo)) :=
  overlapRestriction_isWeakHomotopyEquivalence sq sq' a b c wf wg lo hi ha

example (ha : IsWeakHomotopyEquivalence a.hom) (hb : IsWeakHomotopyEquivalence b.hom)
    (hc : IsWeakHomotopyEquivalence c.hom) :
    IsWeakHomotopyEquivalence (map sq sq' a b c wf wg).hom :=
  map_isWeakHomotopyEquivalence sq sq' a b c wf wg ha hb hc
