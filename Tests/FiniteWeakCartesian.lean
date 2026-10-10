/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.DoubleMappingCylinder.Finite.WeakCartesian

/-!
# Original finite weak-cartesian comparison consumers

The source fiber chart preserves its actual attaching point, the overlap map
retains its full band parameter, and whole weak edges suffice for both original
endpoint comparisons. The hypotheses include the actual compact graph condition
and genuine vertical fibrations, without any chosen homotopy inverse.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open Quillen Quillen.DoubleCylinder Quillen.DoubleCylinder.FiniteNormalization
universe u
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

example (x : A') (t : Parameter)
    (z : {z : (data sq' a b c wf wg).R //
      ((data sq' a b c wf wg).k0 ≫ (data sq' a b c wf wg).q0) z =
        overlapHomeomorph sq' (x,t)}) :
    (overlapSourceFiberHomeomorph sq' a b c wf wg x t z).val = z.val.1 := rfl

example (z : A × Parameter) :
    (data sq' a b c wf wg).k0 z =
      leftPullbackBandHomeomorph f' g' sq' lower upper zero_lt_upper b
        (leftEdge a b wf z.1,z.2) := rfl

example (z : A × Parameter) :
    (data sq' a b c wf wg).k1 z =
      rightPullbackBandHomeomorph f' g' sq' lower upper lower_lt_one c
        (rightEdge a c wg z.1,z.2) := rfl

variable
  (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
  (hc : HomotopyLiftingProperty c.hom)
  (hgraph : ∀ (S : Type u) [TopologicalSpace S] [CompactSpace S] [LocallyCompactSpace S]
    (v : C(S,Overlap sq')), IsClosed (Set.ofPred (fun z : S × Overlap sq' ↦ v z.1 = z.2)))
  (hf0 : IsWeakHomotopyEquivalence (leftEdge a b wf))
  (hf1 : IsWeakHomotopyEquivalence (rightEdge a c wg))

example : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
      (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
      (left_square sq sq' a b c wf wg)) :=
  leftEndComparison_isWeak_of_weak_edges sq sq' a b c wf wg ha hb hc hgraph hf0 hf1

example : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
      (Subdivision.rightEnd (e := e')).hom c.hom (Subdivision.rightEnd (e := e)).hom
      (right_square sq sq' a b c wf wg)) :=
  rightEndComparison_isWeak_of_weak_edges sq sq' a b c wf wg ha hb hc hgraph hf0 hf1

example (x : B) (t : unitInterval) :
    (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
      (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
      (left_square sq sq' a b c wf wg) x).val.2.2 t =
        Subdivision.leftEnd (e := e') (b x) := rfl
