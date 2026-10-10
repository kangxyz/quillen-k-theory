/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyPullback.WeakPushout
public import Quillen.Topology.Realization.DoubleCylinderCompactGraph

/-! # Original weak-cartesian pushout comparison regressions

Only the two original incoming comparisons are weak hypotheses. The target
cylinder's Hausdorff instance supplies its actual graph condition here, and
both outgoing comparison maps retain the original points and constant paths.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Quillen Quillen.CartesianPushout
open scoped Topology unitInterval
universe u
variable {A B C P A' B' C' P' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (hf : TheoremA.homotopyExtensionProperty f) (hf' : TheoremA.homotopyExtensionProperty f')
  [hHaus : T2Space (Cylinder f' g')]
  (hL : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison b.hom f'.hom a.hom f.hom (congrArg TopCat.Hom.hom wf)))
  (hR : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison c.hom g'.hom a.hom g.hom (congrArg TopCat.Hom.hom wg)))

include sq sq' wf wg wi wj hf hf' hL hR hHaus in
example : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom wi)) := by
  apply leftComparison_isWeakHomotopyEquivalence sq sq' a b c p wf wg wi wj hf hf' _ hL hR
  intro K _ _ _ d
  exact isClosed_eq (d.continuous.comp continuous_fst) continuous_snd

include sq sq' wf wg wi wj hf hf' hL hR hHaus in
example : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom wj)) := by
  apply rightComparison_isWeakHomotopyEquivalence sq sq' a b c p wf wg wi wj hf hf' _ hL hR
  intro K _ _ _ d
  exact isClosed_eq (d.continuous.comp continuous_fst) continuous_snd

example (x : B) :
    (HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom wi) x).val =
      (b x,i x,ContinuousMap.const unitInterval (i' (b x))) := rfl

example (x : C) :
    (HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom wj) x).val =
      (c x,j x,ContinuousMap.const unitInterval (j' (c x))) := rfl

example (x : B) (t : unitInterval) :
    (HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom wi) x).val.2.2 t
      =
      i' (b x) := rfl

example (x : C) (t : unitInterval) :
    (HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom wj) x).val.2.2 t
      =
      j' (c x) := rfl

section RealizedTarget
open scoped Simplicial
variable {X Y Z : SSet.{u}} (α : X ⟶ Y) (β : X ⟶ Z)
  {iR : |Y| ⟶ P'} {jR : |Z| ⟶ P'}
  (sqR : IsPushout (SSet.toTop.map α) (SSet.toTop.map β) iR jR)
  (aR : A ⟶ |X|) (bR : B ⟶ |Y|) (cR : C ⟶ |Z|)
  (wfR : f ≫ bR = aR ≫ SSet.toTop.map α) (wgR : g ≫ cR = aR ≫ SSet.toTop.map β)
  (wiR : i ≫ p = bR ≫ iR) (wjR : j ≫ p = cR ≫ jR)
  (hfR : TheoremA.homotopyExtensionProperty (SSet.toTop.map α))
  (hLR : IsWeakHomotopyEquivalence (HomotopyPullback.comparison bR.hom
    (SSet.toTop.map α).hom aR.hom f.hom (congrArg TopCat.Hom.hom wfR)))
  (hRR : IsWeakHomotopyEquivalence (HomotopyPullback.comparison cR.hom
    (SSet.toTop.map β).hom aR.hom g.hom (congrArg TopCat.Hom.hom wgR)))

include sq sqR wfR wgR wiR wjR hf hfR hLR hRR in
example : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison p.hom iR.hom bR.hom i.hom (congrArg TopCat.Hom.hom wiR)) :=
  leftComparison_isWeakHomotopyEquivalence sq sqR aR bR cR p wfR wgR wiR wjR hf hfR
    (fun _ _ _ _ d ↦ DoubleCylinder.compactMap_isClosed_graph α β
      (cylinderSquare (SSet.toTop.map α) (SSet.toTop.map β)) d) hLR hRR

include sq sqR wfR wgR wiR wjR hf hfR hLR hRR in
example : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison p.hom jR.hom cR.hom j.hom (congrArg TopCat.Hom.hom wjR)) :=
  rightComparison_isWeakHomotopyEquivalence sq sqR aR bR cR p wfR wgR wiR wjR hf hfR
    (fun _ _ _ _ d ↦ DoubleCylinder.compactMap_isClosed_graph α β
      (cylinderSquare (SSet.toTop.map α) (SSet.toTop.map β)) d) hLR hRR
end RealizedTarget
