/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.HomotopySquare
public import Quillen.Topology.Prespectrum.HomotopyLoop
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyReparam
public import Quillen.Topology.Prespectrum.PushoutHomotopySquare
public import Quillen.Topology.Prespectrum.HomotopySquareInterchange
public import Quillen.Topology.Prespectrum.PushoutArrowHomotopy

/-!
# Homotopy Square Composition

Support for pasting the actual moving polynomial-span composition square.
No geometric triple or rectangle comparison is reconstructed here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.Square

/-- Paste two whole moving squares in the original path coordinate. -/
def pastePaths {E F : LoopPrespectrum.{u}}
    {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
    (S : H₀.Square H₁ L M) (T : K₀.Square K₁ M N) :
    (H₀.trans K₀).Square (H₁.trans K₁) L N := by
  let swapSquare {a₀ b₀ a₁ b₁ : E ⟶ F}
      {A₀ : Homotopy a₀ b₀} {A₁ : Homotopy a₁ b₁}
      {B : Homotopy a₀ a₁} {C : Homotopy b₀ b₁}
      (V : A₀.Square A₁ B C) (n : ℕ) :
      (B.level n).Homotopy (C.level n) := {
    toFun := fun z ↦ V.level n (z.2.1, (z.1, z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left z := V.left n z.1 z.2
    map_one_left z := V.right n z.1 z.2 }
  let joint n := (swapSquare S n).trans (swapSquare T n)
  refine {
    level := fun n ↦ ⟨fun z ↦ joint n (z.2.1, (z.1, z.2.2)), by fun_prop⟩
    at_zero := ?_
    at_one := ?_
    left := ?_
    right := ?_
    at_point := ?_
    comm := ?_ }
  · intro n s x
    change ((swapSquare S n).trans (swapSquare T n)) (s, (0, x)) =
      ((H₀.levelHomotopy n).trans (K₀.levelHomotopy n)) (s, x)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact S.at_zero n _ x
    · exact T.at_zero n _ x
  · intro n s x
    change ((swapSquare S n).trans (swapSquare T n)) (s, (1, x)) =
      ((H₁.levelHomotopy n).trans (K₁.levelHomotopy n)) (s, x)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact S.at_one n _ x
    · exact T.at_one n _ x
  · intro n r x
    exact (joint n).apply_zero (r, x)
  · intro n r x
    exact (joint n).apply_one (r, x)
  · intro n r s
    change ((swapSquare S n).trans (swapSquare T n)) (s, (r, E.point n)) = _
    rw [ContinuousMap.Homotopy.trans_apply]
    split
    · exact S.at_point n r _
    · exact T.at_point n r _
  · intro n r s x t
    change ((swapSquare S (n + 1)).trans (swapSquare T (n + 1)))
      (s, (r, E.structureMap n x t)) =
        F.structureMap n (((swapSquare S n).trans (swapSquare T n)) (s, (r, x))) t
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split
    · exact S.comm n r _ x t
    · exact T.comm n r _ x t

/-- Reverse both path faces of a moving square. -/
def reversePaths {E F : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    (S : H₀.Square H₁ L M) : H₀.symm.Square H₁.symm M L where
  level n := ⟨fun z ↦ S.level n (z.1, (unitInterval.symm z.2.1, z.2.2)), by fun_prop⟩
  at_zero n s x := S.at_zero n (unitInterval.symm s) x
  at_one n s x := S.at_one n (unitInterval.symm s) x
  left n r x := by simpa using S.right n r x
  right n r x := by simpa using S.left n r x
  at_point n r s := S.at_point n r (unitInterval.symm s)
  comm n r s x t := S.comm n r (unitInterval.symm s) x t

/-- Postcomposition retains the entire joint square and its four original boundary tracks. -/
def postcompose {E F G : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    (S : H₀.Square H₁ L M) (k : F ⟶ G) :
    (H₀.postcomp k).Square (H₁.postcomp k) (L.postcomp k) (M.postcomp k) where
  level n := ⟨fun z ↦ k.map n (S.level n z), by fun_prop⟩
  at_zero n s x := congrArg (k.map n) (S.at_zero n s x)
  at_one n s x := congrArg (k.map n) (S.at_one n s x)
  left n r x := congrArg (k.map n) (S.left n r x)
  right n r x := congrArg (k.map n) (S.right n r x)
  at_point n r s := (congrArg (k.map n) (S.at_point n r s)).trans (k.map_point n)
  comm n r s x t := (congrArg (k.map (n + 1)) (S.comm n r s x t)).trans
    (congrArg (fun p ↦ p t) (k.comm n (S.level n (r, (s, x)))))

/-- Full-level boundary identities change only the specified arrow transports of a square. -/
def ofBoundaryLevels {E F : LoopPrespectrum.{u}}
    {f₀ g₀ f₁ g₁ f₀' g₀' f₁' g₁' : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    (S : H₀.Square H₁ L M)
    (H₀' : Homotopy f₀' g₀') (H₁' : Homotopy f₁' g₁')
    (L' : Homotopy f₀' f₁') (M' : Homotopy g₀' g₁')
    (h₀ : ∀ n, H₀'.level n = H₀.level n) (h₁ : ∀ n, H₁'.level n = H₁.level n)
    (hL : ∀ n, L'.level n = L.level n) (hM : ∀ n, M'.level n = M.level n) :
    H₀'.Square H₁' L' M' where
  level := S.level
  at_zero n s x := (S.at_zero n s x).trans (DFunLike.congr_fun (h₀ n).symm (s, x))
  at_one n s x := (S.at_one n s x).trans (DFunLike.congr_fun (h₁ n).symm (s, x))
  left n r x := (S.left n r x).trans (DFunLike.congr_fun (hL n).symm (r, x))
  right n r x := (S.right n r x).trans (DFunLike.congr_fun (hM n).symm (r, x))
  at_point := S.at_point
  comm := S.comm

end Quillen.LoopPrespectrum.Homotopy.Square

namespace Quillen.LoopPrespectrum
/-- Reversal swaps two composition routes without changing their full levels under transport. -/
theorem Homotopy.reverseTwoRoutes_level {E F : LoopPrespectrum.{u}}
    {f f' a b : E ⟶ F} (H : Homotopy f a) (K : Homotopy f' b) (e : f = f') (n : ℕ) :
    ((K.symm.trans (H.cast e rfl)).symm).level n =
      (H.symm.trans (K.cast e.symm rfl)).level n := by
  rw [Homotopy.symm_trans, Homotopy.symm_symm]
  apply Homotopy.trans_level_congr <;> rfl

end Quillen.LoopPrespectrum

namespace Quillen.LoopPrespectrum.HomotopyPushout
/-- Two identical moving leg squares retain both charts and the actual moving middle cylinder. -/
def identicalLegMovingSquare {A B A' B' : LoopPrespectrum.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') {a₀ a₁ : A ⟶ A'} {b₀ b₁ : B ⟶ B'}
    (H₀ : Homotopy (f ≫ b₀) (a₀ ≫ f')) (H₁ : Homotopy (f ≫ b₁) (a₁ ≫ f'))
    (L : Homotopy a₀ a₁) (M : Homotopy b₀ b₁)
    (S : H₀.Square H₁ (Homotopy.precomp f M) (L.postcomp f')) :
    (mapSquareHomotopy f f f' f' a₀ b₀ b₀ H₀ H₀).Square
      (mapSquareHomotopy f f f' f' a₁ b₁ b₁ H₁ H₁)
      (Homotopy.precomp f (M.postcomp (inl f' f')))
      (Homotopy.precomp f (M.postcomp (inr f' f'))) := by
  let iL := inl f' f'
  let iR := inr f' f'
  let plus := (S.postcompose iL).ofBoundaryLevels
    (H₀.postcomp iL) (H₁.postcomp iL)
    (Homotopy.precomp f (M.postcomp iL))
    (L.postcomp (f' ≫ iL))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  let middle := Homotopy.Square.interchange L (glue f' f')
  let minus := (S.reversePaths.postcompose iR).ofBoundaryLevels
    (H₀.symm.postcomp iR) (H₁.symm.postcomp iR)
    (L.postcomp (f' ≫ iR))
    (Homotopy.precomp f (M.postcomp iR))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  exact plus.pastePaths (middle.pastePaths minus)
end Quillen.LoopPrespectrum.HomotopyPushout

namespace Quillen.LoopPrespectrum.HomotopyPushout
variable {A B A' B' A'' B'' : LoopPrespectrum.{u}}
    (f : A ⟶ B) (g : A' ⟶ B') (h : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (c : A' ⟶ A'') (d : B' ⟶ B'')
    (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))

/-- The original two leg squares paste with their exact geometric order. -/
def identicalLegPastedTrack : Homotopy (f ≫ (b ≫ d)) ((a ≫ c) ≫ h) :=
  ((H.postcomp d).trans ((Homotopy.precomp a K).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)).cast
      (Category.assoc _ _ _) rfl

/-- The complete original composite span cylinder, with literal endpoint transports. -/
def identicalLegActualCompositeTrack :
    Homotopy (f ≫ ((b ≫ d) ≫ inl h h)) (f ≫ ((b ≫ d) ≫ inr h h)) :=
  ((mapSquareHomotopy f f g g a b b H H).postcomp
    (mapOfHomotopies g g h h c d d K K)).cast
      (by simp only [Category.assoc, inl_mapOfHomotopies])
      (by simp only [Category.assoc, inr_mapOfHomotopies])

/-- Literal quotient descent identifies the actual composite cylinder on all generators. -/
theorem identicalLegActualCompositeDesc :
    desc f f ((b ≫ d) ≫ inl h h) ((b ≫ d) ≫ inr h h)
      (identicalLegActualCompositeTrack f g h a b c d H K) =
    mapOfHomotopies f f g g a b b H H ≫
      mapOfHomotopies g g h h c d d K K := by
  apply hom_ext
  · rw [inl_desc, ← Category.assoc, inl_mapOfHomotopies]
    simp only [Category.assoc, inl_mapOfHomotopies]
  · rw [inr_desc, ← Category.assoc, inr_mapOfHomotopies]
    simp only [Category.assoc, inr_mapOfHomotopies]
  · intro n s x
    rfl

/-- Reassociation of all five original cylinder pieces compares actual span-map composition. -/
def identicalLegCompositionPasting :
    (identicalLegActualCompositeTrack f g h a b c d H K).RelHomotopy
      (mapSquareHomotopy f f h h (a ≫ c) (b ≫ d) (b ≫ d)
        (identicalLegPastedTrack f g h a b c d H K)
        (identicalLegPastedTrack f g h a b c d H K)) := by
  let iL := inl h h
  let iR := inr h h
  let P := H.postcomp (d ≫ iL)
  let Q : Homotopy ((a ≫ g) ≫ (d ≫ iL)) ((a ≫ c) ≫ (h ≫ iL)) :=
    (Homotopy.precomp a (K.postcomp iL)).cast
    (by simp only [Category.assoc]) (by simp only [Category.assoc])
  let T := Homotopy.precomp (a ≫ c) (glue h h)
  let U : Homotopy ((a ≫ c) ≫ (h ≫ iR)) ((a ≫ g) ≫ (d ≫ iR)) :=
    (Homotopy.precomp a (K.symm.postcomp iR)).cast
    (by simp only [Category.assoc]) (by simp only [Category.assoc])
  let V := H.symm.postcomp (d ≫ iR)
  have J : (P.trans ((Q.trans (T.trans U)).trans V)).RelHomotopy
      ((P.trans Q).trans (T.trans (U.trans V))) :=
    ((Homotopy.RelHomotopy.refl P).hcomp
      (Homotopy.RelHomotopy.transAssoc Q (T.trans U) V)).trans
      (((Homotopy.RelHomotopy.refl P).hcomp
        ((Homotopy.RelHomotopy.refl Q).hcomp
          (Homotopy.RelHomotopy.transAssoc T U V))).trans
        (Homotopy.RelHomotopy.transAssoc P Q (T.trans (U.trans V))).symm)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    unfold identicalLegActualCompositeTrack mapSquareHomotopy
    change ((_root_.Quillen.LoopPrespectrum.Homotopy.trans _ _).postcomp _).level n = _
    rw [Homotopy.postcomp_trans, Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr
    · change (H.postcomp (inl g g ≫ mapOfHomotopies g g h h c d d K K)).level n = P.level n
      rw [inl_mapOfHomotopies]
    · apply Homotopy.trans_level_congr
      · have overlap : (glue g g).postcomp (mapOfHomotopies g g h h c d d K K) =
            mapSquareHomotopy g g h h c d d K K := glue_desc g g _ _ _
        change (Homotopy.precomp a ((glue g g).postcomp
          (mapOfHomotopies g g h h c d d K K))).level n = (Q.trans (T.trans U)).level n
        rw [overlap]
        unfold mapSquareHomotopy
        rw [Homotopy.precomp_trans, Homotopy.precomp_trans]
        apply Homotopy.trans_level_congr
        · rfl
        · apply Homotopy.trans_level_congr <;> rfl
      · change (H.symm.postcomp (inr g g ≫ mapOfHomotopies g g h h c d d K K)).level n = V.level n
        rw [inr_mapOfHomotopies]
  · intro n
    unfold mapSquareHomotopy
    apply Homotopy.trans_level_congr
    · change (((H.postcomp d).trans ((Homotopy.precomp a K).cast _ _)).postcomp iL).level n = _
      rw [Homotopy.postcomp_trans]
      apply Homotopy.trans_level_congr <;> rfl
    · apply Homotopy.trans_level_congr
      · rfl
      · change ((((H.postcomp d).trans ((Homotopy.precomp a K).cast _ _)).symm).postcomp
          iR).level n = _
        rw [Homotopy.symm_trans, Homotopy.postcomp_trans]
        apply Homotopy.trans_level_congr <;> rfl

/-- The whole actual span-map composite compares with the span using the original pasted squares.
Both polynomial charts stay fixed; the entire source cylinder keeps its reparameterization. -/
def identicalLegCompositionHomotopy :
    Homotopy (mapOfHomotopies f f g g a b b H H ≫ mapOfHomotopies g g h h c d d K K)
      (mapOfHomotopies f f h h (a ≫ c) (b ≫ d) (b ≫ d)
        (identicalLegPastedTrack f g h a b c d H K)
        (identicalLegPastedTrack f g h a b c d H K)) :=
  (descHomotopy f f ((b ≫ d) ≫ inl h h) ((b ≫ d) ≫ inr h h)
    (identicalLegCompositionPasting f g h a b c d H K)).cast
      (identicalLegActualCompositeDesc f g h a b c d H K) rfl

end Quillen.LoopPrespectrum.HomotopyPushout
