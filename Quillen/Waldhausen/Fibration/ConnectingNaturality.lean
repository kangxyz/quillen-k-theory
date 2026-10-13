/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.CanonicalFiberNaturality
public import Quillen.Waldhausen.Fibration.LongExactSequence

/-!
# Naturality of the original change-of-weak connecting maps

Any functor exact for both nested structures preserves the actual connecting
homomorphisms when both original canonical comparisons are weak equivalences.
The original canonical rebasing removes strict preservation of chosen zero.
No connecting-square or arbitrary replacement boundary is supplied as input.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

lemma changeWeakConnectingHom_natural_of_zeroEq (h0 : F.obj V.zero = W.zero)
    (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M)) (n : ℕ) :
    (KMap (acyclicFunctor_exact N M hF hFc) n).comp (changeWeakConnectingHom N hN n) =
    (changeWeakConnectingHom M hM n).comp (KMap hFc (n+1)) := by
  ext x
  apply (canonicalFiberKMap_bijective_of_weak M hM n).injective
  have H := DFunLike.congr_fun (canonicalFiberKMap_natural N M hF hFc h0 n)
    (changeWeakConnectingHom N hN n x)
  simp only [MonoidHom.comp_apply] at H ⊢
  rw [← H, canonicalFiberKMap_connecting, canonicalFiberKMap_connecting,
    KMap_eq_piMap_of_zeroEq hFc (coarse_zero_eq N M h0)]
  exact DFunLike.congr_fun (HomotopyFiber.connectingHom_mapAt_natural
    (deloopingMap hF).hom (deloopingMap hFc).hom (changeWeakMap_natural N M hF hFc)
    V.kBasepoint N.coarse.kBasepoint W.kBasepoint M.coarse.kBasepoint
    (changeWeakMap_basepoint N) (changeWeakMap_basepoint M)
    (deloopingMap_basepoint_of_zeroEq hF h0)
    (deloopingMap_basepoint_of_zeroEq hFc (coarse_zero_eq N M h0)) n) x


lemma changeWeakConnectingHom_natural
    (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M)) (n : ℕ) :
    (KMap (acyclicFunctor_exact N M hF hFc) n).comp (changeWeakConnectingHom N hN n) =
    (changeWeakConnectingHom M hM n).comp (KMap hFc (n+1)) := by
  let e := Quillen.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)
  have hFc' := hFc.of_iso e
  have H := changeWeakConnectingHom_natural_of_zeroEq N M hF.rebase hFc'
    (Quillen.rebaseFunctor_obj_base _ _ _ _) hN hM n
  rw [← KMap_eq_of_iso (acyclicFunctor_exact N M hF hFc)
      (acyclicFunctor_exact N M hF.rebase hFc') (acyclicFunctorIso N M hFc hFc' e) n,
    ← KMap_eq_of_iso hFc hFc' e (n+1)] at H
  exact H

end Quillen.Waldhausen.Fibration
