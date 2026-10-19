/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SmallModel.Fiber
public import Quillen.Waldhausen.Fibration.ConnectingNaturality

/-!
# Original connecting maps in the genuine small model

The actual small-model homeomorphisms preserve the original full canonical
fiber map, its based point and connecting homomorphism. Exact evaluation from
a common-universe category into a category with smaller homs uses precisely
these homeomorphisms and the original canonically rebased K-maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u
namespace Quillen.Waldhausen.Fibration

private theorem piMap_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (h : f = g) : piMap n f hf = piMap n g hg := by
  subst g
  rfl

/-- Weakness of the original canonical comparison transports to its actual small model. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence_smallModel
    {C : Type*} [Category* C] {W : Structure C}
    (N : NestedWeakEquivalences W)
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N.smallModel) := by
  have hh := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (smallModelChangeWeakFiberHomeomorph N).toHomotopyEquiv).comp h
  rw [smallModel_canonicalFiberMap_square] at hh
  exact hh.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv
    (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv)

/-- The actual acyclic small-model homeomorphism induces this K-equivalence. -/
def acyclicSmallKEquiv {C : Type*} [Category* C] {W : Structure C}
    (N : NestedWeakEquivalences W) (n : ℕ) :
    (acyclicStructure N).K n ≃* (acyclicStructure N.smallModel).K n :=
  homotopyEquivPiEquiv (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv
    (acyclicSmallDeloopingHomeomorph_basepoint N) n

/-- The complete small-model fiber homeomorphism retains the original based point. -/
theorem smallModelChangeWeakFiberHomeomorph_basepoint {C : Type*} [Category* C] {W : Structure C}
    (N : NestedWeakEquivalences W) :
    smallModelChangeWeakFiberHomeomorph N
      (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint
        W.kBasepoint (changeWeakMap_basepoint N)) =
      HomotopyFiber.basepoint (changeWeakMap N.smallModel) N.smallModel.coarse.kBasepoint
        W.smallModel.kBasepoint (changeWeakMap_basepoint N.smallModel) := by
  apply Subtype.ext
  apply Prod.ext
  · exact W.smallModelDeloopingHomeomorph_basepoint
  · exact ContinuousMap.ext (fun _ ↦ N.coarse.smallModelDeloopingHomeomorph_basepoint)

/-- The original connecting map is preserved by the actual small-model homeomorphisms. -/
theorem acyclicSmallKEquiv_connecting {C : Type*} [Category* C] {W : Structure C}
    (N : NestedWeakEquivalences W)
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (x : N.coarse.K (n + 1)) :
    acyclicSmallKEquiv N n (changeWeakConnectingHom N h n x) =
      changeWeakConnectingHom N.smallModel
        (canonicalFiberMap_isWeakHomotopyEquivalence_smallModel N h) n
        (N.coarse.smallModelKEquiv (n + 1) x) := by
  apply (canonicalFiberKMap_bijective_of_weak N.smallModel
    (canonicalFiberMap_isWeakHomotopyEquivalence_smallModel N h) n).injective
  have hs :
      (piMap n (smallModelChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun
        (smallModelChangeWeakFiberHomeomorph_basepoint N)).comp (canonicalFiberKMap N n) =
      (canonicalFiberKMap N.smallModel n).comp (acyclicSmallKEquiv N n).toMonoidHom := by
    change (piMap n _ _).comp (piMap n _ _) = (piMap n _ _).comp (piMap n _ _)
    rw [← homotopyGroupMapHom_comp, ← homotopyGroupMapHom_comp]
    congr 1
    exact smallModel_canonicalFiberMap_square N
  have hc := HomotopyFiber.connectingHom_mapAt_natural
    (f := changeWeakMap N) (g := changeWeakMap N.smallModel)
    W.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
    N.coarse.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
    (smallModel_changeWeak_square N)
    W.kBasepoint N.coarse.kBasepoint W.smallModel.kBasepoint N.smallModel.coarse.kBasepoint
    (changeWeakMap_basepoint N) (changeWeakMap_basepoint N.smallModel)
    W.smallModelDeloopingHomeomorph_basepoint
    N.coarse.smallModelDeloopingHomeomorph_basepoint n
  have hm : (smallModelChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun =
      HomotopyFiber.mapAt W.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        N.coarse.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        (smallModel_changeWeak_square N) N.coarse.kBasepoint N.smallModel.coarse.kBasepoint
        N.coarse.smallModelDeloopingHomeomorph_basepoint := by
    ext z
    apply Subtype.ext
    rfl
  have hx : piMap n (smallModelChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun
      (smallModelChangeWeakFiberHomeomorph_basepoint N)
      (canonicalFiberKMap N n (changeWeakConnectingHom N h n x)) =
      canonicalFiberKMap N.smallModel n
        (acyclicSmallKEquiv N n (changeWeakConnectingHom N h n x)) :=
    DFunLike.congr_fun hs (changeWeakConnectingHom N h n x)
  have hc' : piMap n (smallModelChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun
      (smallModelChangeWeakFiberHomeomorph_basepoint N)
      (HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
        W.kBasepoint (changeWeakMap_basepoint N) n x) =
      HomotopyFiber.connectingHom (changeWeakMap N.smallModel) N.smallModel.coarse.kBasepoint
        W.smallModel.kBasepoint (changeWeakMap_basepoint N.smallModel) n
        (N.coarse.smallModelKEquiv (n + 1) x) := by
    exact (DFunLike.congr_fun (piMap_congr n _ _ _ _ hm) _).trans
      (DFunLike.congr_fun hc x)
  exact hx.symm.trans ((congrArg
    (piMap n (smallModelChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun
      (smallModelChangeWeakFiberHomeomorph_basepoint N))
    (canonicalFiberKMap_connecting N h n x)).trans
      (hc'.trans (canonicalFiberKMap_connecting N.smallModel
        (canonicalFiberMap_isWeakHomotopyEquivalence_smallModel N h) n
        (N.coarse.smallModelKEquiv (n + 1) x)).symm))

/-- Lowering the actual lifted acyclic model gives its original small-model K-coordinate. -/
theorem acyclicSmallDown_KMap_acyclicSmallKEquiv {C : Type (u + 1)} [Category.{u} C]
    {W : Structure C} (N : NestedWeakEquivalences W) (n : ℕ)
    (x : (acyclicStructure N).K n) :
    KMap ((acyclicSmallDown_exact N).comp (acyclicStructure N).smallModel_up_exact) n
      (acyclicSmallKEquiv N n x) = (acyclicStructure N).smallModelKEquiv n x := by
  have hs : (acyclicSmallSSetIso N).hom ≫
      sSetMap ((acyclicSmallDown_exact N).comp (acyclicStructure N).smallModel_up_exact) =
      (acyclicStructure N).smallModelSSetIso.hom := by
    ext m A : 4
    apply Subtype.ext
    rfl
  have hh := congrArg (fun f ↦ (SSet.toTop.map f).hom) hs
  rw [SSet.toTop.map_comp] at hh
  have hk : (KMap ((acyclicSmallDown_exact N).comp
      (acyclicStructure N).smallModel_up_exact) n).comp
        (acyclicSmallKEquiv N n).toMonoidHom =
      ((acyclicStructure N).smallModelKEquiv n).toMonoidHom := by
    rw [KMap_eq_piMap_of_zeroEq _ rfl n]
    change (piMap n _ _).comp (piMap n _ _) = piMap n _ _
    rw [← homotopyGroupMapHom_comp]
    exact piMap_congr n _ _ _ _ hh
  exact DFunLike.congr_fun hk x

/-- Actual fine/coarse exact evaluation preserves the original connecting maps
across the hom universes after the specified acyclic functor square. -/
theorem changeWeakConnectingHom_evaluation
    {C : Type (u + 1)} [Category.{u + 1} C]
    {D : Type (u + 1)} [Category.{u} D]
    {V : Structure C} {W : Structure D}
    (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
    {F : C ⥤ D} (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)
    {A : AcyclicCategory N ⥤ AcyclicCategory M}
    (hA : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
      (acyclicStructure M).cof (acyclicStructure M).weq A)
    (hAinc : A ⋙ acyclicInclusion M = acyclicInclusion N ⋙ F)
    (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M)) (n : ℕ)
    (x : N.coarse.K (n + 1)) :
    KMap (hA.comp (acyclicStructure M).smallModel_up_exact) n
      (changeWeakConnectingHom N hN n x) =
    (acyclicStructure M).smallModelKEquiv n
      (changeWeakConnectingHom M hM n
        ((M.coarse.smallModelKEquiv (n + 1)).symm
          (KMap (hFc.comp M.coarse.smallModel_up_exact) (n + 1) x))) := by
  let hf := hF.comp W.smallModel_up_exact
  let hc := hFc.comp M.coarse.smallModel_up_exact
  let ha := acyclicFunctor_exact N M.smallModel hf hc
  let hl := (acyclicSmallDown_exact M).comp (acyclicStructure M).smallModel_up_exact
  have hn : KMap ha n (changeWeakConnectingHom N hN n x) =
      changeWeakConnectingHom M.smallModel
        (canonicalFiberMap_isWeakHomotopyEquivalence_smallModel M hM) n
        (KMap hc (n + 1) x) :=
    DFunLike.congr_fun (changeWeakConnectingHom_natural N M.smallModel hf hc hN
      (canonicalFiberMap_isWeakHomotopyEquivalence_smallModel M hM) n) x
  have hb : (acyclicFunctor N M.smallModel hc ⋙ acyclicSmallDown M) ⋙
      acyclicInclusion M = acyclicInclusion N ⋙ F := rfl
  let : (acyclicInclusion M).Full := inferInstanceAs ((acyclicObjects M).ι).Full
  let : (acyclicInclusion M).Faithful := inferInstanceAs ((acyclicObjects M).ι).Faithful
  have hAi := Functor.fullyFaithfulCancelRight (acyclicInclusion M)
    (eqToIso (hb.trans hAinc.symm))
  have hk := KMap_eq_of_iso (ha.comp hl)
    (hA.comp (acyclicStructure M).smallModel_up_exact)
    (Functor.isoWhiskerRight hAi AsSmall.up) n
  calc
    _ = KMap hl n (KMap ha n (changeWeakConnectingHom N hN n x)) :=
      (DFunLike.congr_fun hk (changeWeakConnectingHom N hN n x)).symm.trans
        (DFunLike.congr_fun (KMap_comp_KMap ha hl n).symm
          (changeWeakConnectingHom N hN n x))
    _ = KMap hl n (changeWeakConnectingHom M.smallModel
        (canonicalFiberMap_isWeakHomotopyEquivalence_smallModel M hM) n
        (KMap hc (n + 1) x)) := congrArg (KMap hl n) hn
    _ = _ := by
      have hs := acyclicSmallKEquiv_connecting M hM n
        ((M.coarse.smallModelKEquiv (n + 1)).symm (KMap hc (n + 1) x))
      rw [MulEquiv.apply_symm_apply] at hs
      exact (congrArg (KMap hl n) hs.symm).trans
        (acyclicSmallDown_KMap_acyclicSmallKEquiv M n _)

end Quillen.Waldhausen.Fibration
