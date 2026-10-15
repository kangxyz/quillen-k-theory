/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.ConnectingNaturality

/-! # Original boundary and full-path naturality consumers -/
@[expose] public section

open Quillen.Waldhausen
open Quillen.Waldhausen.Fibration


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
namespace QuillenTest.BoundaryNaturality

open Quillen
open Waldhausen Waldhausen.Fibration
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    {V : Structure C} {W : Structure D}
    (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W) {F : C ⥤ D}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

/-- The actual entire canonical fiber path agrees at every real parameter. -/
theorem original_full_path (h0 : F.obj V.zero = W.zero)
    (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    (fiberFunctorMap N M hF hFc h0 (canonicalFiberMap N x)).1.2 t =
      (canonicalFiberMap M (deloopingMap (acyclicFunctor_exact N M hF hFc) x)).1.2 t := by
  exact congrArg (fun z => z.1.2 t)
    (ContinuousMap.congr_fun (canonicalFiberMap_natural N M hF hFc h0) x)

/-- Composition retains the actual original ambient arrow, including both nested lifts. -/
theorem original_composed_acyclic_map {E : Type u} [Category.{v} E] {T : Structure E}
    (L : NestedWeakEquivalences T) {G : D ⥤ E}
    (hGc : IsExact M.coarse.cof M.coarse.weq L.coarse.cof L.coarse.weq G)
    {A B : AcyclicCategory N} (f : A ⟶ B) :
    ((acyclicFunctor N L (hFc.comp hGc)).map f).hom = G.map (F.map f.hom) := rfl

/-- All three recurring ORIGINAL localization arrows form genuine natural squares. -/
theorem all_original_squares
    (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M)) (n : ℕ) :
    (KMap hFc n).comp (KMap (changeWeak_exact N) n) =
        (KMap (changeWeak_exact M) n).comp (KMap hF n) ∧
    (KMap hF n).comp (KMap (acyclicInclusion_exact N) n) =
        (KMap (acyclicInclusion_exact M) n).comp (KMap (acyclicFunctor_exact N M hF hFc) n) ∧
    (KMap (acyclicFunctor_exact N M hF hFc) n).comp (changeWeakConnectingHom N hN n) =
        (changeWeakConnectingHom M hM n).comp (KMap hFc (n+1)) :=
  ⟨changeWeakKMap_natural N M hF hFc n, acyclicInclusionKMap_natural N M hF hFc n,
    changeWeakConnectingHom_natural N M hF hFc hN hM n⟩

/-- The original K1-to-K0 boundary is retained without strict chosen-zero preservation. -/
theorem original_zero_boundary
    (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M)) (x : N.coarse.K 1) :
    KMap (acyclicFunctor_exact N M hF hFc) 0 (changeWeakConnectingHom N hN 0 x) =
      changeWeakConnectingHom M hM 0 (KMap hFc 1 x) :=
  DFunLike.congr_fun (changeWeakConnectingHom_natural N M hF hFc hN hM 0) x

include hF in
/-- A class with zero original boundary keeps zero boundary after the exact functor. -/
theorem original_boundary_kernel
    (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M)) (n : ℕ) (x : N.coarse.K (n+1))
    (hx : changeWeakConnectingHom N hN n x = 1) :
    changeWeakConnectingHom M hM n (KMap hFc (n+1) x) = 1 := by
  have H := DFunLike.congr_fun (changeWeakConnectingHom_natural N M hF hFc hN hM n) x
  simp only [MonoidHom.comp_apply, hx, map_one] at H
  exact H.symm

/-- The acyclic natural isomorphism has exactly the original object components. -/
theorem original_iso_component {G : C ⥤ D}
    (hGc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq G) (e : F ≅ G)
    (X : AcyclicCategory N) :
    ((acyclicFunctorIso N M hFc hGc e).hom.app X).hom = e.hom.app X.obj := rfl
end QuillenTest.BoundaryNaturality
