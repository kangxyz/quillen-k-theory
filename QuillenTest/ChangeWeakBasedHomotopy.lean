/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.ChangeWeakBasedHomotopy

/-! # Original based-additivity endpoint and independent-time consumers -/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v
namespace QuillenTest.ChangeWeakBasedHomotopy

open Quillen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  [HasBinaryCoproducts D] {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
  (hs : IsCofibrationSequence V W a b)

/-- The initial face is the original rebased middle map after original subdivision. -/
theorem original_initial_face
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    realizedDiagonalMap (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N))
        (subdividedBasedAdditivityHomotopy V W a b hs (0, x)) =
      realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq
        (isCofibrationSequence_changeWeak V W N a b hs).exactG.rebase)
        (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) x) :=
  (subdividedBasedAdditivityHomotopy_changeWeak V W N a b hs 0 x).trans
    ((subdividedBasedAdditivityHomotopy V N.coarse a b
      (isCofibrationSequence_changeWeak V W N a b hs)).toHomotopy.apply_zero x)

/-- The final face is the unchanged normalized sum in quotient/subobject order. -/
theorem original_final_face
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    realizedDiagonalMap (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N))
        (subdividedBasedAdditivityHomotopy V W a b hs (1, x)) =
      realizedDiagonalMap (normalizedSumMap V N.coarse
        (isCofibrationSequence_changeWeak V W N a b hs).exactH
        (isCofibrationSequence_changeWeak V W N a b hs).exactF) x :=
  (subdividedBasedAdditivityHomotopy_changeWeak V W N a b hs 1 x).trans
    ((subdividedBasedAdditivityHomotopy V N.coarse a b
      (isCofibrationSequence_changeWeak V W N a b hs)).toHomotopy.apply_one x)

/-- The original source basepoint track stays constant for every comparison time. -/
theorem original_basepoint_time (t : unitInterval) :
    realizedDiagonalMap (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N))
        (subdividedBasedAdditivityHomotopy V W a b hs (t, subdivisionBasepoint V)) =
      realizedDiagonalMap (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N))
        (subdividedBasedAdditivityHomotopy V W a b hs (0, subdivisionBasepoint V)) := by
  apply congrArg
  exact ((subdividedBasedAdditivityHomotopy V W a b hs).eq_fst t
    (Set.mem_singleton _)).trans
    ((subdividedBasedAdditivityHomotopy V W a b hs).toHomotopy.apply_zero _).symm

/-- A second path parameter is independent of the complete original additivity time. -/
theorem original_two_parameters
    {x y : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|}
    (p : Path x y) (s t : unitInterval) :
    realizedDiagonalMap (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N))
        (subdividedBasedAdditivityHomotopy V W a b hs (s, p t)) =
      subdividedBasedAdditivityHomotopy V N.coarse a b
        (isCofibrationSequence_changeWeak V W N a b hs) (s, p t) :=
  subdividedBasedAdditivityHomotopy_changeWeak V W N a b hs s (p t)

end QuillenTest.ChangeWeakBasedHomotopy
