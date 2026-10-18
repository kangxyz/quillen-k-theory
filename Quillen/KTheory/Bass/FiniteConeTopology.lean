/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ConeTrack
public import Quillen.Topology.Prespectrum.LoopTranspose
public import Quillen.Topology.Prespectrum.StrictSquareVanishing
public import Quillen.Waldhausen.SConstruction.Iterated.FiniteConnectivity
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP

/-!
# Original topology and growth of finite unlooped cone iterates

The unlooped square cone is exactly `ConeTrack.diagram`. Its finite iterates
preserve the original all-point vanishing offset above cutoff two. Actual parameter looping
loses one degree per loop, including arbitrary loop components. Original Model diagrams
supply every initial topology and growth hypothesis. No later cone is treated as a Model,
and no tower transitions, action identification, or comparison equivalence is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace Quillen.KTheory.Bass.FiniteConeTopology
variable {C : Type u} [Category.{v} C]

/-- Finite iteration of the same unlooped cone used by the original cone action. -/
def iterate (Q : C ⥤ Arrow (Arrow C)) : ℕ → (C ⥤ LoopPrespectrum.{w}) →
    (C ⥤ LoopPrespectrum.{w})
  | 0, F => F
  | i + 1, F => ConeTrack.diagram Q (iterate Q i F)

/-- One unlooped square cone retains T1 separation at every original level. -/
instance diagramSpaceT1Space (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) [∀ X m, T1Space ((F.obj X).space m)]
    (X : C) (m : ℕ) : T1Space (((ConeTrack.diagram Q F).obj X).space m) := by
  let S := F.mapArrow.mapArrow.obj (Q.obj X)
  let : T1Space (S.left.left.space m) :=
    inferInstanceAs (T1Space ((F.obj (Q.obj X).left.left).space m))
  let : T1Space (S.left.right.space m) :=
    inferInstanceAs (T1Space ((F.obj (Q.obj X).left.right).space m))
  let : T1Space (S.right.left.space m) :=
    inferInstanceAs (T1Space ((F.obj (Q.obj X).right.left).space m))
  let : T1Space (S.right.right.space m) :=
    inferInstanceAs (T1Space ((F.obj (Q.obj X).right.right).space m))
  change T1Space ((mappingCone (StrictSquare.comparison S)).space m)
  infer_instance

/-- Every finite unlooped cone retains the original levelwise T1 separation. -/
instance iterateSpaceT1Space (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) [∀ X m, T1Space ((F.obj X).space m)]
    (X : C) (m : ℕ) : T1Space (((iterate Q i F).obj X).space m) := by
  induction i generalizing X m with
  | zero => exact inferInstanceAs (T1Space ((F.obj X).space m))
  | succ i ih =>
    let : ∀ Y k, T1Space (((iterate Q i F).obj Y).space k) := ih
    exact diagramSpaceT1Space Q (iterate Q i F) X m

/-- Genuine point HEP passes through all unlooped cones without a separation premise. -/
theorem iterate_point_homotopyExtensionProperty (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (h : ∀ X m, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (X : C) (m : ℕ) : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} (((iterate Q i F).obj X).point m))) := by
  induction i generalizing X m with
  | zero => exact h X m
  | succ i ih =>
    exact StrictSquare.cone_point_homotopyExtensionProperty
      ((iterate Q i F).mapArrow.mapArrow.obj (Q.obj X)) m
      (ih (Q.obj X).left.left m) (ih (Q.obj X).left.right m)
      (ih (Q.obj X).right.left m) (ih (Q.obj X).right.right m)

/-- Every unlooped cone iterate preserves the exact all-point linear vanishing offset. -/
theorem iterate_homotopyGroup_subsingleton (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (h : ∀ X m, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (c : ℕ)
    (hπ : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x))
    (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : ((iterate Q i F).obj X).space (n + c + 2)) :
    Subsingleton (HomotopyGroup.Pi k (((iterate Q i F).obj X).space (n + c + 2)) x) := by
  induction i generalizing X n k with
  | zero => exact hπ X n k hk x
  | succ i ih =>
    let S := (iterate Q i F).mapArrow.mapArrow.obj (Q.obj X)
    have hp := iterate_point_homotopyExtensionProperty Q i F h
    have hs (z : (StrictSquare.span S).space (n + c + 2)) (j : ℕ) (hj : j < n + 2) :
        Subsingleton (HomotopyGroup.Pi j ((StrictSquare.span S).space (n + c + 2)) z) :=
      HomotopyPushout.homotopyGroup_subsingleton S.left.hom S.hom.left _ n
        (hp (Q.obj X).left.left _) (hp (Q.obj X).left.right _)
        (hp (Q.obj X).right.left _)
        (fun a j hj => ih (X := (Q.obj X).left.left) n j hj a)
        (fun b j hj => ih (X := (Q.obj X).left.right) n j hj b)
        (fun d j hj => ih (X := (Q.obj X).right.left) n j hj d) z j hj
    exact ReducedMappingCone.homotopyGroup_subsingleton
      ((StrictSquare.span S).point _) (S.right.right.point _)
      ((StrictSquare.comparison S).map _) ((StrictSquare.comparison S).map_point _)
      (StrictSquare.span_point_homotopyExtensionProperty S _
        (hp (Q.obj X).left.left _) (hp (Q.obj X).left.right _)
        (hp (Q.obj X).right.left _)) (hp (Q.obj X).right.right _) n hs
      (fun d j hj => ih (X := (Q.obj X).right.right) n j hj d) x k hk

/-- All actual loop iterates retain T1 separation. -/
instance loopsSpaceT1Space (j : ℕ) (E : LoopPrespectrum.{w})
    [∀ m, T1Space (E.space m)] (m : ℕ) : T1Space ((loops j E).space m) := by
  induction j with
  | zero => exact inferInstanceAs (T1Space (E.space m))
  | succ j ih =>
    let : T1Space ((loops j E).space m) := ih
    exact parameterLoopingSpaceT1Space (loops j E) m

/-- Closed genuine point HEP persists through all actual parameter loops. -/
theorem loops_point_homotopyExtensionProperty (j : ℕ) (E : LoopPrespectrum.{w})
    [∀ m, T1Space (E.space m)]
    (h : ∀ m, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} (E.point m)))) (m : ℕ) :
    Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((loops j E).point m))) := by
  induction j with
  | zero => exact h m
  | succ j ih =>
    exact parameterLooping_point_homotopyExtensionProperty (loops j E) m isClosed_singleton ih

/-- Each actual parameter loop loses one degree at every displayed loop component. -/
theorem loops_homotopyGroup_subsingleton (j : ℕ) (E : LoopPrespectrum.{w}) (c : ℕ)
    (hπ : ∀ n k, k < n + 2 → ∀ x : E.space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
    (n k : ℕ) (hk : k < n + 2) (x : (loops j E).space (n + (c + j) + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((loops j E).space (n + (c + j) + 2)) x) := by
  induction j generalizing n k with
  | zero => exact hπ n k hk x
  | succ j ih =>
    have he : n + (c + (j + 1)) + 2 = (n + 1) + (c + j) + 2 := by omega
    revert x
    rw [he]
    intro x
    exact Quillen.subsingleton_pi_loop_of_succ
      ((loops j E).point ((n + 1) + (c + j) + 2)) k
      (ih (n + 1) (k + 1) (by omega) ((loops j E).point _)) x

open Quillen.Waldhausen.IteratedS

/-- Genuine Model input supplies T1 separation to all finite normalized cone-loop stages. -/
instance modelLoopsIterateSpaceT1Space (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ)
    (F : C ⥤ Model.{w}) (X : C) (m : ℕ) :
    T1Space ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space m) := by
  let : ∀ Y n, T1Space (((F ⋙ prespectrumFunctor).obj Y).space n) :=
    fun Y n => prespectrumSpaceT1Space (F.obj Y) n
  infer_instance

/-- No new well-basedness hypothesis is required at a normalized finite Model stage. -/
theorem modelLoopsIterate_point_homotopyExtensionProperty
    (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ) (F : C ⥤ Model.{w}) (X : C) (m : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).point m))) := by
  let : ∀ Y n, T1Space (((F ⋙ prespectrumFunctor).obj Y).space n) :=
    fun Y n => prespectrumSpaceT1Space (F.obj Y) n
  exact loops_point_homotopyExtensionProperty j _
    (iterate_point_homotopyExtensionProperty Q i (F ⋙ prespectrumFunctor)
      (fun Y n => prespectrum_point_homotopyExtensionProperty (F.obj Y) n) X) m

/-- The genuine normalized Model stage has offset equal to the number of loops alone. -/
theorem modelLoopsIterate_homotopyGroup_subsingleton
    (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ) (F : C ⥤ Model.{w})
    (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : (loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space (n + j + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space (n + j + 2)) x) := by
  have hπ := iterate_homotopyGroup_subsingleton Q i (F ⋙ prespectrumFunctor)
    (fun Y n => prespectrum_point_homotopyExtensionProperty (F.obj Y) n) 0
    (fun Y n k hk x => prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (F.obj Y) (n + 1) k (by omega) x) X
  have hl := loops_homotopyGroup_subsingleton j _ 0 hπ n k hk
  have he : n + (0 + j) + 2 = n + j + 2 := by omega
  exact (he ▸ hl) x

end Quillen.KTheory.Bass.FiniteConeTopology
