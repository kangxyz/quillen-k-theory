/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackTransport
public import Quillen.Topology.Prespectrum.SelfTrackRepresentative

/-!
# Original self-tracks descend to higher homotopy classes

The jointly continuous family on actual based cubes supplies its own
conjugacy square when the cube moves. Explicit component normalization then
descends the original track class to the homotopy quotient. The result is a
function only: spatial additivity and stable successor compatibility are not
asserted here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Quillen

/-- Evaluation of an actual self-homotopy is conjugate along its original image path. -/
theorem selfHomotopy_eval_transport {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} (H : f.Homotopy f)
    {x₀ x₁ : X} (β : Path x₀ x₁) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (β.map f.continuous)
        (⟦H.evalAt x₀⟧ : FundamentalGroup Y (f x₀)) =
      (⟦H.evalAt x₁⟧ : FundamentalGroup Y (f x₁)) := by
  let c : FundamentalGroupoid.mk (f x₀) ⟶ FundamentalGroupoid.mk (f x₁) :=
    ⟦β.map f.continuous⟧
  let a : FundamentalGroup Y (f x₀) := ⟦H.evalAt x₀⟧
  let b : FundamentalGroup Y (f x₁) := ⟦H.evalAt x₁⟧
  have hn : c ≫ b = a ≫ c :=
    (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality
      (⟦β⟧ : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁)
  change Groupoid.inv c ≫ (a ≫ c) = b
  rw [← hn]
  simp

namespace LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Joint continuity retains the original track time and every original cube coordinate. -/
def Homotopy.genLoopHomotopy (H : Homotopy f f) (n m : ℕ) :
    (genLoopPostcompContinuousMap (N := Fin (m + 1)) (f.map n) (f.map_point n)).Homotopy
      (genLoopPostcompContinuousMap (f.map n) (f.map_point n)) where
  toFun z := H.genLoopPath n z.2 z.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × GenLoop (Fin (m + 1))
      (E.space n) (E.point n)) × (Fin (m + 1) → unitInterval) ↦
        H.level n (z.1.1, z.1.2 z.2))
    fun_prop
  map_zero_left p := (H.genLoopPath n p).source
  map_one_left p := (H.genLoopPath n p).target

/-- Evaluation of the joint family is exactly the already existing original cube path. -/
@[simp] theorem Homotopy.genLoopHomotopy_evalAt (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    (H.genLoopHomotopy n m).evalAt p = H.genLoopPath n p := by
  apply Path.ext
  rfl

/-- An actual path of cubes transports the original track by its own conjugacy square. -/
theorem Homotopy.genLoopPath_transport (H : Homotopy f f) (n m : ℕ)
    {p q : GenLoop (Fin (m + 1)) (E.space n) (E.point n)} (β : Path p q) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        (β.map (genLoopPostcompContinuousMap (f.map n) (f.map_point n)).continuous)
        (⟦H.genLoopPath n p⟧ : FundamentalGroup _ _) =
      (⟦H.genLoopPath n q⟧ : FundamentalGroup _ _) := by
  exact selfHomotopy_eval_transport (H.genLoopHomotopy n m) β

/-- Homotopic original sphere representatives have the same normalized higher track class. -/
theorem Homotopy.genLoopSelfTrackClass_congr (H : Homotopy f f) (n m : ℕ)
    {p q : GenLoop (Fin (m + 1)) (E.space n) (E.point n)} (h : GenLoop.Homotopic p q) :
    genLoopSelfTrackClass m _ (H.genLoopPath n p) =
      genLoopSelfTrackClass m _ (H.genLoopPath n q) := by
  obtain ⟨P⟩ := h
  let β := genLoopPathOfHomotopyRel P
  have ht := genLoopSelfTrackNormalization_transport m
    (β.map (genLoopPostcompContinuousMap (f.map n) (f.map_point n)).continuous)
    (⟦H.genLoopPath n p⟧ : FundamentalGroup _ _)
  rw [H.genLoopPath_transport n m β] at ht
  exact ht.symm

/-- The actual original self-track induces a function on the finite homotopy quotient.
No group law or stable successor equation is included in this declaration. -/
def Homotopy.homotopyClassOperation (H : Homotopy f f) (n m : ℕ) :
    HomotopyGroup.Pi (m + 1) (E.space n) (E.point n) →
      HomotopyGroup.Pi (m + 2) (F.space n) (F.point n) :=
  Quotient.lift (fun p ↦ genLoopSelfTrackClass m _ (H.genLoopPath n p))
    (fun _ _ h ↦ H.genLoopSelfTrackClass_congr n m h)

/-- The quotient operation evaluates the original representative and the original track. -/
@[simp] theorem Homotopy.homotopyClassOperation_mk (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    H.homotopyClassOperation n m ⟦p⟧ =
      genLoopSelfTrackClass m _ (H.genLoopPath n p) := rfl

end LoopPrespectrum
end Quillen
