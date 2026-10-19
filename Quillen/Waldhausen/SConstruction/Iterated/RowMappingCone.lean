/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RowHomotopyPushout
public import Quillen.Topology.Prespectrum.MappingCone

/-!
# Row interchange on a prescribed comparison cone

A whole row-equivariance equation for the specified comparison descends the genuine vertex
and overlap transpose to its original reduced cone. The cone height and both structure
parameters remain independent. The comparison equation is explicit; applications must prove
it for their original overlap homotopy, rather than select a different comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.RowMappingCone
open LoopPrespectrum
variable {A B C D : Model.{u}} (f : A ⟶ B) (g : A ⟶ C)
  (d : RowHomotopyPushout.spectrum f g ⟶ prespectrum D)

/-- The actual row transpose on the original quotient cone. -/
def rowSwap (k : ℕ)
    (hd : ∀ x, RowHomotopyPushout.vertex k D (d.map (k + 3) x) =
      d.map (k + 3) (RowHomotopyPushout.rowSwap f g k x)) :
    C((mappingCone d).space (k + 3), (mappingCone d).space (k + 3)) :=
  ReducedMappingCone.map _ _ (d.map (k + 3)) _ _ (d.map (k + 3))
    (RowHomotopyPushout.rowSwap f g k) (RowHomotopyPushout.vertex k D)
    (RowHomotopyPushout.rowSwap_point f g k) (RowHomotopyPushout.vertex_point k D) hd

/-- The full Laurent inclusion retains the original vertex transpose. -/
theorem rowSwap_inclusion (k : ℕ) (hd) (y : (prespectrum D).space (k + 3)) :
    rowSwap f g d k hd ((mappingConeInclusion d).map (k + 3) y) =
      (mappingConeInclusion d).map (k + 3) (RowHomotopyPushout.vertex k D y) := rfl

/-- Every original cone-cylinder point keeps exactly the same cone height. -/
theorem rowSwap_cylinder (k : ℕ) (hd) (h : unitInterval)
    (x : (RowHomotopyPushout.spectrum f g).space (k + 3)) :
    rowSwap f g d k hd ((mappingConeHomotopy d).level (k + 3) (h, x)) =
      (mappingConeHomotopy d).level (k + 3)
        (h, RowHomotopyPushout.rowSwap f g k x) := rfl

/-- The row transpose fixes the original cone point and tip. -/
theorem rowSwap_point (k : ℕ) (hd) :
    rowSwap f g d k hd ((mappingCone d).point (k + 3)) = (mappingCone d).point (k + 3) :=
  ReducedMappingCone.map_point ..

/-- The whole cone transpose is involutive, not merely an equivalence on homotopy groups. -/
theorem rowSwap_involutive (k : ℕ) (hd) : Function.Involutive (rowSwap f g d k hd) := by
  intro q
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl y =>
      exact congrArg ((mappingConeInclusion d).map (k + 3))
        ((stageRowSwapHomeomorph k D).symm_apply_apply y)
    | inr z =>
      exact congrArg (fun y => (mappingConeHomotopy d).level (k + 3) (z.1, y))
        (RowHomotopyPushout.rowSwap_involutive f g k z.2)

/-- The exact two-structure identity on both original cone cells. -/
theorem structure_rowSwap (k : ℕ) (hd) (x : (mappingCone d).space (k + 1))
    (s t : unitInterval) :
    rowSwap f g d k hd ((mappingCone d).structureMap (k + 2)
      ((mappingCone d).structureMap (k + 1) x s) t) =
        (mappingCone d).structureMap (k + 2)
          ((mappingCone d).structureMap (k + 1) x t) s := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y =>
      exact congrArg ((mappingConeInclusion d).map (k + 3))
        (stageLoopMap_rowSwap k D y s t)
    | inr z =>
      exact congrArg (fun y => (mappingConeHomotopy d).level (k + 3) (z.1, y))
        (RowHomotopyPushout.structure_rowSwap f g k z.2 s t)

variable (b : B ⟶ D) (c : C ⟶ D)
  (H : Homotopy (prespectrumMap f ≫ prespectrumMap b)
    (prespectrumMap g ≫ prespectrumMap c))

/-- The comparison square follows from the entire prescribed overlap track, cell by cell. -/
theorem comparison_rowSwap (k : ℕ)
    (hH : ∀ t x, RowHomotopyPushout.vertex k D (H.level (k + 3) (t, x)) =
      H.level (k + 3) (t, RowHomotopyPushout.vertex k A x))
    (x : (RowHomotopyPushout.spectrum f g).space (k + 3)) :
    RowHomotopyPushout.vertex k D
      ((HomotopyPushout.desc (prespectrumMap f) (prespectrumMap g)
        (prespectrumMap b) (prespectrumMap c) H).map (k + 3) x) =
      (HomotopyPushout.desc (prespectrumMap f) (prespectrumMap g)
        (prespectrumMap b) (prespectrumMap c) H).map (k + 3)
          (RowHomotopyPushout.rowSwap f g k x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl y => exact RowHomotopyPushout.vertex_naturality k b y
      | inr y => exact RowHomotopyPushout.vertex_naturality k c y
    | inr z => exact hH z.1 z.2

end Quillen.Waldhausen.IteratedS.RowMappingCone
