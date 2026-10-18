/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictSquarePushout

/-!
# Original cells of square-cone pushout interchange

The three outer pushout strata and two original cone strata retain all their
parameters. The cylinder formulas allow arbitrary points of the inner source
span. The final formula displays the independent cone height and both original
overlap times explicitly, without normalization or reparametrization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.StrictSquare.Pushout
open HomotopyPushout
variable {S₀ S₁ S₂ : Arrow (Arrow LoopPrespectrum.{u})}
  (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂)

/-- The original left target inclusion keeps its target point. -/
theorem totalIso_left_inclusion (n : ℕ) (x : S₁.right.right.space n) :
    (totalIso f g).hom.map n
      (HomotopyPushout.left (mappingConeMap (strictSquareComparisonFunctor.map f))
        (mappingConeMap (strictSquareComparisonFunctor.map g)) n
        ((mappingConeInclusion (comparison S₁)).map n x)) =
      (mappingConeInclusion (comparison (square f g))).map n
        (HomotopyPushout.left f.right.right g.right.right n x) := rfl

/-- The original right target inclusion keeps its target point. -/
theorem totalIso_right_inclusion (n : ℕ) (x : S₂.right.right.space n) :
    (totalIso f g).hom.map n
      (HomotopyPushout.right (mappingConeMap (strictSquareComparisonFunctor.map f))
        (mappingConeMap (strictSquareComparisonFunctor.map g)) n
        ((mappingConeInclusion (comparison S₂)).map n x)) =
      (mappingConeInclusion (comparison (square f g))).map n
        (HomotopyPushout.right f.right.right g.right.right n x) := rfl

/-- The whole original target overlap is included with its unchanged time. -/
theorem totalIso_overlap_inclusion (n : ℕ) (s : unitInterval) (x : S₀.right.right.space n) :
    (totalIso f g).hom.map n
      (cylinder (mappingConeMap (strictSquareComparisonFunctor.map f))
        (mappingConeMap (strictSquareComparisonFunctor.map g)) n
        (s, (mappingConeInclusion (comparison S₀)).map n x)) =
      (mappingConeInclusion (comparison (square f g))).map n
        (cylinder f.right.right g.right.right n (s,x)) := rfl

/-- The left cone cylinder keeps its height and the entire inner source span. -/
theorem totalIso_left_cylinder (n : ℕ) (r : unitInterval) (x : (span S₁).space n) :
    (totalIso f g).hom.map n
      (HomotopyPushout.left (mappingConeMap (strictSquareComparisonFunctor.map f))
        (mappingConeMap (strictSquareComparisonFunctor.map g)) n
        ((mappingConeHomotopy (comparison S₁)).level n (r,x))) =
      (mappingConeHomotopy (comparison (square f g))).level n
        (r, (spanIso f g).hom.map n (HomotopyPushout.left (spanMap f) (spanMap g) n x)) := rfl

/-- The right cone cylinder keeps its height and the entire inner source span. -/
theorem totalIso_right_cylinder (n : ℕ) (r : unitInterval) (x : (span S₂).space n) :
    (totalIso f g).hom.map n
      (HomotopyPushout.right (mappingConeMap (strictSquareComparisonFunctor.map f))
        (mappingConeMap (strictSquareComparisonFunctor.map g)) n
        ((mappingConeHomotopy (comparison S₂)).level n (r,x))) =
      (mappingConeHomotopy (comparison (square f g))).level n
        (r, (spanIso f g).hom.map n (HomotopyPushout.right (spanMap f) (spanMap g) n x)) := rfl

/-- Cone height and outer overlap time remain independent throughout the actual descent. -/
theorem totalIso_overlap_cylinder (n : ℕ) (r s : unitInterval) (x : (span S₀).space n) :
    (totalIso f g).hom.map n
      (cylinder (mappingConeMap (strictSquareComparisonFunctor.map f))
        (mappingConeMap (strictSquareComparisonFunctor.map g)) n
        (s, (mappingConeHomotopy (comparison S₀)).level n (r,x))) =
      (mappingConeHomotopy (comparison (square f g))).level n
        (r, (spanIso f g).hom.map n (cylinder (spanMap f) (spanMap g) n (s,x))) := rfl

/-- The deepest cell retains its cone height and swaps only the two original overlap positions. -/
theorem totalIso_three_parameters (n : ℕ) (r s t : unitInterval)
    (x : S₀.left.left.space n) :
    (totalIso f g).hom.map n
      (cylinder (mappingConeMap (strictSquareComparisonFunctor.map f))
        (mappingConeMap (strictSquareComparisonFunctor.map g)) n
        (s, (mappingConeHomotopy (comparison S₀)).level n
          (r, cylinder S₀.left.hom S₀.hom.left n (t,x)))) =
      (mappingConeHomotopy (comparison (square f g))).level n
        (r, cylinder (top f g) (left f g) n
          (t, cylinder f.left.left g.left.left n (s,x))) := rfl

end Quillen.LoopPrespectrum.StrictSquare.Pushout
