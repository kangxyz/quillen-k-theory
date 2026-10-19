/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictSquareZeroMap

/-! # The literal zero endpoint of the original unlooped reduced square cone

The zero cylinder is collapsed by the original reduced-cone basepoint relation.
This is a map equality, so it introduces no additional contraction or time segment.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T)

/-- Four literal zero corner maps induce the literal zero map on the unlooped cone. -/
theorem StrictSquare.coneMap_eq_zero
    (h00 : a.left.left = zeroHom S.left.left T.left.left)
    (h01 : a.left.right = zeroHom S.left.right T.left.right)
    (h10 : a.right.left = zeroHom S.right.left T.right.left)
    (h11 : a.right.right = zeroHom S.right.right T.right.right) :
    mappingConeMap (strictSquareComparisonFunctor.map a) =
      zeroHom (mappingCone (StrictSquare.comparison S))
        (mappingCone (StrictSquare.comparison T)) := by
  have hs := StrictSquare.spanMap_eq_zero a h00 h01 h10
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y =>
      change ReducedMappingCone.inr ((StrictSquare.span T).point n) (T.right.right.point n)
        ((StrictSquare.comparison T).map n) (a.right.right.map n y) = _
      rw [h11]
      rfl
    | inr z =>
      change ReducedMappingCone.cylinder ((StrictSquare.span T).point n)
        (T.right.right.point n) ((StrictSquare.comparison T).map n)
        (z.1, (StrictSquare.spanMap a).map n z.2) = _
      rw [hs]
      exact ReducedMappingCone.cylinder_base ((StrictSquare.span T).point n)
        (T.right.right.point n) ((StrictSquare.comparison T).map n) z.1

end Quillen.LoopPrespectrum
