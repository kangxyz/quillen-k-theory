/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopy
public import Quillen.Topology.Prespectrum.ParameterLooping

/-! Whole relative comparisons of zero loops give actual homotopies into parameter-correct loops. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}}
  {H K : Homotopy (zeroHom E F) (zeroHom E F)}

/-- Curry the original comparison into based loops while retaining all independent times. -/
def zeroLoopMapHomotopy (J : H.RelHomotopy K) : Homotopy H.zeroLoopMap K.zeroLoopMap where
  level n := {
    toFun z := ((J.at z.1).zeroLoopMap).map n z.2
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun z : (unitInterval × E.space n) × unitInterval ↦
        J.level n (z.1.1, (z.2, z.1.2)))
      fun_prop }
  at_zero n x := by
    apply Path.ext
    funext s
    exact (J.level n).apply_zero (s, x)
  at_one n x := by
    apply Path.ext
    funext s
    exact (J.level n).apply_one (s, x)
  at_point n r := by
    apply Path.ext
    funext s
    exact ((J.level n).eq_fst r (Or.inr (Or.inr rfl))).trans (H.at_point n s)
  comm n r x t := by
    apply Path.ext
    funext s
    exact J.comm n r s x t

/-- Every original relative comparison coordinate remains the actual loop evaluation. -/
lemma zeroLoopMapHomotopy_apply (J : H.RelHomotopy K) (n : ℕ)
    (r s : unitInterval) (x : E.space n) :
    Path.toContinuousMap (J.zeroLoopMapHomotopy.level n (r, x)) s =
      J.level n (r, (s, x)) := rfl

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
