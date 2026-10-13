/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.PushoutVanishing
public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeVanishing
public import Quillen.Topology.Prespectrum.StrictSquareTopology

/-!
# The exact finite loss in the original Bass operation

Finite vanishing of the four original corners passes through the original reduced span and
cone with no loss above cutoff two. The original parameter-loop space then loses precisely
one degree, at every actual loop component. Only the original four point HEP hypotheses
enter this fixed-level assertion; neither separation nor an Omega condition is required.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.StrictSquare
variable (S : Arrow (Arrow LoopPrespectrum.{u})) (m n : ℕ)

/-- The genuine strict-square Bass operation loses one degree of finite vanishing. -/
theorem loopedCone_homotopyGroup_subsingleton
    (hA : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.left.point m))))
    (hB : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.right.point m))))
    (hC : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.left.point m))))
    (hD : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.right.point m))))
    (hπA : ∀ a k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (S.left.left.space m) a))
    (hπB : ∀ b k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (S.left.right.space m) b))
    (hπC : ∀ c k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (S.right.left.space m) c))
    (hπD : ∀ d k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (S.right.right.space m) d))
    (γ : (strictSquareLoopedConeFunctor.obj S).space m) (k : ℕ) (hk : k < n + 1) :
    Subsingleton (HomotopyGroup.Pi k ((strictSquareLoopedConeFunctor.obj S).space m) γ) := by
  have hs (z : (span S).space m) (j : ℕ) (hj : j < n + 2) :
      Subsingleton (HomotopyGroup.Pi j ((span S).space m) z) :=
    HomotopyPushout.homotopyGroup_subsingleton S.left.hom S.hom.left m n hA hB hC
      hπA hπB hπC z j hj
  have hc := ReducedMappingCone.homotopyGroup_subsingleton
    ((span S).point m) (S.right.right.point m) ((comparison S).map m)
    ((comparison S).map_point m) (span_point_homotopyExtensionProperty S m hA hB hC) hD
    n hs hπD ((mappingCone (comparison S)).point m) (k + 1) (by omega)
  exact subsingleton_pi_loop_of_succ ((mappingCone (comparison S)).point m) k hc γ

end Quillen.LoopPrespectrum.StrictSquare
