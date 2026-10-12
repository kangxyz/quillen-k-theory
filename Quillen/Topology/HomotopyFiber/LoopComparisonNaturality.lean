/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HomotopyFiber.BasedHomotopySquareMap
public import Quillen.Topology.HomotopyFiber.LoopPrefixBasepointNaturality

/-! # Based naturality of the original inverse comparisons from an actual fiber square -/
@[expose] public section
noncomputable section
open scoped Topology
universe u v u' v' w w'
namespace Quillen.HomotopyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  {A : Type w} {A' : Type w'}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  [TopologicalSpace A] [TopologicalSpace A']

/-- An actual square of fiber comparisons induces the corrected naturality square of the
unchanged inverse loop comparisons. Every source and target basepoint path is displayed. -/
theorem loopComparison_naturality_pi [ContractibleSpace X] [ContractibleSpace X']
    {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (y : Y) (z : Y') (h : v y = z)
    (c : C(A, HomotopyFiber f y)) (d : C(A', HomotopyFiber f' z)) (a : C(A, A'))
    (J : ((basedHomotopySquareMap u v H y z h).comp c).Homotopy (d.comp a))
    (x : A) (x' : A') (p : Path (a x) x') (n : ℕ) (b : HomotopyGroup.Pi n A x) :
    homotopyGroupMap (basedLoopMap v h) (basedLoopMap_refl v h)
      (pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath
        f (c x).val.1 y (toPath f y (c x))) n
        (homotopyGroupMap (loopEquivOfContractibleSourcePath f (c x).val.1 y
          (toPath f y (c x))).invFun rfl (homotopyGroupMap c rfl b))) =
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath
      f' (d x').val.1 z (toPath f' z (d x'))) n
      (homotopyGroupMap (loopEquivOfContractibleSourcePath f' (d x').val.1 z
        (toPath f' z (d x'))).invFun rfl
        (homotopyGroupMap d rfl (pathTransport p n (homotopyGroupMap a rfl b)))) := by
  let M := basedHomotopySquareMap u v H y z h
  let q : Path (M (c x)) (d x') := (J.evalAt x).trans (p.map d.continuous)
  have ht : pathTransport q n (homotopyGroupMap M rfl (homotopyGroupMap c rfl b)) =
      homotopyGroupMap d rfl (pathTransport p n (homotopyGroupMap a rfl b)) := by
    rw [pathTransport_trans]
    rw [← homotopyGroupMap_comp c rfl M rfl]
    dsimp only [M]
    exact (congrArg (pathTransport (p.map d.continuous) n)
      (pathTransport_homotopyGroupMap_homotopy J x n b)).trans
      ((congrArg (pathTransport (p.map d.continuous) n)
        (homotopyGroupMap_comp a rfl d rfl b)).trans
          (pathTransport_naturality d p n (homotopyGroupMap a rfl b)))
  have hs := loopInverse_basedHomotopySquare_pi u v H (c x).val.1 y z h
    (toPath f y (c x)) n (homotopyGroupMap c rfl b)
  have hq := loopInverse_pathTransport_pi q n
    (homotopyGroupMap M rfl (homotopyGroupMap c rfl b))
  rw [ht] at hq
  exact hs.trans hq

end Quillen.HomotopyFiber
