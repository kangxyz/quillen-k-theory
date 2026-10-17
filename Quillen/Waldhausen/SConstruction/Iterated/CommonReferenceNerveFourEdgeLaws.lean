/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeExt

/-! The whole four-edge evaluator preserves the native point and independent structure time. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
open CutOpenCarrier LoopPrespectrum.HomotopyPushout
variable {V W T : Model.{u}} (E : V ⟶ W) (J : W ⟶ T)

private theorem plus_point (n : ℕ) (y : |parameterSSet (E ≫ J)|) :
    nativePlus E J n y ((prespectrum V).point n) = (nativeSpan J).point n := by
  change LoopPrespectrum.HomotopyPushout.left (prespectrumMap J) (prespectrumMap J) n
    (pointwisePrespectrumFamily (E ≫ J) n y ((prespectrum V).point n)) = _
  rw [pointwisePrespectrumFamily_point]; rfl

private theorem minus_point (n : ℕ) (y : |parameterSSet (E ≫ J)|) :
    nativeMinus E J n y ((prespectrum V).point n) = (nativeSpan J).point n := by
  change LoopPrespectrum.HomotopyPushout.right (prespectrumMap J) (prespectrumMap J) n
    (pointwisePrespectrumFamily (E ≫ J) n y ((prespectrum V).point n)) = _
  rw [pointwisePrespectrumFamily_point]
  exact right_point _ _ n

private theorem cylinder_point_native (n : ℕ) (y : |parameterSSet E|) (s : I) :
    nativeCylinder E J n y s ((prespectrum V).point n) = (nativeSpan J).point n := by
  change LoopPrespectrum.HomotopyPushout.cylinder _ _ n
    (s, pointwisePrespectrumFamily E n y ((prespectrum V).point n)) = _
  rw [pointwisePrespectrumFamily_point]
  exact cylinder_point _ _ n s

/-- The full tree evaluator preserves the actual native point in every degree. -/
theorem nativeEval_point (n : ℕ) (z : space E J) :
    nativeEval E J n z ((prespectrum V).point n) = (nativeSpan J).point n := by
  refine congrFun (funext_cells E J
    (fun z ↦ nativeEval E J n z ((prespectrum V).point n))
    (fun _ ↦ (nativeSpan J).point n) ?_ ?_ ?_ ?_ ?_ ?_) z
  · intro y; rw [nativeEval_plus]; exact plus_point E J n y
  · intro y; rw [nativeEval_minus]; exact minus_point E J n y
  · intro y s; rw [nativeEval_edge12]; exact cylinder_point_native E J n y _
  · intro y s; rw [nativeEval_edge01]; exact cylinder_point_native E J n y _
  · intro y s; rw [nativeEval_edge03]; exact cylinder_point_native E J n y _
  · intro y s; rw [nativeEval_edge34]; exact cylinder_point_native E J n y _

private theorem plus_structure (n : ℕ) (y : |parameterSSet (E ≫ J)|)
    (x : (prespectrum V).space n) (r : I) :
    nativePlus E J (n + 1) y ((prespectrum V).structureMap n x r) =
      (nativeSpan J).structureMap n (nativePlus E J n y x) r := by
  change LoopPrespectrum.HomotopyPushout.left _ _ (n + 1)
    (pointwisePrespectrumFamily (E ≫ J) (n + 1) y ((prespectrum V).structureMap n x r)) =
      LoopPrespectrum.HomotopyPushout.left _ _ (n + 1) ((prespectrum T).structureMap n
        (pointwisePrespectrumFamily (E ≫ J) n y x) r)
  rw [pointwisePrespectrumFamily_structure]

private theorem minus_structure (n : ℕ) (y : |parameterSSet (E ≫ J)|)
    (x : (prespectrum V).space n) (r : I) :
    nativeMinus E J (n + 1) y ((prespectrum V).structureMap n x r) =
      (nativeSpan J).structureMap n (nativeMinus E J n y x) r := by
  change LoopPrespectrum.HomotopyPushout.right _ _ (n + 1)
    (pointwisePrespectrumFamily (E ≫ J) (n + 1) y ((prespectrum V).structureMap n x r)) =
      LoopPrespectrum.HomotopyPushout.right _ _ (n + 1) ((prespectrum T).structureMap n
        (pointwisePrespectrumFamily (E ≫ J) n y x) r)
  rw [pointwisePrespectrumFamily_structure]

private theorem cylinder_structure (n : ℕ) (y : |parameterSSet E|) (s r : I)
    (x : (prespectrum V).space n) :
    nativeCylinder E J (n + 1) y s ((prespectrum V).structureMap n x r) =
      (nativeSpan J).structureMap n (nativeCylinder E J n y s x) r := by
  change LoopPrespectrum.HomotopyPushout.cylinder _ _ (n + 1)
    (s, pointwisePrespectrumFamily E (n + 1) y ((prespectrum V).structureMap n x r)) =
      LoopPrespectrum.HomotopyPushout.cylinder _ _ (n + 1)
        (s, (prespectrum W).structureMap n (pointwisePrespectrumFamily E n y x) r)
  rw [pointwisePrespectrumFamily_structure]

/-- The structure coordinate remains independent of every whole tree and overlap coordinate. -/
theorem nativeEval_structure (n : ℕ) (z : space E J) (x : (prespectrum V).space n) (r : I) :
    nativeEval E J (n + 1) z ((prespectrum V).structureMap n x r) =
      (nativeSpan J).structureMap n (nativeEval E J n z x) r := by
  refine congrFun (funext_cells E J
    (fun z ↦ nativeEval E J (n + 1) z ((prespectrum V).structureMap n x r))
    (fun z ↦ (nativeSpan J).structureMap n (nativeEval E J n z x) r)
    ?_ ?_ ?_ ?_ ?_ ?_) z
  · intro y; rw [nativeEval_plus, nativeEval_plus]; exact plus_structure E J n y x r
  · intro y; rw [nativeEval_minus, nativeEval_minus]; exact minus_structure E J n y x r
  · intro y s; rw [nativeEval_edge12, nativeEval_edge12]; exact cylinder_structure E J n y _ r x
  · intro y s; rw [nativeEval_edge01, nativeEval_edge01]; exact cylinder_structure E J n y _ r x
  · intro y s; rw [nativeEval_edge03, nativeEval_edge03]; exact cylinder_structure E J n y _ r x
  · intro y s; rw [nativeEval_edge34, nativeEval_edge34]; exact cylinder_structure E J n y _ r x

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
