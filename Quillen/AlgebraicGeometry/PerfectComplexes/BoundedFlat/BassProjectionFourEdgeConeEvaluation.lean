/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeNative
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeCone
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeCompactFamily
public import Quillen.Topology.Prespectrum.MappingCone

/-! Exact evaluation of the unreduced Laurent cone into the original native Bass cone. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => BassH0Merge.normalizedMap (polynomialProjection P a)
local notation "F" => reference P a E
local notation "β" => beta P a E

/-- The native mapping cone of the bounded-flat coefficient Bass square comparison. -/
abbrev nativeBassCone :=
  LoopPrespectrum.mappingCone (boundedFlatCoefficientBassSquareComparison P a)
/-- The realized unreduced cone on the four-edge whole-reference tree. -/
abbrev scalarCone := FourEdgeTree.coneSpace E J F β

/-- Evaluate a Laurent parameter and include its value in the native Bass cone at level `n`. -/
def laurentValue (n : ℕ) (z : |parameterSSet F|) (x : (prespectrum V).space n) :
    (nativeBassCone P a).space n :=
  (LoopPrespectrum.mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n
    (pointwisePrespectrumFamily F n z x)

/-- Evaluate the four-edge tree in the native cone cylinder at the supplied cone height. -/
def coneCylinderValue (n : ℕ) (z : FourEdgeTree.space E J × TopCat.I.{u + 1})
    (x : (prespectrum V).space n) : (nativeBassCone P a).space n :=
  ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
    (z.2.down, FourEdgeTree.nativeEval E J n z.1 x)

/-- The actual whole-reference compatibility supplies the entire cylinder attachment. -/
theorem coneCylinderValue_zero (n : ℕ) (z : FourEdgeTree.space E J) :
    coneCylinderValue P a E n (z, ULift.up 0) =
      laurentValue P a E n (SSet.toTop.map β z) := by
  funext x
  dsimp only [coneCylinderValue, laurentValue]
  rw [ReducedMappingCone.cylinder_zero, beta_native]; rfl

theorem coneCylinderValue_one (n : ℕ) (z : FourEdgeTree.space E J) :
    coneCylinderValue P a E n (z, ULift.up 1) =
      fun _ ↦ (nativeBassCone P a).point n := by
  funext x
  exact ReducedMappingCone.cylinder_one _ _ _ _

/-- The original native cone value is descended through the single unreduced cone pushout. -/
def coneEval (n : ℕ) :
    scalarCone P a E → (prespectrum V).space n → (nativeBassCone P a).space n :=
  FourEdgeTree.SetDescent.value β (SSet.stdSimplex.isTerminalObj₀.from _)
    (laurentValue P a E n) (fun _ _ ↦ (nativeBassCone P a).point n)
    (coneCylinderValue P a E n) (coneCylinderValue_zero P a E n)
    (coneCylinderValue_one P a E n)

theorem coneEval_laurent (n : ℕ) (z : |parameterSSet F|) (x : (prespectrum V).space n) :
    coneEval P a E n (FourEdgeTree.laurentInclusion E J F β z) x =
      laurentValue P a E n z x :=
  congrFun (FourEdgeTree.SetDescent.value_left _ _ _ _ _ _ _ z) x

theorem coneEval_tip (n : ℕ) (x : (prespectrum V).space n) :
    coneEval P a E n (FourEdgeTree.tip E J F β) x = (nativeBassCone P a).point n :=
  congrFun (FourEdgeTree.SetDescent.value_right _ _ _ _ _ _ _ _) x

theorem coneEval_cylinder (n : ℕ) (z : FourEdgeTree.space E J) (t : I)
    (x : (prespectrum V).space n) :
    coneEval P a E n (FourEdgeTree.cylinder E J F β (z, t)) x =
      ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
        (t, FourEdgeTree.nativeEval E J n z x) :=
  congrFun (FourEdgeTree.SetDescent.value_cylinder _ _ _ _ _ _ _ (z, ULift.up t)) x

/-- Every native input retains both the original overlap time and the independent cone time. -/
theorem coneEval_overlapCylinder (n : ℕ) (y : |parameterSSet E|) (s t : I)
    (x : (prespectrum V).space n) :
    coneEval P a E n (FourEdgeTree.overlapCylinder E J F β ((y, s), t)) x =
      ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
        (t, LoopPrespectrum.HomotopyPushout.cylinder (prespectrumMap J) (prespectrumMap J) n
          (s, pointwisePrespectrumFamily E n y x)) := by
  change coneEval P a E n (FourEdgeTree.cylinder E J F β
    (FourEdgeTree.overlap E J (y, s), t)) x = _
  rw [coneEval_cylinder, FourEdgeTree.nativeEval_overlap]; rfl

/-- Compact parameterizations retain joint continuity in the genuine native input. -/
theorem coneEval_compact_continuous {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, scalarCone P a E)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦ coneEval P a E n (p z.1) z.2) := by
  apply FourEdgeTree.SetDescent.value_compact_continuous
  · intro S _ _ q
    exact ((LoopPrespectrum.mappingConeInclusion
      (boundedFlatCoefficientBassSquareComparison P a)).map n).continuous.comp
        (pointwisePrespectrumFamily_compact_continuous F q n)
  · intro S _ _ q
    exact continuous_const
  · intro S _ _ q
    let q' : C(S, FourEdgeTree.space E J) := ⟨fun s ↦ (q s).1, by fun_prop⟩
    exact (ReducedMappingCone.cylinder _ _
      ((boundedFlatCoefficientBassSquareComparison P a).map n)).continuous.comp
        ((show Continuous (fun z : S × (prespectrum V).space n ↦ (q z.1).2.down) by
          fun_prop).prodMk (FourEdgeTree.nativeEval_compact_continuous E J q' n))

/-- The resulting actual native cone family is continuous on every compact scalar family. -/
def compactConeFamily {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, scalarCone P a E)) (n : ℕ) :
    C(S × (prespectrum V).space n, (nativeBassCone P a).space n) :=
  ⟨fun z ↦ coneEval P a E n (p z.1) z.2, coneEval_compact_continuous P a E p n⟩

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
