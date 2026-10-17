/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetConeMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSpanNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetNative

/-! Every point of the original ordinary cone action recovers the fixed coefficient Bass map. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetCone
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree
open LoopPrespectrum
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "U" => normalizedMap (coefficientMap P f)
local notation "Ja" => normalizedMap (polynomialProjection P a)
local notation "Jb" => normalizedMap (polynomialProjection P b)
local notation "Eb" => E ≫ U
local notation "Fb" => WholeReference.reference P b Eb
local notation "βb" => beta P b Eb
local notation "B" => boundedFlatCoefficientBassConeMap P f

/-- The exact Laurent source map recovers the original Laurent coefficient map at all levels. -/
theorem laurent_native (n : ℕ) (y : |parameterSSet (WholeReference.reference P a E)|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily Fb n (laurent P f E y) x =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map f))).map n
          (pointwisePrespectrumFamily (WholeReference.reference P a E) n y x) := by
  have hm : laurent P f E y = mapParameter (toTargetNode P f E)
      (mapParameter (Target.sourceBoundaryNode P f E) y) := by
    obtain ⟨k, N, z, rfl⟩ := exists_parameter (WholeReference.reference P a E) y
    change mapParameter (fun N ↦ toTargetNode P f E (Target.sourceBoundaryNode P f E N))
      (CommonReferenceNerve.parameter _ N z) = _
    simp only [mapParameter_parameter]
  rw [hm, toTarget_native]
  exact pointwisePrespectrumFamily_attachPostcomp (WholeReference.reference P a E)
    (Target.sourcePost P f) (Target.reference P f E) (Target.sourceBoundaryAnchor P f E) n y x

/-- The unchanged first-half surface has the original Bass comparison value. -/
theorem surface_native (n : ℕ) (z : FourEdgeTree.space E Ja) (s : I)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily Fb n (surface P f E (z, s)) x =
      (boundedFlatCoefficientBassComparisonHomotopy P f).level n
        (s, nativeEval E Ja n z x) :=
  (toTarget_native P f E n (Target.tree P f E (z, s)) x).trans
    (Target.tree_native P f E n z s x)

/-- The entire Laurent baseline recovers the literal coefficient cone-map inclusion. -/
theorem coneMap_native_laurent (n : ℕ)
    (y : |parameterSSet (WholeReference.reference P a E)|) (x : (prespectrum V).space n) :
    coneEval P b Eb n (coneMap P f E
      (laurentInclusion E Ja (WholeReference.reference P a E) (beta P a E) y)) x =
      (B).map n (coneEval P a E n
        (laurentInclusion E Ja (WholeReference.reference P a E) (beta P a E) y) x) := by
  rw [coneMap_laurent, coneEval_laurent]
  change coneEval P b Eb n (laurentInclusion Eb Jb Fb βb (laurent P f E y)) x = _
  rw [coneEval_laurent]
  change (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)).map n
    (pointwisePrespectrumFamily Fb n (laurent P f E y) x) = _
  rw [laurent_native]
  exact (congrArg (fun k ↦ k.map n
    (pointwisePrespectrumFamily (WholeReference.reference P a E) n y x))
      (boundedFlatCoefficientBassConeMap_inclusion P f)).symm

/-- The same original tip is fixed by the actual pointed cone map. -/
theorem coneMap_native_tip (n : ℕ) (x : (prespectrum V).space n) :
    coneEval P b Eb n (coneMap P f E
      (tip E Ja (WholeReference.reference P a E) (beta P a E))) x =
      (B).map n (coneEval P a E n
        (tip E Ja (WholeReference.reference P a E) (beta P a E)) x) := by
  rw [coneMap_tip, coneEval_tip, coneEval_tip, (B).map_point]

/-- Both original cone-height halves recover the exact original native cylinder formula. -/
theorem coneMap_native_cylinder (n : ℕ) (z : FourEdgeTree.space E Ja) (t : I)
    (x : (prespectrum V).space n) :
    coneEval P b Eb n (coneMap P f E
      (cylinder E Ja (WholeReference.reference P a E) (beta P a E) (z, t))) x =
      (B).map n (coneEval P a E n
        (cylinder E Ja (WholeReference.reference P a E) (beta P a E) (z, t)) x) := by
  rcases cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [coneMap_lower, coneEval_laurent, coneEval_cylinder,
      boundedFlatCoefficientBassConeMap_cylinder, Homotopy.trans_lower_cell]
    change (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)).map n
      (pointwisePrespectrumFamily Fb n (surface P f E (z, s)) x) = _
    rw [surface_native]; rfl
  · rw [coneMap_upper, coneEval_cylinder, coneEval_cylinder,
      boundedFlatCoefficientBassConeMap_cylinder, Homotopy.trans_upper_cell]
    rw [TargetSpan.treeMap_native]
    rfl

/-- Every ordinary scalar-cone point has its actual original native coefficient-map value. -/
theorem coneMap_native (n : ℕ) (z : scalarCone P a E) (x : (prespectrum V).space n) :
    coneEval P b Eb n (coneMap P f E z) x = (B).map n (coneEval P a E n z x) := by
  have h := SetDescent.funext (beta P a E)
    (SSet.stdSimplex.isTerminalObj₀.from (FourEdgeTree.simplicial E Ja))
    (fun z ↦ coneEval P b Eb n (coneMap P f E z) x)
    (fun z ↦ (B).map n (coneEval P a E n z x))
    (fun z ↦ coneMap_native_cylinder P f E n z.1 z.2.down x)
    (fun y ↦ coneMap_native_laurent P f E n y x)
    (fun y ↦ by
      have hy : y = (default : |tipSSet.{u + 1}|) := Subsingleton.elim _ _
      subst y
      exact coneMap_native_tip P f E n x)
  exact congrFun h z

/-- Compact scalar families retain joint continuity in every genuine native input. -/
theorem coneMap_compact_continuous {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, scalarCone P a E)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      coneEval P b Eb n (coneMap P f E (p z.1)) z.2) :=
  coneEval_compact_continuous P b Eb ((coneMap P f E).comp p) n

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetCone
