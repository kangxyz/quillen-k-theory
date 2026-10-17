/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminal
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSource
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! The original target surface in the literal target Laurent reference, with both full seams. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetCone
open BassH0Merge CommonReferenceNerve

private theorem map_comp {V W V' W' V'' W'' : Model.{u}}
    {F : V ⟶ W} {G : V' ⟶ W'} {H : V'' ⟶ W''}
    (h : CommonReferenceNerve.Node F → CommonReferenceNerve.Node G)
    (g : CommonReferenceNerve.Node G → CommonReferenceNerve.Node H)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node F))|) :
    mapParameter (fun N ↦ g (h N)) y = mapParameter g (mapParameter h y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  simp only [mapParameter_parameter]

private theorem map_inverse_reanchor {V W : Model.{u}} {F G : V ⟶ W}
    (η : F.functor ≅ G.functor) (y : |nerve (Codiscrete (CommonReferenceNerve.Node G))|) :
    mapParameter (CommonReferenceProduct.reanchor η.symm)
      (mapParameter (CommonReferenceProduct.reanchor η) y) = y := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter G y
  rw [mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter G ns z)
  funext i
  simp only [CommonReferenceProduct.reanchor, Iso.symm_self_id_assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "U" => normalizedMap (coefficientMap P f)
local notation "Ja" => normalizedMap (polynomialProjection P a)

/-- The actual full H0 reference is transported into the literal target Laurent reference. -/
def toTargetNode : CommonReferenceNerve.Node (Target.reference P f E) →
    CommonReferenceNerve.Node (WholeReference.reference P b (E ≫ U)) :=
  CommonReferenceProduct.reanchor (Target.terminalBoundaryAnchor P f E).symm

/-- The Laurent source map retains its full original coefficient postcomposition anchor. -/
def sourceNode (N : CommonReferenceNerve.Node (WholeReference.reference P a E)) :
    CommonReferenceNerve.Node (WholeReference.reference P b (E ≫ U)) :=
  toTargetNode P f E (Target.sourceBoundaryNode P f E N)

/-- The actual complete Laurent coefficient map in the target reference. -/
def laurent : C(|nerve (Codiscrete (CommonReferenceNerve.Node (WholeReference.reference P a E)))|,
    |nerve (Codiscrete (CommonReferenceNerve.Node (WholeReference.reference P b (E ≫ U))))|) :=
  mapParameter (sourceNode P f E)

/-- The original whole H0 target surface, with its full reference transport and unchanged time. -/
def surface : C(FourEdgeTree.space E Ja × I,
    |nerve (Codiscrete (CommonReferenceNerve.Node (WholeReference.reference P b (E ≫ U))))|) :=
  (mapParameter (toTargetNode P f E)).comp (Target.tree P f E)

/-- The full original Laurent map is the source of this unchanged surface. -/
theorem surface_zero (z : FourEdgeTree.space E Ja) :
    surface P f E (z, 0) = laurent P f E (SSet.toTop.map (beta P a E) z) := by
  change mapParameter (toTargetNode P f E) (Target.tree P f E (z, 0)) = _
  rw [Target.tree_source]
  exact (map_comp (Target.sourceBoundaryNode P f E) (toTargetNode P f E) _).symm

/-- The exact target beta seam holds before any cone quotient or native evaluation. -/
theorem surface_one (z : FourEdgeTree.space E Ja) :
    surface P f E (z, 1) =
      SSet.toTop.map (beta P b (E ≫ U)) (TargetSpan.treeMap P f E z) := by
  change mapParameter (toTargetNode P f E) (Target.tree P f E (z, 1)) = _
  rw [Target.tree_terminal]
  exact map_inverse_reanchor (Target.terminalBoundaryAnchor P f E) _

/-- Full reference transport preserves every native level, including the actual loop input. -/
theorem toTarget_native (n : ℕ)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node (Target.reference P f E)))|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (WholeReference.reference P b (E ≫ U)) n
      (mapParameter (toTargetNode P f E) y) x =
    pointwisePrespectrumFamily (Target.reference P f E) n y x :=
  pointwise_reanchor (Target.terminalBoundaryAnchor P f E).symm n y x

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetCone
