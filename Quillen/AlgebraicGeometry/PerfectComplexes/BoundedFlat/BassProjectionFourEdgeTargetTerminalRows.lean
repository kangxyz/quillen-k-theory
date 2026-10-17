/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeProjectionBinaryRows

/-!
# The full target Bass row of the original H0 diagram

The two original target binary rows retain their common full normalized source. The inverse
chart uses its actual projection equality transport. No native-value cancellation is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge BassH1Join CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
local notation "U" => normalizedMap (coefficientMap P f)
local notation "F" => BassH0Diagram.reference P f

/-- The complete target binary row occupies the original final three rectangle labels. -/
def terminalChartRow : Fin 3 → Fin 18 := ![15, 16, 17]

/-- Every positive target node retains its entire original precomposed binary reference. -/
theorem terminal_plus_nodes (i : Fin 3) :
    BassH0Diagram.plusNodes P f (terminalChartRow i) =
      preReferenceNode F U (terminalBaseAnchor P f)
        (binaryNodes (laurentPlus P b) (polynomialProjection P b) i) := by
  have h (j : Fin 3) := native_target_row
    (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P b) (laurentPlus P b)
    (coefficientMap P f) (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) f)
    (coefficientMap_naturality P (underToLaurent R) f)
    (laurentProjection P a) (laurentPlus_projection P a) j
  have he := (h 0).symm.trans ((terminal_normal_node P f).trans
    (preReferenceNode_source F U (terminalBaseAnchor P f)).symm)
  have hi : DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i) =
      terminalChartRow i := by fin_cases i <;> rfl
  have hh := (h i).trans (preBinaryNodes_of_source he i)
  rw [hi] at hh
  exact hh

/-- The inverse target row uses its distinct chart and exact shared-source transport. -/
theorem terminal_minus_nodes (i : Fin 3) :
    BassH0Diagram.minusNodes P f (terminalChartRow i) =
      preReferenceNode F U
        (terminalBaseAnchor P f ≪≫ isoWhiskerLeft (U).functor (BassProjectionPath.sourceIso P b))
        (binaryNodes (laurentMinus P b) (polynomialProjection P b) i) := by
  have h (j : Fin 3) := native_target_row
    (polynomialProjection P a) (laurentMinus P a)
    (polynomialProjection P b) (laurentMinus P b)
    (coefficientMap P f) (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) f)
    (coefficientMap_naturality P (underToLaurentInvert R) f)
    (laurentProjection P a) (laurentMinus_projection P a) j
  have hc := (BassH0Diagram.shared_nodes P f 4).symm.trans (terminal_normal_node P f)
  have ht := preReferenceNode_source_transport F U (BassProjectionPath.source_eq P b)
    (terminalBaseAnchor P f)
  have he := (h 0).symm.trans (hc.trans (ht.trans
    (preReferenceNode_source F U
      (terminalBaseAnchor P f ≪≫
        isoWhiskerLeft (U).functor (BassProjectionPath.sourceIso P b))).symm))
  have hi : DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i) =
      terminalChartRow i := by fin_cases i <;> rfl
  have hh := (h i).trans (preBinaryNodes_of_source he i)
  rw [hi] at hh
  exact hh

/-- The two original target paths retain their common center and separate raw intermediates. -/
def terminalRow : Fin 5 → Fin 31 := ![26, 27, 28, 29, 30]

/-- The full five-node terminal Bass family is literally precomposed by the coefficient map. -/
theorem terminal_nodes (i : Fin 5) :
    BassH0Diagram.nodes P f (terminalRow i) =
      preReferenceNode F U (terminalBaseAnchor P f) (BassProjectionPath.nodes P b i) := by
  fin_cases i
  · exact (BassH0Diagram.plus_nodes P f 15).trans (terminal_plus_nodes P f 0)
  · exact (BassH0Diagram.plus_nodes P f 16).trans (terminal_plus_nodes P f 1)
  · exact (BassH0Diagram.plus_nodes P f 17).trans (terminal_plus_nodes P f 2)
  · refine (BassH0Diagram.minus_nodes P f 16).trans ((terminal_minus_nodes P f 1).trans ?_)
    exact (pre_anchor_node F U (terminalBaseAnchor P f) (BassProjectionPath.sourceIso P b)
      (binaryNodes (laurentMinus P b) (polynomialProjection P b) 1)).symm
  · refine (BassH0Diagram.minus_nodes P f 17).trans ((terminal_minus_nodes P f 2).trans ?_)
    exact (pre_anchor_node F U (terminalBaseAnchor P f) (BassProjectionPath.sourceIso P b)
      (binaryNodes (laurentMinus P b) (polynomialProjection P b) 2)).symm

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
