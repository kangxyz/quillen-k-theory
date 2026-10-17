/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalAttachmentNodes
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenMap

/-! The actual terminal reference transport preserves both original sheets and their clocks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalAttachmentMap
open CommonReferenceNerve CommonReferenceProduct CutOpenCarrier
open CoefficientBassSeedTerminalAttachmentNodes
open CoefficientBassSeedTerminalAttachmentTriangle CoefficientBassSeedTerminalShiftedTriangle
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "K" => CoefficientBassSeedTargetChartAttachment.Jb P
  (b := CategoryTheory.Functor.obj (laurentUnderFunctor R) b)
local notation "F" => sourcePolynomial P f α
local notation "G" => sourceLaurent P f α
local notation "F'" => targetPolynomial P f α
local notation "G'" => targetLaurent P f α
local notation "ε₀" => targetOrdinary P f α
local notation "ε₁" => targetShifted P f α
local notation "η₀" => ordinary P f α
local notation "η₁" => shifted P f α

/-- The complete polynomial node reanchor uses the original terminal normalization. -/
def polynomialMap : |parameterSSet F| ⟶ |parameterSSet F'| :=
  SSet.toTop.map (nerveMap (Codiscrete.functorOfFun
    (reanchor (CoefficientBassSeedTerminalPolynomialReference.referenceIso P f α))))

/-- The complete Laurent node reanchor uses the same actual input and reference transport. -/
def laurentMap : |parameterSSet G| ⟶ |parameterSSet G'| :=
  SSet.toTop.map (nerveMap (Codiscrete.functorOfFun
    (reanchor (CoefficientBassSeedTerminalLaurentReference.referenceIso P f α))))

/-- The ordinary whole attaching square is the proved full parameter equality. -/
theorem ordinary_square :
    SSet.toTop.map (attaching F K G ε₀) ≫ laurentMap P f α =
      polynomialMap P f α ≫ SSet.toTop.map (attaching F' K G' η₀) := by
  ext x
  exact ordinary_parameter P f α x

/-- The shifted whole attaching square retains the original inner Laurent unit. -/
theorem shifted_square :
    SSet.toTop.map (attaching F K G ε₁) ≫ laurentMap P f α =
      polynomialMap P f α ≫ SSet.toTop.map (attaching F' K G' η₁) := by
  ext x
  exact shifted_parameter P f α x

/-- Transport the existing chosen target carrier through its two actual attachment squares. -/
def map : space F K G ε₀ ε₁ ⟶ space F' K G' η₀ η₁ :=
  CutOpenMap.map F K G F' K G' ε₀ ε₁ η₀ η₁
    (polynomialMap P f α) (laurentMap P f α)
    (ordinary_square P f α) (shifted_square P f α)

/-- The original tipMinus cell keeps its full reference and unchanged clock. -/
@[simp] theorem map_tipMinus :
    map P f α (tipMinus F K G ε₀ ε₁) =
      tipMinus F' K G' η₀ η₁ :=
  CutOpenMap.map_tipMinus F K G F' K G' ε₀ ε₁ η₀ η₁
    (polynomialMap P f α) (laurentMap P f α)
    (ordinary_square P f α) (shifted_square P f α)

/-- The original tipPlus cell keeps its full reference and unchanged clock. -/
@[simp] theorem map_tipPlus :
    map P f α (tipPlus F K G ε₀ ε₁) =
      tipPlus F' K G' η₀ η₁ :=
  CutOpenMap.map_tipPlus F K G F' K G' ε₀ ε₁ η₀ η₁
    (polynomialMap P f α) (laurentMap P f α)
    (ordinary_square P f α) (shifted_square P f α)

/-- The original laurent cell keeps its full reference and unchanged clock. -/
@[simp] theorem map_laurent (x : |parameterSSet G|) :
    map P f α (laurentInclusion F K G ε₀ ε₁ x) =
      laurentInclusion F' K G' η₀ η₁ (laurentMap P f α x) :=
  CutOpenMap.map_laurent F K G F' K G' ε₀ ε₁ η₀ η₁
    (polynomialMap P f α) (laurentMap P f α)
    (ordinary_square P f α) (shifted_square P f α) x

/-- The original cylinderMinus cell keeps its full reference and unchanged clock. -/
@[simp] theorem map_cylinderMinus (x : |parameterSSet F|) (t : I) :
    map P f α (cylinderMinus F K G ε₀ ε₁ (x, t)) =
      cylinderMinus F' K G' η₀ η₁ (polynomialMap P f α x, t) :=
  CutOpenMap.map_cylinderMinus F K G F' K G' ε₀ ε₁ η₀ η₁
    (polynomialMap P f α) (laurentMap P f α)
    (ordinary_square P f α) (shifted_square P f α) x t

/-- The original cylinderPlus cell keeps its full reference and unchanged clock. -/
@[simp] theorem map_cylinderPlus (x : |parameterSSet F|) (t : I) :
    map P f α (cylinderPlus F K G ε₀ ε₁ (x, t)) =
      cylinderPlus F' K G' η₀ η₁ (polynomialMap P f α x, t) :=
  CutOpenMap.map_cylinderPlus F K G F' K G' ε₀ ε₁ η₀ η₁
    (polynomialMap P f α) (laurentMap P f α)
    (ordinary_square P f α) (shifted_square P f α) x t

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalAttachmentMap
