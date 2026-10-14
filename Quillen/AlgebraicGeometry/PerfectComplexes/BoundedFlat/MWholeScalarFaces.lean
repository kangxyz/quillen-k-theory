/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNodes

/-! Concrete whole original M parameters and all twelve exact scalar boundary joins. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWhole
open BassMWholeOrder

/-- The common-order certificate discharges all 46 finite label equations. -/
theorem indexEqualities : BassMScalarPasting.IndexEqualities vertexIndex oldIndex where
  sourcePlus := source_plus_index
  sourceMiddle := source_middle_index
  sourceMinus := source_minus_index
  sidePlus := boundary_side_plus_index
  sideMinus := boundary_side_minus_index
  firstPlus := boundary_first_plus_index
  secondPlus := boundary_second_plus_index
  middle := boundary_middle_index
  secondMinus := boundary_second_minus_index
  firstMinus := boundary_first_minus_index

/-- All 71 actual support chains have the concrete order required for native family transfer. -/
theorem supportOrders : BassMFamilyTransfer.SupportOrders vertexIndex oldIndex where
  oldPlus := oldOldPlus_monotone
  oldMinus := oldOldMinus_monotone
  oldH0Plus := oldH0Plus_monotone
  oldH0Minus := oldH0Minus_monotone
  oldBottom := oldBottom_monotone
  firstPlus := oldFirstPlus_monotone
  firstMinus := oldFirstMinus_monotone
  middlePlus := oldMiddlePlus_monotone
  middleMinus := oldMiddleMinus_monotone
  productPlus := oldPlusProduct_monotone
  productMinus := oldMinusProduct_monotone
  vertexPlus := vertexPlus_monotone
  vertexMinus := vertexMinus_monotone
  vertexMiddle := vertexMiddle_monotone

abbrev h0Parameter := BassMScalarPasting.h0 oldIndex
abbrev h1Parameter := BassMScalarPasting.h1.{u} oldIndex
abbrev plusParameter := BassMScalarPasting.plus oldIndex
abbrev minusParameter := BassMScalarPasting.minus oldIndex
abbrev bottomParameter := BassMScalarPasting.bottom.{u} oldIndex

/-- The pure complete M family pastes the two literal original stages at their native speeds. -/
def mParameter := BassMScalarPasting.parameter.{u} vertexIndex oldIndex indexEqualities

/-- The whole source-M/H0-target edge is literally shared in the actual common family. -/
theorem m_h0_scalar (t : unitInterval) : mParameter.{u} (0, t) = h0Parameter (1, t) :=
  BassMScalarPasting.parameter_zero vertexIndex oldIndex indexEqualities t

/-- The whole target-M/H1-target edge keeps the original five-piece reassociation endpoint. -/
theorem m_h1_scalar (t : unitInterval) : mParameter.{u} (1, t) = h1Parameter.{u} (1, t) :=
  BassMScalarPasting.parameter_one vertexIndex oldIndex indexEqualities t

/-- The complete positive M side is the unchanged original chart target edge, with its pause. -/
theorem m_plus_scalar (r : unitInterval) : mParameter.{u} (r, 0) = plusParameter (r, 1) :=
  BassMScalarPasting.parameter_plus vertexIndex oldIndex indexEqualities r

/-- The complete inverse M side retains the distinct original chart target edge and its pause. -/
theorem m_minus_scalar (r : unitInterval) : mParameter.{u} (r, 1) = minusParameter (r, 1) :=
  BassMScalarPasting.parameter_minus vertexIndex oldIndex indexEqualities r

theorem h0_plus_scalar (s : unitInterval) : h0Parameter (s, 0) = plusParameter (0, s) :=
  BassMScalarPasting.h0_plus_scalar oldIndex s

theorem h0_minus_scalar (s : unitInterval) : h0Parameter (s, 1) = minusParameter (0, s) :=
  BassMScalarPasting.h0_minus_scalar oldIndex s

theorem h0_bottom_scalar (t : unitInterval) : h0Parameter (0, t) = bottomParameter.{u} (0, t) :=
  BassMScalarPasting.h0_bottom_scalar oldIndex t

theorem plus_bottom_scalar (r : unitInterval) : plusParameter (r, 0) = bottomParameter.{u} (r, 0) :=
  BassMScalarPasting.plus_bottom_scalar oldIndex r

theorem minus_bottom_scalar (r : unitInterval) :
    minusParameter (r, 0) = bottomParameter.{u} (r, 1) :=
  BassMScalarPasting.minus_bottom_scalar oldIndex r

theorem h1_plus_scalar (s : unitInterval) : h1Parameter.{u} (s, 0) = plusParameter (1, s) :=
  BassMScalarPasting.h1_plus_scalar oldIndex s

theorem h1_minus_scalar (s : unitInterval) : h1Parameter.{u} (s, 1) = minusParameter (1, s) :=
  BassMScalarPasting.h1_minus_scalar oldIndex s

theorem h1_bottom_scalar (t : unitInterval) : h1Parameter.{u} (0, t) = bottomParameter.{u} (1, t) :=
  BassMScalarPasting.h1_bottom_scalar oldIndex t

end Quillen.PerfectComplexes.BassMWhole
