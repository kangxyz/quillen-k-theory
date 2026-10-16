/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import QuillenTest.CoefficientBassUnitSupportOrder
public import QuillenTest.DiagramTransportGroupNaturality
public import QuillenTest.GenLoopSelfTrackClass
public import QuillenTest.GlobalUnitKOneInversion
public import QuillenTest.GlobalUnitKOneRestriction
public import QuillenTest.LargeCofiberRelations
public import QuillenTest.LaurentNegativeCoordinate
public import QuillenTest.MappingConeKZeroRelation
public import QuillenTest.NativeRankOneClass
public import QuillenTest.NativeTautologicalConeClass
public import QuillenTest.RankOneFlatPullback
public import QuillenTest.ScalarSupportedBoundary
public import QuillenTest.TautologicalCoordinateCompatibility
public import QuillenTest.Topology.Prespectrum.TelescopeStableInclusion

/-! # Joint import regression for the checked TT foundation leaves

This consumer checks coexistence of the independently verified foundation APIs
and the original coordinate owner. It does not assert classical localization,
an all-degree Laurent splitting, a complete unit cube, or raw stage stability.
-/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine

universe u

namespace QuillenTest.TTFoundationIntegration

/-- Joint imports retain the original coordinate rather than shadowing its name. -/
theorem original_coordinate_retained (R : CommRingCat.{u}) :
    tautologicalInclusionFirstProjection R = tautologicalFirstCoordinate R :=
  TautologicalCoordinateCompatibility.first_projection_eq_original_first_coordinate R

end QuillenTest.TTFoundationIntegration
