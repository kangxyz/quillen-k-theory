/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import QuillenTest.CoefficientBassUnitSupportOrder
public import QuillenTest.CoefficientPolynomialSpanUnitSimplex
public import QuillenTest.CommonReferenceNerve
public import QuillenTest.DiagramTransportGroupNaturality
public import QuillenTest.FullSubcategoryLiftPushout
public import QuillenTest.GenLoopNormalizedSelfTrack
public import QuillenTest.GenLoopSelfTrackClass
public import QuillenTest.GenLoopSelfTrackSpatial
public import QuillenTest.GenLoopSelfTrackSpatialProduct
public import QuillenTest.GlobalUnitKOneInversion
public import QuillenTest.GlobalUnitKOneRestriction
public import QuillenTest.LargeCofiberRelations
public import QuillenTest.LaurentNegativeCoordinate
public import QuillenTest.LaurentOverlapScalarBoundary
public import QuillenTest.LaurentRankOnePhiBoundary
public import QuillenTest.LineCoordinateChart
public import QuillenTest.LineCoordinateTensor
public import QuillenTest.LineCoordinateUnit
public import QuillenTest.LoopNormalizedSelfTrackNaturality
public import QuillenTest.MappingConeKZeroRelation
public import QuillenTest.NativeAffineBase
public import QuillenTest.NativeRankOneClass
public import QuillenTest.NativeTautologicalConeClass
public import QuillenTest.NativeTautologicalCoordinateCone
public import QuillenTest.OriginalUnitSquareSimplex
public import QuillenTest.OriginalUnitSquareSupport
public import QuillenTest.RankOneFlatPullback
public import QuillenTest.RestrictionIsoEquivalence
public import QuillenTest.ScalarSupportedBoundary
public import QuillenTest.SelfTrackHomotopyAdditivity
public import QuillenTest.SelfTrackHomotopyClass
public import QuillenTest.SimplexLiftSquareOperations
public import QuillenTest.TautologicalCoefficientCoordinate
public import QuillenTest.TautologicalCoordinateCompatibility
public import QuillenTest.TautologicalCoordinateCone
public import QuillenTest.TautologicalFirstCoordinate
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

namespace QuillenTest.TTCheckpointIntegration

/-- Joint imports retain the original coordinate rather than shadowing its name. -/
theorem original_coordinate_retained (R : CommRingCat.{u}) :
    tautologicalInclusionFirstProjection R = tautologicalFirstCoordinate R :=
  TautologicalCoordinateCompatibility.first_projection_eq_original_first_coordinate R

end QuillenTest.TTCheckpointIntegration
