/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TwistMinusUnit
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalQuotient
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of the canonical negative twist and its original maps -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineTwistMinus

open Quillen

/-- The functorial map is the unique map retaining the original inclusion square. -/
theorem original_map_unique (R : CommRingCat.{u}) {M N : (twoChartLine R).Modules}
    (f : M ⟶ N) : ∃! g : twistMinus R M ⟶ twistMinus R N,
      g ≫ twistMinusInclusion R N = twistMinusInclusion R M ≫ prod.map f f := by
  let := twistMinusInclusion_mono R N
  refine ⟨twistMinusMap R f, twistMinusMap_inclusion R f, ?_⟩
  intro g hg
  exact (cancel_mono (twistMinusInclusion R N)).mp
    (hg.trans (twistMinusMap_inclusion R f).symm)

/-- Composition retains the literal two successive maps of original module squares. -/
theorem original_composite_inclusion (R : CommRingCat.{u})
    {M N P : (twoChartLine R).Modules} (f : M ⟶ N) (g : N ⟶ P) :
    twistMinusMap R (f ≫ g) ≫ twistMinusInclusion R P =
      twistMinusInclusion R M ≫ prod.map f f ≫ prod.map g g := by
  rw [twistMinusMap_inclusion, prod.map_map]

/-- The positive projection after the restricted inclusion is the original chart isomorphism. -/
theorem original_positive_projection (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (twistMinusInclusion R M) ≫
      (Scheme.Modules.restrictFunctor (plusChart R)).map prod.fst =
        (twistMinusPlusIso R M).hom := by
  rw [twistMinusInclusion_plus, Category.assoc, moduleFirstColumn_fst, Category.comp_id]

/-- The twist of the original Euler sequence remains short exact with its literal mapped arrows. -/
theorem original_twisted_sequence (R : CommRingCat.{u}) :
    ((tautologicalSequence R).map (twistMinusFunctor R)).ShortExact :=
  twistMinusFunctor_shortExact R _ (tautologicalSequence_shortExact R)

/-- The unit specialization retains the original tautological subobject and its mono. -/
theorem original_unit_inclusion (R : CommRingCat.{u}) :
    (twistMinusUnitIso R).inv ≫ twistMinusInclusion R _ = tautologicalLineInclusion R :=
  tautologicalToTwistMinusUnit_inclusion R

/-- Overlap coefficients have the actual scalar transition and original overlap comparison. -/
theorem original_scalar_transition (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) :
    (Scheme.Modules.restrictFunctor (pullback.fst (plusChart R) (minusChart R))).map
        (twistMinusPlusIso R M).hom ≫
      (moduleMulIso _ (overlapCoordinateUnit R)).hom ≫
      (AlgebraicGeometry.Scheme.Modules.Coherent.overlapRestrictIso (plusChart R) (minusChart
        R)).hom.app M =
    (AlgebraicGeometry.Scheme.Modules.Coherent.overlapRestrictIso (plusChart R) (minusChart
      R)).hom.app
        (twistMinus R M) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd (plusChart R) (minusChart R))).map
        (twistMinusMinusIso R M).hom :=
  twistMinus_transition R M

/-- The original functor preserves vector bundles over a nonreduced base. -/
theorem nonreduced_vector_bundle (M : (twoChartLine (.of (ZMod 4))).Modules)
    [IsFiniteLocallyFree _ M] :
    IsFiniteLocallyFree _ ((twistMinusFunctor (.of (ZMod 4))).obj M) :=
  twistMinus_finiteLocallyFree _ M

/-- Empty geometry over the zero ring is included without nontriviality assumptions. -/
theorem zero_ring_vector_bundle (M : (twoChartLine (.of (ZMod 1))).Modules)
    [IsFiniteLocallyFree _ M] :
    IsFiniteLocallyFree _ ((twistMinusFunctor (.of (ZMod 1))).obj M) :=
  twistMinus_finiteLocallyFree _ M

end QuillenTest.ProjectiveLineTwistMinus
