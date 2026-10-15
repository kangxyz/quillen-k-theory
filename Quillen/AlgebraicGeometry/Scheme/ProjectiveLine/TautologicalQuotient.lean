/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RankOneQuotient
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The actual tautological quotient line

On the genuine two-chart projective line over an arbitrary commutative ring, the cokernel of the
tautological inclusion has chart rows `(-t, 1)` and `(-1, s)`. Their actual cokernel universal
properties supply chart trivializations with inverse Laurent transition, and hence finite local
freeness. The original inclusion and projection form the displayed short exact sequence.
-/
@[expose] public section

open ModuleCat
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- The actual cokernel of the tautological subline in the original unit square. -/
def tautologicalQuotientLine : (twoChartLine R).Modules :=
  cokernel (tautologicalLineInclusion R)

/-- The original cokernel projection onto the tautological quotient line. -/
def tautologicalQuotientMap :
    ((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
      SheafOfModules.unit (twoChartLine R).ringCatSheaf) ⟶ tautologicalQuotientLine R :=
  cokernel.π (tautologicalLineInclusion R)

/-- The original tautological inclusion and its cokernel form a short complex. -/
def tautologicalSequence : ShortComplex (twoChartLine R).Modules :=
  ShortComplex.mk (tautologicalLineInclusion R) (tautologicalQuotientMap R)
    (cokernel.condition _)

theorem tautologicalSequence_shortExact : (tautologicalSequence R).ShortExact :=
  { exact := ShortComplex.exact_cokernel (tautologicalLineInclusion R)
    mono_f := by change Mono (tautologicalLineInclusion R); infer_instance
    epi_g := by change Epi (cokernel.π (tautologicalLineInclusion R)); infer_instance }

/-- The positive chart cokernel trivialization induced by the literal row `(-t, 1)`. -/
def tautologicalQuotientPlusIso : (tautologicalQuotientLine R).restrict (plusChart R) ≅
    SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  CokernelCofork.mapIsoOfIsColimit
    (isColimitOfHasCokernelOfPreservesColimit (Scheme.Modules.restrictFunctor (plusChart R))
      (tautologicalLineInclusion R))
    (graphRowIsCokernel (unitMul _ (polynomialCoordinate R)))
    (Arrow.isoMk (tautologicalLinePlusIso R) (unitSquareRestrictionIso (plusChart R)) (by
      change (tautologicalLinePlusIso R).hom ≫ graphColumn (unitMul _ (polynomialCoordinate R)) =
        (Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalLineInclusion R) ≫
          (unitSquareRestrictionIso (plusChart R)).hom
      rw [tautologicalLineInclusion_plus]
      simpa only [Category.assoc] using
        (congrArg (fun k => (tautologicalLinePlusIso R).hom ≫ k)
          (firstColumn_unitSquareRestrictionIso (plusChart R) (polynomialCoordinate R))).symm))

/-- The negative chart cokernel trivialization induced by the literal row `(-1, s)`. -/
def tautologicalQuotientMinusIso : (tautologicalQuotientLine R).restrict (minusChart R) ≅
    SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  CokernelCofork.mapIsoOfIsColimit
    (isColimitOfHasCokernelOfPreservesColimit (Scheme.Modules.restrictFunctor (minusChart R))
      (tautologicalLineInclusion R))
    (cographRowIsCokernel (unitMul _ (polynomialCoordinate R)))
    (Arrow.isoMk (tautologicalLineMinusIso R) (unitSquareRestrictionIso (minusChart R)) (by
      change (tautologicalLineMinusIso R).hom ≫ cographColumn (unitMul _ (polynomialCoordinate R)) =
        (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalLineInclusion R) ≫
          (unitSquareRestrictionIso (minusChart R)).hom
      rw [tautologicalLineInclusion_minus]
      simpa only [Category.assoc] using
        (congrArg (fun k => (tautologicalLineMinusIso R).hom ≫ k)
          (secondColumn_unitSquareRestrictionIso (minusChart R) (polynomialCoordinate R))).symm))

/-- The positive trivialization sends the actual quotient projection to its signed row. -/
lemma tautologicalQuotientMap_plus :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalQuotientMap R) ≫
      (tautologicalQuotientPlusIso R).hom = firstRow (plusChart R) (polynomialCoordinate R) := by
  simp only [tautologicalQuotientPlusIso, tautologicalQuotientMap, firstRow,
    CokernelCofork.mapIsoOfIsColimit]
  exact CokernelCofork.π_mapOfIsColimit
    (isColimitOfHasCokernelOfPreservesColimit (Scheme.Modules.restrictFunctor (plusChart R))
      (tautologicalLineInclusion R)) _ _

/-- The negative trivialization sends the actual quotient projection to its signed row. -/
lemma tautologicalQuotientMap_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalQuotientMap R) ≫
      (tautologicalQuotientMinusIso R).hom = secondRow (minusChart R) (polynomialCoordinate R) := by
  simp only [tautologicalQuotientMinusIso, tautologicalQuotientMap, secondRow,
    CokernelCofork.mapIsoOfIsColimit]
  exact CokernelCofork.π_mapOfIsColimit
    (isColimitOfHasCokernelOfPreservesColimit (Scheme.Modules.restrictFunctor (minusChart R))
      (tautologicalLineInclusion R)) _ _


/-- The original tautological quotient map is an epimorphism. -/
instance tautologicalQuotientMap_epi : Epi (tautologicalQuotientMap R) := by
  change Epi (cokernel.π (tautologicalLineInclusion R))
  infer_instance

/-- The actual quotient chart trivializations have inverse Laurent-coordinate transition. -/
lemma tautologicalQuotientLine_transition :
    (Scheme.Modules.restrictFunctor (pullback.fst (plusChart R) (minusChart R))).map
        (tautologicalQuotientPlusIso R).hom ≫
      (columnTransition (plusChart R) (minusChart R) (overlapCoordinateUnit R)⁻¹).hom =
    (AlgebraicGeometry.Scheme.Modules.Coherent.overlapRestrictIso (plusChart R) (minusChart
      R)).hom.app
        (tautologicalQuotientLine R) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd (plusChart R) (minusChart R))).map
        (tautologicalQuotientMinusIso R).hom := by
  let := tautologicalQuotientMap_epi R
  let := (Scheme.Modules.restrictFunctor (plusChart R)).map_epi (tautologicalQuotientMap R)
  let := (Scheme.Modules.restrictFunctor
    (pullback.fst (plusChart R) (minusChart R))).map_epi
      ((Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalQuotientMap R))
  apply (cancel_epi ((Scheme.Modules.restrictFunctor
    (pullback.fst (plusChart R) (minusChart R))).map
      ((Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalQuotientMap R)))).mp
  have hn := (AlgebraicGeometry.Scheme.Modules.Coherent.overlapRestrictIso (plusChart R) (minusChart
    R)).hom.naturality
    (tautologicalQuotientMap R)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Functor.map_comp, tautologicalQuotientMap_plus]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, tautologicalQuotientMap_minus]
  exact rows_compatible (plusChart R) (minusChart R)
    (polynomialCoordinate R) (polynomialCoordinate R) (overlapCoordinateUnit R) rfl rfl

/-- The actual tautological quotient is finite locally free over every base ring. -/
instance tautologicalQuotientLine_finiteLocallyFree :
    IsFiniteLocallyFree (twoChartLine R) (tautologicalQuotientLine R) := by
  let e : SheafOfModules.free (R := (Spec (.of (Polynomial R))).ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf := coproductUniqueIso _
  have : IsFiniteLocallyFree (Spec (.of (Polynomial R)))
      (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) := finiteLocallyFree_of_iso e
  let charts : Bool → (Spec (.of (Polynomial R)) ⟶ twoChartLine R) :=
    fun b => if b then plusChart R else minusChart R
  have hi : ∀ b, IsOpenImmersion (charts b) := by
    intro b
    cases b <;> dsimp [charts] <;> infer_instance
  let := hi
  apply finiteLocallyFree_of_affineCharts (tautologicalQuotientLine R)
    (fun _ : Bool => CommRingCat.of (Polynomial R)) charts
  · intro x
    have hx : x ∈ (plusChart R).opensRange ⊔ (minusChart R).opensRange := by
      rw [chart_ranges_cover]; trivial
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · intro b
    cases b
    · exact finiteLocallyFree_of_iso (tautologicalQuotientMinusIso R).symm
    · exact finiteLocallyFree_of_iso (tautologicalQuotientPlusIso R).symm

end AlgebraicGeometry.Scheme.ProjectiveLine
