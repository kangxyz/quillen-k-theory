/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RankOneGluing
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Locality

/-!
# The tautological line on the original two-chart projective line

The original polynomial columns `(1, t)` and `(s, 1)` glue as module subsheaves
of the actual global structure-module square. Their transition on the genuine
Laurent intersection is multiplication by `T`, with inverse `T⁻¹`. The resulting
module sheaf has explicit chart trivializations, a global monomorphism, and
finite local freeness over an arbitrary commutative base ring.

This constructs the tautological line on `twoChartLine`; no identification with
Proj or computation of its derived global sections is asserted here.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- The original polynomial coordinate section under the canonical affine section isomorphism. -/
def polynomialCoordinate : Γ(Spec (.of (Polynomial R)), ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom Polynomial.X

lemma laurentPlus_coordinate :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
      ((laurentPlus R).appTop.hom (polynomialCoordinate R)) = LaurentPolynomial.T 1 := by
  have h := congrArg (fun f => CommRingCat.Hom.hom f (polynomialCoordinate R))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  simpa [laurentPlus, polynomialCoordinate] using h

lemma laurentMinus_coordinate :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
      ((laurentMinus R).appTop.hom (polynomialCoordinate R)) = LaurentPolynomial.T (-1) := by
  have h := congrArg (fun f => CommRingCat.Hom.hom f (polynomialCoordinate R))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent :
        Polynomial R →+* LaurentPolynomial R)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  simpa [laurentMinus, polynomialCoordinate] using h

lemma overlap_coordinates_mul :
    (pullback.fst (plusChart R) (minusChart R)).appTop.hom (polynomialCoordinate R) *
      (pullback.snd (plusChart R) (minusChart R)).appTop.hom (polynomialCoordinate R) = 1 := by
  apply (ConcreteCategory.bijective_of_isIso (chart_isPullback R).isoPullback.hom.appTop).1
  change (chart_isPullback R).isoPullback.hom.appTop.hom (_ * _) =
    (chart_isPullback R).isoPullback.hom.appTop.hom 1
  rw [map_mul, map_one]
  have hp := congrArg (fun f => f.appTop) (chart_isPullback R).isoPullback_hom_fst
  have hm := congrArg (fun f => f.appTop) (chart_isPullback R).isoPullback_hom_snd
  simp only [Scheme.Hom.comp_appTop] at hp hm
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hp, hm]
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom).1
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom (_ * _) =
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom 1
  rw [map_mul, map_one, laurentPlus_coordinate, laurentMinus_coordinate]
  rw [← LaurentPolynomial.T_add]
  norm_num

/-- The reciprocal original chart coordinates form a unit on their actual pullback. -/
def overlapCoordinateUnit : (Γ(pullback (plusChart R) (minusChart R), ⊤))ˣ where
  val := (pullback.fst (plusChart R) (minusChart R)).appTop.hom (polynomialCoordinate R)
  inv := (pullback.snd (plusChart R) (minusChart R)).appTop.hom (polynomialCoordinate R)
  val_inv := overlap_coordinates_mul R
  inv_val := (mul_comm _ _).trans (overlap_coordinates_mul R)

lemma overlapCoordinateUnit_coordinates :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
      ((chart_isPullback R).isoPullback.hom.appTop.hom (overlapCoordinateUnit R)) =
        LaurentPolynomial.T 1 := by
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
    (((pullback.fst (plusChart R) (minusChart R)).appTop ≫
      (chart_isPullback R).isoPullback.hom.appTop).hom (polynomialCoordinate R)) = _
  rw [← Scheme.Hom.comp_appTop, (chart_isPullback R).isoPullback_hom_fst]
  exact laurentPlus_coordinate R

lemma overlapCoordinateUnit_inv_coordinates :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
      ((chart_isPullback R).isoPullback.hom.appTop.hom (↑(overlapCoordinateUnit R)⁻¹)) =
        LaurentPolynomial.T (-1) := by
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
    (((pullback.snd (plusChart R) (minusChart R)).appTop ≫
      (chart_isPullback R).isoPullback.hom.appTop).hom (polynomialCoordinate R)) = _
  rw [← Scheme.Hom.comp_appTop, (chart_isPullback R).isoPullback_hom_snd]
  exact laurentMinus_coordinate R

/-- A subobject with the original two tautological column trivializations. -/
structure TautologicalLineData where
  /-- The glued module sheaf. -/
  obj : (twoChartLine R).Modules
  /-- Its original global inclusion into the unit square. -/
  inclusion : obj ⟶ ((SheafOfModules.unit (twoChartLine R).ringCatSheaf :
    (twoChartLine R).Modules) ⨯ SheafOfModules.unit (twoChartLine R).ringCatSheaf)
  /-- The inclusion is a monomorphism. -/
  mono : Mono inclusion
  /-- Trivialization on the positive polynomial chart. -/
  plusIso : obj.restrict (plusChart R) ≅
    SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf
  /-- Trivialization on the negative polynomial chart. -/
  minusIso : obj.restrict (minusChart R) ≅
    SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf
  /-- The inclusion restricts to the column `(1, t)`. -/
  plus_eq : (Scheme.Modules.restrictFunctor (plusChart R)).map inclusion =
    plusIso.hom ≫ firstColumn (plusChart R) (polynomialCoordinate R)
  /-- The inclusion restricts to the column `(s, 1)`. -/
  minus_eq : (Scheme.Modules.restrictFunctor (minusChart R)).map inclusion =
    minusIso.hom ≫ secondColumn (minusChart R) (polynomialCoordinate R)

/-- The subobject obtained by actual module-sheaf gluing of the two columns. -/
def tautologicalLineData : TautologicalLineData R := Classical.choice (by
  let := firstColumn_mono (plusChart R) (polynomialCoordinate R)
  let := secondColumn_mono (minusChart R) (polynomialCoordinate R)
  obtain ⟨N, i, hi, eU, eV, hU, hV⟩ :=
    AlgebraicGeometry.Scheme.Modules.Coherent.exists_glued_subobject
    (plusChart R) (minusChart R)
    (firstColumn (plusChart R) (polynomialCoordinate R))
    (secondColumn (minusChart R) (polynomialCoordinate R))
    (columnTransition (plusChart R) (minusChart R) (overlapCoordinateUnit R))
    (columns_compatible (plusChart R) (minusChart R)
      (polynomialCoordinate R) (polynomialCoordinate R) (overlapCoordinateUnit R) rfl rfl)
  exact ⟨⟨N, i, hi, eU, eV, hU, hV⟩⟩)

/-- The genuine tautological rank-one submodule sheaf of the global structure-module square. -/
def tautologicalLine : (twoChartLine R).Modules := (tautologicalLineData R).obj

/-- The actual global inclusion of the tautological sheaf into the structure-module square. -/
def tautologicalLineInclusion : tautologicalLine R ⟶
    ((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
      SheafOfModules.unit (twoChartLine R).ringCatSheaf) :=
  (tautologicalLineData R).inclusion

instance : Mono (tautologicalLineInclusion R) := (tautologicalLineData R).mono

/-- Original positive-chart trivialization of the tautological sheaf. -/
def tautologicalLinePlusIso : (tautologicalLine R).restrict (plusChart R) ≅
    SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  (tautologicalLineData R).plusIso

/-- Original negative-chart trivialization of the tautological sheaf. -/
def tautologicalLineMinusIso : (tautologicalLine R).restrict (minusChart R) ≅
    SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  (tautologicalLineData R).minusIso

lemma tautologicalLineInclusion_plus :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalLineInclusion R) =
      (tautologicalLinePlusIso R).hom ≫ firstColumn (plusChart R) (polynomialCoordinate R) :=
  (tautologicalLineData R).plus_eq

lemma tautologicalLineInclusion_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalLineInclusion R) =
      (tautologicalLineMinusIso R).hom ≫ secondColumn (minusChart R) (polynomialCoordinate R) :=
  (tautologicalLineData R).minus_eq

/-- The actual chart trivializations have precisely the original `T` transition. -/
lemma tautologicalLine_transition :
    (Scheme.Modules.restrictFunctor (pullback.fst (plusChart R) (minusChart R))).map
        (tautologicalLinePlusIso R).hom ≫
      (columnTransition (plusChart R) (minusChart R) (overlapCoordinateUnit R)).hom =
    (AlgebraicGeometry.Scheme.Modules.Coherent.overlapRestrictIso (plusChart R) (minusChart
      R)).hom.app
        (tautologicalLine R) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd (plusChart R) (minusChart R))).map
        (tautologicalLineMinusIso R).hom := by
  let := secondColumn_mono (minusChart R) (polynomialCoordinate R)
  have hn := (AlgebraicGeometry.Scheme.Modules.Coherent.overlapRestrictIso (plusChart R) (minusChart
    R)).hom.naturality
    (tautologicalLineInclusion R)
  dsimp only [Functor.comp_map] at hn
  rw [tautologicalLineInclusion_plus, tautologicalLineInclusion_minus,
    Functor.map_comp, Functor.map_comp, Category.assoc] at hn
  rw [columns_compatible (plusChart R) (minusChart R)
    (polynomialCoordinate R) (polynomialCoordinate R) (overlapCoordinateUnit R) rfl rfl] at hn
  exact (cancel_mono ((Scheme.Modules.restrictFunctor
    (pullback.snd (plusChart R) (minusChart R))).map
      (secondColumn (minusChart R) (polynomialCoordinate R)))).mp (by
        simpa only [Category.assoc] using hn)

private theorem finiteLocallyFree_unit (X : Scheme.{u}) :
    IsFiniteLocallyFree X (SheafOfModules.unit X.ringCatSheaf) := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit X.ringCatSheaf := coproductUniqueIso _
  exact finiteLocallyFree_of_iso e

/-- The original tautological sheaf is finite locally free over every base ring. -/
instance tautologicalLine_finiteLocallyFree :
    IsFiniteLocallyFree (twoChartLine R) (tautologicalLine R) := by
  have : IsFiniteLocallyFree (Spec (.of (Polynomial R)))
      (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) := finiteLocallyFree_unit _
  let charts : Bool → (Spec (.of (Polynomial R)) ⟶ twoChartLine R) :=
    fun b => if b then plusChart R else minusChart R
  have hi : ∀ b, IsOpenImmersion (charts b) := by
    intro b
    cases b <;> dsimp [charts] <;> infer_instance
  let := hi
  apply finiteLocallyFree_of_affineCharts (tautologicalLine R)
    (fun _ : Bool => CommRingCat.of (Polynomial R))
    charts
  · intro x
    have hx : x ∈ (plusChart R).opensRange ⊔ (minusChart R).opensRange := by
      rw [chart_ranges_cover]; trivial
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · intro b
    cases b
    · exact finiteLocallyFree_of_iso (tautologicalLineMinusIso R).symm
    · exact finiteLocallyFree_of_iso (tautologicalLinePlusIso R).symm

end AlgebraicGeometry.Scheme.ProjectiveLine
