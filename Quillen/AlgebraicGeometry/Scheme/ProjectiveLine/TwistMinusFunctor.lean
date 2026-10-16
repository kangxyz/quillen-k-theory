/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TwistMinus
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.SubobjectObstructionNaturality
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap

/-!
# Functoriality and exactness of the negative twist

Original kernel maps define an additive endofunctor. Natural chart trivializations retain the
Laurent transition T. Chartwise exactness proves preservation of short exact sequences and finite
locally free sheaves over every base ring.
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
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) {M N P : (twoChartLine R).Modules}

/-- The original positive-chart cokernel map induced by a module morphism. -/
def twistMinusPlusCokernelMap (f : M ⟶ N) :=
  cokernel.map (moduleFirstColumn (plusChart R) M (polynomialCoordinate R))
    (moduleFirstColumn (plusChart R) N (polynomialCoordinate R))
    ((Scheme.Modules.restrictFunctor (plusChart R)).map f)
    ((Scheme.Modules.restrictFunctor (plusChart R)).map (prod.map f f))
    (moduleFirstColumn_naturality (plusChart R) f (polynomialCoordinate R)).symm

/-- The original negative-chart cokernel map induced by a module morphism. -/
def twistMinusMinusCokernelMap (f : M ⟶ N) :=
  cokernel.map (moduleSecondColumn (minusChart R) M (polynomialCoordinate R))
    (moduleSecondColumn (minusChart R) N (polynomialCoordinate R))
    ((Scheme.Modules.restrictFunctor (minusChart R)).map f)
    ((Scheme.Modules.restrictFunctor (minusChart R)).map (prod.map f f))
    (moduleSecondColumn_naturality (minusChart R) f (polynomialCoordinate R)).symm

/-- The paired direct images of the original chart cokernel maps. -/
def twistMinusObstructionMap (f : M ⟶ N) :=
  prod.map ((Scheme.Modules.pushforward (plusChart R)).map (twistMinusPlusCokernelMap R f))
    ((Scheme.Modules.pushforward (minusChart R)).map (twistMinusMinusCokernelMap R f))

lemma twistMinusObstruction_naturality (f : M ⟶ N) :
    prod.map f f ≫ twistMinusObstruction R N =
      twistMinusObstruction R M ≫ twistMinusObstructionMap R f := by
  apply prod.hom_ext
  · simp only [twistMinusObstruction, twistMinusObstructionMap,
      Category.assoc, prod.lift_fst, prod.map_fst]
    rw [← Category.assoc, prod.lift_fst]
    exact subobjectObstruction_naturality (plusChart R) _ _
      ((Scheme.Modules.restrictFunctor (plusChart R)).map f) (prod.map f f)
      (moduleFirstColumn_naturality (plusChart R) f (polynomialCoordinate R)).symm
  · simp only [twistMinusObstruction, twistMinusObstructionMap,
      Category.assoc, prod.lift_snd, prod.map_snd]
    rw [← Category.assoc, prod.lift_snd]
    exact subobjectObstruction_naturality (minusChart R) _ _
      ((Scheme.Modules.restrictFunctor (minusChart R)).map f) (prod.map f f)
      (moduleSecondColumn_naturality (minusChart R) f (polynomialCoordinate R)).symm

/-- The canonical map of kernels induced by the original square of module morphisms. -/
def twistMinusMap (f : M ⟶ N) : twistMinus R M ⟶ twistMinus R N :=
  kernel.map (twistMinusObstruction R M) (twistMinusObstruction R N)
    (prod.map f f) (twistMinusObstructionMap R f) (twistMinusObstruction_naturality R f).symm

lemma twistMinusMap_inclusion (f : M ⟶ N) :
    twistMinusMap R f ≫ twistMinusInclusion R N = twistMinusInclusion R M ≫ prod.map f f :=
  kernel.lift_ι _ _ _

/-- The canonical negative-twist endofunctor on all module sheaves. -/
def twistMinusFunctor : (twoChartLine R).Modules ⥤ (twoChartLine R).Modules where
  obj := twistMinus R
  map := twistMinusMap R
  map_id M := by
    let := twistMinusInclusion_mono R M
    apply (cancel_mono (twistMinusInclusion R M)).mp
    rw [twistMinusMap_inclusion, prod.map_id_id, Category.comp_id, Category.id_comp]
  map_comp {X Y Z} f g := by
    let := twistMinusInclusion_mono R Z
    apply (cancel_mono (twistMinusInclusion R Z)).mp
    rw [twistMinusMap_inclusion, Category.assoc, twistMinusMap_inclusion,
      ← Category.assoc, twistMinusMap_inclusion, Category.assoc, prod.map_map]

lemma twistMinusMap_plus (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (twistMinusMap R f) ≫
        (twistMinusPlusIso R N).hom =
      (twistMinusPlusIso R M).hom ≫ (Scheme.Modules.restrictFunctor (plusChart R)).map f := by
  let := moduleFirstColumn_mono (plusChart R) N (polynomialCoordinate R)
  apply (cancel_mono (moduleFirstColumn (plusChart R) N (polynomialCoordinate R))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (plusChart R)).map
    (twistMinusMap_inclusion R f)
  rw [Functor.map_comp, Functor.map_comp, twistMinusInclusion_plus, twistMinusInclusion_plus] at h
  rw [Category.assoc, ← moduleFirstColumn_naturality] at h
  simpa only [Category.assoc] using h

lemma twistMinusMap_minus (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (twistMinusMap R f) ≫
        (twistMinusMinusIso R N).hom =
      (twistMinusMinusIso R M).hom ≫ (Scheme.Modules.restrictFunctor (minusChart R)).map f := by
  let := moduleSecondColumn_mono (minusChart R) N (polynomialCoordinate R)
  apply (cancel_mono (moduleSecondColumn (minusChart R) N (polynomialCoordinate R))).mp
  have h := congrArg (Scheme.Modules.restrictFunctor (minusChart R)).map
    (twistMinusMap_inclusion R f)
  rw [Functor.map_comp, Functor.map_comp, twistMinusInclusion_minus, twistMinusInclusion_minus] at h
  rw [Category.assoc, ← moduleSecondColumn_naturality] at h
  simpa only [Category.assoc] using h

instance twistMinusFunctor_additive : (twistMinusFunctor R).Additive where
  map_add {M N} f g := by
    let := twistMinusInclusion_mono R N
    apply (cancel_mono (twistMinusInclusion R N)).mp
    change twistMinusMap R (f + g) ≫ _ = (twistMinusMap R f + twistMinusMap R g) ≫ _
    rw [Preadditive.add_comp, twistMinusMap_inclusion, twistMinusMap_inclusion,
      twistMinusMap_inclusion, ← Preadditive.comp_add]
    congr 1
    apply prod.hom_ext <;> simp [Preadditive.add_comp]

/-- The original positive-chart trivializations form a natural isomorphism. -/
def twistMinusPlusNatIso :
    twistMinusFunctor R ⋙ Scheme.Modules.restrictFunctor (plusChart R) ≅
      Scheme.Modules.restrictFunctor (plusChart R) :=
  NatIso.ofComponents (twistMinusPlusIso R) (fun f => twistMinusMap_plus R f)

/-- The original negative-chart trivializations form a natural isomorphism. -/
def twistMinusMinusNatIso :
    twistMinusFunctor R ⋙ Scheme.Modules.restrictFunctor (minusChart R) ≅
      Scheme.Modules.restrictFunctor (minusChart R) :=
  NatIso.ofComponents (twistMinusMinusIso R) (fun f => twistMinusMap_minus R f)

lemma twistMinus_transition (M : (twoChartLine R).Modules) :
    (Scheme.Modules.restrictFunctor (pullback.fst (plusChart R) (minusChart R))).map
        (twistMinusPlusIso R M).hom ≫
      (moduleColumnTransition (plusChart R) (minusChart R) M (overlapCoordinateUnit R)).hom =
    (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso (plusChart R) (minusChart R)).hom.app
      (twistMinus R M) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd (plusChart R) (minusChart R))).map
        (twistMinusMinusIso R M).hom := by
  let := moduleSecondColumn_mono (minusChart R) M (polynomialCoordinate R)
  have hn := (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso (plusChart R) (minusChart
    R)).hom.naturality
    (twistMinusInclusion R M)
  dsimp only [Functor.comp_map] at hn
  rw [twistMinusInclusion_plus, twistMinusInclusion_minus,
    Functor.map_comp, Functor.map_comp, Category.assoc] at hn
  rw [moduleColumns_compatible (plusChart R) (minusChart R) M
    (polynomialCoordinate R) (polynomialCoordinate R) (overlapCoordinateUnit R) rfl rfl] at hn
  exact (cancel_mono ((Scheme.Modules.restrictFunctor
    (pullback.snd (plusChart R) (minusChart R))).map
      (moduleSecondColumn (minusChart R) M (polynomialCoordinate R)))).mp (by
        simpa only [Category.assoc] using hn)

end AlgebraicGeometry.Scheme.ProjectiveLine

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

lemma twistMinusFunctor_shortExact (S : ShortComplex (twoChartLine R).Modules)
    (hS : S.ShortExact) : (S.map (twistMinusFunctor R)).ShortExact := by
  apply shortExact_of_restrict_openCover (fun _ : Bool => Spec (.of (Polynomial R)))
    (polynomialChart R) (polynomialChart_cover R)
  intro b
  cases b
  · exact ShortComplex.shortExact_of_iso (S.mapNatIso (twistMinusMinusNatIso R)).symm
      (hS.map_of_exact (Scheme.Modules.restrictFunctor (minusChart R)))
  · exact ShortComplex.shortExact_of_iso (S.mapNatIso (twistMinusPlusNatIso R)).symm
      (hS.map_of_exact (Scheme.Modules.restrictFunctor (plusChart R)))

instance twistMinus_finiteLocallyFree (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] :
    IsFiniteLocallyFree (twoChartLine R) (twistMinus R M) := by
  apply finiteLocallyFree_of_affineCharts (twistMinus R M)
    (fun _ : Bool => CommRingCat.of (Polynomial R)) (polynomialChart R)
  · intro x
    obtain ⟨b, y, hy⟩ := polynomialChart_cover R x
    exact ⟨b, y, hy⟩
  · intro b
    cases b
    · exact finiteLocallyFree_of_iso (twistMinusMinusIso R M).symm
    · exact finiteLocallyFree_of_iso (twistMinusPlusIso R M).symm
end AlgebraicGeometry.Scheme.ProjectiveLine
