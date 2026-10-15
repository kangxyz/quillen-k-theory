/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassFirstStableGroup
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStepMap

/-!
# Original coefficient naturality of the first Bass group comparison

The original Laurent cone-inclusion equation and signed loop-shift naturality retain the actual
raw coefficient step map. Surjectivity of the original Laurent quotient then identifies its
signed degree-minus-one action with the already-defined PerfectK-based negative-group map.
-/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- Original Laurent classes commute with the unchanged coefficient map of the actual Bass step.
-/
@[reassoc]
theorem boundedFlatBassFirstLaurentMap_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatBassFirstLaurentMap R ≫
      (stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap f) =
    Quillen.Bass.affineKZeroFunctor.map (Quillen.Bass.laurentFunctor.map f) ≫
      boundedFlatBassFirstLaurentMap S := by
  have hd := eqToHom_naturality
    (fun d : ℤ => (stableHomotopyFunctor d).map (boundedFlatBassConeMap f))
    (show (0 : ℤ) = -1 + 1 by decide)
  have hc : (stableHomotopyFunctor 0).map
      (mappingConeInclusion (boundedFlatBassSquareComparison R)) ≫
      (stableHomotopyFunctor 0).map (boundedFlatBassConeMap f) =
      (stableHomotopyFunctor 0).map
        (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f))) ≫
      (stableHomotopyFunctor 0).map
        (mappingConeInclusion (boundedFlatBassSquareComparison S)) := by
    rw [← Functor.map_comp, boundedFlatBassConeMap_inclusion, Functor.map_comp]
  have hk := boundedFlatAffineStableKZeroIso_naturality (laurentMap f)
  simp only [boundedFlatBassFirstLaurentMap, boundedFlatAffineBassStepMap, Category.assoc]
  rw [parameterStableHomotopyIso_inv_naturality, ← reassoc_of% hd, reassoc_of% hc,
    reassoc_of% hk]
  rfl

/-- The first-step isomorphism retains the original ring-map action on both sides. -/
@[reassoc]
theorem boundedFlatBassFirstStableGroupIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatBassFirstStableGroupIso R).hom ≫
      (stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap f) =
    Quillen.Bass.negativeKMap f 1 ≫ (boundedFlatBassFirstStableGroupIso S).hom := by
  let : Epi (Quillen.Bass.negativeKπ R 0) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (Quillen.Bass.negativeKπ_surjective R 0)
  apply (cancel_epi (Quillen.Bass.negativeKπ R 0)).mp
  rw [← Category.assoc, boundedFlatBassFirstStableGroupIso_π,
    boundedFlatBassFirstLaurentMap_naturality]
  rw [← Category.assoc, ← Quillen.Bass.negativeKπ_naturality, Category.assoc,
    boundedFlatBassFirstStableGroupIso_π]
  rfl

/-- The original raw first-step maps form a functor on their signed degree-minus-one groups. -/
def boundedFlatBassFirstStableFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1} where
  obj R := stableHomotopyGroup (boundedFlatAffineBassStep R) (-1)
  map f := (stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap f)
  map_id R := by
    apply (cancel_epi (boundedFlatBassFirstStableGroupIso R).hom).mp
    simpa only [Category.comp_id, Quillen.Bass.negativeKMap_id, Category.id_comp] using
      boundedFlatBassFirstStableGroupIso_naturality (𝟙 R)
  map_comp {R S T} f g := by
    apply (cancel_epi (boundedFlatBassFirstStableGroupIso R).hom).mp
    rw [boundedFlatBassFirstStableGroupIso_naturality, Quillen.Bass.negativeKMap_comp,
      Category.assoc, ← boundedFlatBassFirstStableGroupIso_naturality g,
      ← Category.assoc, ← boundedFlatBassFirstStableGroupIso_naturality f, Category.assoc]

/-- The original PerfectK-based first Bass cokernel and actual first-step stable groups are
naturally isomorphic on the unchanged ring-map actions. -/
def boundedFlatBassFirstStableIso :
    Quillen.Bass.negativeKFunctor 1 ≅ boundedFlatBassFirstStableFunctor.{u} :=
  NatIso.ofComponents boundedFlatBassFirstStableGroupIso
    (fun f => (boundedFlatBassFirstStableGroupIso_naturality f).symm)

end Quillen.PerfectComplexes
