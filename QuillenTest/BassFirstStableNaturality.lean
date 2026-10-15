/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassFirstStableNaturality

/-!
Consumers retain original Laurent representatives, arbitrary signed first-step classes and the
literal coefficient maps of the new group functor. Composition here is an equality of signed
stable group maps.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace QuillenTest.BassFirstStableNaturality

open Quillen

/-- The natural first-step functor keeps the literal original raw coefficient map. -/
theorem original_coefficient {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatBassFirstStableFunctor.map f =
      (stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap f) := rfl

/-- Every original Laurent representative has the same image along the actual coefficient map. -/
theorem original_laurent_class {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : Quillen.Bass.affineKZeroFunctor.obj (Quillen.Bass.laurentFunctor.obj R)) :
    (boundedFlatBassFirstLaurentMap R ≫
      (stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap f)) x =
    (Quillen.Bass.affineKZeroFunctor.map (Quillen.Bass.laurentFunctor.map f) ≫
      boundedFlatBassFirstLaurentMap S) x :=
  ConcreteCategory.congr_hom (boundedFlatBassFirstLaurentMap_naturality f) x

/-- The actual inverse comparison is natural on arbitrary genuine signed first-step classes. -/
theorem original_inverse {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : stableHomotopyGroup (boundedFlatAffineBassStep R) (-1)) :
    Quillen.Bass.negativeKMap f 1 ((boundedFlatBassFirstStableGroupIso R).inv x) =
      (boundedFlatBassFirstStableGroupIso S).inv
        ((stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap f) x) := by
  apply (ConcreteCategory.bijective_of_isIso (boundedFlatBassFirstStableGroupIso S).hom).injective
  have h := ConcreteCategory.congr_hom (boundedFlatBassFirstStableGroupIso_naturality f)
    ((boundedFlatBassFirstStableGroupIso R).inv x)
  have hR := ConcreteCategory.congr_hom (boundedFlatBassFirstStableGroupIso R).inv_hom_id x
  have hS := ConcreteCategory.congr_hom (boundedFlatBassFirstStableGroupIso S).inv_hom_id
    ((stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap f) x)
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h hR hS
  rw [hR] at h
  exact h.symm.trans hS.symm

/-- The two actual raw coefficient maps compose on their unchanged signed stable groups. -/
theorem original_composition {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap (f ≫ g)) =
      (stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap f) ≫
        (stableHomotopyFunctor (-1)).map (boundedFlatAffineBassStepMap g) :=
  boundedFlatBassFirstStableFunctor.map_comp f g

end QuillenTest.BassFirstStableNaturality
