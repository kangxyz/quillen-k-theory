/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.CategoryTheory.TheoremB.MappingCylinderSourceCollar
import Quillen.CategoryTheory.TheoremB.FiberwiseDeformationBaseChange

/-!
# Source-collar geometry regression consumers

The source is the original cylinder endpoint, its actual collar is a product,
and the whole deformation stays over every original induced base projection.
The last test changes base through an arbitrary space without assuming that a
pullback preserves the cylinder's pushout.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Quillen Quillen.TheoremB.MappingCylinderSourceCollar
open scoped Topology unitInterval
universe u
variable {A B M T : TopCat.{u}} {f : A ⟶ B}
  {l : A ⊗ TopCat.I ⟶ M} {c : B ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
  (cut : unitInterval) (hcut : 0 < cut)

example : IsOpen (collarSet sq cut) := collar_isOpen sq cut

example : c ⁻¹' collarSet sq cut = ∅ := preimage_target sq cut

example (a : A) : (source sq cut hcut a).val = (TopCat.ι₀ ≫ l) a := rfl

example : source sq cut hcut ≫ inclusion sq cut = TopCat.ι₀ ≫ l := rfl

example (z : A × Interval cut) :
    (collarHomeomorph sq cut z).val = l (z.1,ULift.up z.2.val) := rfl

example (a : A) :
    (collarHomeomorph sq cut).symm (source sq cut hcut a) = (a,⟨0,hcut⟩) :=
  collarHomeomorph_symm_source sq cut hcut a

example : (strongDeformationRetract sq cut hcut).toHomotopyEquiv.toFun =
    (source sq cut hcut).hom := rfl

example :
    (source sq cut hcut ▷ TopCat.I) ≫ (strongDeformationRetract sq cut hcut).H =
      fst A TopCat.I ≫ source sq cut hcut :=
  (strongDeformationRetract sq cut hcut).fixed

example (base : B ⟶ T) :
    (strongDeformationRetract sq cut hcut).H ≫ inclusion sq cut ≫
        TheoremA.mappingCylinderProjection sq ≫ base =
      fst (Collar sq cut) TopCat.I ≫ inclusion sq cut ≫
        TheoremA.mappingCylinderProjection sq ≫ base := deformation_over sq cut hcut base

example (base : B ⟶ T) (x : Collar sq cut) (t : TopCat.I) :
    (TheoremA.mappingCylinderProjection sq ≫ base)
        ((strongDeformationRetract sq cut hcut).H (x,t)).val =
      (TheoremA.mappingCylinderProjection sq ≫ base) x.val :=
  ConcreteCategory.congr_hom (deformation_over sq cut hcut base) (x,t)

example (base : B ⟶ T) {D : Type u} [TopologicalSpace D] (g : C(D,T)) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (FiberwiseMappingPath.BaseChangedSource
        (inclusion sq cut ≫ TheoremA.mappingCylinderProjection sq ≫ base).hom
        (source sq cut hcut).hom g)
      (FiberwiseMappingPath.BaseChangedTarget
        (inclusion sq cut ≫ TheoremA.mappingCylinderProjection sq ≫ base).hom g)) :=
  ⟨(strongDeformationRetract sq cut hcut).baseChangeHomotopyEquiv
    (inclusion sq cut ≫ TheoremA.mappingCylinderProjection sq ≫ base)
    (deformation_over sq cut hcut base) g⟩
