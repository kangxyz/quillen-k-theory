/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeReanchorReferences

/-! The literal four displayed cylinders under input reanchoring. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E E' : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (δ : E'.functor ≅ E.functor)
local notation "J" => normalizedMap (polynomialProjection P a)

/-- Map the first original normalization cylinder without changing its interval. -/
def first : FourEdgeTree.first E J ⟶ FourEdgeTree.simplicial E' J :=
  descend (𝟙 _) (FourEdgeTree.attachment E J)
    (onReference δ ≫ FourEdgeTree.oneVertex E' J)
    (onReference (isoWhiskerRight δ (J).functor) ≫ FourEdgeTree.plusVertex E' J)
    (onReference δ ▷ Δ[1] ≫
      FourEdgeTree.edge12 E' J)
    (by simp only [SSet.ι₀_comp_assoc, FourEdgeTree.edge12_zero, Category.id_comp])
    (by
      rw [SSet.ι₁_comp_assoc, FourEdgeTree.edge12_one, ← Category.assoc,
        ← attachment, Category.assoc])

@[reassoc] theorem first_one :
    FourEdgeTree.firstOne E J ≫ first P a E E' δ =
      onReference δ ≫ FourEdgeTree.oneVertex E' J := descend_left _ _ _ _ _ _ _

@[reassoc] theorem first_plus :
    FourEdgeTree.firstPlus E J ≫ first P a E E' δ =
      onReference (isoWhiskerRight δ (J).functor) ≫ FourEdgeTree.plusVertex E' J :=
  descend_right _ _ _ _ _ _ _

@[reassoc] theorem first_cylinder :
    DoubleCylinder.simplicialCylinder (𝟙 _) (FourEdgeTree.attachment E J) ≫ first P a E E' δ =
      onReference δ ▷ Δ[1] ≫
        FourEdgeTree.edge12 E' J :=
  descend_cylinder _ _ _ _ _ _ _

/-- The positive geometric cylinder attaches to the unchanged first-branch map. -/
def second : FourEdgeTree.second E J ⟶ FourEdgeTree.simplicial E' J :=
  descend (𝟙 _) (FourEdgeTree.firstOne E J)
    (onReference δ ≫ FourEdgeTree.zeroVertex E' J) (first P a E E' δ)
    (onReference δ ▷ Δ[1] ≫
      FourEdgeTree.edge01 E' J)
    (by simp only [SSet.ι₀_comp_assoc, FourEdgeTree.edge01_zero, Category.id_comp])
    (by
      rw [SSet.ι₁_comp_assoc, FourEdgeTree.edge01_one, first_one])

@[reassoc] theorem second_zero :
    FourEdgeTree.secondZero E J ≫ second P a E E' δ =
      onReference δ ≫ FourEdgeTree.zeroVertex E' J := descend_left _ _ _ _ _ _ _

@[reassoc] theorem second_first :
    FourEdgeTree.firstInSecond E J ≫ second P a E E' δ = first P a E E' δ :=
  descend_right _ _ _ _ _ _ _

@[reassoc] theorem second_cylinder :
    DoubleCylinder.simplicialCylinder (𝟙 _) (FourEdgeTree.firstOne E J) ≫ second P a E E' δ =
      onReference δ ▷ Δ[1] ≫
        FourEdgeTree.edge01 E' J :=
  descend_cylinder _ _ _ _ _ _ _

/-- The inverse geometric cylinder retains the entire previously constructed branch. -/
def third : FourEdgeTree.third E J ⟶ FourEdgeTree.simplicial E' J :=
  descend (FourEdgeTree.secondZero E J) (𝟙 _) (second P a E E' δ)
    (onReference δ ≫ FourEdgeTree.threeVertex E' J)
    (onReference δ ▷ Δ[1] ≫
      FourEdgeTree.edge03 E' J)
    (by
      rw [SSet.ι₀_comp_assoc, FourEdgeTree.edge03_zero, second_zero])
    (by simp only [SSet.ι₁_comp_assoc, FourEdgeTree.edge03_one, Category.id_comp])

@[reassoc] theorem third_second :
    FourEdgeTree.secondInThird E J ≫ third P a E E' δ = second P a E E' δ :=
  descend_left _ _ _ _ _ _ _

@[reassoc] theorem third_three :
    FourEdgeTree.thirdThree E J ≫ third P a E E' δ =
      onReference δ ≫ FourEdgeTree.threeVertex E' J := descend_right _ _ _ _ _ _ _

@[reassoc] theorem third_cylinder :
    DoubleCylinder.simplicialCylinder (FourEdgeTree.secondZero E J) (𝟙 _) ≫ third P a E E' δ =
      onReference δ ▷ Δ[1] ≫
        FourEdgeTree.edge03 E' J :=
  descend_cylinder _ _ _ _ _ _ _

/-- Change the complete input reference while retaining both polynomial summands. -/
def map : FourEdgeTree.simplicial E J ⟶ FourEdgeTree.simplicial E' J :=
  descend (FourEdgeTree.thirdThree E J) (FourEdgeTree.attachment E J) (third P a E E' δ)
    (onReference (isoWhiskerRight δ (J).functor) ≫ FourEdgeTree.minusVertex E' J)
    (onReference δ ▷ Δ[1] ≫ FourEdgeTree.edge34 E' J)
    (by rw [SSet.ι₀_comp_assoc, FourEdgeTree.edge34_zero, third_three])
    (by
      rw [SSet.ι₁_comp_assoc, FourEdgeTree.edge34_one, ← Category.assoc,
        ← attachment, Category.assoc])

@[reassoc] theorem map_third :
    FourEdgeTree.thirdInTree E J ≫ map P a E E' δ = third P a E E' δ :=
  descend_left _ _ _ _ _ _ _

@[reassoc] theorem map_second :
    FourEdgeTree.secondInTree E J ≫ map P a E E' δ = second P a E E' δ := by
  rw [FourEdgeTree.secondInTree, Category.assoc, map_third, third_second]

@[reassoc] theorem map_first :
    FourEdgeTree.firstInTree E J ≫ map P a E E' δ = first P a E E' δ := by
  rw [FourEdgeTree.firstInTree, Category.assoc, map_second, second_first]

@[reassoc] theorem map_plus :
    FourEdgeTree.plusVertex E J ≫ map P a E E' δ =
      onReference (isoWhiskerRight δ (J).functor) ≫ FourEdgeTree.plusVertex E' J := by
  rw [FourEdgeTree.plusVertex, Category.assoc, map_first, first_plus]

@[reassoc] theorem map_minus :
    FourEdgeTree.minusVertex E J ≫ map P a E E' δ =
      onReference (isoWhiskerRight δ (J).functor) ≫ FourEdgeTree.minusVertex E' J :=
  descend_right _ _ _ _ _ _ _

@[reassoc] theorem map_edge12 :
    FourEdgeTree.edge12 E J ≫ map P a E E' δ =
      onReference δ ▷ Δ[1] ≫ FourEdgeTree.edge12 E' J := by
  rw [FourEdgeTree.edge12, Category.assoc, map_first, first_cylinder]

@[reassoc] theorem map_edge01 :
    FourEdgeTree.edge01 E J ≫ map P a E E' δ =
      onReference δ ▷ Δ[1] ≫ FourEdgeTree.edge01 E' J := by
  rw [FourEdgeTree.edge01, Category.assoc, map_second, second_cylinder]

@[reassoc] theorem map_edge03 :
    FourEdgeTree.edge03 E J ≫ map P a E E' δ =
      onReference δ ▷ Δ[1] ≫ FourEdgeTree.edge03 E' J := by
  rw [FourEdgeTree.edge03, Category.assoc, map_third, third_cylinder]

@[reassoc] theorem map_edge34 :
    FourEdgeTree.edge34 E J ≫ map P a E E' δ =
      onReference δ ▷ Δ[1] ≫ FourEdgeTree.edge34 E' J :=
  descend_cylinder _ _ _ _ _ _ _

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
