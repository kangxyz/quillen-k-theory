/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Realization.PrismGluing
public import Quillen.Topology.Realization.SimplicialColimits

/-! # Realization preserves the simplicial interval cylinder -/
@[expose] public section


noncomputable section

open Convexity CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u

namespace Quillen

/-- The canonical cylinder comparison is a homeomorphism on representable simplicial sets. -/
instance realizationCylinderComparison_standard_isIso (n : ℕ) :
    IsIso (realizationCylinderComparison (Δ[n] : SSet.{u})) := by
  let e : |(Δ[n] ⊗ Δ[1] : SSet.{u})| ≃ₜ (|(Δ[n] : SSet.{u})| × TopCat.I.{u}) :=
    (realizationPrismHomeomorph n).trans
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm.prodCongr TopCat.I.homeomorph.symm)
  have heq : realizationCylinderComparison (Δ[n] : SSet.{u}) =
      (TopCat.isoOfHomeo e).hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply Prod.ext
    · exact ((SimplexCategory.toTopHomeo ⦋n⦌).symm_apply_apply _).symm
    · rfl
  rw [heq]
  infer_instance

/-- The canonical cylinder comparison as a natural transformation. -/
def realizationCylinderComparisonNatTrans :
    tensorRight (Δ[1] : SSet.{u}) ⋙ SSet.toTop ⟶ SSet.toTop ⋙ tensorRight TopCat.I where
  app := realizationCylinderComparison
  naturality _ _ f := realizationCylinderComparison_naturality f

/-- Geometric realization takes the simplicial cylinder to the actual topological cylinder. -/
instance realizationCylinderComparison_isIso (X : SSet.{u}) :
    IsIso (realizationCylinderComparison X) := by
  let K := Presheaf.functorToRepresentables X
  have : ∀ j, IsIso ((Functor.whiskerLeft K realizationCylinderComparisonNatTrans).app j) := by
    intro j
    change IsIso (realizationCylinderComparison (SSet.stdSimplex.obj j.unop.obj.unop))
    cases j.unop.obj.unop using SimplexCategory.rec with
    | _ n => exact realizationCylinderComparison_standard_isIso n
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft K realizationCylinderComparisonNatTrans)
  have : PreservesColimit K (tensorRight (Δ[1] : SSet.{u})) := by infer_instance
  have : PreservesColimit (K ⋙ tensorRight (Δ[1] : SSet.{u})) SSet.toTop := by infer_instance
  have : PreservesColimit K SSet.toTop := by infer_instance
  have : PreservesColimit (K ⋙ SSet.toTop) (tensorRight TopCat.I.{u}) := by infer_instance
  exact isIso_app_coconePt_of_preservesColimit K realizationCylinderComparisonNatTrans
    (Presheaf.coconeOfRepresentable X) (Presheaf.colimitOfRepresentable X)

/-- The natural cylinder isomorphism in `TopCat`. -/
def realizationCylinderIso (X : SSet.{u}) : |X ⊗ Δ[1]| ≅ |X| ⊗ TopCat.I :=
  asIso (realizationCylinderComparison X)

end Quillen
