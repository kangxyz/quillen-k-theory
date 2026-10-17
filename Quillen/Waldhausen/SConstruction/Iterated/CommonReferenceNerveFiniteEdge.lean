/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteParameter
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexParameterPaths

/-!
# Whole-reference finite edges in the original cylinder coordinates

The finite-simplex parameter respects every ordered face. For an edge, its realization uses
exactly the original cylinder inverse and the affine edge clock, on the entire source nerve.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FiniteParameter
variable {V W V' W' : Model.{u}} (E : V ⟶ W) (F : V' ⟶ W')
variable {q : ℕ} (f : Node E → Fin (q + 1) → Node F)

/-- An ordered face of the finite parameter retains the whole first nerve coordinate. -/
theorem parameter_restrict {m : ℕ} (h : ⦋m⦌ ⟶ ⦋q⦌)
    (x : |nerve (Codiscrete (Node E))|) (z : StdSimplex ℝ (Fin (m + 1))) :
    parameter E F (fun e i ↦ f e (h.toOrderHom i)) (x, z) =
      parameter E F f (x, StdSimplex.map h.toOrderHom z) := by
  let X := nerve (Codiscrete (Node E))
  let p₀ : (|X| ⊗ |(Δ[m] : SSet.{u})| : TopCat.{u}) :=
    (x, (SimplexCategory.toTopHomeo ⦋m⦌).symm z)
  let p₁ : (|X| ⊗ |(Δ[q] : SSet.{u})| : TopCat.{u}) :=
    (x, (SimplexCategory.toTopHomeo ⦋q⦌).symm (StdSimplex.map h.toOrderHom z))
  have hz : SSet.toTop.map (SSet.stdSimplex.map h)
      ((SimplexCategory.toTopHomeo ⦋m⦌).symm z) =
        (SimplexCategory.toTopHomeo ⦋q⦌).symm (StdSimplex.map h.toOrderHom z) := by
    apply (SimplexCategory.toTopHomeo ⦋q⦌).injective
    rw [SimplexCategory.toTopHomeo_naturality_apply,
      Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    rfl
  have hp : (|X| ◁ SSet.toTop.map (SSet.stdSimplex.map h)) p₀ = p₁ :=
    Prod.ext rfl hz
  have hn : (realizationProductSimplexIso X m).inv ≫
      SSet.toTop.map (X ◁ SSet.stdSimplex.map h) =
        (|X| ◁ SSet.toTop.map (SSet.stdSimplex.map h)) ≫
          (realizationProductSimplexIso X q).inv :=
    prodComparison_inv_natural_whiskerLeft SSet.toTop (SSet.stdSimplex.map h)
  have hi : SSet.toTop.map (X ◁ SSet.stdSimplex.map h)
      ((realizationProductSimplexIso X m).inv p₀) =
        (realizationProductSimplexIso X q).inv p₁ := by
    calc
      _ = ((realizationProductSimplexIso X m).inv ≫
          SSet.toTop.map (X ◁ SSet.stdSimplex.map h)) p₀ :=
        (CategoryTheory.comp_apply _ _ p₀).symm
      _ = ((|X| ◁ SSet.toTop.map (SSet.stdSimplex.map h)) ≫
          (realizationProductSimplexIso X q).inv) p₀ :=
        ConcreteCategory.congr_hom hn p₀
      _ = (realizationProductSimplexIso X q).inv
          ((|X| ◁ SSet.toTop.map (SSet.stdSimplex.map h)) p₀) :=
        CategoryTheory.comp_apply _ _ p₀
      _ = _ := congrArg (realizationProductSimplexIso X q).inv hp
  change SSet.toTop.map (simplicial E F (fun e i ↦ f e (h.toOrderHom i)))
      ((realizationProductSimplexIso X m).inv p₀) =
    SSet.toTop.map (simplicial E F f) ((realizationProductSimplexIso X q).inv p₁)
  rw [← simplicial_restrict, Functor.map_comp, CategoryTheory.comp_apply, hi]

/-- The actual interval comparison is the finite product comparison followed by its interval iso. -/
theorem cylinderIso_eq (X : SSet.{u}) :
    realizationCylinderIso X = realizationProductSimplexIso X 1 ≪≫
      (MonoidalCategory.tensorLeft |X|).mapIso SSet.stdSimplex.toTopObjIsoI := by
  apply Iso.ext
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [realizationCylinderIso, realizationCylinderComparison, realizationProductSimplexIso]

/-- The one-dimensional finite parameter uses the unchanged realized cylinder coordinate. -/
theorem parameter_cylinder (g : Node E → Fin 2 → Node F)
    (x : |nerve (Codiscrete (Node E))|) (t : unitInterval) :
    SSet.toTop.map (simplicial E F g)
        ((realizationCylinderIso (nerve (Codiscrete (Node E)))).inv (x, ULift.up t)) =
      parameter E F g (x, StdSimplex.homeomorphI.symm t) := by
  rw [cylinderIso_eq]
  rfl

/-- Every ordered finite edge is the literal original cylinder family on all source points. -/
theorem simplicial_edge (h : ⦋1⦌ ⟶ ⦋q⦌)
    (x : |nerve (Codiscrete (Node E))|) (t : unitInterval) :
    SSet.toTop.map (simplicial E F (fun e i ↦ f e (h.toOrderHom i)))
        ((realizationCylinderIso (nerve (Codiscrete (Node E)))).inv (x, ULift.up t)) =
      parameter E F f (x, SimplexParameters.edge (h.toOrderHom 0) (h.toOrderHom 1) t) := by
  rw [parameter_cylinder, parameter_restrict]
  have hd : StdSimplex.homeomorphI.symm t =
      StdSimplex.duple (0 : Fin 2) 1 (unitInterval.nonneg (unitInterval.symm t))
        (unitInterval.nonneg t) (by simp) := by
    apply StdSimplex.homeomorphI.injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    simp [StdSimplex.homeomorphI_apply_coe, StdSimplex.duple]
  have hz : StdSimplex.map h.toOrderHom (StdSimplex.homeomorphI.symm t) =
      SimplexParameters.edge (h.toOrderHom 0) (h.toOrderHom 1) t := by
    calc
      _ = StdSimplex.map h.toOrderHom
          (StdSimplex.duple (0 : Fin 2) 1 (unitInterval.nonneg (unitInterval.symm t))
            (unitInterval.nonneg t) (by simp)) :=
        congrArg (StdSimplex.map h.toOrderHom) hd
      _ = StdSimplex.duple (h.toOrderHom 0) (h.toOrderHom 1)
          (unitInterval.nonneg (unitInterval.symm t)) (unitInterval.nonneg t) (by simp) :=
        StdSimplex.map_duple _ _ _ _ _ _
      _ = _ := rfl
  rw [hz]

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FiniteParameter
