/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.Functoriality

/-! # Original-map consumers for the first genuine iterated-S structure map -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
open Quillen Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v u' v'
namespace QuillenTest.IteratedSFirstStage

open Quillen
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- At the genuine nondegenerate parameter the whole original grid survives,
including every unchanged morphism, inside the new S-row. -/
theorem original_grid_recovered (A : (sSet W.cof W.weq).obj (op ⦋1⦌)) :
    let B := (suspensionCylinder W).app (op ⦋1⦌) (A, ⟨𝟙 ⦋1⦌⟩)
    (∀ p, (B.val.obj p).obj.obj (interval 0 1 (by decide)) = A.val.obj p) ∧
    (∀ {p q} (f : p ⟶ q), (B.val.map f).hom.app (interval 0 1 (by decide)) = A.val.map f) :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Both original faces and the whole original zero track are literal equalities. -/
theorem original_simplicial_faces (n : SimplexCategoryᵒᵖ)
    (A : (sSet W.cof W.weq).obj n) (τ : n.unop ⟶ ⦋1⦌) :
    (∀ c : Fin 2, (suspensionCylinder W).app n
      (A, ⟨SimplexCategory.const n.unop ⦋1⦌ c⟩) = (doubleZero W).app n A) ∧
    (suspensionCylinder W).app n (zeroSimplex W.cof W.weq W.zero W.isZero n, ⟨τ⟩) =
      (doubleZero W).app n (zeroSimplex W.cof W.weq W.zero W.isZero n) :=
  ⟨suspensionCylinder_endpoint W n A, suspensionCylinder_zeroSimplex W n τ⟩

/-- The loop is the actual realized cylinder, not a separately chosen path. -/
theorem original_realization_formula (x : W.Delooping) (t : unitInterval) :
    loopStructureMap W x t = SSet.toTop.map (suspensionCylinder W)
      ((realizationCylinderIso (sSet W.cof W.weq)).inv (x, ULift.up t)) := rfl

/-- The actual loop endpoints and the original K-basepoint are fixed. -/
theorem original_based_loop (x : W.Delooping) :
    loopStructureMap W x 0 = doubleBasepoint W ∧
    loopStructureMap W x 1 = doubleBasepoint W ∧
    loopStructureMap W W.kBasepoint = Path.refl (doubleBasepoint W) :=
  ⟨(loopStructureMap W x).source, (loopStructureMap W x).target, loopStructureMap_basepoint W⟩

/-- The original K-group homomorphism is exactly the proved loop-space map,
under the genuine degree-shift equivalence, in every degree including zero. -/
theorem original_degree_raising_map (n : ℕ) (a : W.K n) :
    loopShiftMulEquiv n (degreeRaisingMap W n a) =
      piMap n (loopStructureMap W) (loopStructureMap_basepoint W) a :=
  (loopShiftMulEquiv n).apply_symm_apply _

section Naturality
variable {D : Type u} [Category.{v} D] (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (h0 : F.obj W.zero = V.zero)

/-- Strict cylinder and based-loop naturality use exactly the original induced maps. -/
theorem original_naturality (x : W.Delooping) :
    (sSetMap hF ▷ Δ[1]) ≫ suspensionCylinder V =
      suspensionCylinder W ≫ doubleDiagonalMap W V hF ∧
    basedLoopMap (SSet.toTop.map (doubleDiagonalMap W V hF)).hom
      (doubleDiagonalMap_basepoint W V hF h0) (loopStructureMap W x) =
        loopStructureMap V (deloopingMap hF x) :=
  ⟨suspensionCylinder_naturality W V hF h0, loopStructureMap_naturality W V hF h0 x⟩
end Naturality

/-- The underlying one-row comparison works across independent category universes. -/
theorem original_one_row_independent_universes {D : Type u'} [Category.{v'} D]
    (V : Structure D) {F : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)
    (h0 : F.obj W.zero = V.zero) :
    QuotientRows.oneEmbedding W ⋙ QuotientRows.postcompose W V hF ⦋1⦌ =
      F ⋙ QuotientRows.oneEmbedding V :=
  QuotientRows.oneEmbedding_postcompose W V hF h0

end QuillenTest.IteratedSFirstStage
