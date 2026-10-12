/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremA.GeometricCells

/-!
# The original replacement skeleton as a geometric simplex attachment

The actual enriched coproduct pushout is transported through the specified
coordinate homeomorphisms. The old and new skeletons, their original inclusion,
and every original attaching and characteristic map are retained.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits Opposite MonoidalCategory Convexity
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.TheoremA
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The complete enriched boundary map is the original parameterized boundary inclusion. -/
theorem realizedReplacementBoundary_square (n : ℕ) :
    SSet.toTop.map (diagonalMap (replacementCellsBoundaryι H n)) ≫
        (TopCat.isoOfHomeo (realizedReplacementCellsHomeomorph H n)).hom =
      (TopCat.isoOfHomeo (realizedReplacementBoundariesHomeomorph H n)).hom ≫
        Quillen.parameterizedSimplexBoundaryInclusion (replacementCellParameters H n) n := by
  apply (realizedDiagonalSigmaIsColimit
    (fun s : (nerve D).nonDegenerate n ↦ replacementCellBoundary H s)).hom_ext
  intro ⟨s⟩
  have hi :
      SSet.toTop.map (diagonalMap
        (bisimplicialSigmaι (fun s ↦ replacementCellBoundary H s) s)) ≫
          SSet.toTop.map (diagonalMap (replacementCellsBoundaryι H n)) =
      SSet.toTop.map (diagonalMap (replacementCellBoundaryι H s)) ≫
        SSet.toTop.map (diagonalMap
          (bisimplicialSigmaι (fun s ↦ replacementCell H s) s)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  dsimp only [Cofan.mk_ι_app]
  rw [← Category.assoc, hi, Category.assoc]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change realizedReplacementCellsHomeomorph H n
      (SSet.toTop.map (diagonalMap (bisimplicialSigmaι (fun s ↦ replacementCell H s) s))
        (SSet.toTop.map (diagonalMap (replacementCellBoundaryι H s)) x)) =
    Quillen.parameterizedSimplexBoundaryInclusion (replacementCellParameters H n) n
      (realizedReplacementBoundariesHomeomorph H n
        (SSet.toTop.map (diagonalMap
          (bisimplicialSigmaι (fun s ↦ replacementCellBoundary H s) s)) x))
  rw [realizedReplacementCellsHomeomorph_inclusion,
    realizedReplacementBoundariesHomeomorph_inclusion]
  exact congrArg (fun z : |H.obj (s.val.obj 0)| × StdSimplex ℝ (Fin (n + 1)) ↦
    ((⟨s, z.1⟩ : replacementCellParameters H n), z.2))
      (ConcreteCategory.congr_hom (realizedEnrichedBoundary_square (H.obj (s.val.obj 0)) n) x)

/-- The original attaching map, expressed in the actual geometric boundary coordinates. -/
def replacementGeometricAttaching (n : ℕ) :
    TopCat.of (replacementCellParameters H n × simplexBoundary n) ⟶
      (realizedReplacementSkeleton H).obj n :=
  (TopCat.isoOfHomeo (realizedReplacementBoundariesHomeomorph H n)).inv ≫
    SSet.toTop.map (diagonalMap (replacementCellsAttaching H n))

/-- The original characteristic map, expressed in the actual geometric simplex coordinates. -/
def replacementGeometricCharacteristic (n : ℕ) :
    TopCat.of (replacementCellParameters H n × StdSimplex ℝ (Fin (n + 1))) ⟶
      (realizedReplacementSkeleton H).obj (n + 1) :=
  (TopCat.isoOfHomeo (realizedReplacementCellsHomeomorph H n)).inv ≫
    SSet.toTop.map (diagonalMap (replacementCellsCharacteristic H n))

/-- Every actual replacement successor is a genuine parameterized simplex attachment. -/
theorem replacementGeometric_isPushout (n : ℕ) :
    IsPushout
      (Quillen.parameterizedSimplexBoundaryInclusion (replacementCellParameters H n) n)
      (replacementGeometricAttaching H n) (replacementGeometricCharacteristic H n)
      ((realizedReplacementSkeleton H).map (homOfLE (Nat.le_succ n))) := by
  apply (realizedReplacementSkeleton_isPushout H n).flip.of_iso
    (TopCat.isoOfHomeo (realizedReplacementBoundariesHomeomorph H n))
    (TopCat.isoOfHomeo (realizedReplacementCellsHomeomorph H n)) (Iso.refl _) (Iso.refl _)
  · exact realizedReplacementBoundary_square H n
  · simp only [replacementGeometricAttaching, Iso.refl_hom, Category.comp_id,
      Iso.hom_inv_id_assoc]
  · simp only [replacementGeometricCharacteristic, Iso.refl_hom, Category.comp_id,
      Iso.hom_inv_id_assoc]
  · simp

end Quillen.TheoremA
