/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeMergedColumns

/-! The two unchanged right binary rows of the original merged composition rectangle. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The first right row retains the original first-triple reference, before any chart projection. -/
theorem merged_first_right_row (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
    preReferenceNode (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap p)
      (rightRowReference (NormalizedTripleSimplex.sourceMap c q p) c q p (Iso.refl _))
      (binaryNodes c q i) := by
  have hn := (DoubleSquareMergedSimplex.first_nodes p q p' q' a b c hp hq (rightIndex i)).trans
    (DoubleSquareCommonSimplex.first_nodes p q p' q' a b c hp hq (rightIndex i))
  refine hn.trans ?_
  simpa only [tripleRightNode, Iso.refl_trans, preBinaryNodes, preReferenceNode] using
    triple_right_row (NormalizedTripleSimplex.sourceMap c q p) c q p (Iso.refl _) i

/-- The second right row retains its actual middle-square source equality. -/
theorem merged_middle_right_row (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
    preReferenceNode (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap p)
      (rightRowReference (NormalizedTripleSimplex.sourceMap c q p) q' b p
        (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq)) (binaryNodes q' b i) :=
  (merged_middle_nodes p q p' q' a b c hp hq (rightIndex i)).trans
    (triple_right_row (NormalizedTripleSimplex.sourceMap c q p) q' b p
      (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq) i)

end Quillen.PerfectComplexes.BassH1Join
