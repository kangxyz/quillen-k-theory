/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceCoherence

/-! The last three actual reference isomorphisms of the frozen chart diagram. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassReferenceMerge
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The last chart source retains its literal equality-transported binary comparison. -/
theorem last_source_reference :
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 15).2 =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm) ≪≫
          boundedFlatNormalizedPullbackCompIso (q' ≫ p') a) := by
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
        (Category.assoc q' p' a)))) ≪≫
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (Category.assoc q' p' a).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (q' ≫ p') a) = _
  rw [← smallIso_trans]
  apply congrArg smallIso
  apply Iso.ext
  simp only [Iso.trans_hom, eqToIso.hom, ← Category.assoc, eqToHom_trans]

/-- The raw normalization intermediate follows the source through the original first piece. -/
theorem last_intermediate_reference :
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 16).2 =
      (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 15).2 ≪≫
        smallIso (isoWhiskerLeft (boundedFlatNormalizedPullback a)
          (BinaryNormalizationSimplex.geometricIso q' p')) := by
  change _ ≪≫ (_ ≪≫ _) = (_ ≪≫ _) ≪≫ _
  exact (Iso.trans_assoc _ _ _).symm

/-- The final chart reference is the same source followed by the native total normalization iso. -/
theorem last_target_reference :
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 17).2 =
      (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 15).2 ≪≫
        smallIso (isoWhiskerLeft (boundedFlatNormalizedPullback a)
          (boundedFlatNormalizedPullbackCompIso q' p')) := by
  apply Iso.ext
  change (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq).hom ≫
      ((NormalizedTripleSimplex.leftFirst q' p' a).hom ≫
        (NormalizedTripleSimplex.leftSecond q' p' a).hom) =
    ((DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq).hom ≫
      (NormalizedTripleSimplex.rightFirst q' p' a).hom) ≫
        (NormalizedTripleSimplex.rightSecond q' p' a).hom
  rw [NormalizedTripleSimplex.two_routes, Category.assoc]

end Quillen.PerfectComplexes.BassReferenceMerge
