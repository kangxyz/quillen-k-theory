/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReferenceRows

/-! Full source-total and target-total binary rows of the unchanged moving rectangle. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join

section BinaryMatch
variable {X Y Z : Scheme.{u}} {U : Model.{u + 1}}
  (F : modelOf (boundedFlatPerfectWaldhausen Z) ⟶ U)
  (J : modelOf (boundedFlatPerfectWaldhausen X) ⟶ U)
  (f : X ⟶ Y) (g : Y ⟶ Z) {f' : X ⟶ Y} {g' : Y ⟶ Z}
  (hf : f = f') (hg : g = g')

include hf hg in
/-- Actual factor equalities and a full common source identify an entire postcomposed binary row. -/
theorem post_binary_families_match
    {N M : Fin 3 → Σ H : modelOf (boundedFlatPerfectWaldhausen Z) ⟶ U, F.functor ≅ H.functor}
    {ρ : F.functor ≅ (BinaryNormalizationSimplex.sourceMap f g ≫ J).functor}
    {σ : F.functor ≅ (BinaryNormalizationSimplex.sourceMap f' g' ≫ J).functor}
    (hN : ∀ i, N i = postReferenceNode F J ρ (binaryNodes f g i))
    (hM : ∀ i, M i = postReferenceNode F J σ (binaryNodes f' g' i))
    (he : N 0 = M 0) (i : Fin 3) : N i = M i := by
  subst f'
  subst g'
  exact post_families_match F J (BinaryNormalizationSimplex.sourceMap f g)
    (binaryNodes f g) hN hM 0 he i
end BinaryMatch

section Rectangle
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

def sourceTotalIndex : Fin 3 → Fin 18 := ![0, 1, 2]
def targetTotalIndex : Fin 3 → Fin 18 := ![0, 14, 15]

/-- The original source total is precisely its unchanged native binary normalization row. -/
theorem rectangle_source_total_nodes (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq (sourceTotalIndex i) =
      binaryNodes c (q ≫ p) i := by
  fin_cases i <;> rfl

/-- The original outer square supplies the target binary row's literal geometric source equality. -/
abbrev targetTotalSourceEq := ProjectionReference.outerAnchor
  p q p' q' a b c hp hq (q ≫ p) (q' ≫ p') rfl rfl

/-- All target-total binary nodes retain the original outer source transport. -/
theorem rectangle_target_total_nodes (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq (targetTotalIndex i) =
    anchorNode (eqToIso (targetTotalSourceEq p q p' q' a b c hp hq))
      (binaryNodes (q' ≫ p') a i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (targetTotalSourceEq p q p' q' a b c hp hq)
    change (Iso.refl (NormalizedTripleSimplex.sourceMap c q p).functor).hom ≫
      eqToHom (targetTotalSourceEq p q p' q' a b c hp hq) =
      (eqToIso (targetTotalSourceEq p q p' q' a b c hp hq) ≪≫ Iso.refl _).hom
    simp
  · have he : ProjectionReference.nodes p q p' q' a b c hp hq (q ≫ p) rfl 14 =
        DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 14 := anchorNode_refl _
    exact he.symm.trans (ProjectionReference.shared_nodes p q p' q' a b c hp hq
      (q ≫ p) (q' ≫ p') rfl rfl 3)
  · have he : ProjectionReference.nodes p q p' q' a b c hp hq (q ≫ p) rfl 15 =
        DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 15 := anchorNode_refl _
    exact he.symm.trans (ProjectionReference.shared_nodes p q p' q' a b c hp hq
      (q ≫ p) (q' ≫ p') rfl rfl 4)
end Rectangle

end Quillen.PerfectComplexes.BassMOuterJoin
