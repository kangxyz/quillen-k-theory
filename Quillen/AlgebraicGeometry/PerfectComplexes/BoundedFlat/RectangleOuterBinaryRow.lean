/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ReferenceRowTransport

/-! The original outer binary row of a rectangle, with its actual source equality transport. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
open BassReferenceMerge
variable {V : Model.{u + 1}} {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (F : V ⟶ modelOf (boundedFlatPerfectWaldhausen C'))
  (P : V ⟶ modelOf (boundedFlatPerfectWaldhausen A))
  (ρ : F.functor ≅ (P ≫ NormalizedTripleSimplex.sourceMap c q p).functor)

/-- Actual precomposition and reference transport of each original full rectangle node. -/
def preRectangleNodes (i : Fin 18) :=
  preReferenceNode F P ρ (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq i)

def outerIndex : Fin 3 → Fin 18 := ![0, 14, 15]

include hp hq in
/-- The original total square equation identifies the outer binary source functor. -/
theorem rectangle_outer_eq : (NormalizedTripleSimplex.sourceMap c q p).functor =
    (BinaryNormalizationSimplex.sourceMap (q' ≫ p') a).functor :=
  congrArg (fun K ↦ AsSmall.down ⋙ K ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback
      (DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm)

/-- Only the actual rectangle's geometric source equality enters the binary row reference. -/
def rectangleOuterReference : F.functor ≅
    (P ≫ BinaryNormalizationSimplex.sourceMap (q' ≫ p') a).functor :=
  ρ ≪≫ isoWhiskerLeft P.functor (eqToIso (rectangle_outer_eq p q p' q' a b c hp hq))

theorem rectangle_outer_noninitial_functor (i : Fin 2) :
    (preRectangleNodes p q p' q' a b c hp hq F P ρ (outerIndex i.succ)).1.functor =
      (preBinaryNodes F P (q' ≫ p') a
        (rectangleOuterReference p q p' q' a b c hp hq F P ρ) i.succ).1.functor := by
  fin_cases i <;> rfl

/-- The full original source, raw intermediate, and normalized target form the actual binary row. -/
theorem rectangle_outer_row (i : Fin 3) :
    preRectangleNodes p q p' q' a b c hp hq F P ρ (outerIndex i) =
      preBinaryNodes F P (q' ≫ p') a
        (rectangleOuterReference p q p' q' a b c hp hq F P ρ) i := by
  fin_cases i
  · change preReferenceNode F P ρ ⟨NormalizedTripleSimplex.sourceMap c q p, Iso.refl _⟩ =
      preReferenceNode F P (rectangleOuterReference p q p' q' a b c hp hq F P ρ)
        ⟨BinaryNormalizationSimplex.sourceMap (q' ≫ p') a, Iso.refl _⟩
    rw [preReferenceNode_source, preReferenceNode_source]
    exact preReferenceNode_source_transport F P (rectangle_outer_eq p q p' q' a b c hp hq) ρ
  · apply Sigma.ext (Model.Hom.ext
      (rectangle_outer_noninitial_functor p q p' q' a b c hp hq F P ρ 0))
    apply heq_of_eq
    change ρ ≪≫ isoWhiskerLeft P.functor
        (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 14).2 =
      (ρ ≪≫ isoWhiskerLeft P.functor (eqToIso (rectangle_outer_eq p q p' q' a b c hp hq))) ≪≫
        isoWhiskerLeft P.functor (BinaryNormalizationSimplex.first (q' ≫ p') a)
    rw [ProjectionReference.last_raw_reference, smallIso_trans, smallIso_eqToIso,
      isoWhiskerLeft_trans, Iso.trans_assoc]
    rfl
  · apply Sigma.ext (Model.Hom.ext
      (rectangle_outer_noninitial_functor p q p' q' a b c hp hq F P ρ 1))
    apply heq_of_eq
    change ρ ≪≫ isoWhiskerLeft P.functor
        (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 15).2 =
      (ρ ≪≫ isoWhiskerLeft P.functor (eqToIso (rectangle_outer_eq p q p' q' a b c hp hq))) ≪≫
        isoWhiskerLeft P.functor (BinaryNormalizationSimplex.total (q' ≫ p') a)
    rw [last_source_reference, smallIso_trans, smallIso_eqToIso,
      isoWhiskerLeft_trans, Iso.trans_assoc]
    rfl

end Quillen.PerfectComplexes.BassH0Merge
