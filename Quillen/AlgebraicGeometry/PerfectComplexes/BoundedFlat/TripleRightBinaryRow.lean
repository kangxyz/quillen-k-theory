/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryRowEndpoint

/-! The actual split-triple right row retains the original precomposed binary nodes. -/
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
variable {X Y Z T : Scheme.{u}}
  (F : modelOf (boundedFlatPerfectWaldhausen T) ⟶ modelOf (boundedFlatPerfectWaldhausen X))
  (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  (ρ : F.functor ≅ (NormalizedTripleSimplex.sourceMap f g h).functor)

def rightIndex : Fin 3 → Fin 8 := ![5, 6, 7]

def tripleRightNode (i : Fin 3) :
    Σ G : modelOf (boundedFlatPerfectWaldhausen T) ⟶ modelOf (boundedFlatPerfectWaldhausen X),
      F.functor ≅ G.functor :=
  ⟨SplitTripleSimplex.vertices f g h (rightIndex i),
    ρ ≪≫ SplitTripleSimplex.references f g h (rightIndex i)⟩

def rightRowReference : F.functor ≅
    (normalizedMap h ≫ BinaryNormalizationSimplex.sourceMap f g).functor :=
  ρ ≪≫ NormalizedTripleSimplex.rightFirst f g h

theorem triple_right_functor (i : Fin 3) : (tripleRightNode F f g h ρ i).1.functor =
    (preBinaryNodes F (normalizedMap h) f g (rightRowReference F f g h ρ) i).1.functor := by
  fin_cases i <;> rfl

/-- Every full right-row node uses the exact original binary geometric and normalization pieces. -/
theorem triple_right_row (i : Fin 3) : tripleRightNode F f g h ρ i =
    preBinaryNodes F (normalizedMap h) f g (rightRowReference F f g h ρ) i := by
  fin_cases i
  · apply Sigma.ext (Model.Hom.ext (triple_right_functor F f g h ρ 0))
    apply heq_of_eq
    change ρ ≪≫ NormalizedTripleSimplex.rightFirst f g h =
      (ρ ≪≫ NormalizedTripleSimplex.rightFirst f g h) ≪≫
        isoWhiskerLeft (normalizedMap h).functor
          (Iso.refl (BinaryNormalizationSimplex.sourceMap f g).functor)
    rw [isoWhiskerLeft_refl]
    exact (Iso.trans_refl (ρ ≪≫ NormalizedTripleSimplex.rightFirst f g h)).symm
  · apply Sigma.ext (Model.Hom.ext (triple_right_functor F f g h ρ 1))
    apply heq_of_eq
    change ρ ≪≫ (NormalizedTripleSimplex.rightFirst f g h ≪≫
      smallIso (isoWhiskerLeft (boundedFlatNormalizedPullback h)
        (BinaryNormalizationSimplex.geometricIso f g))) =
      (ρ ≪≫ NormalizedTripleSimplex.rightFirst f g h) ≪≫
        isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback h ⋙ AsSmall.up)
          (smallIso (BinaryNormalizationSimplex.geometricIso f g))
    rw [smallIso_precomp, Iso.trans_assoc]
  · apply Sigma.ext (Model.Hom.ext (triple_right_functor F f g h ρ 2))
    apply heq_of_eq
    have he : NormalizedTripleSimplex.leftFirst f g h ≪≫
        NormalizedTripleSimplex.leftSecond f g h =
      NormalizedTripleSimplex.rightFirst f g h ≪≫ NormalizedTripleSimplex.rightSecond f g h :=
      Iso.ext (NormalizedTripleSimplex.two_routes f g h)
    change ρ ≪≫ (NormalizedTripleSimplex.leftFirst f g h ≪≫
      NormalizedTripleSimplex.leftSecond f g h) = _
    rw [he]
    change ρ ≪≫ (NormalizedTripleSimplex.rightFirst f g h ≪≫
      smallIso (isoWhiskerLeft (boundedFlatNormalizedPullback h)
        (boundedFlatNormalizedPullbackCompIso f g))) =
      (ρ ≪≫ NormalizedTripleSimplex.rightFirst f g h) ≪≫
        isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback h ⋙ AsSmall.up)
          (smallIso (boundedFlatNormalizedPullbackCompIso f g))
    rw [smallIso_precomp, Iso.trans_assoc]

end Quillen.PerfectComplexes.BassH0Merge
