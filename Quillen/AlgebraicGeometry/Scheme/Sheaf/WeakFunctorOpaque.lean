/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.WeakFunctorMap

/-! # Opaque typed boundary for the original plain tensor, total and image chain -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- The literal tensor, total and ordinary image expression, with no altered map. -/
@[irreducible] def plusTensorTotalImageFunctor
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : D ⥤ CochainComplex.Plus X.Modules) (T : X.Modules ⥤ X.Modules) [T.Additive] :
    D ⥤ CochainComplex Y.Modules ℤ :=
  (F ⋙ CochainComplex.Plus.ι X.Modules) ⋙ T.mapHomologicalComplex (.up ℤ) ⋙
    godementTotal X ⋙ (Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)

/-- Definitional equality at functor level avoids concrete component evaluation. -/
lemma plusTensorTotalImageFunctor_eq
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : D ⥤ CochainComplex.Plus X.Modules) (T : X.Modules ⥤ X.Modules) [T.Additive] :
    plusTensorTotalImageFunctor p F T =
      (F ⋙ CochainComplex.Plus.ι X.Modules) ⋙ T.mapHomologicalComplex (.up ℤ) ⋙
        godementTotal X ⋙ (Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ) := by
  unfold plusTensorTotalImageFunctor
  rfl

lemma plusTensorTotalImageFunctor_map_quasiIso
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : D ⥤ CochainComplex.Plus X.Modules) (T : X.Modules ⥤ X.Modules)
    [T.Additive] [T.PreservesHomology] {K L : D} (a : K ⟶ L)
    (ha : QuasiIso (F.map a).hom) :
    QuasiIso ((plusTensorTotalImageFunctor p F T).map a) := by
  rw [plusTensorTotalImageFunctor_eq]
  exact plus_tensor_totalImage_functor_map_quasiIso (D := D) (X := X) (Y := Y)
    p F T (K := K) (L := L) a ha

end Quillen.SchemeSheaf
