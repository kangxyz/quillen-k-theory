/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GodementWeakTransformation

/-! # Typed weak-map transport before concrete functor specialization -/
@[expose] public section
noncomputable section
universe u v w x y
open CategoryTheory AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- The exact associator and actual total/image whiskering, with typed endpoints. -/
@[irreducible] def plusReassociatedTotalImageMap
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    {M : Type x} [Category.{y} M] (A : D ⥤ M)
    (B : M ⥤ CochainComplex.Plus X.Modules)
    (C : D ⥤ CochainComplex.Plus X.Modules)
    (E : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (a : A ⋙ B ⟶ C ⋙ E) :
    A ⋙ B ⋙ godementTotalPlus X ⋙
        (Scheme.Modules.pushforward p).mapCochainComplexPlus ⟶
      C ⋙ E ⋙ godementTotalPlus X ⋙
        (Scheme.Modules.pushforward p).mapCochainComplexPlus :=
  (Functor.associator A B
    (godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus)).inv ≫
    Functor.whiskerRight a
      (godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus) ≫
    (Functor.associator C E
      (godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus)).hom

lemma plusReassociatedTotalImageMap_quasiIso
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    {M : Type x} [Category.{y} M] (A : D ⥤ M)
    (B : M ⥤ CochainComplex.Plus X.Modules)
    (C : D ⥤ CochainComplex.Plus X.Modules)
    (E : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (a : A ⋙ B ⟶ C ⋙ E) (ha : ∀ K, QuasiIso (a.app K).hom) (K : D) :
    QuasiIso ((plusReassociatedTotalImageMap p A B C E a).app K).hom := by
  let F := godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus
  let e₁ := Functor.associator A B F
  let e₂ := Functor.associator C E F
  let aF := Functor.whiskerRight a F
  unfold plusReassociatedTotalImageMap
  exact plus_nattrans_comp_quasiIso e₁.inv (aF ≫ e₂.hom)
    (plus_natIso_hom_quasiIso e₁.symm)
    (plus_nattrans_comp_quasiIso aF e₂.hom
      (plus_whiskerTotalImage_quasiIso p a ha) (plus_natIso_hom_quasiIso e₂)) K

lemma complex_map_quasiIso_of_natIso
    {D : Type v} [Category.{w} D] {X : Scheme.{u}}
    {F G : D ⥤ CochainComplex X.Modules ℤ} (e : F ≅ G)
    {K L : D} (a : K ⟶ L) (ha : QuasiIso (G.map a)) : QuasiIso (F.map a) := by
  let := ha
  let : QuasiIso (e.hom.app K) := inferInstance
  let : QuasiIso (e.hom.app L) := inferInstance
  have : QuasiIso (F.map a ≫ e.hom.app L) := by
    rw [e.hom.naturality a]
    infer_instance
  exact quasiIso_of_comp_right (F.map a) (e.hom.app L)

end Quillen.SchemeSheaf
