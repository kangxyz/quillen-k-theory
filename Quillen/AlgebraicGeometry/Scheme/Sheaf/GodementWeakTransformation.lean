/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GodementWeakComposition

/-! # Natural original weak-arrow composition before specialization -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory AlgebraicGeometry
namespace Quillen.SchemeSheaf
variable {D : Type v} [Category.{w} D] {X : Scheme.{u}}
    {F G H : D ⥤ CochainComplex.Plus X.Modules}

lemma plus_nattrans_comp_quasiIso (a : F ⟶ G) (b : G ⟶ H)
    (ha : ∀ K, QuasiIso (a.app K).hom) (hb : ∀ K, QuasiIso (b.app K).hom) (K : D) :
    QuasiIso ((a ≫ b).app K).hom := by
  let := ha K
  let := hb K
  exact plus_quasiIso_comp (a.app K) (b.app K)

lemma plus_natIso_hom_quasiIso (e : F ≅ G) (K : D) : QuasiIso (e.hom.app K).hom :=
  plus_iso_quasiIso (e.hom.app K)

lemma plus_whiskerTotalImage_quasiIso {Y : Scheme.{u}} (p : X ⟶ Y)
    (a : F ⟶ G) (ha : ∀ K, QuasiIso (a.app K).hom) (K : D) :
    QuasiIso ((Functor.whiskerRight a
      (godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus)).app K).hom := by
  let := ha K
  exact pushGodementPlus_map_quasiIso p (a.app K)

end Quillen.SchemeSheaf
