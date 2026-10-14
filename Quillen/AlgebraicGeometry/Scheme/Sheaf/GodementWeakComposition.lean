/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalExact

/-! # Original weak maps through actual Godement total and original image -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- Ordinary image preserves the weak map only after the actual flasque total. -/
lemma pushGodementPlus_map_quasiIso {X Y : Scheme.{u}} (p : X ⟶ Y)
    {A B : CochainComplex.Plus X.Modules} (m : A ⟶ B) [QuasiIso m.hom] :
    QuasiIso (((godementTotalPlus X ⋙
      (Scheme.Modules.pushforward p).mapCochainComplexPlus).map m).hom) := by
  change QuasiIso (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).map
    ((godementTotal X).map m.hom))
  exact Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal.totalPushforwardPlus_quasiIso p m

/-- Original weak maps compose in the actual Plus category. -/
lemma plus_quasiIso_comp {X : Scheme.{u}} {A B C : CochainComplex.Plus X.Modules}
    (m : A ⟶ B) (n : B ⟶ C) [QuasiIso m.hom] [QuasiIso n.hom] :
    QuasiIso (m ≫ n).hom := by
  change QuasiIso (m.hom ≫ n.hom)
  infer_instance

/-- Original isomorphisms of Plus objects are weak on their actual underlying complexes. -/
lemma plus_iso_quasiIso {X : Scheme.{u}} {A B : CochainComplex.Plus X.Modules}
    (m : A ⟶ B) [IsIso m] : QuasiIso m.hom := by
  let : IsIso m.hom := Functor.map_isIso (CochainComplex.Plus.ι X.Modules) m
  infer_instance

end Quillen.SchemeSheaf
