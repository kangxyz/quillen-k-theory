/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.WeakFunctorTransport

/-! # Typed plain-complex weak maps of actual tensor, total and image functors -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- Exact tensor precedes the actual total; image is applied only between flasque totals. -/
lemma plus_tensor_totalImage_functor_map_quasiIso
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : D ⥤ CochainComplex.Plus X.Modules) (T : X.Modules ⥤ X.Modules)
    [T.Additive] [T.PreservesHomology] {K L : D} (a : K ⟶ L) (ha : QuasiIso (F.map a).hom) :
    QuasiIso ((((F ⋙ CochainComplex.Plus.ι X.Modules) ⋙
      T.mapHomologicalComplex (.up ℤ) ⋙ godementTotal X ⋙
      (Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).map a)) := by
  let := ha
  let t := T.mapCochainComplexPlus.map (F.map a)
  let : QuasiIso t.hom := by
    change QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map (F.map a).hom)
    infer_instance
  exact Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal.totalPushforwardPlus_quasiIso p t

end Quillen.SchemeSheaf
