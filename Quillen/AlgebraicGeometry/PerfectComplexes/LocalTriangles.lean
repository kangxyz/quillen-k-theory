/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedStructure
public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.Closure

/-!
# Strict local models for distinguished triangles

A distinguished triangle whose first two objects have global strict models
has a strict model for its third object near every point. Derived morphisms
are locally represented by chain maps, their mapping cones are strict, and
the triangle comparison is the proved uniqueness of distinguished cones.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CochainComplex

universe u

namespace Quillen.PerfectComplexes

/-- Locally replace a distinguished triangle with a genuine chain mapping
cone triangle when its first two vertices have strict perfect models. -/
theorem exists_local_strictModel_of_triangle {X : Scheme.{u}}
    (T : Triangle (Derived X)) (hT : T ∈ distTriang (Derived X))
    {P Q K : Complex X} (hP : strictPerfect X P) (hQ : strictPerfect X Q)
    (eP : T.obj₁ ≅ (toDerived X).obj P) (eQ : T.obj₂ ≅ (toDerived X).obj Q)
    (eK : T.obj₃ ≅ (toDerived X).obj K) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      HasStrictModel ((@restrict Y X j hj).obj K) := by
  let φ := eP.inv ≫ T.mor₁ ≫ eQ.hom
  obtain ⟨Y, j, hj, y, hy, g, hg⟩ := exists_local_chain_representative_any_lift hP φ x
  let := hj
  let F := exactDerivedRestrict j
  let η := exactDerivedRestrictFactors j
  let a : F.obj T.obj₁ ≅ (toDerived Y).obj ((restrict j).obj P) := F.mapIso eP ≪≫ η.app P
  let b : F.obj T.obj₂ ≅ (toDerived Y).obj ((restrict j).obj Q) := F.mapIso eQ ≪≫ η.app Q
  have hcomm : F.map T.mor₁ ≫ b.hom = a.hom ≫ (toDerived Y).map g := by
    rw [← hg F η]
    dsimp only [a, b, liftedDerivedHom, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    dsimp only [φ]
    rw [F.map_comp, F.map_comp]
    simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id_assoc]
  let T' := F.mapTriangle.obj T
  let C' := (toDerived Y).mapTriangle.obj (mappingCone.triangle g)
  have hT' : T' ∈ distTriang (Derived Y) := F.map_distinguished T hT
  have hC' : C' ∈ distTriang (Derived Y) := mappingConeTriangle_distinguished g
  let et : T' ≅ C' := isoTriangleOfIso₁₂ T' C' hT' hC' a b hcomm
  let c : F.obj T.obj₃ ≅ (toDerived Y).obj ((restrict j).obj K) := F.mapIso eK ≪≫ η.app K
  refine ⟨Y, j, hj, y, hy, ⟨mappingCone g,
    strictPerfect_mappingCone (strictPerfect_restrict j hP) (strictPerfect_restrict j hQ) g⟩,
    ⟨c.symm ≪≫ Triangle.π₃.mapIso et⟩⟩

end Quillen.PerfectComplexes
