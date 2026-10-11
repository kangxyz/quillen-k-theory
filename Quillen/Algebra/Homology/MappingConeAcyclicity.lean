/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.MappingConeQuasiIso

/-!
# Acyclicity of the original quasi-isomorphism cone

The original distinguished mapping-cone triangle proves the forward cone
criterion for quasi-isomorphisms, complementing the existing converse theorem.
-/

@[expose] public section
noncomputable section

section
open CategoryTheory CategoryTheory.Pretriangulated CochainComplex
namespace Quillen.HomologicalAlgebra
/-- The actual mapping cone of an original quasi-isomorphism is acyclic. -/
theorem mappingCone_acyclic_of_quasiIso {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (s : K ⟶ L) [QuasiIso s] : (mappingCone s).Acyclic := by
  let P := HomotopyCategory.subcategoryAcyclic A
  have hs := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2
    (show QuasiIso s from inferInstance)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hs
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    ((P.trW_iff_of_distinguished (mappingCone.triangleh s)
      (HomotopyCategory.mappingCone_triangleh_distinguished s)).1 hs)
end Quillen.HomologicalAlgebra
end
