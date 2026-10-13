/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Cartesian products of modules

The categorical product is identified with the literal Cartesian module, preserving both
projections.
-/

@[expose] public section

section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace ModuleCat
variable {R : Type u} [Ring R] (M N : ModuleCat.{v} R)

/-- The categorical product identified with the literal Cartesian module. -/
def prodIsoCartesian : M ⨯ N ≅ ModuleCat.of R (M × N) :=
  (biprod.isoProd M N).symm ≪≫ biprodIsoProd M N

/-- The Cartesian comparison preserves the first projection. -/
theorem prodIsoCartesian_hom_fst :
    (prodIsoCartesian M N).hom ≫ ofHom (LinearMap.fst R M N) = prod.fst := by
  rw [← biprodIsoProd_inv_comp_fst, prodIsoCartesian, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, biprod.isoProd_inv, biprod.lift_fst]

/-- The Cartesian comparison preserves the second projection. -/
theorem prodIsoCartesian_hom_snd :
    (prodIsoCartesian M N).hom ≫ ofHom (LinearMap.snd R M N) = prod.snd := by
  rw [← biprodIsoProd_inv_comp_snd, prodIsoCartesian, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, biprod.isoProd_inv, biprod.lift_snd]
/-- The linear signed pair map is the difference of the original categorical composites. -/
theorem ofHom_pairDifference {M N P : ModuleCat.{v} R} (p : M ⟶ P) (q : N ⟶ P) :
    ofHom (p.hom.comp (LinearMap.fst R M N) - q.hom.comp (LinearMap.snd R M N)) =
      ofHom (LinearMap.fst R M N) ≫ p - ofHom (LinearMap.snd R M N) ≫ q := rfl

end ModuleCat
end

end
