/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.AffineKernel

/-!
# The genuine closed-unit kernel is exactly ideal multiplication

The previous exponent proof only needed inclusion in I M. Exactness and
annihilation of the genuine closed target give the reverse inclusion too.
Thus the unit-kernel filtration is locally the actual ideal-power filtration.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme.ClosedImmersion.General
open FiniteModuleLocalization.IdealClosedSupport
variable {Z : Scheme.{u}} [IsLocallyNoetherian Z]
  (R : CommRingCat.{u}) [IsNoetherianRing R]
  (i : Z ⟶ Spec R) [IsClosedImmersion i]
  (I : Ideal R) (e : Z ≅ Spec (Ideal.closedRing R I))
  (hi : i = e.hom ≫ Ideal.closedMap R I)

include e hi in
/-- On actual finite global sections, the image of the genuine unit-kernel
inclusion is precisely the actual submodule I M. -/
theorem kernelUnit_range_eq_idealProduct (M : FiniteTypeSheaves (Spec R)) :
    LinearMap.range (((finiteTypeSheavesSpecModuleEquivalence R).functor.map
      (kernel.ι ((coherentAdjunction i).unit.app M))).hom.hom) =
        idealProduct I ((finiteTypeSheavesSpecModuleEquivalence R).functor.obj M) := by
  let F := (finiteTypeSheavesSpecModuleEquivalence R).functor
  let η := (coherentAdjunction i).unit.app M
  let f := F.map (kernel.ι η)
  let q := F.map η
  have htarget : killedBy I (F.obj ((coherentPushforward i).obj ((coherentPullback i).obj M))) :=
    (coherentPushforward_essImage_iff R i I e hi _).mp
      ((coherentPushforward i).obj_mem_essImage _)
  have hS : (ShortComplex.kernelSequence η).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact η,
      epi_g := coherentAdjunction_affine_unit_epi R i M }
  have hS' := (hS.map_of_exact F).map_of_exact (forget₂ (FGModuleCat R) (ModuleCat R))
  have he : Function.Exact f.hom.hom q.hom.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS'.exact
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact kernelUnit_section_mem_idealProduct R i I e hi M x
  · intro hy
    have hq : q.hom.hom y = 0 := by
      refine Submodule.smul_induction_on hy (fun r hr m _ ↦ ?_)
        (fun x y hx hy ↦ by simp only [map_add, hx, hy, zero_add])
      rw [q.hom.hom.map_smul]
      exact htarget r hr _
    exact (he y).mp hq

end Quillen.CoherentScheme.ClosedImmersion.General
