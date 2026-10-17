/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
public import Mathlib.CategoryTheory.Retract
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-!
# Actual perfect complements of original derived retracts

A literal derived retract between original perfect sheaf complexes has an
actual perfect complex complement on the same scheme. A genuine source fraction
represents the original retract inclusion; its literal cone is perfect, and
the actual split distinguished triangle gives the original complex biproduct.
The original retract inclusion is the original first-summand inclusion under
the resulting derived isomorphism. No idempotent-completeness premise,
quasi-compactness, or strict representative is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A literal original derived retract of perfect complexes has an actual
perfect complex complement. The actual cone of a fraction representative
supplies the complement; its inclusion retains the original retract map. -/
lemma exists_actual_perfect_complement_of_derived_retract {X : Scheme.{u}}
    {E P : CochainComplex X.Modules ℤ} (hE : locallyPerfect X E) (hP : locallyPerfect X P)
    (r : Retract ((DerivedCategory.Q (C := X.Modules)).obj E)
      ((DerivedCategory.Q (C := X.Modules)).obj P)) :
    ∃ (C : CochainComplex X.Modules ℤ), locallyPerfect X C ∧
      ∃ e : (DerivedCategory.Q (C := X.Modules)).obj P ≅ (DerivedCategory.Q (C := X.Modules)).obj
        (E ⊞ C),
        r.i ≫ e.hom = (DerivedCategory.Q (C := X.Modules)).map (biprod.inl : E ⟶ E ⊞ C) := by
  let : PreservesBinaryBiproducts (DerivedCategory.Q (C := X.Modules))
    := preservesBinaryBiproducts_of_preservesBiproducts
    _
  obtain ⟨M, s, hs, f, hfac⟩ := DerivedCategory.right_fac r.i
  have := hs
  have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).mp hs
  change r.i = inv ((DerivedCategory.Q (C := X.Modules)).map s) ≫
    (DerivedCategory.Q (C := X.Modules)).map f at hfac
  have hM : locallyPerfect X M := (locallyPerfect_iff_of_quasiIso s).mpr hE
  have hsf : (DerivedCategory.Q (C := X.Modules)).map s ≫ r.i =
    (DerivedCategory.Q (C := X.Modules)).map f := by
    rw [hfac, IsIso.hom_inv_id_assoc]
  have hret : (DerivedCategory.Q (C := X.Modules)).map f ≫
    (r.r ≫ inv ((DerivedCategory.Q (C := X.Modules)).map s)) = 𝟙 _ := by
    rw [← hsf, Category.assoc, r.retract_assoc, IsIso.hom_inv_id]
  have : IsSplitMono ((DerivedCategory.Q (C := X.Modules)).map f) := IsSplitMono.mk'
    ⟨r.r ≫ inv ((DerivedCategory.Q (C := X.Modules)).map s),
    hret⟩
  let T := (DerivedCategory.Q (C := X.Modules)).mapTriangle.obj
    (CochainComplex.mappingCone.triangle f)
  have hT : T ∈ distTriang (DerivedCategory X.Modules)
    := DerivedCategory.mappingCone_triangle_distinguished f
  have hz : T.mor₃ = 0 := T.mor₃_eq_zero_of_mono₁ hT (by
    change Mono ((DerivedCategory.Q (C := X.Modules)).map f)
    infer_instance)
  obtain ⟨e, he, _⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hz
  change (DerivedCategory.Q (C := X.Modules)).map f ≫ e.hom = biprod.inl at he
  let e' := e ≪≫ biprod.mapIso (asIso ((DerivedCategory.Q (C := X.Modules)).map s)) (Iso.refl _) ≪≫
    ((DerivedCategory.Q (C := X.Modules)).mapBiprod E (CochainComplex.mappingCone f)).symm
  refine ⟨CochainComplex.mappingCone f, locallyPerfect_mappingCone hM hP f, e', ?_⟩
  apply (cancel_epi ((DerivedCategory.Q (C := X.Modules)).map s)).mp
  dsimp only [e', Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hsf, ← Category.assoc, ← Category.assoc, he]
  apply (cancel_mono ((DerivedCategory.Q (C := X.Modules)).mapBiprod E
    (CochainComplex.mappingCone f)).hom).mp
  simp [← Functor.map_comp]

end Quillen.PerfectComplexes
