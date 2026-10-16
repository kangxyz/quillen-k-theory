/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Algebra.ModuleComplex.PrincipalProjectiveDescent
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalFreeExtension
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedMorphisms
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
/-!
# Actual principal-open strict extension up to a shift

Every strict-perfect complex on an affine principal open, with genuinely
finite-projective section terms, extends after adjoining its original shift.
The comparison is an actual chain-homotopy equivalence from the original
geometric restriction. In particular the original target is an explicit
homotopy retract, and a literal retract in the original ambient sheaf derived
category. Arbitrary rings are allowed; this does not assert extension of the
unstabilized target, global strictification, or Thomason–Trobaugh cofinality.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization

/-- Every strict-perfect target on an affine principal open extends after adding
its original shift, up to an actual chain-homotopy equivalence. -/
theorem exists_principal_strict_extension_after_shift (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    ∃ Q : StrictPerfect (Spec R), Nonempty
      (HomotopyEquiv ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
        r)).obj Q.obj)
        (P.obj ⊞ P.obj⟦(1 : ℤ)⟧)) := by
  let S := CommRingCat.of (Localization.Away r)
  let : (tilde.functor S).Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor
  let : (associatedComplex S).Additive := inferInstance
  let : PreservesBinaryBiproducts (associatedComplex S) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts (associatedComplex S)
  let K := (sectionsComplex S).obj P.obj
  have hK := moduleStrictPerfect_sections S P.property
  obtain ⟨a, b, hb⟩ := hK.1
  obtain ⟨Q, hQbound, hQfree, ⟨eQ⟩⟩ :=
    exists_bounded_finiteFree_stable_descent r K a b hb
      (fun i => (hK.2 i).1) (fun i => (hK.2 i).2)
  have hQ : moduleStrictPerfect R Q := by
    refine ⟨⟨a - 1, b, hQbound⟩, fun i => ?_⟩
    let := (hQfree i).1
    exact ⟨(hQfree i).2, inferInstance⟩
  let eP : (associatedComplex S).obj K ≅ P.obj := associatedSectionsIso S P.property
  let eSum : (associatedComplex S).obj (K ⊞ K⟦(1 : ℤ)⟧) ≅
      (P.obj ⊞ P.obj⟦(1 : ℤ)⟧) :=
    (associatedComplex S).mapBiprod _ _ ≪≫ biprod.mapIso eP
      (((associatedComplex S).commShiftIso (1 : ℤ)).app K ≪≫
        (shiftFunctor _ (1 : ℤ)).mapIso eP)
  refine ⟨⟨(associatedComplex R).obj Q, strictPerfect_associated R hQ⟩, ⟨?_⟩⟩
  exact ((HomotopyEquiv.ofIso ((principalRestrictionAssociatedComplexIso R r).app Q).symm).trans
    ((tilde.functor S).mapHomotopyEquiv eQ)).trans (HomotopyEquiv.ofIso eSum)

/-- The original target is an actual homotopy retract of a restricted strict
complex. This is density up to summands, with explicit geometric chain maps. -/
theorem exists_principal_strict_homotopy_retract (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    ∃ (Q : StrictPerfect (Spec R))
      (i : P.obj ⟶ (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
        Q.obj)
      (p : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj Q.obj ⟶
        P.obj),
      Nonempty (Homotopy (i ≫ p) (𝟙 P.obj)) := by
  obtain ⟨Q, ⟨e⟩⟩ := exists_principal_strict_extension_after_shift R r P
  refine ⟨Q, biprod.inl ≫ e.inv, e.hom ≫ biprod.fst, ⟨?_⟩⟩
  simpa only [Category.assoc, Category.comp_id, Category.id_comp, biprod.inl_fst] using
    (e.homotopyInvHomId.compLeft (biprod.inl : P.obj ⟶ P.obj ⊞ P.obj⟦(1 : ℤ)⟧)).compRight
      (biprod.fst : P.obj ⊞ P.obj⟦(1 : ℤ)⟧ ⟶ P.obj)

/-- The shift-sum lies in the actual derived essential image of original
strict restriction, with no freeness hypothesis on the original target. -/
theorem exists_principal_strict_derived_extension_after_shift (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    ∃ Q : StrictPerfect (Spec R), Nonempty
      ((DerivedCategory.Q).obj
        ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
        r)).obj Q.obj) ≅
        (DerivedCategory.Q).obj (P.obj ⊞ P.obj⟦(1 : ℤ)⟧)) := by
  obtain ⟨Q, ⟨e⟩⟩ := exists_principal_strict_extension_after_shift R r P
  exact ⟨Q, ⟨asIso ((DerivedCategory.Q).map e.hom)⟩⟩

/-- Every original strict target is a retract of an actual restricted strict
object in the original ambient sheaf derived category. -/
theorem exists_principal_strict_derived_retract (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    ∃ Q : StrictPerfect (Spec R), Nonempty
      (Retract ((DerivedCategory.Q).obj P.obj)
        ((DerivedCategory.Q).obj
          ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen
          R r)).obj Q.obj))) := by
  obtain ⟨Q, i, p, ⟨h⟩⟩ := exists_principal_strict_homotopy_retract R r P
  refine ⟨Q, ⟨⟨(DerivedCategory.Q).map i, (DerivedCategory.Q).map p, ?_⟩⟩⟩
  rw [← Functor.map_comp, DerivedCategory.Q_map_eq_of_homotopy _ h, CategoryTheory.Functor.map_id]

end Quillen.PerfectComplexes.Affine
