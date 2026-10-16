/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalImageExtensions
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives

/-! Semantic consumers of genuine principal strict weak-image closure. -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open HomologicalComplex Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
namespace QuillenTest.PrincipalStrictImageClosure

open Quillen

/-- Even when the actual localized chain map is not supplied as the localization
of a global map, its literal cone has a global strict restriction witness. -/
theorem actual_local_cone_extension (R : CommRingCat.{u}) (r : R)
    {P K : ModuleComplex R} (hP : moduleStrictPerfect R P) (hK : moduleStrictPerfect R K)
    (f : (localize r (.up ℤ)).obj P ⟶ (localize r (.up ℤ)).obj K) :
    ∃ N : ModuleComplex R, moduleStrictPerfect R N ∧
      ∃ q : (localize r (.up ℤ)).obj N ⟶ CochainComplex.mappingCone f, QuasiIso q := by
  have h : principalModuleDerivedImage R r (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) :=
    (principalModuleDerivedImage R r).ext_of_isTriangulatedClosed₃
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))
      (DerivedCategory.mappingCone_triangle_distinguished f)
      ⟨P, hP, ⟨Iso.refl _⟩⟩ ⟨K, hK, ⟨Iso.refl _⟩⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  have : CochainComplex.IsKProjective ((localize r (.up ℤ)).obj N) :=
    isKProjective_of_moduleStrictPerfect _ (moduleStrictPerfect_localize R r hN)
  obtain ⟨q, hq⟩ := _root_.CochainComplex.exists_chain_representative_of_isKProjective e.hom
  have : IsIso (DerivedCategory.Q.map q) := by rw [hq]; infer_instance
  exact ⟨N, hN, q, (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).mp inferInstance⟩

/-- A weak arrow pointing away from the requested target still yields an
actual original restriction witness into that target, in every homology degree. -/
theorem actual_backward_weak_witness (R : CommRingCat.{u}) (r : R)
    {A B : StrictPerfect (Spec (.of (Localization.Away r)))} (f : A ⟶ B)
    (hf : (strictWaldhausen _).weq f)
    (hB : Quillen.Waldhausen.ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) B) :
    ∃ (E : StrictPerfect (Spec R))
      (q : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E.obj ⟶
        A.obj),
      ∀ n, IsIso (homologyMap q n) := by
  obtain ⟨E, q, hq⟩ := (principal_strict_image_iff_of_weak R r f hf).mpr hB
  have : QuasiIso q.hom := hq
  exact ⟨E, q.hom, fun _ => inferInstance⟩

/-- The middle object in the original cofibration quotient square has an
actual original strict restriction witness with all original homology maps invertible. -/
theorem actual_quotient_square_extension (R : CommRingCat.{u}) (r : R)
    {A B Q : StrictPerfect (Spec (.of (Localization.Away r)))} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (strictWaldhausen _).cof i)
    (h : IsPushout i ((strictWaldhausen _).isZero.from_ A) q ((strictWaldhausen _).isZero.to_ Q))
    (hA : Quillen.Waldhausen.ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) A)
    (hQ : Quillen.Waldhausen.ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) Q) :
    ∃ (E : StrictPerfect (Spec R))
      (p : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E.obj ⟶
        B.obj),
      ∀ n, IsIso (homologyMap p n) := by
  obtain ⟨E, p, hp⟩ := principal_strict_image_extension R r hi h hA hQ
  have : QuasiIso p.hom := hp
  exact ⟨E, p.hom, fun _ => inferInstance⟩

/-- The quotient adapter retains the original two arrows and permits an
arbitrary actual zero object and independent category universes. -/
theorem actual_zero_pushout_quotient {C : Type u} [Category.{v} C] [Abelian C]
    {A B Z Q : C} {i : A ⟶ B} {f : A ⟶ Z} {q : B ⟶ Q} {g : Z ⟶ Q}
    [Mono i] (hZ : IsZero Z) (h : IsPushout i f q g) :
    Epi q ∧ ∃ w : i ≫ q = 0, (ShortComplex.mk i q w).Exact := by
  obtain ⟨w, hw⟩ := Quillen.Abelian.shortExact_of_mono_pushout_zero hZ h
  exact ⟨hw.epi_g, w, hw.exact⟩

end QuillenTest.PrincipalStrictImageClosure
