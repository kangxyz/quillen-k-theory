/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.AffineExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.OverlapCompatibility
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedMorphisms
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
/-! # Actual perfect gluing from the original derived overlap isomorphism -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
open scoped ZeroObject
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
variable {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k]
  {A : CochainComplex U.Modules ℤ} {B : CochainComplex V.Modules ℤ} {L : CochainComplex X.Modules ℤ}

/-- A specified original derived overlap isomorphism, compatible with arbitrary
original local target maps, glues to actual local quasi-isomorphisms and strict
target triangles. Those local comparisons realize precisely the original isomorphism. -/
theorem exists_perfect_glue_of_derived_overlap_immersions
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) (hA : locallyPerfect U A) (hB :
      locallyPerfect V B)
    (e : (DerivedCategory.Q (C := (pullback j k).Modules)).obj ((restrict (pullback.fst j k)).obj A)
      ≅
      (DerivedCategory.Q (C := (pullback j k).Modules)).obj ((restrict (pullback.snd j k)).obj B))
    (p : A ⟶ (restrict j).obj L) (q : B ⟶ (restrict k).obj L)
    (he : (DerivedCategory.Q (C := (pullback j k).Modules)).map
      ((restrict (pullback.fst j k)).map p) =
      e.hom ≫ (DerivedCategory.Q (C := (pullback j k).Modules)).map
        ((restrict (pullback.snd j k)).map q ≫
          (openSquareRestrictIso (pullback.snd j k) (pullback.fst j k)
            k j pullback.condition.symm).hom.app L)) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      ∃ (u : A ⟶ (restrict j).obj P) (v : B ⟶ (restrict k).obj P) (d : P ⟶ L),
        QuasiIso u ∧ QuasiIso v ∧
        u ≫ (restrict j).map d = p ∧ v ≫ (restrict k).map d = q ∧
        (DerivedCategory.Q (C := (pullback j k).Modules)).map ((restrict (pullback.fst j k)).map u)
          =
          e.hom ≫ (DerivedCategory.Q (C := (pullback j k).Modules)).map
            ((restrict (pullback.snd j k)).map v ≫
              (openSquareRestrictIso (pullback.snd j k) (pullback.fst j k)
                k j pullback.condition.symm).hom.app P) := by
  let W := pullback j k
  let a := pullback.fst j k
  let b := pullback.snd j k
  let : HasDerivedCategory.{u+1} W.Modules := HasDerivedCategory.standard _
  obtain ⟨K, α, β, hα, hβ, hfac, ⟨H⟩⟩ :=
    Quillen.CochainComplex.exists_weak_span_homotopy_of_derived_iso e
      ((restrict a).map p) ((restrict b).map q ≫
        (openSquareRestrictIso b a k j pullback.condition.symm).hom.app L) he
  have H' : Homotopy (α ≫ (restrict a).map p)
      (β ≫ (restrict b).map q ≫
        (openSquareRestrictIso b a k j pullback.condition.symm).hom.app L) := by
    simpa only [Category.assoc] using H
  let P := glued a b j k pullback.condition α β
  let u := first a b j k pullback.condition α β
  let v := second a b j k pullback.condition α β
  have hu : QuasiIso u := first_quasiIso a b j k pullback.condition α β
    (by intro x hx; rw [IsOpenImmersion.range_pullbackFst]; exact hx)
  have hv : QuasiIso v := second_quasiIso a b j k pullback.condition α β
    (by intro x hx; rw [IsOpenImmersion.range_pullbackSnd]; exact hx)
  refine ⟨P, locallyPerfect_of_two_openImmersions j k hcover
    ((locallyPerfect_iff_of_quasiIso u).mp hA) ((locallyPerfect_iff_of_quasiIso v).mp hB),
    u, v, desc a b j k pullback.condition α β p q H', hu, hv,
    first_desc a b j k pullback.condition α β p q H',
    second_desc a b j k pullback.condition α β p q H', ?_⟩
  apply (cancel_epi ((DerivedCategory.Q (C := W.Modules)).map α)).mp
  rw [← Category.assoc]
  change (DerivedCategory.Q (C := W.Modules)).map α ≫ (DerivedCategory.Q (C := W.Modules)).map
    ((restrict a).map u) =
    ((DerivedCategory.Q (C := W.Modules)).map α ≫ e.hom) ≫ (DerivedCategory.Q (C := W.Modules)).map
      ((restrict b).map v ≫
        (openSquareRestrictIso b a k j pullback.condition.symm).hom.app P)
  change (DerivedCategory.Q (C := W.Modules)).map α ≫ e.hom =
    (DerivedCategory.Q (C := W.Modules)).map β at hfac
  rw [hfac]
  simpa only [W, a, b, P, u, v, Functor.map_comp, Category.assoc] using
    DerivedCategory.Q_map_eq_of_homotopy _ (overlapHomotopy a b j k pullback.condition α β)

/-- Arbitrary compatible original derived target morphisms admit one actual
perfect global source and one actual chain map, recovering the given overlap
isomorphism and both original derived target morphisms. -/
theorem exists_perfect_glue_of_derived_target_immersions
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) (hA : locallyPerfect U A) (hB :
      locallyPerfect V B)
    (e : (DerivedCategory.Q (C := (pullback j k).Modules)).obj ((restrict (pullback.fst j k)).obj A)
      ≅
      (DerivedCategory.Q (C := (pullback j k).Modules)).obj ((restrict (pullback.snd j k)).obj B))
    (φ : (DerivedCategory.Q (C := U.Modules)).obj A ⟶ (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj L))
    (ψ : (DerivedCategory.Q (C := V.Modules)).obj B ⟶ (DerivedCategory.Q (C := V.Modules)).obj
      ((restrict k).obj L))
    (he : restrictDerivedHom (pullback.fst j k) φ =
      e.hom ≫ restrictDerivedHom (pullback.snd j k) ψ ≫
        (DerivedCategory.Q (C := (pullback j k).Modules)).map
          ((openSquareRestrictIso (pullback.snd j k) (pullback.fst j k)
            k j pullback.condition.symm).hom.app L)) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      ∃ (u : (DerivedCategory.Q (C := U.Modules)).obj A ≅
          (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P))
        (v : (DerivedCategory.Q (C := V.Modules)).obj B ≅
          (DerivedCategory.Q (C := V.Modules)).obj ((restrict k).obj P)) (d : P ⟶ L),
        u.hom ≫ (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map d) = φ ∧
        v.hom ≫ (DerivedCategory.Q (C := V.Modules)).map ((restrict k).map d) = ψ ∧
        restrictDerivedHom (pullback.fst j k) u.hom =
          e.hom ≫ restrictDerivedHom (pullback.snd j k) v.hom ≫
            (DerivedCategory.Q (C := (pullback j k).Modules)).map
              ((openSquareRestrictIso (pullback.snd j k) (pullback.fst j k)
                k j pullback.condition.symm).hom.app P) := by
  let W := pullback j k
  let a := pullback.fst j k
  let b := pullback.snd j k
  let Q := DerivedCategory.Q (C := W.Modules)
  let c := openSquareRestrictIso b a k j pullback.condition.symm
  obtain ⟨A', s, hDenIso2, p, hFac2⟩ := DerivedCategory.right_fac φ
  have hs : QuasiIso s :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hDenIso2
  have hp : DerivedCategory.Q.map s ≫ (φ) = DerivedCategory.Q.map p := by
    let := hDenIso2
    rw [hFac2, IsIso.hom_inv_id_assoc]
  obtain ⟨B', t, hDenIso1, q, hFac1⟩ := DerivedCategory.right_fac ψ
  have ht : QuasiIso t :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).1 hDenIso1
  have hq : DerivedCategory.Q.map t ≫ (ψ) = DerivedCategory.Q.map q := by
    let := hDenIso1
    rw [hFac1, IsIso.hom_inv_id_assoc]
  let e' : Q.obj ((restrict a).obj A') ≅ Q.obj ((restrict b).obj B') :=
    asIso (Q.map ((restrict a).map s)) ≪≫ e ≪≫
      (asIso (Q.map ((restrict b).map t))).symm
  have hp' : Q.map ((restrict a).map s) ≫ restrictDerivedHom a φ =
      Q.map ((restrict a).map p) := by
    simpa only [restrictDerivedHom_comp, restrictDerivedHom_map] using
      congrArg (restrictDerivedHom a) hp
  have hq' : Q.map ((restrict b).map t) ≫ restrictDerivedHom b ψ =
      Q.map ((restrict b).map q) := by
    simpa only [restrictDerivedHom_comp, restrictDerivedHom_map] using
      congrArg (restrictDerivedHom b) hq
  have he' : Q.map ((restrict a).map p) =
      e'.hom ≫ Q.map ((restrict b).map q ≫ c.hom.app L) := by
    rw [Functor.map_comp, ← hp', he, ← hq']
    simp [e', Category.assoc, Q, c, a, b, W]
  obtain ⟨P, hP, u', v', d, hu', hv', hpu, hqv, heu⟩ :=
    exists_perfect_glue_of_derived_overlap_immersions j k hcover
      ((locallyPerfect_iff_of_quasiIso s).mpr hA)
      ((locallyPerfect_iff_of_quasiIso t).mpr hB) e' p q he'
  let u : (DerivedCategory.Q (C := U.Modules)).obj A ≅
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P) :=
    (asIso ((DerivedCategory.Q (C := U.Modules)).map s)).symm ≪≫
      asIso ((DerivedCategory.Q (C := U.Modules)).map u')
  let v : (DerivedCategory.Q (C := V.Modules)).obj B ≅
      (DerivedCategory.Q (C := V.Modules)).obj ((restrict k).obj P) :=
    (asIso ((DerivedCategory.Q (C := V.Modules)).map t)).symm ≪≫
      asIso ((DerivedCategory.Q (C := V.Modules)).map v')
  refine ⟨P, hP, u, v, d, ?_, ?_, ?_⟩
  · change (inv ((DerivedCategory.Q (C := U.Modules)).map s) ≫
      (DerivedCategory.Q (C := U.Modules)).map u') ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, hpu, ← hp]
    simp
  · change (inv ((DerivedCategory.Q (C := V.Modules)).map t) ≫
      (DerivedCategory.Q (C := V.Modules)).map v') ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, hqv, ← hq]
    simp
  · have h := congrArg (fun f ↦ inv (Q.map ((restrict a).map s)) ≫ f) heu
    simpa only [u, v, e', Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      restrictDerivedHom_comp, restrictDerivedHom_inv_map, restrictDerivedHom_map,
      Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc] using h


end Quillen.PerfectComplexes.OpenHomotopyGluing
