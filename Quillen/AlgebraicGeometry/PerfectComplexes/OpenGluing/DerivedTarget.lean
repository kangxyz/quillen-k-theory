/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.Derived
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Perfect gluing with prescribed original derived target morphisms

Actual weak source denominators represent both local derived morphisms. Their
conjugated overlap isomorphism is passed to the original cone gluing construction.
The resulting actual global map recovers both specified morphisms and the
specified overlap isomorphism at the original local derived objects.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
variable {X : Scheme.{u}} (U V : X.Opens)
  {A : CochainComplex U.toScheme.Modules ℤ} {B : CochainComplex V.toScheme.Modules ℤ}
    {L : CochainComplex X.Modules ℤ}

/-- Arbitrary compatible original derived target morphisms admit one actual
perfect global source and one actual chain map, recovering the given overlap
isomorphism and both original derived target morphisms. -/
theorem exists_perfect_glue_of_derived_target
    (hUV : U ⊔ V = ⊤) (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    (e : (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
      ((restrict (pullback.fst U.ι V.ι)).obj A) ≅
      (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
        ((restrict (pullback.snd U.ι V.ι)).obj B))
    (φ : (DerivedCategory.Q (C := U.toScheme.Modules)).obj A ⟶
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj L))
    (ψ : (DerivedCategory.Q (C := V.toScheme.Modules)).obj B ⟶
      (DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj L))
    (he : restrictDerivedHom (pullback.fst U.ι V.ι) φ =
      e.hom ≫ restrictDerivedHom (pullback.snd U.ι V.ι) ψ ≫
        (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).map
          ((openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
            V.ι U.ι pullback.condition.symm).hom.app L)) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      ∃ (u : (DerivedCategory.Q (C := U.toScheme.Modules)).obj A ≅
          (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P))
        (v : (DerivedCategory.Q (C := V.toScheme.Modules)).obj B ≅
          (DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj P)) (d : P ⟶ L),
        u.hom ≫ (DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map d) = φ ∧
        v.hom ≫ (DerivedCategory.Q (C := V.toScheme.Modules)).map ((restrict V.ι).map d) = ψ ∧
        restrictDerivedHom (pullback.fst U.ι V.ι) u.hom =
          e.hom ≫ restrictDerivedHom (pullback.snd U.ι V.ι) v.hom ≫
            (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).map
              ((openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
                V.ι U.ι pullback.condition.symm).hom.app P) := by
  let W := pullback U.ι V.ι
  let a := pullback.fst U.ι V.ι
  let b := pullback.snd U.ι V.ι
  let Q := DerivedCategory.Q (C := W.Modules)
  let c := openSquareRestrictIso b a V.ι U.ι pullback.condition.symm
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
    exists_perfect_glue_of_derived_overlap U V hUV
      ((locallyPerfect_iff_of_quasiIso s).mpr hA)
      ((locallyPerfect_iff_of_quasiIso t).mpr hB) e' p q he'
  let u : (DerivedCategory.Q (C := U.toScheme.Modules)).obj A ≅
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P) :=
    (asIso ((DerivedCategory.Q (C := U.toScheme.Modules)).map s)).symm ≪≫
      asIso ((DerivedCategory.Q (C := U.toScheme.Modules)).map u')
  let v : (DerivedCategory.Q (C := V.toScheme.Modules)).obj B ≅
      (DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj P) :=
    (asIso ((DerivedCategory.Q (C := V.toScheme.Modules)).map t)).symm ≪≫
      asIso ((DerivedCategory.Q (C := V.toScheme.Modules)).map v')
  refine ⟨P, hP, u, v, d, ?_, ?_, ?_⟩
  · change (inv ((DerivedCategory.Q (C := U.toScheme.Modules)).map s) ≫
      (DerivedCategory.Q (C := U.toScheme.Modules)).map u') ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, hpu, ← hp]
    simp
  · change (inv ((DerivedCategory.Q (C := V.toScheme.Modules)).map t) ≫
      (DerivedCategory.Q (C := V.toScheme.Modules)).map v') ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, hqv, ← hq]
    simp
  · have h := congrArg (fun f ↦ inv (Q.map ((restrict a).map s)) ≫ f) heu
    simpa only [u, v, e', Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      restrictDerivedHom_comp, restrictDerivedHom_inv_map, restrictDerivedHom_map,
      Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc] using h

/-- The actual global target map is weak precisely when both prescribed
local derived target morphisms are invertible. -/
theorem quasiIso_iff_of_derived_target
    (hUV : U ⊔ V = ⊤) {P : CochainComplex X.Modules ℤ}
    (u : (DerivedCategory.Q (C := U.toScheme.Modules)).obj A ≅
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P))
    (v : (DerivedCategory.Q (C := V.toScheme.Modules)).obj B ≅
      (DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj P))
    (d : P ⟶ L)
    (φ : (DerivedCategory.Q (C := U.toScheme.Modules)).obj A ⟶
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj L))
    (ψ : (DerivedCategory.Q (C := V.toScheme.Modules)).obj B ⟶
      (DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj L))
    (hφ : u.hom ≫ (DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map d) = φ)
    (hψ : v.hom ≫ (DerivedCategory.Q (C := V.toScheme.Modules)).map ((restrict V.ι).map d) = ψ) :
    QuasiIso d ↔ IsIso φ ∧ IsIso ψ := by
  constructor
  · intro hd
    let := hd
    rw [← hφ, ← hψ]
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hφi, hψi⟩
    have hu : IsIso ((DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map d)) := by
      have : IsIso (u.hom ≫ (DerivedCategory.Q (C := U.toScheme.Modules)).map
        ((restrict U.ι).map d)) := hφ ▸ hφi
      exact IsIso.of_isIso_comp_left u.hom _
    have hv : IsIso ((DerivedCategory.Q (C := V.toScheme.Modules)).map ((restrict V.ι).map d)) := by
      have : IsIso (v.hom ≫ (DerivedCategory.Q (C := V.toScheme.Modules)).map
        ((restrict V.ι).map d)) := hψ ▸ hψi
      exact IsIso.of_isIso_comp_left v.hom _
    have huq : QuasiIso ((restrict U.ι).map d) := by
      let : HasDerivedCategory.{u+1} U.toScheme.Modules := HasDerivedCategory.standard _
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hu
    have hvq : QuasiIso ((restrict V.ι).map d) := by
      let : HasDerivedCategory.{u+1} V.toScheme.Modules := HasDerivedCategory.standard _
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hv
    apply quasiIso_of_openCover d (fun t : Bool => if t then U else V)
    · intro x
      have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
      rcases hx with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩
    · intro t
      cases t
      · exact hvq
      · exact huq

end Quillen.PerfectComplexes.OpenHomotopyGluing
