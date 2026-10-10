/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.AffineExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.OverlapCompatibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedMorphisms
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRightFractions

/-! # Actual perfect gluing from the original derived overlap isomorphism -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
open scoped ZeroObject
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
variable {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k]
  {A : Complex U} {B : Complex V} {L : Complex X}

/-- A specified original derived overlap isomorphism, compatible with arbitrary
original local target maps, glues to actual local quasi-isomorphisms and strict
target triangles. Those local comparisons realize precisely the original isomorphism. -/
theorem exists_perfect_glue_of_derived_overlap_immersions
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) (hA : locallyPerfect U A) (hB :
      locallyPerfect V B)
    (e : (toDerived (pullback j k)).obj ((restrict (pullback.fst j k)).obj A) ≅
      (toDerived (pullback j k)).obj ((restrict (pullback.snd j k)).obj B))
    (p : A ⟶ (restrict j).obj L) (q : B ⟶ (restrict k).obj L)
    (he : (toDerived (pullback j k)).map ((restrict (pullback.fst j k)).map p) =
      e.hom ≫ (toDerived (pullback j k)).map
        ((restrict (pullback.snd j k)).map q ≫
          (openSquareRestrictIso (pullback.snd j k) (pullback.fst j k)
            k j pullback.condition.symm).hom.app L)) :
    ∃ P : Complex X, locallyPerfect X P ∧
      ∃ (u : A ⟶ (restrict j).obj P) (v : B ⟶ (restrict k).obj P) (d : P ⟶ L),
        QuasiIso u ∧ QuasiIso v ∧
        u ≫ (restrict j).map d = p ∧ v ≫ (restrict k).map d = q ∧
        (toDerived (pullback j k)).map ((restrict (pullback.fst j k)).map u) =
          e.hom ≫ (toDerived (pullback j k)).map
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
  apply (cancel_epi ((toDerived W).map α)).mp
  rw [← Category.assoc]
  change (toDerived W).map α ≫ (toDerived W).map ((restrict a).map u) =
    ((toDerived W).map α ≫ e.hom) ≫ (toDerived W).map
      ((restrict b).map v ≫
        (openSquareRestrictIso b a k j pullback.condition.symm).hom.app P)
  change (toDerived W).map α ≫ e.hom = (toDerived W).map β at hfac
  rw [hfac]
  simpa only [W, a, b, P, u, v, Functor.map_comp, Category.assoc] using
    toDerived_map_eq_of_homotopy (overlapHomotopy a b j k pullback.condition α β)

/-- Arbitrary compatible original derived target morphisms admit one actual
perfect global source and one actual chain map, recovering the given overlap
isomorphism and both original derived target morphisms. -/
theorem exists_perfect_glue_of_derived_target_immersions
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) (hA : locallyPerfect U A) (hB :
      locallyPerfect V B)
    (e : (toDerived (pullback j k)).obj ((restrict (pullback.fst j k)).obj A) ≅
      (toDerived (pullback j k)).obj ((restrict (pullback.snd j k)).obj B))
    (φ : (toDerived U).obj A ⟶ (toDerived U).obj ((restrict j).obj L))
    (ψ : (toDerived V).obj B ⟶ (toDerived V).obj ((restrict k).obj L))
    (he : restrictDerivedHom (pullback.fst j k) φ =
      e.hom ≫ restrictDerivedHom (pullback.snd j k) ψ ≫
        (toDerived (pullback j k)).map
          ((openSquareRestrictIso (pullback.snd j k) (pullback.fst j k)
            k j pullback.condition.symm).hom.app L)) :
    ∃ P : Complex X, locallyPerfect X P ∧
      ∃ (u : (toDerived U).obj A ≅
          (toDerived U).obj ((restrict j).obj P))
        (v : (toDerived V).obj B ≅
          (toDerived V).obj ((restrict k).obj P)) (d : P ⟶ L),
        u.hom ≫ (toDerived U).map ((restrict j).map d) = φ ∧
        v.hom ≫ (toDerived V).map ((restrict k).map d) = ψ ∧
        restrictDerivedHom (pullback.fst j k) u.hom =
          e.hom ≫ restrictDerivedHom (pullback.snd j k) v.hom ≫
            (toDerived (pullback j k)).map
              ((openSquareRestrictIso (pullback.snd j k) (pullback.fst j k)
                k j pullback.condition.symm).hom.app P) := by
  let W := pullback j k
  let a := pullback.fst j k
  let b := pullback.snd j k
  let Q := toDerived W
  let c := openSquareRestrictIso b a k j pullback.condition.symm
  obtain ⟨A', s, p, hs, hp⟩ := toDerived_right_fraction φ
  obtain ⟨B', t, q, ht, hq⟩ := toDerived_right_fraction ψ
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
  let u : (toDerived U).obj A ≅
      (toDerived U).obj ((restrict j).obj P) :=
    (asIso ((toDerived U).map s)).symm ≪≫
      asIso ((toDerived U).map u')
  let v : (toDerived V).obj B ≅
      (toDerived V).obj ((restrict k).obj P) :=
    (asIso ((toDerived V).map t)).symm ≪≫
      asIso ((toDerived V).map v')
  refine ⟨P, hP, u, v, d, ?_, ?_, ?_⟩
  · change (inv ((toDerived U).map s) ≫ (toDerived U).map u') ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, hpu, ← hp]
    simp
  · change (inv ((toDerived V).map t) ≫ (toDerived V).map v') ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, hqv, ← hq]
    simp
  · have h := congrArg (fun f ↦ inv (Q.map ((restrict a).map s)) ≫ f) heu
    simpa only [u, v, e', Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      restrictDerivedHom_comp, restrictDerivedHom_inv_map, restrictDerivedHom_map,
      Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc] using h


end Quillen.PerfectComplexes.OpenHomotopyGluing
