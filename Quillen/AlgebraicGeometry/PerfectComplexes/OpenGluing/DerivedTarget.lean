/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRightFractions
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.Derived

/-! # Perfect gluing with prescribed original derived target morphisms

Actual weak source denominators represent both local derived morphisms. Their
conjugated overlap isomorphism is passed to the original cone gluing construction.
The resulting actual global map recovers both specified morphisms and the
specified overlap isomorphism at the original local derived objects.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
variable {X : Scheme.{u}} (U V : X.Opens)
  {A : Complex U.toScheme} {B : Complex V.toScheme} {L : Complex X}

/-- Arbitrary compatible original derived target morphisms admit one actual
perfect global source and one actual chain map, recovering the given overlap
isomorphism and both original derived target morphisms. -/
theorem exists_perfect_glue_of_derived_target
    (hUV : U ⊔ V = ⊤) (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    (e : (toDerived (pullback U.ι V.ι)).obj ((restrict (pullback.fst U.ι V.ι)).obj A) ≅
      (toDerived (pullback U.ι V.ι)).obj ((restrict (pullback.snd U.ι V.ι)).obj B))
    (φ : (toDerived U.toScheme).obj A ⟶ (toDerived U.toScheme).obj ((restrict U.ι).obj L))
    (ψ : (toDerived V.toScheme).obj B ⟶ (toDerived V.toScheme).obj ((restrict V.ι).obj L))
    (he : restrictDerivedHom (pullback.fst U.ι V.ι) φ =
      e.hom ≫ restrictDerivedHom (pullback.snd U.ι V.ι) ψ ≫
        (toDerived (pullback U.ι V.ι)).map
          ((openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
            V.ι U.ι pullback.condition.symm).hom.app L)) :
    ∃ P : Complex X, locallyPerfect X P ∧
      ∃ (u : (toDerived U.toScheme).obj A ≅
          (toDerived U.toScheme).obj ((restrict U.ι).obj P))
        (v : (toDerived V.toScheme).obj B ≅
          (toDerived V.toScheme).obj ((restrict V.ι).obj P)) (d : P ⟶ L),
        u.hom ≫ (toDerived U.toScheme).map ((restrict U.ι).map d) = φ ∧
        v.hom ≫ (toDerived V.toScheme).map ((restrict V.ι).map d) = ψ ∧
        restrictDerivedHom (pullback.fst U.ι V.ι) u.hom =
          e.hom ≫ restrictDerivedHom (pullback.snd U.ι V.ι) v.hom ≫
            (toDerived (pullback U.ι V.ι)).map
              ((openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
                V.ι U.ι pullback.condition.symm).hom.app P) := by
  let W := pullback U.ι V.ι
  let a := pullback.fst U.ι V.ι
  let b := pullback.snd U.ι V.ι
  let Q := toDerived W
  let c := openSquareRestrictIso b a V.ι U.ι pullback.condition.symm
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
    exists_perfect_glue_of_derived_overlap U V hUV
      ((locallyPerfect_iff_of_quasiIso s).mpr hA)
      ((locallyPerfect_iff_of_quasiIso t).mpr hB) e' p q he'
  let u : (toDerived U.toScheme).obj A ≅
      (toDerived U.toScheme).obj ((restrict U.ι).obj P) :=
    (asIso ((toDerived U.toScheme).map s)).symm ≪≫
      asIso ((toDerived U.toScheme).map u')
  let v : (toDerived V.toScheme).obj B ≅
      (toDerived V.toScheme).obj ((restrict V.ι).obj P) :=
    (asIso ((toDerived V.toScheme).map t)).symm ≪≫
      asIso ((toDerived V.toScheme).map v')
  refine ⟨P, hP, u, v, d, ?_, ?_, ?_⟩
  · change (inv ((toDerived U.toScheme).map s) ≫ (toDerived U.toScheme).map u') ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, hpu, ← hp]
    simp
  · change (inv ((toDerived V.toScheme).map t) ≫ (toDerived V.toScheme).map v') ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, hqv, ← hq]
    simp
  · have h := congrArg (fun f ↦ inv (Q.map ((restrict a).map s)) ≫ f) heu
    simpa only [u, v, e', Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      restrictDerivedHom_comp, restrictDerivedHom_inv_map, restrictDerivedHom_map,
      Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc] using h

/-- The actual global target map is weak precisely when both prescribed
local derived target morphisms are invertible. -/
theorem quasiIso_iff_of_derived_target
    (hUV : U ⊔ V = ⊤) {P : Complex X}
    (u : (toDerived U.toScheme).obj A ≅ (toDerived U.toScheme).obj ((restrict U.ι).obj P))
    (v : (toDerived V.toScheme).obj B ≅ (toDerived V.toScheme).obj ((restrict V.ι).obj P))
    (d : P ⟶ L)
    (φ : (toDerived U.toScheme).obj A ⟶ (toDerived U.toScheme).obj ((restrict U.ι).obj L))
    (ψ : (toDerived V.toScheme).obj B ⟶ (toDerived V.toScheme).obj ((restrict V.ι).obj L))
    (hφ : u.hom ≫ (toDerived U.toScheme).map ((restrict U.ι).map d) = φ)
    (hψ : v.hom ≫ (toDerived V.toScheme).map ((restrict V.ι).map d) = ψ) :
    QuasiIso d ↔ IsIso φ ∧ IsIso ψ := by
  constructor
  · intro hd
    let := hd
    rw [← hφ, ← hψ]
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hφi, hψi⟩
    have hu : IsIso ((toDerived U.toScheme).map ((restrict U.ι).map d)) := by
      have : IsIso (u.hom ≫ (toDerived U.toScheme).map ((restrict U.ι).map d)) := hφ ▸ hφi
      exact IsIso.of_isIso_comp_left u.hom _
    have hv : IsIso ((toDerived V.toScheme).map ((restrict V.ι).map d)) := by
      have : IsIso (v.hom ≫ (toDerived V.toScheme).map ((restrict V.ι).map d)) := hψ ▸ hψi
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
