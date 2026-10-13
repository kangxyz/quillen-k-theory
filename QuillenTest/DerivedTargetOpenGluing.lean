/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.DerivedTarget

/-! # Consumers of original derived-target perfect gluing -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.OpenHomotopyGluing
universe u
namespace QuillenTest.DerivedTargetOpenGluing

/-- The actual weak denominator remains a right fraction after any open restriction. -/
theorem original_fraction_restricts {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {K L : Complex X} (φ : (toDerived X).obj K ⟶ (toDerived X).obj L) :
    ∃ (M : Complex X) (s : M ⟶ K) (p : M ⟶ L), QuasiIso s ∧
      (toDerived Y).map ((restrict j).map s) ≫ restrictDerivedHom j φ =
        (toDerived Y).map ((restrict j).map p) := by
  obtain ⟨M, s, p, hs, hp⟩ := toDerived_right_fraction φ
  exact ⟨M, s, p, hs, by simpa using congrArg (restrictDerivedHom j) hp⟩

variable {X : Scheme.{u}} (U V : X.Opens)
  {A : Complex U.toScheme} {B : Complex V.toScheme} {L : Complex X}
  (hUV : U ⊔ V = ⊤) (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
  (e : (toDerived (pullback U.ι V.ι)).obj ((restrict (pullback.fst U.ι V.ι)).obj A) ≅
    (toDerived (pullback U.ι V.ι)).obj ((restrict (pullback.snd U.ι V.ι)).obj B))
  (φ : (toDerived U.toScheme).obj A ⟶ (toDerived U.toScheme).obj ((restrict U.ι).obj L))
  (ψ : (toDerived V.toScheme).obj B ⟶ (toDerived V.toScheme).obj ((restrict V.ι).obj L))
  (he : restrictDerivedHom (pullback.fst U.ι V.ι) φ =
    e.hom ≫ restrictDerivedHom (pullback.snd U.ι V.ι) ψ ≫
      (toDerived (pullback U.ι V.ι)).map
        ((openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
          V.ι U.ι pullback.condition.symm).hom.app L))

include hUV hA hB he in
/-- Both prescribed maps are recovered from one actual global chain map. -/
theorem both_original_target_maps_recovered :
    ∃ (P : Complex X) (_ : locallyPerfect X P) (d : P ⟶ L)
      (u : (toDerived U.toScheme).obj A ≅ (toDerived U.toScheme).obj ((restrict U.ι).obj P))
      (v : (toDerived V.toScheme).obj B ≅ (toDerived V.toScheme).obj ((restrict V.ι).obj P)),
      (toDerived U.toScheme).map ((restrict U.ι).map d) = u.inv ≫ φ ∧
      (toDerived V.toScheme).map ((restrict V.ι).map d) = v.inv ≫ ψ := by
  obtain ⟨P, hP, u, v, d, hp, hq, _⟩ :=
    exists_perfect_glue_of_derived_target U V hUV hA hB e φ ψ he
  refine ⟨P, hP, d, u, v, ?_, ?_⟩
  · rw [← hp, u.inv_hom_id_assoc]
  · rw [← hq, v.inv_hom_id_assoc]

include hUV hA hB he in
/-- The original transition is recovered as an equality of complete derived isomorphisms. -/
theorem original_transition_iso_recovered :
    ∃ (P : Complex X) (_ : locallyPerfect X P)
      (u : (toDerived U.toScheme).obj A ≅ (toDerived U.toScheme).obj ((restrict U.ι).obj P))
      (v : (toDerived V.toScheme).obj B ≅ (toDerived V.toScheme).obj ((restrict V.ι).obj P)),
      e = restrictDerivedIso (pullback.fst U.ι V.ι) u ≪≫
        (restrictDerivedIso (pullback.snd U.ι V.ι) v ≪≫
          (toDerived (pullback U.ι V.ι)).mapIso
            ((openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
              V.ι U.ι pullback.condition.symm).app P)).symm := by
  obtain ⟨P, hP, u, v, d, _, _, h⟩ :=
    exists_perfect_glue_of_derived_target U V hUV hA hB e φ ψ he
  refine ⟨P, hP, u, v, ?_⟩
  apply Iso.ext
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv]
  rw [restrictDerivedIso_hom, h]
  simp [Category.assoc, ← restrictDerivedIso_hom]
  rw [restrictDerivedIso_hom, ← restrictDerivedHom_comp, v.hom_inv_id,
    restrictDerivedHom_id, Category.comp_id]

include hUV hA hB he in
/-- Invertible prescribed local derived maps give an actual global quasi-isomorphism. -/
theorem invertible_targets_give_original_weak_map [IsIso φ] [IsIso ψ] :
    ∃ (P : Complex X) (_ : locallyPerfect X P) (d : P ⟶ L), QuasiIso d := by
  obtain ⟨P, hP, u, v, d, hp, hq, _⟩ :=
    exists_perfect_glue_of_derived_target U V hUV hA hB e φ ψ he
  exact ⟨P, hP, d,
    (quasiIso_iff_of_derived_target U V hUV u v d φ ψ hp hq).mpr ⟨inferInstance, inferInstance⟩⟩

end QuillenTest.DerivedTargetOpenGluing
