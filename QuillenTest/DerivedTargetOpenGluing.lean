/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.DerivedTarget
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
/-! # Consumers of original derived-target perfect gluing -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes.OpenHomotopyGluing
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.DerivedTargetOpenGluing

/-- The actual weak denominator remains a right fraction after any open restriction. -/
theorem original_fraction_restricts {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {K L : CochainComplex X.Modules ℤ} (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L) :
    ∃ (M : CochainComplex X.Modules ℤ) (s : M ⟶ K) (p : M ⟶ L), QuasiIso s ∧
      (DerivedCategory.Q (C := Y.Modules)).map ((restrict j).map s) ≫ restrictDerivedHom j φ =
        (DerivedCategory.Q (C := Y.Modules)).map ((restrict j).map p) := by
  obtain ⟨M, s, hDenIso1, p, hFac1⟩ := DerivedCategory.right_fac φ
  have hs : QuasiIso s :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hDenIso1
  have hp : DerivedCategory.Q.map s ≫ (φ) = DerivedCategory.Q.map p := by
    letI := hDenIso1
    rw [hFac1, IsIso.hom_inv_id_assoc]
  exact ⟨M, s, p, hs, by simpa using congrArg (restrictDerivedHom j) hp⟩

variable {X : Scheme.{u}} (U V : X.Opens)
  {A : CochainComplex U.toScheme.Modules ℤ} {B : CochainComplex V.toScheme.Modules ℤ}
    {L : CochainComplex X.Modules ℤ}
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
          V.ι U.ι pullback.condition.symm).hom.app L))

include hUV hA hB he in
/-- Both prescribed maps are recovered from one actual global chain map. -/
theorem both_original_target_maps_recovered :
    ∃ (P : CochainComplex X.Modules ℤ) (_ : locallyPerfect X P) (d : P ⟶ L)
      (u : (DerivedCategory.Q (C := U.toScheme.Modules)).obj A ≅
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P))
      (v : (DerivedCategory.Q (C := V.toScheme.Modules)).obj B ≅
        (DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj P)),
      (DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map d) = u.inv ≫ φ ∧
      (DerivedCategory.Q (C := V.toScheme.Modules)).map ((restrict V.ι).map d) = v.inv ≫ ψ := by
  obtain ⟨P, hP, u, v, d, hp, hq, _⟩ :=
    exists_perfect_glue_of_derived_target U V hUV hA hB e φ ψ he
  refine ⟨P, hP, d, u, v, ?_, ?_⟩
  · rw [← hp, u.inv_hom_id_assoc]
  · rw [← hq, v.inv_hom_id_assoc]

include hUV hA hB he in
/-- The original transition is recovered as an equality of complete derived isomorphisms. -/
theorem original_transition_iso_recovered :
    ∃ (P : CochainComplex X.Modules ℤ) (_ : locallyPerfect X P)
      (u : (DerivedCategory.Q (C := U.toScheme.Modules)).obj A ≅
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P))
      (v : (DerivedCategory.Q (C := V.toScheme.Modules)).obj B ≅
        (DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj P)),
      e = restrictDerivedIso (pullback.fst U.ι V.ι) u ≪≫
        (restrictDerivedIso (pullback.snd U.ι V.ι) v ≪≫
          (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).mapIso
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
    ∃ (P : CochainComplex X.Modules ℤ) (_ : locallyPerfect X P) (d : P ⟶ L), QuasiIso d := by
  obtain ⟨P, hP, u, v, d, hp, hq, _⟩ :=
    exists_perfect_glue_of_derived_target U V hUV hA hB e φ ψ he
  exact ⟨P, hP, d,
    (quasiIso_iff_of_derived_target U V hUV u v d φ ψ hp hq).mpr ⟨inferInstance, inferInstance⟩⟩

end QuillenTest.DerivedTargetOpenGluing
