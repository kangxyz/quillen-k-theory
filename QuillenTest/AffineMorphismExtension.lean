/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenGluing.AffineMorphismExtension
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

/-!
# Affine morphism extension regression statements

Records weak roof legs for a prescribed local derived isomorphism, the projection
equation for stabilized target extension across an affine chart, and compatibility
with postcomposition. An additional statement specializes affine roofs to the
empty open.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.AffineMorphismExtension
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A specified original local derived isomorphism has two genuinely weak roof legs. -/
theorem both_original_roof_legs_weak {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [CompactSpace U] [IsAffine X]
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (hB : locallyPerfect X B)
    (e : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj A) ≅
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ QuasiIso ((restrict j).map g) ∧
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ e.hom =
        (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map g) := by
  obtain ⟨M, q, g, hM, hq, hg⟩ :=
    OpenDerivedImage.affine_hasDerivedRoofs_of_compact j A B hA hB e.hom
  have hi : IsIso ((DerivedCategory.Q (C := U.Modules)).map ((restrict j).map g)) := by
    rw [← hg]
    infer_instance
  refine ⟨M, q, g, hM, hq,
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hi, ?_⟩
  exact hg

/-- The exact original stabilized projection persists on the extended target map. -/
theorem original_projection_equation {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) {E : CochainComplex U.toScheme.Modules ℤ} {L : CochainComplex X.Modules ℤ}
    (hE : locallyPerfect U.toScheme E) (hL : locallyPerfect X L)
    (φ : (DerivedCategory.Q (C := U.toScheme.Modules)).obj E ⟶
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj L)) :
    ∃ (P : CochainComplex X.Modules ℤ) (_ : locallyPerfect X P)
      (u : (DerivedCategory.Q (C := U.toScheme.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧) ≅
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P)) (d : P ⟶ L),
      (DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map d) =
        u.inv ≫ (DerivedCategory.Q (C := U.toScheme.Modules)).map (biprod.fst : E ⊞ E⟦(1 : ℤ)⟧ ⟶ E)
          ≫ φ := by
  obtain ⟨P, hP, u, d, hu⟩ :=
    exists_stabilized_target_extension_across_affine_chart U V hU hV hUV hE hL φ
  refine ⟨P, hP, u, d, ?_⟩
  rw [← hu, Iso.inv_hom_id_assoc]

/-- Postcomposition of the actual global chain map recovers the original derived composite. -/
theorem original_postcomposition {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) {E : CochainComplex U.toScheme.Modules ℤ} {L N : CochainComplex X.Modules ℤ}
    (hE : locallyPerfect U.toScheme E) (hL : locallyPerfect X L)
    (φ : (DerivedCategory.Q (C := U.toScheme.Modules)).obj E ⟶
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj L))
    (f : L ⟶ N) :
    ∃ (P : CochainComplex X.Modules ℤ) (_ : locallyPerfect X P)
      (r : Retract ((DerivedCategory.Q (C := U.toScheme.Modules)).obj E)
        ((DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P))) (d : P ⟶ L),
      r.i ≫ (DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map (d ≫ f)) =
        φ ≫ (DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map f) := by
  obtain ⟨P, hP, r, d, hd⟩ :=
    exists_retract_target_extension_across_affine_chart U V hU hV hUV hE hL φ
  refine ⟨P, hP, r, d, ?_⟩
  rw [(restrict U.ι).map_comp, (DerivedCategory.Q (C
    := U.toScheme.Modules)).map_comp, ← Category.assoc, hd]

/-- The affine-immersion theorem includes the actual empty open and its original maps. -/
theorem empty_open_roof {X : Scheme.{u}} [IsAffine X] {A B : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect X A) (hB : locallyPerfect X B)
    (φ : (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj
      ((restrict (⊥ : X.Opens).ι).obj A) ⟶
      (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj
        ((restrict (⊥ : X.Opens).ι).obj B)) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect X M ∧
      QuasiIso ((restrict (⊥ : X.Opens).ι).map q) ∧
      (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).map
        ((restrict (⊥ : X.Opens).ι).map q) ≫ φ =
        (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).map
          ((restrict (⊥ : X.Opens).ι).map g) := by
  let : CompactSpace (⊥ : X.Opens).toScheme := isCompact_iff_compactSpace.mp (by simp)
  exact OpenDerivedImage.affine_hasDerivedRoofs_of_compact (⊥ : X.Opens).ι A B hA hB φ

end QuillenTest.AffineMorphismExtension
