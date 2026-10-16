/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.AffineQCTarget
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

/-!
# Quasicoherent target extension across an affine chart

Regression statements retain the stabilized projection and postcomposition
equations for lower-bounded targets with quasicoherent homology. The gluing
statement records the specified derived overlap and both chain-level target
triangles for a cover by two open immersions.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.AffineQCTarget
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The exact original stabilized projection persists on the extended target map. -/
theorem original_projection_equation (R : CommRingCat.{u}) {U X : Scheme.{u}} [QuasiSeparatedSpace
  X] [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) {E : CochainComplex U.Modules ℤ}
      {L : CochainComplex X.Modules ℤ}
    (hE : locallyPerfect U E) (n : ℤ) [L.IsGE n] (hL : ∀ m, (L.homology m).IsQuasicoherent)
    (φ : (DerivedCategory.Q (C := U.Modules)).obj E ⟶ (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj L)) :
    ∃ (P : CochainComplex X.Modules ℤ) (_ : locallyPerfect X P)
      (u : (DerivedCategory.Q (C := U.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧) ≅
        (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P)) (d : P ⟶ L),
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map d) =
        u.inv ≫ (DerivedCategory.Q (C := U.Modules)).map (biprod.fst : E ⊞ E⟦(1 : ℤ)⟧ ⟶ E) ≫ φ := by
  obtain ⟨P, hP, u, d, hu⟩ :=
    exists_stabilized_qc_target_extension_across_spec R j k hcover hE n hL φ
  refine ⟨P, hP, u, d, ?_⟩
  rw [← hu, Iso.inv_hom_id_assoc]

/-- Postcomposition of the actual global chain map recovers the original derived composite. -/
theorem original_postcomposition (R : CommRingCat.{u}) {U X : Scheme.{u}} [QuasiSeparatedSpace X]
  [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) {E : CochainComplex U.Modules ℤ}
      {L N : CochainComplex X.Modules ℤ}
    (hE : locallyPerfect U E) (n : ℤ) [L.IsGE n] (hL : ∀ m, (L.homology m).IsQuasicoherent)
    (φ : (DerivedCategory.Q (C := U.Modules)).obj E ⟶ (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj L))
    (f : L ⟶ N) :
    ∃ (P : CochainComplex X.Modules ℤ) (_ : locallyPerfect X P)
      (r : Retract ((DerivedCategory.Q (C := U.Modules)).obj E)
        ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P))) (d : P ⟶ L),
      r.i ≫ (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map (d ≫ f)) =
        φ ≫ (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map f) := by
  obtain ⟨P, hP, r, d, hd⟩ :=
    exists_retract_qc_target_extension_across_spec R j k hcover hE n hL φ
  refine ⟨P, hP, r, d, ?_⟩
  rw [(restrict j).map_comp, (DerivedCategory.Q (C := U.Modules)).map_comp, ← Category.assoc, hd]

/-- The generic immersion glue preserves the specified original overlap and
both actual local target triangles, with no weak-target hypothesis. -/
theorem specified_overlap_and_strict_triangles {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {A : CochainComplex U.Modules ℤ} {B : CochainComplex V.Modules ℤ}
      {L : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect U A) (hB : locallyPerfect V B)
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
        (u ≫ (restrict j).map d = p ∧ v ≫ (restrict k).map d = q) ∧
        e.hom ≫ (DerivedCategory.Q (C := (pullback j k).Modules)).map
          ((restrict (pullback.snd j k)).map v ≫
            (openSquareRestrictIso (pullback.snd j k) (pullback.fst j k)
              k j pullback.condition.symm).hom.app P) =
          (DerivedCategory.Q (C := (pullback j k).Modules)).map
            ((restrict (pullback.fst j k)).map u) := by
  obtain ⟨P, hP, u, v, d, hu, hv, hup, hvq, he'⟩ :=
    OpenHomotopyGluing.exists_perfect_glue_of_derived_overlap_immersions j k hcover hA hB e p q he
  exact ⟨P, hP, u, v, d, hu, hv, ⟨hup, hvq⟩, he'.symm⟩

end QuillenTest.AffineQCTarget
