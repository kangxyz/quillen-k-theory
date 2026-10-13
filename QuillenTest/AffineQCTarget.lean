/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.AffineQCTarget

/-!
# Quasicoherent target extension across an affine chart

Regression statements retain the stabilized projection and postcomposition
equations for lower-bounded targets with quasicoherent homology. The gluing
statement records the specified derived overlap and both chain-level target
triangles for a cover by two open immersions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.AffineQCTarget
open Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The exact original stabilized projection persists on the extended target map. -/
theorem original_projection_equation (R : CommRingCat.{u}) {U X : Scheme.{u}} [QuasiSeparatedSpace
  X] [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) {E : Complex U} {L : Complex X}
    (hE : locallyPerfect U E) (n : ℤ) [L.IsGE n] (hL : ∀ m, (L.homology m).IsQuasicoherent)
    (φ : (toDerived U).obj E ⟶ (toDerived U).obj ((restrict j).obj L)) :
    ∃ (P : Complex X) (_ : locallyPerfect X P)
      (u : (toDerived U).obj (E ⊞ E⟦(1 : ℤ)⟧) ≅
        (toDerived U).obj ((restrict j).obj P)) (d : P ⟶ L),
      (toDerived U).map ((restrict j).map d) =
        u.inv ≫ (toDerived U).map (biprod.fst : E ⊞ E⟦(1 : ℤ)⟧ ⟶ E) ≫ φ := by
  obtain ⟨P, hP, u, d, hu⟩ :=
    exists_stabilized_qc_target_extension_across_spec R j k hcover hE n hL φ
  refine ⟨P, hP, u, d, ?_⟩
  rw [← hu, Iso.inv_hom_id_assoc]

/-- Postcomposition of the actual global chain map recovers the original derived composite. -/
theorem original_postcomposition (R : CommRingCat.{u}) {U X : Scheme.{u}} [QuasiSeparatedSpace X]
  [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) {E : Complex U} {L N : Complex X}
    (hE : locallyPerfect U E) (n : ℤ) [L.IsGE n] (hL : ∀ m, (L.homology m).IsQuasicoherent)
    (φ : (toDerived U).obj E ⟶ (toDerived U).obj ((restrict j).obj L))
    (f : L ⟶ N) :
    ∃ (P : Complex X) (_ : locallyPerfect X P)
      (r : Retract ((toDerived U).obj E)
        ((toDerived U).obj ((restrict j).obj P))) (d : P ⟶ L),
      r.i ≫ (toDerived U).map ((restrict j).map (d ≫ f)) =
        φ ≫ (toDerived U).map ((restrict j).map f) := by
  obtain ⟨P, hP, r, d, hd⟩ :=
    exists_retract_qc_target_extension_across_spec R j k hcover hE n hL φ
  refine ⟨P, hP, r, d, ?_⟩
  rw [(restrict j).map_comp, (toDerived U).map_comp, ← Category.assoc, hd]

/-- The generic immersion glue preserves the specified original overlap and
both actual local target triangles, with no weak-target hypothesis. -/
theorem specified_overlap_and_strict_triangles {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {A : Complex U} {B : Complex V} {L : Complex X}
    (hA : locallyPerfect U A) (hB : locallyPerfect V B)
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
        (u ≫ (restrict j).map d = p ∧ v ≫ (restrict k).map d = q) ∧
        e.hom ≫ (toDerived (pullback j k)).map
          ((restrict (pullback.snd j k)).map v ≫
            (openSquareRestrictIso (pullback.snd j k) (pullback.fst j k)
              k j pullback.condition.symm).hom.app P) =
          (toDerived (pullback j k)).map ((restrict (pullback.fst j k)).map u) := by
  obtain ⟨P, hP, u, v, d, hu, hv, hup, hvq, he'⟩ :=
    OpenHomotopyGluing.exists_perfect_glue_of_derived_overlap_immersions j k hcover hA hB e p q he
  exact ⟨P, hP, u, v, d, hu, hv, ⟨hup, hvq⟩, he'.symm⟩

end QuillenTest.AffineQCTarget
