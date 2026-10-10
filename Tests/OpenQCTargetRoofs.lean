/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenQCTargetRoofs

/-!
# Affine-open roofs with quasicoherent targets

Regression statements concern roofs from locally perfect sources to lower-bounded
targets with quasicoherent homology. They retain both weak legs for a local
isomorphism, two specified source-support conditions, and the empty-open case.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Tests.OpenQCTargetRoofs
open Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves

/-- A prescribed original derived isomorphism makes both actual restricted
legs weak, even when the target has arbitrary all-sheaf terms. -/
theorem both_actual_legs_weak (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] [CompactSpace U]
    {A B : Complex (Spec R)} (hA : locallyPerfect (Spec R) A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (e : (toDerived U).obj ((restrict j).obj A) ≅ (toDerived U).obj ((restrict j).obj B)) :
    ∃ (M : Complex (Spec R)) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect (Spec R) M ∧
      QuasiIso ((restrict j).map q) ∧ QuasiIso ((restrict j).map g) ∧
      (toDerived U).map ((restrict j).map q) ≫ e.hom = (toDerived U).map ((restrict j).map g) := by
  obtain ⟨M, q, g, hM, hq, hg, _⟩ :=
    Affine.exists_immersion_roof_to_lowerBounded_quasicoherent_target R j hA b hB e.hom
  have hi : IsIso ((toDerived U).map ((restrict j).map g)) := by rw [← hg]; infer_instance
  exact ⟨M, q, g, hM, hq, (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules _).mp hi, hg⟩

/-- The same original denominator simultaneously retains two independently
chosen compact-open support conditions. -/
theorem two_original_supports (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] [CompactSpace U]
    {A B : Complex (Spec R)} (hA : locallyPerfect (Spec R) A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (α : (toDerived U).obj ((restrict j).obj A) ⟶ (toDerived U).obj ((restrict j).obj B))
    (Z T : (Spec R).Opens) (hZ : IsCompact (Z : Set (Spec R))) (hT : IsCompact (T : Set (Spec R)))
    (hz : IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj A)))
    (ht : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A))) :
    ∃ (M : Complex (Spec R)) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect (Spec R) M ∧
      QuasiIso ((restrict j).map q) ∧
      (toDerived U).map ((restrict j).map q) ≫ α = (toDerived U).map ((restrict j).map g) ∧
      IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj M)) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) := by
  obtain ⟨M, q, g, hM, hq, hg, hs⟩ :=
    Affine.exists_immersion_roof_to_lowerBounded_quasicoherent_target R j hA b hB α
  exact ⟨M, q, g, hM, hq, hg, hs Z hZ hz, hs T hT ht⟩

/-- The actual empty open is included, with the unchanged original target. -/
theorem empty_open_original_roof (R : CommRingCat.{u})
    {A B : Complex (Spec R)} (hA : locallyPerfect (Spec R) A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (α : (toDerived (⊥ : (Spec R).Opens).toScheme).obj ((restrict (⊥ : (Spec R).Opens).ι).obj A) ⟶
      (toDerived (⊥ : (Spec R).Opens).toScheme).obj ((restrict (⊥ : (Spec R).Opens).ι).obj B)) :
    ∃ (M : Complex (Spec R)) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect (Spec R) M ∧
      QuasiIso ((restrict (⊥ : (Spec R).Opens).ι).map q) ∧
      (toDerived (⊥ : (Spec R).Opens).toScheme).map ((restrict (⊥ : (Spec R).Opens).ι).map q) ≫ α =
        (toDerived (⊥ : (Spec R).Opens).toScheme).map ((restrict (⊥ : (Spec R).Opens).ι).map g) :=
          by
  obtain ⟨M, q, g, hM, hq, hg, _⟩ :=
    Affine.exists_open_roof_to_lowerBounded_quasicoherent_target R ⊥ (by simp) hA b hB α
  exact ⟨M, q, g, hM, hq, hg⟩

end Tests.OpenQCTargetRoofs
