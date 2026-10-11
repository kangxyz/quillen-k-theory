/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.DoubleMappingCylinder.CollarConnectivity
public import Quillen.Topology.CubicalSubdivision.TwoChartColumnNormalization

/-!
# Finite-range column normalization in the actual double mapping cylinder

The original attaching maps supply every finite connectivity bound used in the grid induction.
Actual ordered height collars give the open cover, and their overlap contractions use the
explicit midpoint. The normalized original path family has each vertical column in one collar
in parameter dimension `d < p + q`. All original face-chart tracks and overlap faces are retained.
This is the geometric normalization step; constructing fillings of the original gap map remains
separate. In particular no conclusion about reduced cones or stable excision is asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace Quillen.DoubleCylinder

/-- Normalize the actual path cube using only the original attaching-map bounds and ordered
collar cuts. No caller-supplied overlap connectivity or band point is required. -/
theorem exists_column_normalization {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f g) l e)
    (lo hi : unitInterval) (hcut : lo < hi) (d p q : ℕ) (hd : d < p + q)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q)
    (b : C(CubicalSubdivision.Cube (d + 1), D))
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂) :
    ∃ mesh : ℕ, ∃ v : C(CubicalSubdivision.Cube (d + 1), D), ∃ H : b.Homotopy v,
      (∀ G : CubicalSubdivision.FaceIndex (d + 1) mesh,
        (∀ s, height f g sq (b (CubicalSubdivision.face G s)) < hi) →
        ∀ t s, height f g sq (H (t, CubicalSubdivision.face G s)) < hi) ∧
      (∀ G : CubicalSubdivision.FaceIndex (d + 1) mesh,
        (∀ s, lo < height f g sq (b (CubicalSubdivision.face G s))) →
        ∀ t s, lo < height f g sq (H (t, CubicalSubdivision.face G s))) ∧
      (∀ G : CubicalSubdivision.FaceIndex (d + 1) mesh,
        (∀ s, height f g sq (b (CubicalSubdivision.face G s)) < hi ∧
          lo < height f g sq (b (CubicalSubdivision.face G s))) →
        ∀ t s, H (t, CubicalSubdivision.face G s) = b (CubicalSubdivision.face G s)) ∧
      (∀ k, (v.comp (CubicalSubdivision.cell (d + 1) mesh k)) ⁻¹'
        (leftCollarSet f g sq hi \ rightCollarSet f g sq lo) ⊆
        Quillen.Cube.thinSupport a₁ b₁ (p + 1)) ∧
      (∀ k, (v.comp (CubicalSubdivision.cell (d + 1) mesh k)) ⁻¹'
        (rightCollarSet f g sq lo \ leftCollarSet f g sq hi) ⊆
        Quillen.Cube.thinSupport a₂ b₂ (q + 1)) ∧
      ∀ x : CubicalSubdivision.Cube d,
        (∀ t, height f g sq (v (Fin.cons t x)) < hi) ∨
          ∀ t, lo < height f g sq (v (Fin.cons t x)) := by
  have hcover (x : CubicalSubdivision.Cube (d + 1)) :
      b x ∈ leftCollarSet f g sq hi ∪ rightCollarSet f g sq lo := by
    rw [collar_cover f g sq hi lo hcut]
    trivial
  obtain ⟨mesh, v, H, _, hU, hV, hfix, hSU, hSV, hcolumn⟩ :=
    CubicalSubdivision.exists_two_chart_column_normalization d b
      (leftCollarSet f g sq hi) (rightCollarSet f g sq lo)
      (leftCollar_isOpen f g sq hi) (rightCollar_isOpen f g sq lo) hcover
      a₁ b₁ a₂ b₂ hab hbc hce p q hd
      (leftOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi hcut p hf)
      (rightOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi hcut q hg)
  exact ⟨mesh, v, H, hU, hV, hfix, hSU, hSV, hcolumn⟩

/-- The original finite attaching bounds also normalize relative path families: their moving
endpoints stay in the correct original collars, and the entire prescribed path over each
boundary parameter remains literally fixed when it lies in the overlap. -/
theorem exists_relative_column_normalization {A B C D : TopCat.{u}}
    (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f g) l e)
    (lo hi : unitInterval) (hcut : lo < hi) (d p q : ℕ) (hd : d < p + q)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q)
    (b : C(CubicalSubdivision.Cube (d + 1), D))
    (hleft : ∀ x, height f g sq (b (Fin.cons 0 x)) < hi)
    (hright : ∀ x, lo < height f g sq (b (Fin.cons 1 x)))
    (hboundary : ∀ t x, x ∈ _root_.Cube.boundary (Fin d) →
      height f g sq (b (Fin.cons t x)) < hi ∧ lo < height f g sq (b (Fin.cons t x)))
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂) :
    ∃ v : C(CubicalSubdivision.Cube (d + 1), D), ∃ H : b.Homotopy v,
      (∀ r x, height f g sq (H (r, Fin.cons 0 x)) < hi) ∧
      (∀ r x, lo < height f g sq (H (r, Fin.cons 1 x))) ∧
      (∀ r t x, x ∈ _root_.Cube.boundary (Fin d) →
        H (r, Fin.cons t x) = b (Fin.cons t x)) ∧
      ∀ x : CubicalSubdivision.Cube d,
        (∀ t, height f g sq (v (Fin.cons t x)) < hi) ∨
          ∀ t, lo < height f g sq (v (Fin.cons t x)) := by
  apply CubicalSubdivision.exists_relative_two_chart_column_normalization d b
    (leftCollarSet f g sq hi) (rightCollarSet f g sq lo)
    (leftCollar_isOpen f g sq hi) (rightCollar_isOpen f g sq lo) _ hleft hright hboundary
    a₁ b₁ a₂ b₂ hab hbc hce p q hd
    (leftOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi hcut p hf)
    (rightOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi hcut q hg)
  intro x
  rw [collar_cover f g sq hi lo hcut]
  trivial

end Quillen.DoubleCylinder
