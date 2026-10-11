/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HomotopyPullback.OverlapCubeLifting
public import Quillen.Topology.DoubleMappingCylinder.CollarConnectivity

/-!
# Original overlap comparison, stored paths and finite lifting consumers

The original deformation time, path time, parameter point and selector all remain explicit.
Constant columns and the whole supplied overlap boundary stay fixed. The actual double-cylinder
collar application proves nonempty fibers from original attaching bounds, including asymmetric
zero connectivity, without replacing the actual constant-path comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u v

namespace Quillen.Tests.OverlapGapLifting

open HomotopyPullback

/-- The actual stored path retains the original time interpolation at every parameter. -/
theorem original_selected_path_value {X : Type v} {Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (U V : Set Y)
    (b : C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (a : C(X, unitInterval))
    (ha0 : ∀ x, x ∉ OpenCover.TwoSet.columnSet (overlapColumnFamily b) U → a x = 0)
    (ha1 : ∀ x, x ∉ OpenCover.TwoSet.columnSet (overlapColumnFamily b) V → a x = 1)
    (ha : ∀ x, overlapColumnFamily b (a x, x) ∈ U ∩ V)
    (r t : unitInterval) (x : X) :
    (overlapColumnContraction b a ha0 ha1 ha (r, x)).val.2.2 t =
      (b x).val.2.2 (Set.Icc.convexComb t (a x) r) := rfl

/-- An original overlap family is unchanged as a full homotopy-pullback point at every time. -/
theorem original_constant_columns_fixed {X : Type v} {Y : Type u}
    [TopologicalSpace X] [NormalSpace X] [TopologicalSpace Y]
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V) (c : C(X, ↥(U ∩ V))) :
    ∃ c' : C(X, ↥(U ∩ V)),
      ∃ H : ((overlapComparison U V).comp c).Homotopy ((overlapComparison U V).comp c'),
        c' = c ∧ ∀ r x, H (r, x) = overlapComparison U V (c x) := by
  obtain ⟨c', H, hfix⟩ := exists_overlap_column_contraction ((overlapComparison U V).comp c)
    hU hV (fun x ↦ Or.inl (fun _ ↦ (c x).property.1))
  have hH (r : unitInterval) (x : X) : H (r, x) = overlapComparison U V (c x) :=
    hfix x (fun _ ↦ rfl) r
  refine ⟨c', H, ?_, hH⟩
  apply ContinuousMap.ext
  intro x
  apply overlapComparison_injective U V
  exact (H.map_one_left x).symm.trans (hH 1 x)

/-- Finite original strict cube lifting fixes the whole boundary track as a continuous path. -/
theorem original_overlap_boundary_path (d p q : ℕ) (hd : d + 1 ≤ p + q)
    {Y : Type u} [TopologicalSpace Y] (U V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (a : C(CubicalTests.boundary.{u} d, ↥(U ∩ V)))
    (b : C(CubicalTests.cube.{u} d,
      HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (w : (overlapComparison U V).comp a = b.comp (CubicalTests.boundaryInclusion d).hom)
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂) :
    ∃ c : C(CubicalTests.cube.{u} d, ↥(U ∩ V)),
      c.comp (CubicalTests.boundaryInclusion d).hom = a ∧
      ∃ H : ((overlapComparison U V).comp c).Homotopy b,
        ∀ z : CubicalTests.boundary.{u} d,
          (⟨fun r ↦ H (r, z.val), by fun_prop⟩ : C(unitInterval,
            HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V))) =
              ContinuousMap.const _ (overlapComparison U V (a z)) := by
  obtain ⟨c, hc, ⟨H⟩⟩ := overlap_cube_strictHELP d p q (by omega) hU hV hcover hUV hVU a b w
    a₁ b₁ a₂ b₂ hab hbc hce
  refine ⟨c, hc, H.toHomotopy, ?_⟩
  intro z
  apply ContinuousMap.ext
  intro r
  exact (H.prop r z.val ⟨z, rfl⟩).trans
    (congrArg (overlapComparison U V) (ContinuousMap.congr_fun hc z))

/-- Actual collar-gap fibers are nonempty from the original f/g bounds in the positive-sum
range, retaining all original pushout maps and the arbitrary target pullback point. -/
theorem original_collar_gap_fiber_nonempty {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
    (lo hi : unitInterval) (hcut : lo < hi) (p q : ℕ) (hpq : 1 ≤ p + q)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q)
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂)
    (y : HomotopyPullback
      (ContinuousMap.subtypeVal (DoubleCylinder.leftCollarSet f g sq hi))
      (ContinuousMap.subtypeVal (DoubleCylinder.rightCollarSet f g sq lo))) :
    Nonempty (HomotopyFiber (overlapComparison
      (DoubleCylinder.leftCollarSet f g sq hi) (DoubleCylinder.rightCollarSet f g sq lo)) y) := by
  obtain ⟨x, hx⟩ := overlapComparison_component_surjective p q (by omega)
    (DoubleCylinder.leftCollar_isOpen f g sq hi) (DoubleCylinder.rightCollar_isOpen f g sq lo)
    (DoubleCylinder.collar_cover f g sq hi lo hcut)
    (DoubleCylinder.leftOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi hcut p hf)
    (DoubleCylinder.rightOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi hcut q hg)
    a₁ b₁ a₂ b₂ hab hbc hce y
  exact ⟨⟨(x, hx.somePath.toContinuousMap), hx.somePath.source, hx.somePath.target⟩⟩

end Quillen.Tests.OverlapGapLifting
