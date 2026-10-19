/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramRowStabilizedTarget
public import Quillen.KTheory.Bass.ModelZigzagSequentialization
public import Quillen.Topology.Prespectrum.ZigzagSequentializationReplacement

/-!
# Sequentialization with the actual proper row targets

The computed row targets and literal unit/refinement backward legs satisfy
all topology, growth and stable-equivalence premises. A whole factorization
of a supplied forward map yields the actual telescope comparison. Identifying
that supplied map with an independent tensor/cup construction is separate.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.ModelRowZigzagSequentialization
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (M : C ⥤ Model.{w}) (X : C)

/-- The unchanged original finite Bass vertices. -/
abbrev vertex := ModelZigzagSequentialization.vertex Q M X

/-- Each proper target is the parameter loop of the actual computed cone row refinement. -/
abbrev target (n : ℕ) := ModelDiagramRowStabilizedTarget.target Q n M X

/-- The literal unit followed by the original proper target replacement. -/
def backward (n : ℕ) : vertex Q M X (n + 1) ⟶ target Q M X n :=
  ModelZigzagSequentialization.unit Q M X n ≫
    ModelDiagramRowStabilizedTarget.currentRefinement Q n M X

/-- Actual unit and row-refinement stability prove stability of the original backward leg. -/
theorem backward_stable (n : ℕ) : IsStableEquivalence (backward Q M X n) :=
  (ModelDiagramSuspension.unit_stable Q n M X).comp
    (ModelDiagramRowStabilizedTarget.currentRefinement_stable Q n M X)

/-- Its exact triangle retains the original successor transport and computed row comparison. -/
theorem backward_eq (n : ℕ) :
    backward Q M X n = eqToHom (ModelDiagramSuspension.successor_obj Q n M X) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q n M X) :=
  ModelDiagramRowStabilizedTarget.current_unit_refinement Q n M X

variable (a : ∀ n, vertex Q M X n ⟶ target Q M X n)

/-- Original finite growth proves stability of each proper-row sequentialization comparison. -/
theorem comparison_stable (n : ℕ) :
    IsStableEquivalence (ZigzagSequentialization.comparison
      (vertex Q M X) (target Q M X) a (backward Q M X) n) := by
  let hE := fun n k => modelDiagramIterate_point_homotopyExtensionProperty Q n M X k
  let hV := fun n k => ModelDiagramRowStabilizedTarget.point_homotopyExtensionProperty Q n M X k
  have hπE : ∀ i n (x : (vertex Q M X i).space (n + 2 * i + 2)) k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k ((vertex Q M X i).space (n + 2 * i + 2)) x) :=
    fun i n x k hk => modelDiagramIterate_homotopyGroup_subsingleton_of_le
      Q i M X (n + 2 * i + 2) (by omega) k (by omega) x
  have hπV : ∀ i n (x : (target Q M X i).space (n + 2 * (i + 1) + 2)) k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k ((target Q M X i).space (n + 2 * (i + 1) + 2)) x) :=
    fun i n x k hk => ModelDiagramRowStabilizedTarget.homotopyGroup_subsingleton_at_offset
      Q i M X (2 * (i + 1)) (by omega) n k hk x
  have hc : Monotone (fun n : ℕ => 2 * n) := by
    intro i j hij
    change 2 * i ≤ 2 * j
    omega
  exact ZigzagSequentialization.comparison_isStableEquivalence
    (vertex Q M X) (target Q M X) a (backward Q M X)
    (fun n k => hE n (k + 1)) (fun n k => hV n (k + 1)) (backward_stable Q M X)
    (ZigzagSequentialization.comparison_coneFiber_isStableEquivalence
      _ _ _ _ (fun n => 2 * n) hc hE hV hπE hπV)
    (ZigzagSequentialization.inr_coneFiber_isStableEquivalence
      _ _ _ _ (fun n => 2 * n) hc hE hV hπE hπV) n

/-- A whole forward factorization gives the original stable telescope comparison. -/
theorem telescopeMap_stable
    (f : ∀ n, vertex Q M X n ⟶ vertex Q M X (n + 1))
    (H : ∀ n, Homotopy (a n) (f n ≫ backward Q M X n)) :
    IsStableEquivalence (ZigzagSequentialization.telescopeMap
      (vertex Q M X) (target Q M X) a (backward Q M X) f H) := by
  let : ∀ n k, T1Space ((vertex Q M X n).space k) :=
    fun n k => modelDiagramIterateSpaceT1Space Q n M X k
  let : ∀ n k, T1Space ((target Q M X n).space k) :=
    fun n k => ModelDiagramRowStabilizedTarget.spaceT1Space Q n M X k
  apply ZigzagSequentialization.telescopeMap_isStableEquivalence_of_linearGrowth
    (vertex Q M X) (target Q M X) a (backward Q M X) (fun n => 2 * n)
    (by intro i j hij; change 2 * i ≤ 2 * j; omega)
    (fun n k => modelDiagramIterate_point_homotopyExtensionProperty Q n M X k)
    (fun n k => ModelDiagramRowStabilizedTarget.point_homotopyExtensionProperty Q n M X k)
    (fun i n x k hk => modelDiagramIterate_homotopyGroup_subsingleton_of_le
      Q i M X (n + 2 * i + 2) (by omega) k (by omega) x)
    (fun i n x k hk => ModelDiagramRowStabilizedTarget.homotopyGroup_subsingleton_at_offset
      Q i M X (2 * (i + 1)) (by omega) n k hk x)
    (backward_stable Q M X) f H

section Replacement
variable (a₀ : ∀ n, vertex Q M X n ⟶ ModelZigzagSequentialization.suspendedVertex Q M X n)

/-- The original suspended-target comparisons have their actual finite-growth excision. -/
theorem suspended_comparison_stable (n : ℕ) :
    IsStableEquivalence (ZigzagSequentialization.comparison
      (vertex Q M X) (ModelZigzagSequentialization.suspendedVertex Q M X)
      a₀ (ModelZigzagSequentialization.unit Q M X) n) := by
  let V := ModelZigzagSequentialization.suspendedVertex Q M X
  let hE := fun n k => modelDiagramIterate_point_homotopyExtensionProperty Q n M X k
  let hV := fun n k => ModelDiagramSuspension.point_homotopyExtensionProperty Q (n + 1) M X k
  have hπE : ∀ i n (x : (vertex Q M X i).space (n + 2 * i + 2)) k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k ((vertex Q M X i).space (n + 2 * i + 2)) x) :=
    fun i n x k hk => modelDiagramIterate_homotopyGroup_subsingleton_of_le
      Q i M X (n + 2 * i + 2) (by omega) k (by omega) x
  have hπV : ∀ i n (x : (V i).space (n + 2 * (i + 1) + 2)) k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k ((V i).space (n + 2 * (i + 1) + 2)) x) :=
    fun i n x k hk => ModelDiagramSuspension.homotopyGroup_subsingleton_at_offset
      Q (i + 1) M X (2 * (i + 1)) (by omega) n k hk x
  have hc : Monotone (fun n : ℕ => 2 * n) := by
    intro i j hij
    change 2 * i ≤ 2 * j
    omega
  exact ZigzagSequentialization.comparison_isStableEquivalence
    (vertex Q M X) V a₀ (ModelZigzagSequentialization.unit Q M X)
    (fun n k => hE n (k + 1)) (fun n k => hV n (k + 1))
    (fun n => ModelDiagramSuspension.unit_stable Q n M X)
    (ZigzagSequentialization.comparison_coneFiber_isStableEquivalence
      _ _ _ _ (fun n => 2 * n) hc hE hV hπE hπV)
    (ZigzagSequentialization.inr_coneFiber_isStableEquivalence
      _ _ _ _ (fun n => 2 * n) hc hE hV hπE hπV) n

/-- Replacing both original legs by their literal row-refinement postcomposites is stable. -/
theorem targetReplacementMap_stable :
    IsStableEquivalence (ZigzagSequentialization.targetReplacementMap
      (vertex Q M X) (ModelZigzagSequentialization.suspendedVertex Q M X)
      a₀ (ModelZigzagSequentialization.unit Q M X) (target Q M X)
      (fun n => ModelDiagramRowStabilizedTarget.currentRefinement Q n M X)) := by
  let : ∀ n k, T1Space ((vertex Q M X n).space k) :=
    fun n k => modelDiagramIterateSpaceT1Space Q n M X k
  let : ∀ n k, T1Space ((ModelZigzagSequentialization.suspendedVertex Q M X n).space k) :=
    fun n k => ModelDiagramSuspension.spaceT1Space Q (n + 1) M X k
  let : ∀ n k, T1Space ((target Q M X n).space k) :=
    fun n k => ModelDiagramRowStabilizedTarget.spaceT1Space Q n M X k
  exact ZigzagSequentialization.targetReplacementMap_isStableEquivalence
    (vertex Q M X) (ModelZigzagSequentialization.suspendedVertex Q M X)
    a₀ (ModelZigzagSequentialization.unit Q M X)
    (suspended_comparison_stable Q M X a₀) (target Q M X)
    (fun n => ModelDiagramRowStabilizedTarget.currentRefinement Q n M X)
    (comparison_stable Q M X
      (fun n => a₀ n ≫ ModelDiagramRowStabilizedTarget.currentRefinement Q n M X))

end Replacement

end Quillen.KTheory.Bass.ModelRowZigzagSequentialization
