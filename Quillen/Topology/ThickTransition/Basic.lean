/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyLifting.Closure
public import Quillen.Topology.HomotopyLifting.Collar.TwoCharts

/-!
# Actual thick transition spaces

The central strip retains the whole ambient space. Near either endpoint
only the corresponding end subspace remains. A strong deformation onto
an end therefore restricts to its open collar, with no choice of inverse
on the other end and no assumption of global lifting.
-/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen

/-- A transition space with independently specified endpoint collars. -/
abbrev ThickTransition {X Y M : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace M] (i : C(X, M)) (j : C(Y, M)) (L R : Set I) :=
  {z : M × I // (z.2 ∈ L → z.1 ∈ Set.range i) ∧ (z.2 ∈ R → z.1 ∈ Set.range j)}

namespace ThickTransition
variable {X Y M B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace M] [TopologicalSpace B]
  (i : C(X, M)) (j : C(Y, M)) (L R : Set I) (q : C(M, B))

/-- The projection retains both the geometric base point and strip height. -/
def projection : C(ThickTransition i j L R, B × I) :=
  ⟨fun z ↦ (q z.1.1, z.1.2), by fun_prop⟩

/-- Restrict the base to the specified set of strip heights. -/
def strip (S : Set I) : Set (B × I) := {z | z.2 ∈ S}

/-- The open-collar total space, with its actual subspace topology. -/
abbrev Collar (S : Set I) :=
  {z : ThickTransition i j L R // projection i j L R q z ∈ strip (B := B) S}

/-- Product points on the chosen end, over the same base collar. -/
abbrev EndCollar (p : C(X, B)) (S : Set I) :=
  {z : X × I // (p.prodMap (ContinuousMap.id I)) z ∈ strip (B := B) S}

variable (S : Set I) (hSR : ∀ t ∈ S, t ∉ R)
  (p : C(X, B)) (hi : q.comp i = p)
  (r : C(M, X)) (hr : p.comp r = q)

/-- Include the end product in the actual thick collar. -/
def endInclusion : C(EndCollar p S, Collar i j L R q S) where
  toFun z := ⟨⟨(i z.1.1, z.1.2),
    fun _ ↦ ⟨z.1.1, rfl⟩, fun h ↦ False.elim (hSR z.1.2 z.2 h)⟩, z.2⟩
  continuous_toFun := by fun_prop

/-- Retract a thick collar onto the product of its end with the height interval. -/
def endRetraction : C(Collar i j L R q S, EndCollar p S) where
  toFun z := ⟨(r z.1.1.1, z.1.1.2), z.2⟩
  continuous_toFun := by fun_prop

variable (D : (ContinuousMap.id M).Homotopy (i.comp r))
  (hD : ∀ t m, q (D (t, m)) = q m)
  (hDi : ∀ t x, D (t, i x) = i x)

/-- The ambient strong deformation restricts to this collar: whenever
an endpoint condition is active, the corresponding end is fixed. -/
def endDeformation : (ContinuousMap.id (Collar i j L R q S)).Homotopy
    ((endInclusion i j L R q S hSR p).comp (endRetraction i j L R q S p r)) where
  toFun z := ⟨⟨(D (z.1, z.2.1.1.1), z.2.1.1.2), by
    constructor
    · intro ht
      obtain ⟨x, hx⟩ := z.2.1.2.1 ht
      exact ⟨x, by rw [← hx, hDi]⟩
    · intro ht
      exact False.elim (hSR z.2.1.1.2 z.2.2 ht)⟩, z.2.2⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext (D.map_zero_left _) rfl
  map_one_left z := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext (D.map_one_left _) rfl

include hSR hi hr hD hDi in
/-- One actual thick collar has weak lifting whenever its end is a
fibration and the ambient end deformation is strictly over the base. -/
theorem weakLifting_collar (hp : HomotopyLiftingProperty p) :
    WeakHomotopyLiftingProperty (baseRestrictionMap (projection i j L R q) (strip (B := B) S)) := by
  refine weakLifting_of_fiberwise_deformation _
    (baseRestrictionMap (p.prodMap (ContinuousMap.id I)) (strip (B := B) S))
    ((hp.prod_id I).baseRestriction _).weak
    (endInclusion i j L R q S hSR p) (endRetraction i j L R q S p r) ?_ ?_
    (endDeformation i j L R q S hSR p r D hDi) ?_
  · apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact Prod.ext (ContinuousMap.congr_fun hi z.1.1) rfl
  · apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact Prod.ext (ContinuousMap.congr_fun hr z.1.1.1) rfl
  · intro t z
    apply Subtype.ext
    exact Prod.ext (hD t z.1.1.1) rfl

/-- Interchanging the two end constraints changes no underlying point. -/
def swapHomeomorph : ThickTransition i j L R ≃ₜ ThickTransition j i R L where
  toFun z := ⟨z.1, z.2.2, z.2.1⟩
  invFun z := ⟨z.1, z.2.2, z.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The same symmetry on any restricted height strip. -/
def swapCollarHomeomorph (S : Set I) : Collar i j L R q S ≃ₜ Collar j i R L q S where
  toFun z := ⟨swapHomeomorph i j L R z.1, z.2⟩
  invFun z := ⟨swapHomeomorph j i R L z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The reflected collar follows from the identical one-ended deformation
argument, with the two end constraints interchanged. -/
theorem weakLifting_opposite_collar
    (S : Set I) (hSL : ∀ t ∈ S, t ∉ L)
    (p : C(Y, B)) (hj : q.comp j = p)
    (r : C(M, Y)) (hr : p.comp r = q)
    (D : (ContinuousMap.id M).Homotopy (j.comp r))
    (hD : ∀ t m, q (D (t, m)) = q m)
    (hDj : ∀ t y, D (t, j y) = j y)
    (hp : HomotopyLiftingProperty p) :
    WeakHomotopyLiftingProperty (baseRestrictionMap (projection i j L R q) (strip (B := B) S)) :=
  (weakLifting_collar j i R L q S hSL p hj r hr D hD hDj hp).of_sourceHomeomorph _
    (swapCollarHomeomorph i j L R q S) rfl

/-- The left end alone occupies heights strictly below one quarter. -/
def leftConstraint : Set I := {t | (t : ℝ) < 1 / 4}
/-- The right end alone occupies heights strictly above three quarters. -/
def rightConstraint : Set I := {t | 3 / 4 < (t : ℝ)}

/-- The projection of an actual two-ended thick transition has weak
covering-homotopy lifting. Both local lifting conclusions are derived
from the specified end fibrations and strong deformations. -/
theorem weakLifting
    (p₀ : C(X, B)) (p₁ : C(Y, B))
    (hp₀ : HomotopyLiftingProperty p₀) (hp₁ : HomotopyLiftingProperty p₁)
    (hi : q.comp i = p₀) (hj : q.comp j = p₁)
    (r₀ : C(M, X)) (r₁ : C(M, Y))
    (hr₀ : p₀.comp r₀ = q) (hr₁ : p₁.comp r₁ = q)
    (D₀ : (ContinuousMap.id M).Homotopy (i.comp r₀))
    (D₁ : (ContinuousMap.id M).Homotopy (j.comp r₁))
    (hD₀ : ∀ t m, q (D₀ (t, m)) = q m)
    (hD₁ : ∀ t m, q (D₁ (t, m)) = q m)
    (hDi : ∀ t x, D₀ (t, i x) = i x)
    (hDj : ∀ t y, D₁ (t, j y) = j y) :
    WeakHomotopyLiftingProperty (projection i j leftConstraint rightConstraint q) := by
  apply weakLifting_of_two_collars _ (ContinuousMap.snd : C(B × I, I))
  · exact weakLifting_collar i j leftConstraint rightConstraint q
      {t | (t : ℝ) < 3 / 4} (by
        intro t ht hR
        change (t : ℝ) < 3 / 4 at ht
        change 3 / 4 < (t : ℝ) at hR
        linarith)
      p₀ hi r₀ hr₀ D₀ hD₀ hDi hp₀
  · exact weakLifting_opposite_collar i j leftConstraint rightConstraint q
      {t | (σ t : ℝ) < 3 / 4} (by
        intro t ht hL
        change 1 - (t : ℝ) < 3 / 4 at ht
        change (t : ℝ) < 1 / 4 at hL
        linarith)
      p₁ hj r₁ hr₁ D₁ hD₁ hDj hp₁

end ThickTransition
end Quillen
