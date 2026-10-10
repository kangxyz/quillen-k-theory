/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremA.RealizationPushoutInvariance

/-!
# Endpoint-relative homotopy extension

A controlled radial deformation of a simplex cylinder allows HEP extensions
into compact-open mapping spaces to preserve all its prescribed boundary
faces. This gives the endpoint pushout-product construction needed for
compatible mapping-cylinder filtrations.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Topology unitInterval BigOperators

universe u

namespace Quillen.TheoremA

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The reciprocal radial scale, moving from the boundary retraction toward
one and stopping there. -/
def simplexBoundaryFlowScale {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : ℝ :=
  min 1 (simplexBoundaryScale z + (s : ℝ))

lemma boundaryScale_le_flowScale {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) :
    simplexBoundaryScale z ≤ simplexBoundaryFlowScale s z := by
  exact le_min (simplexBoundaryScale_le_one z) (le_add_of_nonneg_right s.2.1)

lemma flowScale_pos {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : 0 < simplexBoundaryFlowScale s z :=
  lt_of_lt_of_le (simplexBoundaryScale_pos z) (boundaryScale_le_flowScale s z)

lemma flowScale_le_one {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : simplexBoundaryFlowScale s z ≤ 1 :=
  min_le_left _ _

@[fun_prop] theorem continuous_simplexBoundaryFlowScale {n : ℕ} :
    Continuous (fun p : I × (StdSimplex ℝ (Fin (n + 1)) × I) ↦
      simplexBoundaryFlowScale p.1 p.2) := by
  unfold simplexBoundaryFlowScale
  fun_prop

/-- The barycentric coordinates during controlled radial motion. -/
def simplexBoundaryFlowWeight {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) (i : Fin (n + 1)) : ℝ :=
  ((n + 1 : ℝ) * z.1.weights i + simplexBoundaryFlowScale s z - 1) /
    ((n + 1 : ℝ) * simplexBoundaryFlowScale s z)

lemma simplexBoundaryFlowWeight_nonneg {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) (i : Fin (n + 1)) :
    0 ≤ simplexBoundaryFlowWeight s z i := by
  apply div_nonneg
  · have := ((le_simplexBoundaryDefect z.1 i).trans
      (defect_le_simplexBoundaryScale z)).trans (boundaryScale_le_flowScale s z)
    linarith
  · exact le_of_lt (mul_pos (by positivity) (flowScale_pos s z))

lemma sum_simplexBoundaryFlowWeight {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) :
    ∑ i, simplexBoundaryFlowWeight s z i = 1 := by
  unfold simplexBoundaryFlowWeight
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    StdSimplex.total_of_fintype, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [ne_of_gt (flowScale_pos s z)]
  ring

/-- The simplex component of the controlled boundary flow at time `s`, with barycentric coordinates
given by `simplexBoundaryFlowWeight`. -/
def simplexBoundaryFlowPoint {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (simplexBoundaryFlowWeight s z)
  nonneg i := simplexBoundaryFlowWeight_nonneg s z i
  total := by simpa [Finsupp.sum_fintype] using sum_simplexBoundaryFlowWeight s z

/-- The real height coordinate of the controlled boundary flow, obtained by scaling the
displacement from height `2` by `simplexBoundaryFlowScale`. -/
def simplexBoundaryFlowHeight {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : ℝ :=
  2 + ((z.2 : ℝ) - 2) / simplexBoundaryFlowScale s z

lemma simplexBoundaryFlowHeight_nonneg {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : 0 ≤ simplexBoundaryFlowHeight s z := by
  have hd := flowScale_pos s z
  have ht := (one_sub_height_le_simplexBoundaryScale z).trans (boundaryScale_le_flowScale s z)
  unfold simplexBoundaryFlowHeight
  have h : -(2 : ℝ) ≤ ((z.2 : ℝ) - 2) / simplexBoundaryFlowScale s z := by
    apply (le_div_iff₀ hd).mpr
    linarith
  linarith

lemma simplexBoundaryFlowHeight_le_one {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : simplexBoundaryFlowHeight s z ≤ 1 := by
  have hd := flowScale_pos s z
  have hu := flowScale_le_one s z
  have ht := z.2.2.2
  unfold simplexBoundaryFlowHeight
  have h : ((z.2 : ℝ) - 2) / simplexBoundaryFlowScale s z ≤ -(1 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith
  linarith

/-- Controlled motion from the side-bottom retraction back to the identity. -/
def simplexBoundaryFlow {n : ℕ} (s : I)
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : StdSimplex ℝ (Fin (n + 1)) × I :=
  (simplexBoundaryFlowPoint s z, ⟨simplexBoundaryFlowHeight s z,
    simplexBoundaryFlowHeight_nonneg s z, simplexBoundaryFlowHeight_le_one s z⟩)

@[fun_prop] theorem continuous_simplexBoundaryFlowWeight {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun p : I × (StdSimplex ℝ (Fin (n + 1)) × I) ↦
      simplexBoundaryFlowWeight p.1 p.2 i) := by
  unfold simplexBoundaryFlowWeight
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p
    exact mul_ne_zero (by positivity) (ne_of_gt (flowScale_pos p.1 p.2))

@[fun_prop] theorem continuous_simplexBoundaryFlowPoint {n : ℕ} :
    Continuous (fun p : I × (StdSimplex ℝ (Fin (n + 1)) × I) ↦
      simplexBoundaryFlowPoint p.1 p.2) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  apply continuous_pi
  exact continuous_simplexBoundaryFlowWeight

@[fun_prop] theorem continuous_simplexBoundaryFlow {n : ℕ} :
    Continuous (fun p : I × (StdSimplex ℝ (Fin (n + 1)) × I) ↦
      simplexBoundaryFlow p.1 p.2) := by
  unfold simplexBoundaryFlow
  apply continuous_simplexBoundaryFlowPoint.prodMk
  apply Continuous.subtype_mk
  unfold simplexBoundaryFlowHeight
  apply Continuous.add continuous_const
  apply Continuous.div
  · fun_prop
  · exact continuous_simplexBoundaryFlowScale
  · intro p
    exact ne_of_gt (flowScale_pos p.1 p.2)

@[simp] theorem simplexBoundaryFlow_zero {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) :
    simplexBoundaryFlow 0 z = simplexBoundaryRetract z := by
  have hs : simplexBoundaryFlowScale 0 z = simplexBoundaryScale z := by
    simp [simplexBoundaryFlowScale, min_eq_right (simplexBoundaryScale_le_one z)]
  apply Prod.ext
  · apply StdSimplex.ext
    ext i
    change simplexBoundaryFlowWeight 0 z i = simplexBoundaryRetractWeight z i
    simp only [simplexBoundaryFlowWeight, simplexBoundaryRetractWeight, hs]
  · apply Subtype.ext
    change simplexBoundaryFlowHeight 0 z = simplexBoundaryRetractHeight z
    simp only [simplexBoundaryFlowHeight, simplexBoundaryRetractHeight, hs]

/-- The continuous stopping time vanishes on all prescribed faces. -/
def simplexBoundaryClock {n : ℕ} (z : StdSimplex ℝ (Fin (n + 1)) × I) : I :=
  ⟨1 - simplexBoundaryScale z, sub_nonneg.mpr (simplexBoundaryScale_le_one z), by
    linarith [simplexBoundaryScale_pos z]⟩

@[fun_prop] theorem continuous_simplexBoundaryClock {n : ℕ} :
    Continuous (simplexBoundaryClock (n := n)) := by
  unfold simplexBoundaryClock
  fun_prop

@[simp] theorem simplexBoundaryClock_boundary {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) (hz : z ∈ simplexBoundaryCylinder n) :
    simplexBoundaryClock z = 0 := by
  apply Subtype.ext
  simp [simplexBoundaryClock, simplexBoundaryScale_eq_one z hz]

@[simp] theorem simplexBoundaryFlow_clock {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) :
    simplexBoundaryFlow (simplexBoundaryClock z) z = z := by
  have hs : simplexBoundaryFlowScale (simplexBoundaryClock z) z = 1 := by
    simp [simplexBoundaryFlowScale, simplexBoundaryClock]
  apply Prod.ext
  · apply StdSimplex.ext
    ext i
    change simplexBoundaryFlowWeight (simplexBoundaryClock z) z i = z.1.weights i
    simp only [simplexBoundaryFlowWeight, hs, add_sub_cancel_right, mul_one]
    exact mul_div_cancel_left₀ _ (by positivity)
  · apply Subtype.ext
    change simplexBoundaryFlowHeight (simplexBoundaryClock z) z = (z.2 : ℝ)
    simp [simplexBoundaryFlowHeight, hs]

/-- HEP plus a controlled boundary deformation extends maps relative to
that boundary. The target mapping space is compact-open. -/
theorem homotopyExtensionProperty_controlled_extension
    {A B Z : TopCat.{u}} {i : A ⟶ B} (hi : homotopyExtensionProperty i)
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    (S : Set X) (r : C(X, S)) (v : C(X, I)) (D : C(I × X, X))
    (hD₀ : ∀ x, D (0, x) = (r x).1)
    (hD₁ : ∀ x, D (v x, x) = x)
    (hv : ∀ x : S, v x = 0)
    (F : C(B × S, Z)) (H : C(A × X, Z))
    (h : ∀ a (x : S), H (a, x.1) = F (i a, x)) :
    ∃ K : C(B × X, Z), (∀ a x, K (i a, x) = H (a, x)) ∧
      ∀ b (x : S), K (b, x.1) = F (b, x) := by
  let F₀ : C(B × X, Z) :=
    ⟨fun p ↦ F (p.1, r p.2), by fun_prop⟩
  let H₀ : C((I × A) × X, Z) :=
    ⟨fun p ↦ H (p.1.2, D (p.1.1, p.2)), by fun_prop⟩
  have hstart : ∀ a, H₀.curry (0, a) = F₀.curry (i a) := by
    intro a
    ext x
    change H (a, D (0, x)) = F (i a, r x)
    rw [hD₀]
    exact h a (r x)
  obtain ⟨Q, hQ₀, hQ⟩ := homotopyExtensionProperty_continuous hi
    (TopCat.of C(X, Z)) F₀.curry H₀.curry hstart
  let K : C(B × X, Z) := ⟨fun p ↦ Q (v p.2, p.1) p.2, by fun_prop⟩
  refine ⟨K, ?_, ?_⟩
  · intro a x
    change Q (v x, i a) x = H (a, x)
    rw [hQ]
    change H (a, D (v x, x)) = H (a, x)
    rw [hD₁]
  · intro b x
    change Q (v x.1, b) x.1 = F (b, x)
    rw [hv x, hQ₀]
    change F (b, r x.1) = F (b, x)
    have hr : r x.1 = x := by
      apply Subtype.ext
      rw [← hD₀, ← hv x, hD₁]
    rw [hr]

/-- HEP extends maps across a product with a simplex cylinder while
preserving its entire side-bottom boundary. -/
theorem homotopyExtensionProperty_simplexCylinder_extension
    {A B Z : TopCat.{u}} {i : A ⟶ B} (hi : homotopyExtensionProperty i) (n : ℕ)
    (F : C(B × simplexBoundaryCylinder n, Z))
    (H : C(A × (StdSimplex ℝ (Fin (n + 1)) × I), Z))
    (h : ∀ a (z : simplexBoundaryCylinder n), H (a, z.1) = F (i a, z)) :
    ∃ K : C(B × (StdSimplex ℝ (Fin (n + 1)) × I), Z),
      (∀ a z, K (i a, z) = H (a, z)) ∧
      ∀ b (z : simplexBoundaryCylinder n), K (b, z.1) = F (b, z) :=
  homotopyExtensionProperty_controlled_extension hi (simplexBoundaryCylinder n)
    (simplexBoundaryCylinderRetraction n)
    ⟨simplexBoundaryClock, continuous_simplexBoundaryClock⟩
    ⟨fun p ↦ simplexBoundaryFlow p.1 p.2, continuous_simplexBoundaryFlow⟩
    simplexBoundaryFlow_zero simplexBoundaryFlow_clock
    (fun z ↦ simplexBoundaryClock_boundary z.1 z.2) F H h

/-- Two independent endpoint homotopies as boundary-simplex data. -/
def intervalEndpointHomotopies {B Z : TopCat.{u}}
    (H₀ H₁ : C(B × I, Z)) : C((B × simplexBoundary 1) × I, Z) := by
  let e := ((intervalEndpointDomainHomeomorph B).symm.prodCongr
    (Homeomorph.refl I)).trans Homeomorph.sumProdDistrib
  exact ⟨fun p ↦ Sum.elim H₀ H₁ (e p),
    (H₀.continuous.sumElim H₁.continuous).comp e.continuous⟩

@[simp] theorem intervalEndpointHomotopies_zero {B Z : TopCat.{u}}
    (H₀ H₁ : C(B × I, Z)) (b : B) (t : I) :
    intervalEndpointHomotopies H₀ H₁ ((b, boundaryZero), t) = H₀ (b, t) := by
  simp [intervalEndpointHomotopies, intervalEndpointDomainHomeomorph]

@[simp] theorem intervalEndpointHomotopies_one {B Z : TopCat.{u}}
    (H₀ H₁ : C(B × I, Z)) (b : B) (t : I) :
    intervalEndpointHomotopies H₀ H₁ ((b, boundaryOne), t) = H₁ (b, t) := by
  simp [intervalEndpointHomotopies, intervalEndpointDomainHomeomorph, boundaryZero_ne_one.symm]

/-- HEP on the first factor extends a square of homotopies with both
interval endpoints and the initial-time face prescribed. -/
theorem homotopyExtensionProperty_interval_square_extension
    {A B Z : TopCat.{u}} {i : A ⟶ B} (hi : homotopyExtensionProperty i)
    (f : C(B × I, Z)) (H : C((A × I) × I, Z)) (H₀ H₁ : C(B × I, Z))
    (hf : ∀ a t, H ((a, t), 0) = f (i a, t))
    (h₀ : ∀ b, H₀ (b, 0) = f (b, 0))
    (h₁ : ∀ b, H₁ (b, 0) = f (b, 1))
    (hH₀ : ∀ a t, H ((a, 0), t) = H₀ (i a, t))
    (hH₁ : ∀ a t, H ((a, 1), t) = H₁ (i a, t)) :
    ∃ K : C((B × I) × I, Z),
      (∀ b t, K ((b, t), 0) = f (b, t)) ∧
      (∀ a s t, K ((i a, s), t) = H ((a, s), t)) ∧
      (∀ b t, K ((b, 0), t) = H₀ (b, t)) ∧
      (∀ b t, K ((b, 1), t) = H₁ (b, t)) := by
  let f' : C(B × StdSimplex ℝ (Fin 2), Z) :=
    ⟨fun p ↦ f (p.1, StdSimplex.homeomorphI p.2), by fun_prop⟩
  let L := intervalEndpointHomotopies H₀ H₁
  have hL : ∀ b (x : simplexBoundary 1), L ((b, x), 0) = f' (b, x.1) := by
    intro b x
    rcases boundary_eq_zero_or_one x with rfl | rfl
    · rw [show L ((b, boundaryZero), 0) = H₀ (b, 0) from
        intervalEndpointHomotopies_zero H₀ H₁ b 0]
      simpa [f', boundaryZero] using h₀ b
    · rw [show L ((b, boundaryOne), 0) = H₁ (b, 0) from
        intervalEndpointHomotopies_one H₀ H₁ b 0]
      simpa [f', boundaryOne] using h₁ b
  let F := closedCylinderGlue (simplexBoundary 1) (isClosed_simplexBoundary 1) f' L hL
  let H' : C(A × (StdSimplex ℝ (Fin 2) × I), Z) :=
    ⟨fun p ↦ H ((p.1, StdSimplex.homeomorphI p.2.1), p.2.2), by fun_prop⟩
  have hFH : ∀ a (z : simplexBoundaryCylinder 1), H' (a, z.1) = F (i a, z) := by
    intro a ⟨⟨x, t⟩, hz⟩
    rcases hz with hx | ht
    · have he : F (i a, ⟨(x, t), Or.inl hx⟩) = L ((i a, ⟨x, hx⟩), t) :=
        closedCylinderGlueFun_side _ f' L (i a) ⟨x, hx⟩ t
      rw [he]
      rcases boundary_eq_zero_or_one ⟨x, hx⟩ with he | he
      · have hx' : x = StdSimplex.single 0 := congrArg Subtype.val he
        change H ((a, StdSimplex.homeomorphI x), t) = _
        rw [he, hx', StdSimplex.homeomorphI_single_zero]
        simpa only [L, intervalEndpointHomotopies_zero] using hH₀ a t
      · have hx' : x = StdSimplex.single 1 := congrArg Subtype.val he
        change H ((a, StdSimplex.homeomorphI x), t) = _
        rw [he, hx', StdSimplex.homeomorphI_single_one]
        simpa only [L, intervalEndpointHomotopies_one] using hH₁ a t
    · change t = 0 at ht
      subst t
      rw [show F (i a, ⟨(x, 0), Or.inr rfl⟩) = f' (i a, x) from
        closedCylinderGlueFun_bottom _ f' L hL (i a) x]
      exact hf a (StdSimplex.homeomorphI x)
  obtain ⟨K', hK'A, hK'F⟩ := homotopyExtensionProperty_simplexCylinder_extension hi 1 F H' hFH
  let K : C((B × I) × I, Z) :=
    ⟨fun p ↦ K' (p.1.1, (StdSimplex.homeomorphI.symm p.1.2, p.2)), by fun_prop⟩
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro b t
    change K' (b, (StdSimplex.homeomorphI.symm t, 0)) = f (b, t)
    calc
      _ = F (b, ⟨(_, 0), Or.inr rfl⟩) := hK'F b ⟨(_, 0), Or.inr rfl⟩
      _ = f' (b, StdSimplex.homeomorphI.symm t) :=
        closedCylinderGlueFun_bottom _ f' L hL b _
      _ = f (b, t) := by simp [f']
  · intro a s t
    change K' (i a, (StdSimplex.homeomorphI.symm s, t)) = H ((a, s), t)
    rw [hK'A]
    simp [H']
  · intro b t
    have hs : StdSimplex.homeomorphI.symm 0 = StdSimplex.single 0 :=
      StdSimplex.homeomorphI.injective (by simp)
    change K' (b, (StdSimplex.homeomorphI.symm 0, t)) = H₀ (b, t)
    rw [hs]
    exact (hK'F b ⟨(boundaryZero.1, t), Or.inl boundaryZero.2⟩).trans
      ((closedCylinderGlueFun_side _ f' L b boundaryZero t).trans
        (intervalEndpointHomotopies_zero H₀ H₁ b t))
  · intro b t
    have hs : StdSimplex.homeomorphI.symm 1 = StdSimplex.single 1 :=
      StdSimplex.homeomorphI.injective (by simp)
    change K' (b, (StdSimplex.homeomorphI.symm 1, t)) = H₁ (b, t)
    rw [hs]
    exact (hK'F b ⟨(boundaryOne.1, t), Or.inl boundaryOne.2⟩).trans
      ((closedCylinderGlueFun_side _ f' L b boundaryOne t).trans
        (intervalEndpointHomotopies_one H₀ H₁ b t))

end Quillen.TheoremA
