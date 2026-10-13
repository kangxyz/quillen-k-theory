/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.Reconstruction
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices

/-!
# Set-theoretic reconstruction of the original poset realization

Representatives are reduced using the actual simplex operators: degeneracies
aggregate repeated vertices, and faces remove zero weights. Positive
nondegenerate representatives with equal metric coordinates have equal ordered
vertex ranges and hence are the same original simplex with the same weights.
This constructs a set inverse to the realization coordinate map. No global
continuity of that inverse for the weak realization topology is asserted.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Convexity Opposite
open scoped Simplicial

universe u

namespace Quillen.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Removing zero weights from an ordered simplex uses only its actual faces. -/
theorem exists_positive_face : ∀ (n : ℕ) (s : (nerve P) _⦋n⦌)
    (_ : StrictMono s.obj) (t : StdSimplex ℝ (Fin (n + 1))),
    ∃ (m : ℕ) (q : (nerve P) _⦋m⦌) (w : StdSimplex ℝ (Fin (m + 1))),
      StrictMono q.obj ∧ (∀ i, 0 < w.weights i) ∧
      realizationSimplex q w = realizationSimplex s t := by
  intro n
  induction n with
  | zero =>
      intro s hs t
      refine ⟨0, s, t, hs, ?_, rfl⟩
      intro i
      simp
  | succ n ih =>
      intro s hs t
      by_cases ht : ∀ i, 0 < t.weights i
      · exact ⟨n + 1, s, t, hs, ht, rfl⟩
      · push Not at ht
        obtain ⟨i, hi⟩ := ht
        have hzero : t.weights i = 0 := le_antisymm hi (t.weights_nonneg i)
        obtain ⟨w, hw⟩ : ∃ w : StdSimplex ℝ (Fin (n + 1)),
            StdSimplex.map i.succAbove w = t := by
          apply (StdSimplex.mem_range_map_iff i.succAbove t).mpr
          intro j hj
          have hji : j = i := by simpa using hj
          simpa [hji] using hzero
        have hface : StrictMono ((nerve P).δ i s).obj :=
          hs.comp (Fin.succAboveOrderEmb i).strictMono
        obtain ⟨m, q, z, hq, hz, he⟩ := ih ((nerve P).δ i s) hface w
        refine ⟨m, q, z, hq, hz, he.trans ?_⟩
        exact (realizationSimplex_naturality (SimplexCategory.δ i) s w).symm.trans
          (congrArg (realizationSimplex s) hw)

/-- Every original realized point has positive coordinates on an actual strict chain. -/
theorem exists_positive_realization_representation (z : |nerve P|) :
    ∃ (n : ℕ) (s : (nerve P) _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))),
      StrictMono s.obj ∧ (∀ i, 0 < t.weights i) ∧ realizationSimplex s t = z := by
  obtain ⟨j, t, hj⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (realizationSimplexCoconeIsColimit (nerve P))) z
  change SimplexCategory.toTop.obj j.left at t
  obtain ⟨t⟩ := t
  change (realizationSimplexCocone (nerve P)).ι.app j (ULift.up t) = z at hj
  rw [realizationSimplexCocone_ι_apply] at hj
  obtain ⟨m, a, _, ⟨s, hs⟩, ha⟩ :=
    (nerve P).exists_nonDegenerate (SSet.yonedaEquiv j.hom)
  obtain ⟨n, q, w, hq, hw, he⟩ := exists_positive_face m s
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mp hs) (StdSimplex.map a t)
  refine ⟨n, q, w, hq, hw, he.trans ?_⟩
  rw [realizationSimplex_naturality, ← ha]
  exact hj

/-- Positive coordinates make the metric support exactly the original vertex range. -/
theorem simplexCoordinates_support_of_positive {n : ℕ} (s : (nerve P) _⦋n⦌)
    (t : StdSimplex ℝ (Fin (n + 1))) (ht : ∀ i, 0 < t.weights i) :
    ((simplexCoordinates s t).weights.support : Set P) = Set.range s.obj := by
  classical
  have hsupport : t.weights.support = Finset.univ := by
    ext i
    simp only [Finsupp.mem_support_iff, Finset.mem_univ, iff_true]
    exact ne_of_gt (ht i)
  change ((chainCoordinates s.obj s.monotone.isChain_range t).weights.support : Set P) = _
  rw [chainCoordinates_support, hsupport, Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- Positive strict representatives with equal coordinates give the identical realized point. -/
theorem positive_representatives_eq {n m : ℕ}
    (s : (nerve P) _⦋n⦌) (q : (nerve P) _⦋m⦌)
    (hs : StrictMono s.obj) (hq : StrictMono q.obj)
    (t : StdSimplex ℝ (Fin (n + 1))) (w : StdSimplex ℝ (Fin (m + 1)))
    (ht : ∀ i, 0 < t.weights i) (hw : ∀ i, 0 < w.weights i)
    (h : simplexCoordinates s t = simplexCoordinates q w) :
    realizationSimplex s t = realizationSimplex q w := by
  have hr : Set.range s.obj = Set.range q.obj := by
    rw [← simplexCoordinates_support_of_positive s t ht,
      ← simplexCoordinates_support_of_positive q w hw, h]
  have he : SSet.S.mk s = SSet.S.mk q := by
    apply (SSet.S.eq_iff_ofSimplex_eq s q
      ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mpr hs)
      ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono q).mpr hq)).mpr
    apply le_antisymm
    · exact (PartialOrder.nerve_ofSimplex_le_ofSimplex_iff s q).mpr hr.subset
    · exact (PartialOrder.nerve_ofSimplex_le_ofSimplex_iff q s).mpr hr.symm.subset
  obtain rfl : n = m := SSet.S.dim_eq_of_mk_eq he
  obtain rfl : s = q := (SSet.S.ext_iff s q).mp he
  have htw : t = w := chainCoordinates_injective s.obj s.monotone.isChain_range hs.injective h
  rw [htw]

/-- The original realization coordinate map is injective across arbitrary representatives. -/
theorem realizationCoordinates_injective :
    Function.Injective (realizationCoordinates (P := P)) := by
  intro x y h
  obtain ⟨n, s, t, hs, ht, hx⟩ := exists_positive_realization_representation x
  obtain ⟨m, q, w, hq, hw, hy⟩ := exists_positive_realization_representation y
  rw [← hx, ← hy, realizationCoordinates_simplex, realizationCoordinates_simplex] at h
  exact hx.symm.trans ((positive_representatives_eq s q hs hq t w ht hw h).trans hy)

/-- The coordinate comparison is a bijection of sets; it is not packaged as a homeomorphism. -/
def realizationCoordinatesEquiv : |nerve P| ≃ MetricOrderComplex P :=
  Equiv.ofBijective realizationCoordinates
    ⟨realizationCoordinates_injective, realizationCoordinates_surjective⟩

/-- Reconstruct the original realized point as a set map, with no continuity assertion. -/
def realizationReconstruction : MetricOrderComplex P → |nerve P| :=
  realizationCoordinatesEquiv.symm

@[simp]
theorem realizationCoordinates_reconstruction (x : MetricOrderComplex P) :
    realizationCoordinates (realizationReconstruction x) = x :=
  realizationCoordinatesEquiv.apply_symm_apply x

@[simp]
theorem realizationReconstruction_coordinates (x : |nerve P|) :
    realizationReconstruction (realizationCoordinates x) = x :=
  realizationCoordinatesEquiv.symm_apply_apply x

/-- Reconstruction agrees exactly with every original chart, including its zero faces. -/
@[simp]
theorem realizationReconstruction_simplex {n : SimplexCategory}
    (s : (nerve P).obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    realizationReconstruction (simplexCoordinates s t) = realizationSimplex s t := by
  apply realizationCoordinates_injective
  rw [realizationCoordinates_reconstruction, realizationCoordinates_simplex]

/-- Reconstruction retains every original vertex. -/
@[simp]
theorem realizationReconstruction_vertex (p : P) :
    realizationReconstruction (vertex p) = classifyingSpacePoint.{u, u} p := by
  apply realizationCoordinates_injective
  rw [realizationCoordinates_reconstruction, realizationCoordinates_vertex]

end Quillen.MetricOrderComplex
