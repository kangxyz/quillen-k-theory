/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.SimplexHomotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Realized categorical arrows in the genuine fundamental groupoid

The constructions below use actual continuous paths in the geometric realization.
The composition law is filled inside the realized two-simplex. No edge-path
approximation or presentation theorem for all topological paths is assumed.
-/
@[expose] public section


noncomputable section
open CategoryTheory Opposite Convexity
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen

/-- All paths with the same endpoints in a realized finite simplex are homotopic. -/
theorem realizationStdSimplex_paths_homotopic {n : ℕ}
    {x y : |(Δ[n] : SSet.{u})|} (p q : Path x y) : p.Homotopic q := by
  let e := SimplexCategory.toTopHomeo (SimplexCategory.mk n)
  have H := (stdSimplex_paths_homotopic (p.map e.continuous)
    (q.map e.continuous)).map ⟨e.symm, e.symm.continuous⟩
  have H' := H.pathCast (e.symm_apply_apply x).symm (e.symm_apply_apply y).symm
  convert H' using 1 <;> ext t <;> exact (e.symm_apply_apply _).symm

/-- The edge from one ordered vertex of the standard simplex to another. -/
def simplexEdge (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    (Δ[n] : SSet.{u}).Edge (SSet.stdSimplex.obj₀Equiv.symm i)
      (SSet.stdSimplex.obj₀Equiv.symm j) :=
  .mk (SSet.stdSimplex.edge n i j h)
    (by ext k : 1; fin_cases k; rfl) (by ext k : 1; fin_cases k; rfl)

/-- The first standard triangle edge has exactly the opposite-vertex characteristic map. -/
lemma simplexEdge_01_yoneda :
    SSet.yonedaEquiv.symm (simplexEdge.{u} 2 0 1 (by decide)).edge =
      SSet.stdSimplex.δ 2 := by
  apply SSet.yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply]
  ext k : 1
  fin_cases k <;> rfl

/-- The second standard triangle edge has exactly the opposite-vertex characteristic map. -/
lemma simplexEdge_12_yoneda :
    SSet.yonedaEquiv.symm (simplexEdge.{u} 2 1 2 (by decide)).edge =
      SSet.stdSimplex.δ 0 := by
  apply SSet.yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply]
  ext k : 1
  fin_cases k <;> rfl

/-- The long standard triangle edge has exactly the middle-vertex characteristic map. -/
lemma simplexEdge_02_yoneda :
    SSet.yonedaEquiv.symm (simplexEdge.{u} 2 0 2 (by decide)).edge =
      SSet.stdSimplex.δ 1 := by
  apply SSet.yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply]
  ext k : 1
  fin_cases k <;> rfl

/-- Realizing the characteristic map of a two-simplex takes its three
standard edges to the three prescribed edges. -/
theorem realizationEdgePath_triangle_face
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y)
    (s : X _⦋2⦌) (i : Fin 3) (h : X.δ i s = e.edge)
    (t : unitInterval) :
    SSet.toTop.map (SSet.yonedaEquiv.symm s)
      (SSet.toTop.map (SSet.stdSimplex.δ i) (realizationInterval t)) =
        realizationEdgePath e t := by
  change (SSet.toTop.map (SSet.stdSimplex.δ i) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm s)) _ = _
  rw [← Functor.map_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, h]
  rfl

/-- A simplicial triangle gives the actual relative path homotopy expressing
composition of its two short edges as its long edge. -/
theorem realizationEdgePath_comp
    {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (s : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    ((realizationEdgePath e₀₁).trans (realizationEdgePath e₁₂)).Homotopic
      (realizationEdgePath e₀₂) := by
  let p := realizationEdgePath (simplexEdge.{u} 2 0 1 (by decide))
  let q := realizationEdgePath (simplexEdge.{u} 2 1 2 (by decide))
  let r := realizationEdgePath (simplexEdge.{u} 2 0 2 (by decide))
  let f := (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom
  have hp (t) : f (p t) = realizationEdgePath e₀₁ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    rw [simplexEdge_01_yoneda]
    exact realizationEdgePath_triangle_face e₀₁ s.simplex 2 s.d₂ t
  have hq (t) : f (q t) = realizationEdgePath e₁₂ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    rw [simplexEdge_12_yoneda]
    exact realizationEdgePath_triangle_face e₁₂ s.simplex 0 s.d₀ t
  have hr (t) : f (r t) = realizationEdgePath e₀₂ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    rw [simplexEdge_02_yoneda]
    exact realizationEdgePath_triangle_face e₀₂ s.simplex 1 s.d₁ t
  have h₀ : realizationPoint x₀ = f (realizationPoint (SSet.stdSimplex.obj₀Equiv.symm 0)) := by
    simpa using (hp 0).symm
  have h₂ : realizationPoint x₂ = f (realizationPoint (SSet.stdSimplex.obj₀Equiv.symm 2)) := by
    simpa using (hq 1).symm
  have H := ((realizationStdSimplex_paths_homotopic (p.trans q) r).map f).pathCast h₀ h₂
  convert H using 1
  · ext t
    change ((realizationEdgePath e₀₁).trans (realizationEdgePath e₁₂)) t =
      ((p.trans q).map f.continuous) t
    rw [Path.map_trans]
    simp only [Path.trans_apply]
    split_ifs
    · exact (hp _).symm
    · exact (hq _).symm
  · ext t
    exact (hr t).symm

/-- The path of a composite categorical arrow agrees up to endpoint-fixed
homotopy with the concatenation of the two arrow paths. -/
theorem classifyingSpacePath_comp {C : Type u} [Category.{v} C]
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    ((classifyingSpacePath f).trans (classifyingSpacePath g)).Homotopic
      (classifyingSpacePath (f ≫ g)) :=
  realizationEdgePath_comp ((CategoryTheory.nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl).some

/-- Every category maps canonically into the actual fundamental groupoid of
its classifying space by realizing vertices and arrows. -/
def classifyingFundamentalGroupoidFunctor (C : Type u) [Category.{v} C] :
    C ⥤ FundamentalGroupoid (ClassifyingSpace C) where
  obj x := FundamentalGroupoid.mk (classifyingSpacePoint x)
  map f := ⟦classifyingSpacePath f⟧
  map_id x := by simp [classifyingSpacePath_id]; rfl
  map_comp f g := (Quotient.sound (classifyingSpacePath_comp f g)).symm

/-- All paths with the same endpoints in a realized finite simplex are homotopic. -/
def realizationStdSimplexPathHomotopy {n : ℕ}
    {x y : |(Δ[n] : SSet.{u})|} (p q : Path x y) : p.Homotopy q := by
  let e := SimplexCategory.toTopHomeo (SimplexCategory.mk n)
  have H := (stdSimplexPathHomotopy (p.map e.continuous)
    (q.map e.continuous)).map ⟨e.symm, e.symm.continuous⟩
  have H' := H.pathCast (e.symm_apply_apply x).symm (e.symm_apply_apply y).symm
  refine H'.cast ?_ ?_ <;> ext t <;> exact e.symm_apply_apply _

/-- A simplicial triangle gives the actual relative path homotopy expressing
composition of its two short edges as its long edge. -/
def realizationEdgeCompositionHomotopy
    {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (s : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    ((realizationEdgePath e₀₁).trans (realizationEdgePath e₁₂)).Homotopy
      (realizationEdgePath e₀₂) := by
  let p := realizationEdgePath (simplexEdge.{u} 2 0 1 (by decide))
  let q := realizationEdgePath (simplexEdge.{u} 2 1 2 (by decide))
  let r := realizationEdgePath (simplexEdge.{u} 2 0 2 (by decide))
  let f := (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom
  have hp (t) : f (p t) = realizationEdgePath e₀₁ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    have hface := simplexEdge_01_yoneda
    rw [hface]
    exact realizationEdgePath_triangle_face e₀₁ s.simplex 2 s.d₂ t
  have hq (t) : f (q t) = realizationEdgePath e₁₂ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    have hface := simplexEdge_12_yoneda
    rw [hface]
    exact realizationEdgePath_triangle_face e₁₂ s.simplex 0 s.d₀ t
  have hr (t) : f (r t) = realizationEdgePath e₀₂ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    have hface := simplexEdge_02_yoneda
    rw [hface]
    exact realizationEdgePath_triangle_face e₀₂ s.simplex 1 s.d₁ t
  have h₀ : realizationPoint x₀ = f (realizationPoint (SSet.stdSimplex.obj₀Equiv.symm 0)) := by
    simpa using (hp 0).symm
  have h₂ : realizationPoint x₂ = f (realizationPoint (SSet.stdSimplex.obj₀Equiv.symm 2)) := by
    simpa using (hq 1).symm
  have H := ((realizationStdSimplexPathHomotopy (p.trans q) r).map f).pathCast h₀ h₂
  refine H.cast ?_ ?_
  · ext t
    change ((p.trans q).map f.continuous) t =
      ((realizationEdgePath e₀₁).trans (realizationEdgePath e₁₂)) t
    rw [Path.map_trans]
    simp only [Path.trans_apply]
    split_ifs
    · exact hp _
    · exact hq _
  · ext t
    exact hr t

/-- The explicit composition track retains the full standard-triangle interpolation. -/
theorem realizationEdgeCompositionHomotopy_apply
    {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (s : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) (a t : unitInterval) :
    realizationEdgeCompositionHomotopy s (a, t) =
      SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
        (realizationStdSimplexPathHomotopy
          ((realizationEdgePath (simplexEdge.{u} 2 0 1 (by decide))).trans
            (realizationEdgePath (simplexEdge.{u} 2 1 2 (by decide))))
          (realizationEdgePath (simplexEdge.{u} 2 0 2 (by decide))) (a, t)) := rfl

end Quillen
