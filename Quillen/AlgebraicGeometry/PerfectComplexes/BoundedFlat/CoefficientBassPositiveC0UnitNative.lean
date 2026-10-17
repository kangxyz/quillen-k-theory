/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0UnitStrip
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleLift
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationBassSeed

/-!
# Exact original native unit-edge recovery

The beta conjugation is removed by equality of complete dependent reference nodes and
whole-diagram reanchoring. The affine unit edge is evaluated using the r=0 face of the
original transformation-composition triangle. This yields equality of the whole original
unit track, not a replacement relative homotopy or an inference from equal endpoints.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC0UnitNative
open BassH0Merge CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0UnitStrip LaurentUnitReferenceSpecialization

private def duplicateSourceFace : ⦋2⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 0, 1], by decide⟩

/-- A full two-node iso family evaluates to its actual transformation homotopy, at every level.
The proof uses the complete original triangle, not only its endpoint maps. -/
private theorem unitEdge_native {V W : Model.{v}} (F : V ⟶ W)
    (e : F.functor ≅ F.functor) (n : ℕ) (t : I) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily
      (ModelSimplex.ofIsos F (fun _ : Fin 2 ↦ F) ![Iso.refl _, e]) n
      (edge (k := 1) 0 1 t, x) =
    (prespectrumTransformationHomotopy (F := F) (G := F) e.hom
      (fun _A ↦ W.waldhausen.weq_iso _ inferInstance)).level n (t, x) := by
  have ht := prespectrumSimplexFamily_ofIsos_triangle F (fun _ : Fin 2 ↦ F)
    ![Iso.refl _, e] duplicateSourceFace (𝟙 F.functor) e.hom
    (fun A ↦ W.waldhausen.weq.id_mem (F.functor.obj A))
    (fun A ↦ W.waldhausen.weq_iso _ inferInstance)
    (by change (𝟙 F.functor) ≫ (𝟙 F.functor) = 𝟙 F.functor; simp)
    (by change (𝟙 F.functor) ≫ e.hom = e.hom; simp) n 0 t x
  rw [Quillen.TheoremB.compositionTriangleHomotopy.apply_zero] at ht
  change prespectrumSimplexFamily
    (ModelSimplex.ofIsos F (fun _ : Fin 2 ↦ F) ![Iso.refl _, e]) n
    (StdSimplex.map duplicateSourceFace.toOrderHom
      (Quillen.TheoremB.triangleEdge 0 2 t), x) = _ at ht
  rw [map_triangle_edge] at ht
  have hf0 : duplicateSourceFace.toOrderHom 0 = 0 := rfl
  have hf2 : duplicateSourceFace.toOrderHom 2 = 1 := rfl
  rw [hf0, hf2] at ht
  have h0 := ((prespectrumTransformationCompositionHomotopy (F := F) (G := F) (H := F)
    (𝟙 F.functor) e.hom (fun A ↦ W.waldhausen.weq.id_mem (F.functor.obj A))
    (fun A ↦ W.waldhausen.weq_iso _ inferInstance)).level n).apply_zero (t, x)
  simpa only [Category.id_comp] using ht.trans h0

private theorem identity_node_reanchor {V W : Model.{v}} (F G : V ⟶ W)
    (h : F.functor = G.functor) :
    (⟨F, Iso.refl _⟩ : Node F) =
      (⟨G, eqToIso h ≪≫ Iso.refl _⟩ : Node F) := by
  rw [Iso.trans_refl]
  apply ModelSimplex.reference_node_eq h
  simp only [Iso.refl_hom, Category.id_comp, eqToIso.hom]

private theorem pair_nodes_reanchor {V W : Model.{v}} (F G : V ⟶ W)
    (h : F.functor = G.functor) (e : F.functor ≅ F.functor)
    (e' : G.functor ≅ G.functor)
    (he : (⟨F, e⟩ : Node F) = ⟨G, eqToIso h ≪≫ e'⟩) (j : Fin 2) :
    (![⟨F, Iso.refl _⟩, ⟨F, e⟩] : Fin 2 → Node F) j =
      anchorNode (eqToIso h)
        (⟨G, (![Iso.refl _, e'] : Fin 2 → (G.functor ≅ G.functor)) j⟩ : Node G) := by
  fin_cases j
  · exact identity_node_reanchor F G h
  · exact he

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The direct original normalized projection unit, before the beta source transport. -/
def directUnitNodes (j : Fin 2) : Node (normalizedMap (laurentProjection P d)) :=
  ⟨normalizedMap (laurentProjection P d), (![Iso.refl _, projectionUnit P d] :
    Fin 2 → ((normalizedMap (laurentProjection P d)).functor ≅
      (normalizedMap (laurentProjection P d)).functor)) j⟩

/-- Beta transports both complete unit nodes, including the ordinary source reference. -/
theorem unitNodes_direct (j : Fin 2) :
    unitNodes P d j = anchorNode (projectionSourceIso P d) (directUnitNodes P d j) := by
  exact pair_nodes_reanchor (BassProjectionPath.source P d)
    (normalizedMap (laurentProjection P d)) (projection_source_eq P d)
    (splitProjectionUnit P d) (projectionUnit P d) (projection_source_unit_node P d) j

/-- The complete two-node simplex is unchanged after the actual beta transport cancels. -/
theorem unit_simplex_direct :
    ModelSimplex.ofIsos (BassProjectionPath.source P d)
      (fun j ↦ (unitNodes P d j).1) (fun j ↦ (unitNodes P d j).2) =
    ModelSimplex.ofIsos (normalizedMap (laurentProjection P d))
      (fun j ↦ (directUnitNodes P d j).1) (fun j ↦ (directUnitNodes P d j).2) := by
  calc
    _ = ModelSimplex.reanchorSimplex (projectionSourceIso P d) (directUnitNodes P d) := by
      change ModelSimplex.ofIsos (BassProjectionPath.source P d)
        (fun j ↦ (unitNodes P d j).1) (fun j ↦ (unitNodes P d j).2) =
        ModelSimplex.ofIsos (BassProjectionPath.source P d)
          (fun j ↦ (anchorNode (projectionSourceIso P d) (directUnitNodes P d j)).1)
          (fun j ↦ (anchorNode (projectionSourceIso P d) (directUnitNodes P d j)).2)
      exact ModelSimplex.ofIsos_nodes_congr (unitNodes P d)
        (fun j ↦ anchorNode (projectionSourceIso P d) (directUnitNodes P d j))
        (unitNodes_direct P d)
    _ = _ := ModelSimplex.reanchorSimplex_eq (projectionSourceIso P d) (directUnitNodes P d)

/-- The explicit normalized small-model transformation is exactly the original chosen-zero
normalization used by boundedFlatPerfectUnitHomotopy, at every native level. -/
theorem directUnit_track_level (n : ℕ) :
    (prespectrumTransformationHomotopy
      (F := normalizedMap (laurentProjection P d)) (G := normalizedMap (laurentProjection P d))
      (projectionUnit P d).hom
      (fun _A ↦ (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).waldhausen.weq_iso
          _ inferInstance)).level n =
    (boundedFlatCoefficientLaurentUnitHomotopy P d).level n := rfl

/-- Every value of the direct normalized unit is the original exact global-unit homotopy. -/
theorem directUnit_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    prespectrumSimplexFamily
      (ModelSimplex.ofIsos (normalizedMap (laurentProjection P d))
        (fun j ↦ (directUnitNodes P d j).1) (fun j ↦ (directUnitNodes P d j).2)) n
      (edge (k := 1) 0 1 t, x) =
    (boundedFlatCoefficientLaurentUnitHomotopy P d).level n (t, x) := by
  have h := unitEdge_native (normalizedMap (laurentProjection P d)) (projectionUnit P d) n t x
  rw [directUnit_track_level] at h
  exact h

/-- The whole beta-conjugated split edge is exactly the original unit track, with no new time. -/
theorem splitUnit_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    prespectrumSimplexFamily
      (ModelSimplex.ofIsos (BassProjectionPath.source P d)
        (fun j ↦ (unitNodes P d j).1) (fun j ↦ (unitNodes P d j).2)) n
      (edge (k := 1) 0 1 t, x) =
    (boundedFlatCoefficientLaurentUnitHomotopy P d).level n (t, x) := by
  rw [unit_simplex_direct]
  exact directUnit_native P d n t x

variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- All native values of the actual unit product strip recover the prescribed original tracks. -/
theorem unitProductParameter_native (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (laurentReference P p q) (unitProductParameter P p q)
      n ((r, t), x) =
    (boundedFlatCoefficientLaurentUnitHomotopy P c).level n
      (t, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) := by
  rw [unitProductParameter_family, splitUnit_native]

end Quillen.PerfectComplexes.CoefficientBassPositiveC0UnitNative
