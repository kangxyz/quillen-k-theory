/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0MergedBoundary

/-! One genuine five-node family for the original geometric square homotopy. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.NativeSquareFiveSimplex
variable {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w)

/-- The binary normalization source for the route `p ≫ v` through the commuting square. -/
abbrev source := BinaryNormalizationSimplex.sourceMap p v

include h in
/-- The actual square equality identifies the two original binary source functors. -/
theorem source_eq : (source p v).functor = (BinaryNormalizationSimplex.sourceMap q w).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up) (congrArg boundedFlatNormalizedPullback h)

/--
The isomorphism from the `p, v` binary source to the `q, w` binary source induced by the square
equality `h`.
-/
def sourceIso := eqToIso (source_eq p v q w h)

/-- A model morphism equipped with a natural isomorphism from the fixed `p, v` source functor. -/
abbrev Node := Σ F : modelOf (boundedFlatPerfectWaldhausen Z) ⟶
    modelOf (boundedFlatPerfectWaldhausen X), (source p v).functor ≅ F.functor

/-- Both actual raw normalization intermediates are retained separately. -/
def nodes : Fin 5 → Node p v :=
  ![⟨source p v, Iso.refl _⟩,
    ⟨BinaryNormalizationSimplex.intermediateMap p v, BinaryNormalizationSimplex.first p v⟩,
    ⟨BinaryNormalizationSimplex.targetMap p v, BinaryNormalizationSimplex.total p v⟩,
    ⟨BinaryNormalizationSimplex.intermediateMap q w,
      sourceIso p v q w h ≪≫ BinaryNormalizationSimplex.first q w⟩,
    ⟨BinaryNormalizationSimplex.targetMap q w,
      sourceIso p v q w h ≪≫ BinaryNormalizationSimplex.total q w⟩]

/--
The four-dimensional model simplex joining both binary normalization triangles at their common
source.
-/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen Z))
    (modelOf (boundedFlatPerfectWaldhausen X)) 4 :=
  ModelSimplex.ofIsos (source p v) (fun i ↦ (nodes p v q w h i).1)
    (fun i ↦ (nodes p v q w h i).2)

/-- The face selecting vertices `0, 1, 2`, which carry the `p, v` binary normalization triangle. -/
def firstFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 2], by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
/-- The face selecting vertices `0, 3, 4`, which carry the `q, w` binary normalization triangle. -/
def secondFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 3, 4], by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The first original whole binary normalization triangle. -/
theorem first_face : (simplex p v q w h).face firstFace =
    BinaryNormalizationSimplex.simplex p v := by
  unfold simplex BinaryNormalizationSimplex.simplex
  rw [ModelSimplex.ofIsos_face]
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · fin_cases i <;> rfl
  · intro i j f
    fin_cases i <;> fin_cases j <;> rfl

/-- The source, raw intermediate, and normalized target maps for the second route `q ≫ w`. -/
def secondVertices : Fin 3 → (modelOf (boundedFlatPerfectWaldhausen Z) ⟶
    modelOf (boundedFlatPerfectWaldhausen X)) :=
  ![BinaryNormalizationSimplex.sourceMap q w,
    BinaryNormalizationSimplex.intermediateMap q w, BinaryNormalizationSimplex.targetMap q w]

/--
The identity, first normalization, and total normalization references for the three second-route
vertices.
-/
def secondReferences : ∀ i,
    (BinaryNormalizationSimplex.sourceMap q w).functor ≅ (secondVertices q w i).functor :=
  Fin.cases (Iso.refl _) (Fin.cases (BinaryNormalizationSimplex.first q w)
    (Fin.cases (BinaryNormalizationSimplex.total q w) (fun i ↦ Fin.elim0 i)))

/--
The second-route vertices referenced to the fixed first-route source through the square-induced
isomorphism.
-/
def secondNodes (i : Fin 3) : Node p v :=
  ⟨secondVertices q w i, sourceIso p v q w h ≪≫ secondReferences q w i⟩

theorem second_reference : ModelSimplex.ofIsos (source p v)
    (fun i ↦ (secondNodes p v q w h i).1) (fun i ↦ (secondNodes p v q w h i).2) =
    BinaryNormalizationSimplex.simplex q w :=
  ModelSimplex.ofIsos_change_reference (sourceIso p v q w h) (secondVertices q w)
    (secondReferences q w)

/-- The second whole native binary triangle retains its actual geometric equality transport. -/
theorem second_face : (simplex p v q w h).face secondFace =
    BinaryNormalizationSimplex.simplex q w := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  refine (ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ nodes p v q w h (secondFace.toOrderHom i)) (secondNodes p v q w h) ?_).trans
    (second_reference p v q w h)
  intro i
  fin_cases i
  · apply ModelSimplex.reference_node_eq (source_eq p v q w h)
    simp [sourceIso, secondReferences]
  · rfl
  · rfl

/-- The first literal two-piece normalization path. -/
theorem first_path : PathLift (simplex p v q w h) (binaryPath 0 1 2)
    (boundedFlatPerfectPrespectrumCompHomotopy p v) := by
  intro n t x
  have he := map_binaryPath firstFace 0 1 2 t
  change StdSimplex.map firstFace.toOrderHom (binaryPath (k := 2) 0 1 2 t) =
    binaryPath (k := 4) 0 1 2 t at he
  rw [← he, prespectrumSimplexFamily_face, first_face]
  exact BinaryNormalizationSimplex.native_path p v n t x

/-- The second literal path, with the same endpoint cast as the original exported square. -/
theorem second_path : PathLift (simplex p v q w h) (binaryPath 0 3 4)
    ((boundedFlatPerfectPrespectrumCompHomotopy q w).cast
      (congrArg boundedFlatPerfectPrespectrumMap h).symm rfl) := by
  intro n t x
  have he := map_binaryPath secondFace 0 1 2 t
  change StdSimplex.map secondFace.toOrderHom (binaryPath (k := 2) 0 1 2 t) =
    binaryPath (k := 4) 0 3 4 t at he
  rw [← he, prespectrumSimplexFamily_face, second_face]
  exact BinaryNormalizationSimplex.native_path q w n t x

/-- The unchanged original reversed first binary path followed by the second. -/
def parameter : Path (StdSimplex.single 2 : StdSimplex ℝ (Fin 5)) (StdSimplex.single 4) :=
  (binaryPath 0 1 2).symm.trans (binaryPath 0 3 4)

/-- The whole original exported square homotopy is this exact scalar path, at every level. -/
theorem native : PathLift (simplex p v q w h) parameter
    (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h) := by
  rw [boundedFlatPerfectPrespectrumSquareHomotopy_eq]
  exact PathLift.trans _ (PathLift.symm _ (first_path p v q w h)) (second_path p v q w h)

end Quillen.PerfectComplexes.NativeSquareFiveSimplex
