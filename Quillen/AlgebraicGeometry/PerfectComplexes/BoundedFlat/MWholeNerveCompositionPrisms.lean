/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionReferences
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryNativePath
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductReferenceRows
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily

/-!
# The actual finite-product composition prisms

The two products retain all 31 original H0 nodes and the actual three binary normalization
nodes. Their parameters preserve the two original halves, every native level and all four
varying original H0 sides. Complete endpoint references are checked separately from native
values; no surrounding boundary or higher filler is inferred.
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
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge BassH0Merge BassH1Join
attribute [local irreducible] boundedFlatNormalizedPullback

private theorem binary_nodes_simplex {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ModelSimplex.ofIsos (BinaryNormalizationSimplex.sourceMap f g)
      (fun i ↦ (binaryNodes f g i).1) (fun i ↦ (binaryNodes f g i).2) =
      BinaryNormalizationSimplex.simplex f g := by
  let Fs : Fin 3 → (modelOf (boundedFlatPerfectWaldhausen Z) ⟶
      modelOf (boundedFlatPerfectWaldhausen X)) :=
    ![BinaryNormalizationSimplex.sourceMap f g, BinaryNormalizationSimplex.intermediateMap f g,
      BinaryNormalizationSimplex.targetMap f g]
  let refs : ∀ i, (BinaryNormalizationSimplex.sourceMap f g).functor ≅ (Fs i).functor :=
    Fin.cases (Iso.refl _) (Fin.cases (BinaryNormalizationSimplex.first f g)
      (Fin.cases (BinaryNormalizationSimplex.total f g) (fun j ↦ Fin.elim0 j)))
  exact ModelSimplex.ofIsos_nodes_congr (binaryNodes f g) (fun i ↦ ⟨Fs i, refs i⟩)
    (by intro i; fin_cases i <;> rfl)

private theorem reanchored_product_simplex {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (F₀ : V ⟶ W) (Fs : Fin (p + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (Fs i).functor)
    (G₀ : W ⟶ T) (Gs : Fin (q + 1) → (W ⟶ T))
    (refs : ∀ i, G₀.functor ≅ (Gs i).functor) (η : F.functor ≅ (F₀ ≫ G₀).functor) :
    ModelSimplex.ofIsos F (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).1)
      (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).2) =
      CommonReferenceProduct.simplex F₀ Fs ρ G₀ Gs refs := by
  exact ModelSimplex.reanchorSimplex_eq η
    (fun i ↦ ⟨CommonReferenceProduct.vertices Fs Gs i,
      CommonReferenceProduct.references F₀ Fs ρ G₀ Gs refs i⟩)

private theorem reanchored_product_comp {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (F₀ : V ⟶ W) (Fs : Fin (p + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (Fs i).functor)
    (G₀ : W ⟶ T) (Gs : Fin (q + 1) → (W ⟶ T))
    (refs : ∀ i, G₀.functor ≅ (Gs i).functor) (η : F.functor ≅ (F₀ ≫ G₀).functor)
    (n : ℕ) (x : (prespectrum V).space n)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    prespectrumSimplexFamily
      (ModelSimplex.ofIsos F (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).1)
        (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).2)) n
      (Quillen.SimplexGrid.parameter.{u} p q (z, w), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ Gs refs) n
        (w, prespectrumSimplexFamily (ModelSimplex.ofIsos F₀ Fs ρ) n (z, x)) :=
  (congrArg (fun S ↦ prespectrumSimplexFamily S n
    (Quillen.SimplexGrid.parameter.{u} p q (z, w), x))
    (reanchored_product_simplex F F₀ Fs ρ G₀ Gs refs η)).trans
      (CommonReferenceProduct.prespectrum_comp F₀ Fs ρ G₀ Gs refs n x z w)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The right-first anchor uses the actual Laurent composite-to-binary-source transport. -/
def laurentPrismAnchor :
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)).functor ≅
      (BassH0Diagram.reference P u ≫ BinaryNormalizationSimplex.sourceMap
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (coefficientMap P ((laurentUnderFunctor R).map v))).functor :=
  (rightStartingAnchor P u v w ≪≫ BassH1References.firstIso P u (v ≫ w)) ≪≫
    isoWhiskerLeft (BassH0Diagram.reference P u).functor
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (laurentComposition_total P v w))))

/-- The left-middle anchor uses the actual coefficient composite-to-binary-source transport. -/
def coefficientPrismAnchor :
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)).functor ≅
      (BinaryNormalizationSimplex.sourceMap (coefficientMap P v) (coefficientMap P u) ≫
        BassH0Diagram.reference P w).functor :=
  (h0Anchor P (u ≫ v) w ≪≫ BassH1References.middleIso P (u ≫ v) w) ≪≫
    isoWhiskerRight (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (coefficientMap_comp P u v)))) (BassH0Diagram.reference P w).functor

/-- All 93 actual nodes of H0 followed by the original Laurent binary triangle. -/
def laurentPrismNodes : Fin 93 →
    CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w)) :=
  reanchoredProductNode _ (BassH0Diagram.reference P u)
    (fun i ↦ (BassH0Diagram.nodes P u i).1) (fun i ↦ (BassH0Diagram.nodes P u i).2)
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((laurentUnderFunctor R).map w))
      (coefficientMap P ((laurentUnderFunctor R).map v)))
    (fun i ↦ (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map w))
      (coefficientMap P ((laurentUnderFunctor R).map v)) i).1)
    (fun i ↦ (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map w))
      (coefficientMap P ((laurentUnderFunctor R).map v)) i).2)
    (laurentPrismAnchor P u v w)

/-- All 93 actual nodes of the original coefficient binary triangle followed by H0. -/
def coefficientPrismNodes : Fin 93 →
    CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w)) :=
  reanchoredProductNode _
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P v) (coefficientMap P u))
    (fun i ↦ (binaryNodes (coefficientMap P v) (coefficientMap P u) i).1)
    (fun i ↦ (binaryNodes (coefficientMap P v) (coefficientMap P u) i).2)
    (BassH0Diagram.reference P w)
    (fun i ↦ (BassH0Diagram.nodes P w i).1) (fun i ↦ (BassH0Diagram.nodes P w i).2)
    (coefficientPrismAnchor P u v w)

/-- The literal two-half Laurent time remains independent of both original H0 coordinates. -/
def laurentPrismParameter : C(Quillen.SimplexCubeExtension.Cube, StdSimplex ℝ (Fin 93)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 30 2
    (BassH0Diagram.parameter (z 1, z 2), binaryPath (k := 2) 0 1 2 (z 0)), by fun_prop⟩

/-- The literal two-half coefficient time is the first factor of the actual product. -/
def coefficientPrismParameter : C(Quillen.SimplexCubeExtension.Cube, StdSimplex ℝ (Fin 93)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 2 30
    (binaryPath (k := 2) 0 1 2 (z 0), BassH0Diagram.parameter (z 1, z 2)), by fun_prop⟩

/-- The actual Laurent composition prism in the common full-reference nerve. -/
def laurentPrism : C(Quillen.SimplexCubeExtension.Cube,
    |nerve (Codiscrete (CommonReferenceNerve.Node
      (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)).comp laurentPrismParameter.{u}

/-- The actual coefficient composition prism in the same common full-reference nerve. -/
def coefficientPrism : C(Quillen.SimplexCubeExtension.Cube,
    |nerve (Codiscrete (CommonReferenceNerve.Node
      (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)).comp
    coefficientPrismParameter.{u}

/-- Every original Laurent composition value retains both native normalization halves. -/
theorem laurent_prism_native (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily _ (laurentPrismNodes P u v w) n
      (laurentPrismParameter.{u} ![q, s, t], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (BassH0Diagram.parameter (s, t), x)) := by
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  refine (reanchored_product_comp _ _ _ _ _ _ _ (laurentPrismAnchor P u v w) n x
    (BassH0Diagram.parameter (s, t)) (binaryPath (k := 2) 0 1 2 q)).trans ?_
  rw [binary_nodes_simplex]
  exact BinaryNormalizationSimplex.native_path _ _ n q _

/-- Every original coefficient composition value retains both native normalization halves. -/
theorem coefficient_prism_native (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily _ (coefficientPrismNodes P u v w) n
      (coefficientPrismParameter.{u} ![q, s, t], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (BassH0Diagram.parameter (s, t),
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) := by
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  refine (reanchored_product_comp _ _ _ _ _ _ _ (coefficientPrismAnchor P u v w) n x
    (binaryPath (k := 2) 0 1 2 q) (BassH0Diagram.parameter (s, t))).trans ?_
  rw [binary_nodes_simplex, BinaryNormalizationSimplex.native_path]
  rfl

end Quillen.PerfectComplexes.BassMWholeNerve
