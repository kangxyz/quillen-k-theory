/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ScalarRouteExtraction
public import Quillen.Topology.Realization.ConnectorSimplexFaces

/-!
# The moving square of an original weak triangle

The actual two-arrow weak simplex gives a continuous square between the reversed first edge
and the reversed composite edge. Its moving endpoint is the unchanged second edge; its other
endpoint is constant. This supplies the finite normalization face for selected-zero nulls
without treating a weak transformation as an isomorphism or identifying independent times.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Quillen.SimplexParameters Quillen.LoopPrespectrum Quillen.NumerableConnectorCover
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.WeakTriangleSquare

/-- The first coordinate moves the normalization edge; the second is the original null time. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 3)) :=
  ⟨fun z ↦ simplexBoundaryCone z.2 (edge (k := 1) 0 1 z.1), by fun_prop⟩

private theorem cone_vertex (i : Fin 2) (s : unitInterval) :
    simplexBoundaryCone s (StdSimplex.single i) = (edge (k := 2) 0 i.succ).symm s := by
  apply StdSimplex.ext
  rw [simplexCone_weights]
  simp only [StdSimplex.weights_single, Finsupp.mapDomain_single]
  simp [edge, StdSimplex.duple, Path.symm, Finsupp.smul_single]

/-- The initial complete null uses the original reversed first-edge clock. -/
theorem parameter_zero (s : unitInterval) :
    parameter (0, s) = (edge (k := 2) 0 1).symm s := by
  change simplexBoundaryCone s (edge (k := 1) 0 1 0) = _
  rw [Path.source]
  exact cone_vertex 0 s

/-- The terminal complete null uses the original reversed composite-edge clock. -/
theorem parameter_one (s : unitInterval) :
    parameter (1, s) = (edge (k := 2) 0 2).symm s := by
  change simplexBoundaryCone s (edge (k := 1) 0 1 1) = _
  rw [Path.target]
  exact cone_vertex 1 s

/-- The moving endpoint is the entire unchanged normalization edge. -/
theorem parameter_left (r : unitInterval) : parameter (r, 0) = edge (k := 2) 1 2 r := by
  change simplexBoundaryCone 0 (edge (k := 1) 0 1 r) = _
  rw [simplexCone_zero]
  exact StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm r))
    (unitInterval.nonneg r) (by simp) 0 1 Fin.succ

/-- The other endpoint remains the actual first vertex for every normalization time. -/
theorem parameter_right (r : unitInterval) : parameter (r, 1) = StdSimplex.single 0 :=
  simplexCone_one _

variable {V W : Model.{u}} {F G H : V ⟶ W}
  (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
  (hη : ∀ X, W.waldhausen.weq (η.app X))
  (hθ : ∀ X, W.waldhausen.weq (θ.app X))

private theorem triangle_native :
    HomotopyLift (ModelSimplex.triangle η θ hη hθ)
      (Quillen.SimplexParameters.triangle (𝟙 ⦋2⦌))
      (prespectrumTransformationCompositionHomotopy η θ hη hθ) :=
  triangle_lift _ _ _ _ _ _ (by apply ModelSimplex.ext_diagram; rfl)

/-- The first original transformation is the complete first simplex edge. -/
theorem first_edge : PathLift (ModelSimplex.triangle η θ hη hθ) (edge 0 1)
    (prespectrumTransformationHomotopy η hη) :=
  PathLift.trans_left _ (HomotopyLift.target _ (triangle_native η θ hη hθ))

/-- The second original transformation is the complete second simplex edge. -/
theorem second_edge : PathLift (ModelSimplex.triangle η θ hη hθ) (edge 1 2)
    (prespectrumTransformationHomotopy θ hθ) :=
  PathLift.trans_right _ (HomotopyLift.target _ (triangle_native η θ hη hθ))

/-- The diagonal is the original composite transformation, with no inserted pause. -/
theorem composite_edge : PathLift (ModelSimplex.triangle η θ hη hθ) (edge 0 2)
    (prespectrumTransformationHomotopy (η ≫ θ)
      (fun X ↦ W.waldhausen.weq.comp_mem _ _ (hη X) (hθ X))) :=
  HomotopyLift.source _ (triangle_native η θ hη hθ)

/-- The entire native family retains both square times before evaluation. -/
def family (n : ℕ) :
    C(unitInterval × (unitInterval × (prespectrum V).space n), (prespectrum W).space n) :=
  (prespectrumSimplexFamily (ModelSimplex.triangle η θ hη hθ) n).comp
    ⟨fun z ↦ (parameter (z.1, z.2.1), z.2.2), by fun_prop⟩

/-- Realization of the actual weak triangle supplies all four prescribed whole faces. -/
def square :
    (prespectrumTransformationHomotopy η hη).symm.Square
      (prespectrumTransformationHomotopy (η ≫ θ)
        (fun X ↦ W.waldhausen.weq.comp_mem _ _ (hη X) (hθ X))).symm
      (prespectrumTransformationHomotopy θ hθ)
      (LoopPrespectrum.Homotopy.refl (prespectrumMap F)) where
  level := family η θ hη hθ
  at_zero n s x := by
    change prespectrumSimplexFamily _ n (parameter (0, s), x) = _
    rw [parameter_zero]
    exact first_edge η θ hη hθ n (unitInterval.symm s) x
  at_one n s x := by
    change prespectrumSimplexFamily _ n (parameter (1, s), x) = _
    rw [parameter_one]
    exact composite_edge η θ hη hθ n (unitInterval.symm s) x
  left n r x := by
    change prespectrumSimplexFamily _ n (parameter (r, 0), x) = _
    rw [parameter_left]
    exact second_edge η θ hη hθ n r x
  right n r x := by
    change prespectrumSimplexFamily _ n (parameter (r, 1), x) = _
    rw [parameter_right]
    have h := first_edge η θ hη hθ n 0 x
    rw [Path.source] at h
    exact h.trans ((prespectrumTransformationHomotopy η hη).at_zero n x)
  at_point n r s := prespectrumSimplexFamily_point _ n _
  comm n r s x t := prespectrumSimplexFamily_structure _ n _ x t

/-- The complete selected scalar surface is retained literally by the resulting square. -/
theorem square_apply (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (square η θ hη hθ).level n (r, (s, x)) =
      prespectrumSimplexFamily (ModelSimplex.triangle η θ hη hθ) n (parameter (r, s), x) := rfl

/-- An actual equality of transformations recovers a separately specified original diagonal. -/
def squareOfComposite (ζ : F.functor ⟶ H.functor)
    (hζ : ∀ X, W.waldhausen.weq (ζ.app X)) (e : η ≫ θ = ζ) :
    (prespectrumTransformationHomotopy η hη).symm.Square
      (prespectrumTransformationHomotopy ζ hζ).symm
      (prespectrumTransformationHomotopy θ hθ)
      (LoopPrespectrum.Homotopy.refl (prespectrumMap F)) := by
  subst ζ
  exact square η θ hη hθ

/-- Diagonal equality transport leaves the entire two-time family unchanged. -/
theorem squareOfComposite_apply (ζ : F.functor ⟶ H.functor)
    (hζ : ∀ X, W.waldhausen.weq (ζ.app X)) (e : η ≫ θ = ζ)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (squareOfComposite η θ hη hθ ζ hζ e).level n (r, (s, x)) =
      prespectrumSimplexFamily (ModelSimplex.triangle η θ hη hθ) n (parameter (r, s), x) := by
  subst ζ
  rfl

end Quillen.Waldhausen.IteratedS.WeakTriangleSquare
