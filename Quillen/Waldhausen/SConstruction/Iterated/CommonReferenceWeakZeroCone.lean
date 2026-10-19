/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceWeakZeroSimplex
public import Quillen.Topology.Realization.ConnectorSimplexFaces

/-!
# A finite normalization cone retaining the original weak null

The cone height and the entire old normalization parameter are independent. Its reference slice
is exactly the chosen reversed weak-zero track. This newly specified affine normalization family
is not asserted to equal an independently selected realization-product interior.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Quillen.SimplexParameters Quillen.NumerableConnectorCover
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceWeakZero
variable {V W : Model.{u}} (F : V ⟶ W) {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node F)
  (η : (zeroHom V W).functor ⟶ F.functor)
  (hη : ∀ X, W.waldhausen.weq (η.app X))

/-- The finite cone retains a separate height and the full normalization parameter. -/
def coneParameter : C(unitInterval × StdSimplex ℝ (Fin (k + 2)),
    StdSimplex ℝ (Fin (k + 3))) :=
  ⟨fun z ↦ simplexBoundaryCone z.1 z.2, continuous_simplexBoundaryCone _⟩

/-- The original normalization family is exactly the whole initial face. -/
theorem cone_zero (z : StdSimplex ℝ (Fin (k + 2))) :
    coneParameter (0, z) = StdSimplex.map Fin.succ z := simplexCone_zero z

/-- The terminal face is the selected zero vertex, independent of normalization. -/
theorem cone_one (z : StdSimplex ℝ (Fin (k + 2))) :
    coneParameter (1, z) = StdSimplex.single 0 := simplexCone_one z

/-- On the actual reference vertex the cone uses exactly the original reversed edge time. -/
theorem cone_reference (r : unitInterval) :
    coneParameter (r, StdSimplex.single (0 : Fin (k + 2))) =
      (edge (k := k + 2) 0 1).symm r := by
  apply StdSimplex.ext
  change (simplexBoundaryCone r (StdSimplex.single (0 : Fin (k + 2)))).weights = _
  rw [simplexCone_weights]
  simp only [StdSimplex.weights_single, Finsupp.mapDomain_single]
  change Finsupp.single 0 (r : ℝ) + (1 - (r : ℝ)) • Finsupp.single 1 1 = _
  simp [edge, StdSimplex.duple, Path.symm, Finsupp.smul_single]

/-- Evaluation of the complete finite parameter is continuous at every original level. -/
def coneFamily (n : ℕ) : C((unitInterval × StdSimplex ℝ (Fin (k + 2))) ×
    (prespectrum V).space n, (prespectrum W).space n) :=
  (prespectrumSimplexFamily (simplex F N η hη) n).comp
    ⟨fun z ↦ (coneParameter z.1, z.2), by fun_prop⟩

/-- The whole original normalization family survives, not only its realized vertices. -/
theorem coneFamily_zero (n : ℕ) (z : StdSimplex ℝ (Fin (k + 2)))
    (x : (prespectrum V).space n) :
    coneFamily F N η hη n ((0, z), x) =
      prespectrumSimplexFamily (normalizationSimplex F N) n (z, x) := by
  change prespectrumSimplexFamily (simplex F N η hη) n (coneParameter (0, z), x) = _
  rw [cone_zero]
  exact ModelSimplex.prependWeak_tail_native (normalizationSimplex F N) η hη n z x

/-- The selected null is retained at every original time and level on the reference slice. -/
theorem coneFamily_reference (n : ℕ) (r : unitInterval) (x : (prespectrum V).space n) :
    coneFamily F N η hη n ((r, StdSimplex.single 0), x) =
      (prespectrumTransformationHomotopy η hη).level n (unitInterval.symm r, x) := by
  change prespectrumSimplexFamily (simplex F N η hη) n
    (coneParameter (r, StdSimplex.single 0), x) = _
  rw [cone_reference]
  exact reverse_native F N η hη n r x

/-- The entire terminal normalization face is the actual selected native zero. -/
theorem coneFamily_one (n : ℕ) (z : StdSimplex ℝ (Fin (k + 2)))
    (x : (prespectrum V).space n) :
    coneFamily F N η hη n ((1, z), x) = (prespectrum W).point n := by
  have h := edge_native F N η hη n 0 x
  rw [Path.source] at h
  change prespectrumSimplexFamily (simplex F N η hη) n (coneParameter (1, z), x) = _
  rw [cone_one, h, (prespectrumTransformationHomotopy η hη).at_zero]
  rw [prespectrumMap_zeroHom]
  rfl

/-- The complete family fixes the original point for every normalization and null parameter. -/
theorem coneFamily_point (n : ℕ) (r : unitInterval) (z : StdSimplex ℝ (Fin (k + 2))) :
    coneFamily F N η hη n ((r, z), (prespectrum V).point n) = (prespectrum W).point n :=
  prespectrumSimplexFamily_point _ _ _

/-- The original structure coordinate is independent of the null and normalization parameters. -/
theorem coneFamily_structure (n : ℕ) (r : unitInterval)
    (z : StdSimplex ℝ (Fin (k + 2))) (x : (prespectrum V).space n) (t : unitInterval) :
    coneFamily F N η hη (n + 1) ((r, z), (prespectrum V).structureMap n x t) =
      (prespectrum W).structureMap n (coneFamily F N η hη n ((r, z), x)) t :=
  prespectrumSimplexFamily_structure _ _ _ _ _

end Quillen.Waldhausen.IteratedS.CommonReferenceWeakZero
