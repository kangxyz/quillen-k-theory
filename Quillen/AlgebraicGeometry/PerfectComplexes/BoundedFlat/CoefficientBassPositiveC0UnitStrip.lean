/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierRails

/-!
# The actual coefficient-binary and forward-unit carrier strip

The unit nodes retain the accepted beta-conjugated original Laurent projection unit. Their
product uses the original coefficient triangle and middleIso, and its two whole attachment
sides are the ordinary and commonUnit-shifted projection starts. No tips are identified and
no replacement seed/null word or mixed filler is assumed.
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC0UnitStrip
open BassH0Merge CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierAttachment CoefficientBassPositiveC0CarrierRails
open LaurentUnitReferenceSpecialization
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Both references use the original split projection, with its actual beta-conjugated unit. -/
def unitNodes (d : Under R) : Fin 2 → Node (BassProjectionPath.source P d) :=
  ![⟨BassProjectionPath.source P d, Iso.refl _⟩,
    ⟨BassProjectionPath.source P d, splitProjectionUnit P d⟩]

/-- The six nodes are the literal original composition product with the original middleIso. -/
def unitProductNodes (i : Fin 6) : Node (laurentReference P p q) :=
  BassH1Join.reanchoredProductNode (laurentReference P p q)
    (BassMComponents.coefficientSource P p q)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).1)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).2)
    (BassProjectionPath.source P c) (fun j ↦ (unitNodes P c j).1)
    (fun j ↦ (unitNodes P c j).2) (BassMReferences.middleIso P p q) i

/-- Entire ordinary product column, including all reference isomorphisms. -/
theorem unitProduct_lower_nodes (i : Fin 3) :
    unitProductNodes P p q (SimplexGrid.index 2 1 (i, 0)) =
      coefficientProjectionNode P p q i := by
  have h := BassH1Join.product_row_nodes (laurentReference P p q)
    (BassMComponents.coefficientSource P p q)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).1)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).2)
    (BassProjectionPath.source P c) (fun j ↦ (unitNodes P c j).1)
    (fun j ↦ (unitNodes P c j).2) (BassMReferences.middleIso P p q) i 0
  change unitProductNodes P p q (SimplexGrid.index 2 1 (i, 0)) =
    preReferenceNode (laurentReference P p q) (BassMComponents.coefficientNodes P p q i).1
      (coefficientProjectionNode P p q i).2
      (⟨BassProjectionPath.source P c, Iso.refl _⟩ : Node (BassProjectionPath.source P c)) at h
  exact h.trans (preReferenceNode_source (laurentReference P p q)
    (BassMComponents.coefficientNodes P p q i).1 (coefficientProjectionNode P p q i).2)

/-- The full upper product column is the actual shifted column, not equal to the lower one. -/
theorem unitProduct_upper_nodes (i : Fin 3) :
    unitProductNodes P p q (SimplexGrid.index 2 1 (i, 1)) =
      anchorNode (commonUnit P p q) (coefficientProjectionNode P p q i) := by
  have h := BassH1Join.product_row_nodes (laurentReference P p q)
    (BassMComponents.coefficientSource P p q)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).1)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).2)
    (BassProjectionPath.source P c) (fun j ↦ (unitNodes P c j).1)
    (fun j ↦ (unitNodes P c j).2) (BassMReferences.middleIso P p q) i 1
  have hu := coefficientProjection_shifted_node P p q i
  rw [coefficientProjectionNode_original] at hu
  change unitProductNodes P p q (SimplexGrid.index 2 1 (i, 1)) =
    (⟨(BassMComponents.coefficientNodes P p q i).1 ≫ BassProjectionPath.source P c,
      (coefficientProjectionNode P p q i).2 ≪≫
        isoWhiskerLeft (BassMComponents.coefficientNodes P p q i).1.functor
          (splitProjectionUnit P c)⟩ : Node (laurentReference P p q)) at h
  exact h.trans hu.symm

/-- Original coefficient binary time and forward unit-edge time remain independent. -/
def unitProductParameter : C(I × I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (unitProductNodes P p q)).comp
    ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 2 1
      (binaryPath (k := 2) 0 1 2 z.1, edge (k := 1) 0 1 z.2), by fun_prop⟩

/-- The whole projection start rail is the accepted coefficient-projection node family. -/
theorem projection_start (r : I) :
    positiveProjectionParameter P p q (r, 0) =
      parameter (laurentReference P p q) (coefficientProjectionNode P p q)
        (binaryPath (k := 2) 0 1 2 r) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 r, StdSimplex.map BassProjectionPath.plusFace.toOrderHom
      (binaryPath (k := 2) 0 1 2 0))) = _
  rw [Path.source, StdSimplex.map_single]
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 r, StdSimplex.single 0)) = _
  rw [SimplexGrid.parameter_column, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (binaryPath (k := 2) 0 1 2 r))
    (funext (coefficientProjectionNode_original P p q))

/-- The entire unit strip begins on the ordinary projection start, for every coefficient time. -/
theorem unitProduct_lower (r : I) :
    unitProductParameter P p q (r, 0) = positiveProjectionParameter P p q (r, 0) := by
  rw [projection_start]
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 1
    (binaryPath (k := 2) 0 1 2 r, edge (k := 1) 0 1 0)) = _
  rw [Path.source, SimplexGrid.parameter_column, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (binaryPath (k := 2) 0 1 2 r))
    (funext (unitProduct_lower_nodes P p q))

/-- The entire unit strip ends on the shifted projection start, retaining the actual tau. -/
theorem unitProduct_upper (r : I) :
    unitProductParameter P p q (r, 1) = shiftedProjectionParameter P p q (r, 0) := by
  change unitProductParameter P p q (r, 1) =
    mapParameter (anchorNode (commonUnit P p q)) (positiveProjectionParameter P p q (r, 0))
  rw [projection_start, mapParameter_parameter]
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 1
    (binaryPath (k := 2) 0 1 2 r, edge (k := 1) 0 1 1)) = _
  rw [Path.target, SimplexGrid.parameter_column, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (binaryPath (k := 2) 0 1 2 r))
    (funext (unitProduct_upper_nodes P p q))

/-- Original H0 seed's projection source and its full common-unit-shifted copy. -/
def sourceUnitNodes : Fin 2 → Node (laurentReference P p q) :=
  ![sourceProjectionNodes P p q 0, anchorNode (commonUnit P p q) (sourceProjectionNodes P p q 0)]

/-- Original H1-middle seed's projection source and its separately shifted reference. -/
def targetUnitNodes : Fin 2 → Node (laurentReference P p q) :=
  ![targetProjectionNodes P p q 0, anchorNode (commonUnit P p q) (targetProjectionNodes P p q 0)]

private theorem source_start_node :
    coefficientProjectionNode P p q 0 = sourceProjectionNodes P p q 0 :=
  (coefficientProjectionNode_original P p q 0).symm.trans
    (BassMOuterJoin.source_middle_plus_nodes P p q 0)

private theorem target_start_node :
    coefficientProjectionNode P p q 2 = targetProjectionNodes P p q 0 :=
  (coefficientProjectionNode_original P p q 2).symm.trans
    ((BassMOuterJoin.target_middle_plus_nodes P p q 0).trans
      (BassMOuterJoin.h1_middle_plus_nodes P p q 15).symm)

/-- Both complete original H0 endpoint references match the actual product row. -/
theorem unitProduct_source_nodes (j : Fin 2) :
    unitProductNodes P p q (SimplexGrid.index 2 1 (0, j)) = sourceUnitNodes P p q j := by
  fin_cases j
  · exact (unitProduct_lower_nodes P p q 0).trans (source_start_node P p q)
  · exact (unitProduct_upper_nodes P p q 0).trans
      (congrArg (anchorNode (commonUnit P p q)) (source_start_node P p q))

/-- Both complete H1-middle endpoint references match the actual product row. -/
theorem unitProduct_target_nodes (j : Fin 2) :
    unitProductNodes P p q (SimplexGrid.index 2 1 (2, j)) = targetUnitNodes P p q j := by
  fin_cases j
  · exact (unitProduct_lower_nodes P p q 2).trans (target_start_node P p q)
  · exact (unitProduct_upper_nodes P p q 2).trans
      (congrArg (anchorNode (commonUnit P p q)) (target_start_node P p q))

/-- The entire original-source unit edge is the r=0 product rail. -/
theorem unitProduct_source (t : I) :
    unitProductParameter P p q (0, t) =
      parameter (laurentReference P p q) (sourceUnitNodes P p q) (edge (k := 1) 0 1 t) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 1
    (binaryPath (k := 2) 0 1 2 0, edge (k := 1) 0 1 t)) = _
  rw [Path.source, SimplexGrid.parameter_row, parameter_face]
  exact congrArg (fun N : Fin 2 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (edge (k := 1) 0 1 t))
    (funext (unitProduct_source_nodes P p q))

/-- The entire original-target unit edge is the r=1 product rail. -/
theorem unitProduct_target (t : I) :
    unitProductParameter P p q (1, t) =
      parameter (laurentReference P p q) (targetUnitNodes P p q) (edge (k := 1) 0 1 t) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 1
    (binaryPath (k := 2) 0 1 2 1, edge (k := 1) 0 1 t)) = _
  rw [Path.target, SimplexGrid.parameter_row, parameter_face]
  exact congrArg (fun N : Fin 2 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (edge (k := 1) 0 1 t))
    (funext (unitProduct_target_nodes P p q))

/-- Only the common reference is changed; the complete product diagram stays original. -/
theorem unitProduct_original :
    ModelSimplex.ofIsos (laurentReference P p q)
      (fun i ↦ (unitProductNodes P p q i).1) (fun i ↦ (unitProductNodes P p q i).2) =
    CommonReferenceProduct.simplex (BassMComponents.coefficientSource P p q)
      (fun j ↦ (BassMComponents.coefficientNodes P p q j).1)
      (fun j ↦ (BassMComponents.coefficientNodes P p q j).2)
      (BassProjectionPath.source P c) (fun j ↦ (unitNodes P c j).1)
      (fun j ↦ (unitNodes P c j).2) :=
  ModelSimplex.ofIsos_change_reference (BassMReferences.middleIso P p q) _ _

/-- Whole native product evaluation at all n. Original-unit-track identification remains a
separate exact normalization lemma; it is not a supplied hypothesis of this construction. -/
theorem unitProduct_family (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (laurentReference P p q) (unitProductNodes P p q) n
      (SimplexGrid.parameter.{u + 1} 2 1
        (binaryPath (k := 2) 0 1 2 r, edge (k := 1) 0 1 t), x) =
    prespectrumSimplexFamily
      (ModelSimplex.ofIsos (BassProjectionPath.source P c)
        (fun j ↦ (unitNodes P c j).1) (fun j ↦ (unitNodes P c j).2)) n
      (edge (k := 1) 0 1 t, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) := by
  rw [prespectrumFamily_eq, unitProduct_original]
  refine (CommonReferenceProduct.prespectrum_comp.{u + 1}
    (BassMComponents.coefficientSource P p q)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).1)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).2)
    (BassProjectionPath.source P c) (fun j ↦ (unitNodes P c j).1)
    (fun j ↦ (unitNodes P c j).2) n x
    (binaryPath (k := 2) 0 1 2 r) (edge (k := 1) 0 1 t)).trans ?_
  exact congrArg (fun y ↦ prespectrumSimplexFamily
    (ModelSimplex.ofIsos (BassProjectionPath.source P c)
      (fun j ↦ (unitNodes P c j).1) (fun j ↦ (unitNodes P c j).2)) n
    (edge (k := 1) 0 1 t, y)) (BassMComponents.coefficient_native P p q n r x)

/-- Compact evaluation of the same finite unit strip, with neither parameter changed. -/
theorem unitProductParameter_family (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (laurentReference P p q) (unitProductParameter P p q)
      n ((r, t), x) =
    prespectrumSimplexFamily
      (ModelSimplex.ofIsos (BassProjectionPath.source P c)
        (fun j ↦ (unitNodes P c j).1) (fun j ↦ (unitNodes P c j).2)) n
      (edge (k := 1) 0 1 t, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) :=
  (compactPrespectrumFamily_eq_simplex _ _ (unitProductNodes P p q) (r, t)
    (SimplexGrid.parameter.{u + 1} 2 1
      (binaryPath (k := 2) 0 1 2 r, edge (k := 1) 0 1 t)) rfl n x).trans
    (unitProduct_family P p q n r t x)

/-- The one C0 reversal switches only the coefficient coordinate of the whole unit strip. -/
theorem reversed_unitProduct_rails (t : I) :
    unitProductParameter P p q (unitInterval.symm 0, t) =
      parameter (laurentReference P p q) (targetUnitNodes P p q) (edge (k := 1) 0 1 t) ∧
    unitProductParameter P p q (unitInterval.symm 1, t) =
      parameter (laurentReference P p q) (sourceUnitNodes P p q) (edge (k := 1) 0 1 t) := by
  constructor
  · simpa using unitProduct_target P p q t
  · simpa using unitProduct_source P p q t

end Quillen.PerfectComplexes.CoefficientBassPositiveC0UnitStrip
