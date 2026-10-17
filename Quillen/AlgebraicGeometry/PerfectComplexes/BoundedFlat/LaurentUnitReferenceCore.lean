/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitReferenceNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MComponentReferences

/-!
# The original Laurent beta, total unit, and C0 full references

This module retains the original specialization statements and definitions.
Its imports include the accepted unit owner and the actual defining owner MComponentReferences.
It stops before positive chart-side anchors, p/q/l rail identification, C1, or any mixed lift.
-/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.FunctorIdentityAutomorphism
universe u

namespace Quillen.PerfectComplexes.LaurentUnitReferenceSpecialization
open GlobalUnitReferenceNaturality BassH0Merge
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The prescribed forward Laurent scalar, without an inverse or a polynomial lift. -/
def laurentUnit (d : Under R) :
    (Γ(space (op P, (laurentUnderFunctor R).obj d), ⊤))ˣ :=
  boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj d)
    (laurentGlobalUnit d.right)

/-- The original faithful small-model lift of that same scalar. -/
abbrev smallUnit (d : Under R) :=
  boundedFlatCoefficientSmallUnitIso (op P, (laurentUnderFunctor R).obj d) (laurentUnit P d)

/-- The actual direct projection unit retains its chosen-zero conjugation and both lifts. -/
def projectionUnit (d : Under R) :
    (normalizedMap (laurentProjection P d)).functor ≅
      (normalizedMap (laurentProjection P d)).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    ((boundedFlatPullbackNormalizationIso (laurentProjection P d)).symm ≪≫
      boundedFlatPerfectPullbackUnitIso (laurentProjection P d) (laurentUnit P d) ≪≫
        boundedFlatPullbackNormalizationIso (laurentProjection P d)) AsSmall.up)

/-- This is precisely the positive split source's forward equality to the direct projection. -/
theorem projection_source_eq (d : Under R) :
    (BassProjectionPath.source P d).functor =
      (normalizedMap (laurentProjection P d)).functor :=
  congrArg (fun f ↦ (normalizedMap f).functor) (laurentPlus_projection P d)

/-- The original positive-chart source cast, in its forward orientation. -/
def projectionSourceIso (d : Under R) :
    (BassProjectionPath.source P d).functor ≅
      (normalizedMap (laurentProjection P d)).functor :=
  eqToIso (projection_source_eq P d)

/-- Transport the original direct unit onto the original split source, keeping beta visible. -/
def splitProjectionUnit (d : Under R) :
    (BassProjectionPath.source P d).functor ≅ (BassProjectionPath.source P d).functor :=
  projectionSourceIso P d ≪≫ projectionUnit P d ≪≫ (projectionSourceIso P d).symm

/-- The direct unit is the actual target action by the accepted normalization/lift theorem. -/
theorem projectionUnit_eq_action (d : Under R) :
    projectionUnit P d =
      onFunctor (normalizedMap (laurentProjection P d)).functor (smallUnit P d) :=
  normalizedModelUnit_eq_onFunctor (i := (op P, d))
    (k := (op P, (laurentUnderFunctor R).obj d))
    (laurentProjection P d) (laurentUnit P d)

/-- The concrete beta conjugation cancels only after its actual full reference is used. -/
theorem splitProjectionUnit_eq_action (d : Under R) :
    splitProjectionUnit P d =
      onFunctor (BassProjectionPath.source P d).functor (smallUnit P d) := by
  unfold splitProjectionUnit
  rw [projectionUnit_eq_action]
  have h := reference_intertwine (op P, (laurentUnderFunctor R).obj d) (laurentUnit P d)
    (BassProjectionPath.source P d).functor
    (normalizedMap (laurentProjection P d)).functor (projectionSourceIso P d)
  rw [← Iso.trans_assoc, ← h, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- The beta-specific unit join is equality of complete dependent source nodes. -/
theorem projection_source_unit_node (d : Under R) :
    (⟨BassProjectionPath.source P d, splitProjectionUnit P d⟩ :
      Σ F : modelOf (boundedFlatPerfectWaldhausen (space (op P, d))) ⟶
        modelOf (boundedFlatPerfectWaldhausen
          (space (op P, (laurentUnderFunctor R).obj d))),
        (BassProjectionPath.source P d).functor ≅ F.functor) =
      ⟨normalizedMap (laurentProjection P d), projectionSourceIso P d ≪≫ projectionUnit P d⟩ := by
  have h : splitProjectionUnit P d ≪≫ projectionSourceIso P d =
      projectionSourceIso P d ≪≫ projectionUnit P d := by
    simp only [splitProjectionUnit, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  apply ModelSimplex.reference_node_eq (projection_source_eq P d)
  simpa only [Iso.trans_hom, projectionSourceIso, eqToIso.hom] using congrArg Iso.hom h

variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The chosen tau uses the literal total T, with its original unit and normalization. -/
def commonUnit :
    (BassOverlap.commonReference P p q).functor ≅ (BassOverlap.commonReference P p q).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    ((boundedFlatPullbackNormalizationIso
      (laurentProjection P c ≫ coefficientMap P q ≫ coefficientMap P p)).symm ≪≫
      boundedFlatPerfectPullbackUnitIso
        (laurentProjection P c ≫ coefficientMap P q ≫ coefficientMap P p) (laurentUnit P c) ≪≫
      boundedFlatPullbackNormalizationIso
        (laurentProjection P c ≫ coefficientMap P q ≫ coefficientMap P p)) AsSmall.up)

/-- The concrete total unit is exactly the original small Laurent identity action. -/
theorem commonUnit_eq_action :
    commonUnit P p q = onFunctor (BassOverlap.commonReference P p q).functor (smallUnit P c) :=
  normalizedModelUnit_eq_onFunctor (i := (op P, a))
    (k := (op P, (laurentUnderFunctor R).obj c))
    (laurentProjection P c ≫ coefficientMap P q ≫ coefficientMap P p) (laurentUnit P c)

/-- Every original full Laurent reference intertwines with this fixed actual tau. -/
theorem common_reference (N : BassOverlap.Node P p q) :
    commonUnit P p q ≪≫ N.2 = N.2 ≪≫ onFunctor N.1.functor (smallUnit P c) := by
  rw [commonUnit_eq_action]
  exact reference_intertwine (op P, (laurentUnderFunctor R).obj c) (laurentUnit P c)
    (BassOverlap.commonReference P p q).functor N.1.functor N.2

/-- The C0 source-projection column in a readable form, with its actual middleIso. -/
def coefficientProjectionNode (i : Fin 3) : BassOverlap.Node P p q :=
  ⟨(BassMComponents.coefficientNodes P p q i).1 ≫ BassProjectionPath.source P c,
    BassMReferences.middleIso P p q ≪≫
      isoWhiskerRight (BassMComponents.coefficientNodes P p q i).2
        (BassProjectionPath.source P c).functor⟩

/-- Decode the actual grid before identifying the entire dependent C0 node. -/
theorem coefficientProjectionNode_original (i : Fin 3) :
    BassMReferences.middleNodes P p q (Quillen.SimplexGrid.index 2 4 (i, 0)) =
      coefficientProjectionNode P p q i := by
  have h := BassH1Join.product_row_nodes (BassOverlap.commonReference P p q)
    (BassMComponents.coefficientSource P p q)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).1)
    (fun j ↦ (BassMComponents.coefficientNodes P p q j).2)
    (BassProjectionPath.source P c) (fun j ↦ (BassProjectionPath.nodes P c j).1)
    (fun j ↦ (BassProjectionPath.nodes P c j).2) (BassMReferences.middleIso P p q) i 0
  exact h.trans (preReferenceNode_source (BassOverlap.commonReference P p q)
    (BassMComponents.coefficientNodes P p q i).1
    (BassMReferences.middleIso P p q ≪≫
      isoWhiskerRight (BassMComponents.coefficientNodes P p q i).2
        (BassProjectionPath.source P c).functor))

/-- C0 uses the concrete beta-conjugated projection unit after its original coefficient node. -/
theorem coefficientProjection_unit_reference (i : Fin 3) :
    commonUnit P p q ≪≫ (coefficientProjectionNode P p q i).2 =
      (coefficientProjectionNode P p q i).2 ≪≫
        isoWhiskerLeft (BassMComponents.coefficientNodes P p q i).1.functor
          (splitProjectionUnit P c) := by
  have h : isoWhiskerLeft (BassMComponents.coefficientNodes P p q i).1.functor
      (splitProjectionUnit P c) =
      onFunctor (coefficientProjectionNode P p q i).1.functor (smallUnit P c) := by
    rw [splitProjectionUnit_eq_action]
    apply Iso.ext
    ext X
    rfl
  rw [h]
  exact common_reference P p q (coefficientProjectionNode P p q i)

/-- The actual C0 grid node retains both its original index and its full shifted reference. -/
theorem coefficientProjection_shifted_node (i : Fin 3) :
    anchorNode (commonUnit P p q)
      (BassMReferences.middleNodes P p q (Quillen.SimplexGrid.index 2 4 (i, 0))) =
      (⟨(BassMComponents.coefficientNodes P p q i).1 ≫ BassProjectionPath.source P c,
        (coefficientProjectionNode P p q i).2 ≪≫
          isoWhiskerLeft (BassMComponents.coefficientNodes P p q i).1.functor
            (splitProjectionUnit P c)⟩ : BassOverlap.Node P p q) := by
  rw [coefficientProjectionNode_original]
  exact congrArg (fun ρ : (BassOverlap.commonReference P p q).functor ≅
      (coefficientProjectionNode P p q i).1.functor ↦
    (⟨(coefficientProjectionNode P p q i).1, ρ⟩ : BassOverlap.Node P p q))
      (coefficientProjection_unit_reference P p q i)

end Quillen.PerfectComplexes.LaurentUnitReferenceSpecialization
