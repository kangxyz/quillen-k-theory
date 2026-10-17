/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1BoundarySeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MInternalFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.LaurentUnitReferenceSpecialization
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCarrier

/-!
# Actual positive C0 carrier attachment

The unchanged ordinary and shifted C0 projection strips attach through the fixed C1
polynomial reference. Abstract full-node transport lemmas bound elaboration of the original
reference expressions. This source supplies no mixed filler or identification of the tips.
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierAttachment
open BassH0Merge CommonReferenceNerve
open CoefficientBassPositiveC1BoundaryLift
/-- Abstract full-node cancellation, before specialization to large geometric references. -/
private theorem attach_anchor_cancel {V W T : Model.{v}}
    (F K : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
    (θ : K.functor ≅ F.functor) (η : G.functor ≅ (K ≫ J).functor)
    (ε : G.functor ≅ (F ≫ J).functor)
    (h : η ≪≫ isoWhiskerRight θ J.functor = ε) (N : Node K) :
    attachPostcompNode F J G ε (anchorNode θ.symm N) =
      BassH1Join.postReferenceNode G J η N := by
  rcases N with ⟨H, ρ⟩
  unfold attachPostcompNode anchorNode BassH1Join.postReferenceNode
  change (⟨H ≫ J, ε ≪≫ isoWhiskerRight (θ.symm ≪≫ ρ) J.functor⟩ : Node G) =
    ⟨H ≫ J, η ≪≫ isoWhiskerRight ρ J.functor⟩
  apply congrArg (fun ν : G.functor ≅ (H ≫ J).functor ↦ (⟨H ≫ J, ν⟩ : Node G))
  have hw : isoWhiskerRight θ J.functor ≪≫ isoWhiskerRight θ.symm J.functor =
      Iso.refl (K ≫ J).functor := by
    rw [← isoWhiskerRight_trans, Iso.self_symm_id, isoWhiskerRight_refl]
    rfl
  have hc := congrArg (fun ν ↦ ν ≪≫ isoWhiskerRight θ.symm J.functor) h
  rw [Iso.trans_assoc, hw, Iso.trans_refl] at hc
  rw [isoWhiskerRight_trans, ← Iso.trans_assoc]
  exact congrArg (fun ν ↦ ν ≪≫ isoWhiskerRight ρ J.functor) hc.symm

/-- Abstract reanchoring preserves the whole dependent attachment node. -/
private theorem anchor_attach {V W T : Model.{v}}
    (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
    (τ : G.functor ≅ G.functor) (ε : G.functor ≅ (F ≫ J).functor) (N : Node F) :
    anchorNode τ (attachPostcompNode F J G ε N) =
      attachPostcompNode F J G (τ ≪≫ ε) N := by
  rcases N with ⟨H, ρ⟩
  unfold anchorNode attachPostcompNode
  change (⟨H ≫ J, τ ≪≫ (ε ≪≫ isoWhiskerRight ρ J.functor)⟩ : Node G) =
    ⟨H ≫ J, (τ ≪≫ ε) ≪≫ isoWhiskerRight ρ J.functor⟩
  exact congrArg (fun ν : G.functor ≅ (H ≫ J).functor ↦ (⟨H ≫ J, ν⟩ : Node G))
    (Iso.trans_assoc τ ε (isoWhiskerRight ρ J.functor)).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Extract equality of the actual complete anchors, not equality of evaluated maps. -/
theorem side_anchor :
    BassMOuterJoin.movingSideIso P p q (underToLaurent R) (laurentPlus_projection P c) =
      ordinaryAnchor P p q := by
  have he := (BassMOuterJoin.moving_side_row P p q (underToLaurent R)
    (laurentPlus_projection P c) 0).symm.trans
      ((BassMOuterJoin.plus_side_corner P p q).trans
        (BassMOuterJoin.old_side_row P p q (underToLaurent R)
          (laurentPlus_projection P c) 0))
  have hs := eq_of_heq (Sigma.mk.inj he).2
  change BassMOuterJoin.movingSideIso P p q (underToLaurent R)
      (laurentPlus_projection P c) ≪≫
      isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
        (isoWhiskerRight (BassMOuterJoin.sideBinaryNodes P p q 0).2
          (chartMap P (c := c)).functor) =
    ordinaryAnchor P p q ≪≫
      isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
        (isoWhiskerRight (BassMOuterJoin.sideBinaryNodes P p q 0).2
          (chartMap P (c := c)).functor) at hs
  have hc := congrArg (fun η ↦ η ≪≫
    (isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (isoWhiskerRight (BassMOuterJoin.sideBinaryNodes P p q 0).2
        (chartMap P (c := c)).functor)).symm) hs
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc

/-- Transport all original polynomial nodes to the C1 polynomial reference. -/
def transportPolynomialNode (N : Node (BassMComponents.polynomialSource P p q)) :
    Node (polynomialReference P p q) :=
  anchorNode (BassMOuterJoin.movingSideBaseIso P p q).symm N

/-- The fixed C1 attachment of every transported full node is the original moving node.
No cancellation of the Laurent postcomposition functor is used. -/
theorem attach_transport (N : Node (BassMComponents.polynomialSource P p q)) :
    ordinaryAttachNode P p q (transportPolynomialNode P p q N) =
      BassH1Join.postReferenceNode (laurentReference P p q) (chartMap P (c := c))
        (BassMReferences.movingIso P p q (underToLaurent R) (laurentPlus_projection P c)) N := by
  unfold ordinaryAttachNode transportPolynomialNode
  exact attach_anchor_cancel (polynomialReference P p q) (BassMComponents.polynomialSource P p q)
    (chartMap P (c := c)) (laurentReference P p q) (BassMOuterJoin.movingSideBaseIso P p q)
    (BassMReferences.movingIso P p q (underToLaurent R) (laurentPlus_projection P c))
    (ordinaryAnchor P p q) (side_anchor P p q) N

/-- The original coefficient column, with all its polynomial reference data. -/
def coefficientPolynomialNodes (i : Fin 3) : Node (polynomialReference P p q) :=
  transportPolynomialNode P p q
    (BassMComponents.polynomialNodes P p q (BassMJoin.movingSourceFace.toOrderHom i))

/-- The whole C0 column attaches to the same fixed ordinary attachment as C1. -/
theorem coefficient_column_nodes (i : Fin 3) :
    BassMReferences.middleNodes P p q (SimplexGrid.index 2 4 (i, 2)) =
      ordinaryAttachNode P p q (coefficientPolynomialNodes P p q i) := by
  have hi : BassMJoin.movingSourceFace.toOrderHom i =
      DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [coefficientPolynomialNodes, attach_transport, hi]
  change BassMReferences.middleNodes P p q (SimplexGrid.index 2 4 (i, 2)) =
    BassMReferences.movingNodes P p q (underToLaurent R) (laurentPlus_projection P c)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i))
  exact (BassMJoin.plus_internal_nodes P p q i).symm

/-- This rail uses the original binary speed, without C1's terminal pause. -/
def coefficientPolynomialParameter :
    C(I, |nerve (Codiscrete (Node (polynomialReference P p q)))|) :=
  (parameter (polynomialReference P p q) (coefficientPolynomialNodes P p q)).comp
    (binaryPath (k := 2) 0 1 2).toContinuousMap

/-- The ordinary positive projection strip in C0, with its two independent original times. -/
def positiveProjectionParameter :
    C(I × I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (BassMReferences.middleNodes P p q)).comp
    ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 2 4
      (binaryPath (k := 2) 0 1 2 z.1,
        StdSimplex.map BassProjectionPath.plusFace.toOrderHom
          (binaryPath (k := 2) 0 1 2 z.2)), by fun_prop⟩

/-- The whole boundary of the projection strip, before native evaluation. -/
theorem positiveProjection_right_attach (r : I) :
    positiveProjectionParameter P p q (r, 1) =
      mapParameter (ordinaryAttachNode P p q) (coefficientPolynomialParameter P p q r) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
      (binaryPath (k := 2) 0 1 2 r,
        StdSimplex.map BassProjectionPath.plusFace.toOrderHom
          (binaryPath (k := 2) 0 1 2 1))) = _
  rw [Path.target, StdSimplex.map_single]
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 r, StdSimplex.single 2)) = _
  rw [SimplexGrid.parameter_column, parameter_face]
  change parameter _ _ (binaryPath (k := 2) 0 1 2 r) =
    mapParameter (ordinaryAttachNode P p q)
      (parameter _ _ (binaryPath (k := 2) 0 1 2 r))
  rw [mapParameter_parameter]
  exact congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (binaryPath (k := 2) 0 1 2 r))
      (funext (coefficient_column_nodes P p q))

/-- The second cone uses a genuinely different attachment, shifted by the actual total unit. -/
def shiftedAttachNode : Node (polynomialReference P p q) → Node (laurentReference P p q) :=
  attachPostcompNode (polynomialReference P p q) (chartMap P (c := c))
    (laurentReference P p q)
    (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫ ordinaryAnchor P p q)

/-- The full shifted node equation does not equate the ordinary and shifted nodes. -/
theorem shifted_column_nodes (i : Fin 3) :
    anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q)
      (BassMReferences.middleNodes P p q (SimplexGrid.index 2 4 (i, 2))) =
    shiftedAttachNode P p q (coefficientPolynomialNodes P p q i) := by
  rw [coefficient_column_nodes]
  unfold ordinaryAttachNode shiftedAttachNode
  exact anchor_attach (polynomialReference P p q) (chartMap P (c := c))
    (laurentReference P p q) (LaurentUnitReferenceSpecialization.commonUnit P p q)
    (ordinaryAnchor P p q) (coefficientPolynomialNodes P p q i)

/-- The entire shifted strip is common-unit reanchoring, not a newly chosen path. -/
def shiftedProjectionParameter :
    C(I × I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (mapParameter (anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q))).comp
    (positiveProjectionParameter P p q)

/-- The second strip has the same polynomial rail and its own full shifted attachment. -/
theorem shiftedProjection_right_attach (r : I) :
    shiftedProjectionParameter P p q (r, 1) =
      mapParameter (shiftedAttachNode P p q) (coefficientPolynomialParameter P p q r) := by
  change mapParameter (anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q))
    (positiveProjectionParameter P p q (r, 1)) = _
  rw [positiveProjection_right_attach]
  change mapParameter (anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q))
    (mapParameter (ordinaryAttachNode P p q)
      (parameter _ _ (binaryPath (k := 2) 0 1 2 r))) =
    mapParameter (shiftedAttachNode P p q)
      (parameter _ _ (binaryPath (k := 2) 0 1 2 r))
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (binaryPath (k := 2) 0 1 2 r))
  funext i
  exact (congrArg (anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q))
    (coefficient_column_nodes P p q i).symm).trans (shifted_column_nodes P p q i)

/-- The first C0 null strip and the first polynomial cylinder really join in the accepted U. -/
theorem ordinary_cutOpen_seam (r : I) :
    CutOpenCarrier.laurentInclusion (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (positiveProjectionParameter P p q (r, 1)) =
    CutOpenCarrier.cylinderMinus (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (coefficientPolynomialParameter P p q r, 0) := by
  rw [CutOpenCarrier.cylinderMinus_zero, positiveProjection_right_attach]
  rfl

/-- The other C0 null strip joins the second cylinder; its terminal tip is not identified. -/
theorem shifted_cutOpen_seam (r : I) :
    CutOpenCarrier.laurentInclusion (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (shiftedProjectionParameter P p q (r, 1)) =
    CutOpenCarrier.cylinderPlus (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (coefficientPolynomialParameter P p q r, 0) := by
  rw [CutOpenCarrier.cylinderPlus_zero, shiftedProjection_right_attach]
  rfl

/-- Native attachment equality at every level, including zero, and every unchanged input. -/
theorem positiveProjection_right_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (laurentReference P p q) (positiveProjectionParameter P p q)
      n ((r, 1), x) =
    (prespectrumMap (chartMap P (c := c))).map n
      (compactPrespectrumFamily (polynomialReference P p q)
        (coefficientPolynomialParameter P p q) n (r, x)) := by
  have h := (positiveProjection_right_attach P p q r).trans
    (mapParameter_parameter (ordinaryAttachNode P p q) (coefficientPolynomialNodes P p q)
      (binaryPath (k := 2) 0 1 2 r))
  rw [compactPrespectrumFamily_eq_simplex _ _
      (fun i ↦ ordinaryAttachNode P p q (coefficientPolynomialNodes P p q i))
      (r, 1) (binaryPath (k := 2) 0 1 2 r) h n x,
    compactPrespectrumFamily_eq_simplex _ _ (coefficientPolynomialNodes P p q)
      r (binaryPath (k := 2) 0 1 2 r) rfl n x]
  exact prespectrumFamily_attachPostcomp _ _ _ _ _ n _ x

end Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierAttachment
