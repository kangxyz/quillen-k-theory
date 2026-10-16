/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberSequenceMap
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationPasting
public import Quillen.Waldhausen.SConstruction.Iterated.HomotopyTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyPasting

/-!
# The scalar cone's exact normalization and canonical acyclic null

The coarse cone normalization is joined to the public acyclic cone normalization by the actual
inclusion-whiskered rebase isomorphism. The original zero-to-inclusion cylinder is retained with
its one reversal, and the zero normalization cylinder is proved constant on every input. The
relative square and its rotated boundary retain both normalization edges; no fiber filler or
cancellation of the separated identity summand is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => perfectWaldhausen X
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "A" => perfectOpenScalarConeFunctor j r q hq
local notation "hA" => perfectOpenScalarConeFunctor_waldhausenExact j r q hq
local notation "hC" =>
  Additivity.IsCofibrationSequence.exactH (perfectOpenScalarCofibrationSequence j r)
local notation "hZ" =>
  Additivity.IsCofibrationSequence.exactH (perfectOpenScalarIdentityCofibrationSequence j)
local notation "Z" => zeroFunctor (C := Perfect X) W
local notation "Ar" => Quillen.rebaseFunctor A (Structure.zero V)
  (Structure.zero (acyclicStructure N))
  (Limits.IsZero.iso (IsExact.zero hA (Structure.isZero V))
    (Structure.isZero (acyclicStructure N)))
local notation "hD" => IsExact.comp (IsExact.rebase hA) (acyclicInclusion_coarse_exact N)

/-- The existing coarse normalization of the literal scalar cone. -/
def perfectOpenScalarConeRebaseIso :
    perfectScalarConeFunctor X r ≅
      Quillen.rebaseFunctor (perfectScalarConeFunctor X r) (V).zero (W).zero
        (((hC).zero (V).isZero).iso (W).isZero) :=
  Quillen.rebaseFunctorIso _ _ _ _

/-- The public acyclic cone K-map uses this exact inherited normalization. -/
def perfectOpenScalarAcyclicConeRebaseIso : A ≅ Ar :=
  Quillen.rebaseFunctorIso _ _ _ _

/-- The original zero functor is normalized using the source sequence's exact witness. -/
def perfectOpenScalarZeroRebaseIso :
    Z ≅ Quillen.rebaseFunctor Z (V).zero (W).zero (((hZ).zero (V).isZero).iso (W).isZero) :=
  Quillen.rebaseFunctorIso _ _ _ _

/-- The actual cone normalization comparison, with its inclusion-whiskered second factor. -/
def perfectOpenScalarConeNormalizationIso :
    Quillen.rebaseFunctor (perfectScalarConeFunctor X r) (V).zero (W).zero
        (((hC).zero (V).isZero).iso (W).isZero) ≅ Ar ⋙ acyclicInclusion N :=
  (perfectOpenScalarConeRebaseIso j r).symm ≪≫
    Functor.isoWhiskerRight (perfectOpenScalarAcyclicConeRebaseIso j r q hq)
      (acyclicInclusion N)

/-- The cone normalization edge is an actual fine weak equivalence on every coefficient. -/
theorem perfectOpenScalarConeNormalizationIso_fineWeak (K : Perfect X) :
    (V).weq ((perfectOpenScalarConeNormalizationIso j r q hq).hom.app K) :=
  (V).weq_iso _ inferInstance

/-- The public acyclic rebase followed by the original inclusion retains the chosen zero. -/
theorem perfectOpenScalarAcyclicConeRebase_zero :
    (Ar ⋙ acyclicInclusion N).obj (V).zero = (W).zero := by
  change ((Ar).obj (V).zero).obj = (W).zero
  rw [Quillen.rebaseFunctor_obj_base]
  exact (N).zero_eq.symm

/-- The zero edge on the actual public acyclic rebase is the literal original whiskering. -/
def perfectOpenScalarRebasedZeroToCone : Z ⟶ Ar ⋙ acyclicInclusion N :=
  Functor.whiskerLeft Ar (zeroToAcyclicInclusion N)

/-- The normalization square is an equality of the full original natural transformations. -/
theorem perfectOpenScalarZeroNormalizationSquare :
    normalizedWeakTransformation hZ hC (perfectOpenScalarZeroToCone j r q hq) ≫
        (perfectOpenScalarConeNormalizationIso j r q hq).hom =
      (perfectOpenScalarZeroRebaseIso j).inv ≫ perfectOpenScalarRebasedZeroToCone j r q hq := by
  apply NatTrans.ext
  funext K
  exact ((W).isZero.of_iso ((perfectOpenScalarZeroRebaseIso j).app K).symm).eq_of_src _ _

/-- The normalized zero-to-cone cylinder, with no additional normalization. -/
def perfectOpenScalarNormalizedZeroToConeHomotopy :
    Homotopy (originalPrespectrumMap V W (hZ).rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (originalPrespectrumMap V W (hC).rebase (Quillen.rebaseFunctor_obj_base _ _ _ _)) :=
  originalPrespectrumTransformationHomotopy V W (hZ).rebase (hC).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
    (normalizedWeakTransformation hZ hC (perfectOpenScalarZeroToCone j r q hq))
    (normalizedWeakTransformation_weak hZ hC (perfectOpenScalarZeroToCone j r q hq)
      (perfectOpenScalarZeroToCone_weak j r q hq))

/-- The old cylinder of the actual cone normalization isomorphism. -/
def perfectOpenScalarConeNormalizationHomotopy :
    Homotopy (originalPrespectrumMap V W (hC).rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (originalPrespectrumMap V W hD (perfectOpenScalarAcyclicConeRebase_zero j r q hq)) :=
  originalPrespectrumTransformationHomotopy V W (hC).rebase hD
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (perfectOpenScalarAcyclicConeRebase_zero j r q hq)
    (perfectOpenScalarConeNormalizationIso j r q hq).hom (fun _ => (W).weq_iso _ inferInstance)

/-- The old inverse zero-normalization cylinder, retaining its literal endpoints. -/
def perfectOpenScalarZeroNormalizationHomotopy :
    Homotopy (originalPrespectrumMap V W (hZ).rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (originalPrespectrumMap V W (zeroFunctor_isExact V W) rfl) :=
  originalPrespectrumTransformationHomotopy V W (hZ).rebase (zeroFunctor_isExact V W)
    (Quillen.rebaseFunctor_obj_base _ _ _ _) rfl
    (perfectOpenScalarZeroRebaseIso j).inv (fun _ => (W).weq_iso _ inferInstance)

/-- The original zero-to-inclusion track on the public acyclic cone rebase. -/
def perfectOpenScalarRebasedZeroToConeHomotopy :
    Homotopy (originalPrespectrumMap V W (zeroFunctor_isExact V W) rfl)
      (originalPrespectrumMap V W hD (perfectOpenScalarAcyclicConeRebase_zero j r q hq)) :=
  originalPrespectrumTransformationHomotopy V W (zeroFunctor_isExact V W) hD
    rfl (perfectOpenScalarAcyclicConeRebase_zero j r q hq)
    (perfectOpenScalarRebasedZeroToCone j r q hq)
    (fun K => zeroToAcyclicInclusion_weak N ((Ar).obj K))

/-- The same zero/cone square supplies a genuine relative comparison at every level. -/
def perfectOpenScalarZeroNormalizationTrack :
    ((perfectOpenScalarNormalizedZeroToConeHomotopy j r q hq).trans
      (perfectOpenScalarConeNormalizationHomotopy j r q hq)).RelHomotopy
      ((perfectOpenScalarZeroNormalizationHomotopy j).trans
        (perfectOpenScalarRebasedZeroToConeHomotopy j r q hq)) :=
  originalPrespectrumPastingHomotopy V W (hZ).rebase (hC).rebase (zeroFunctor_isExact V W) hD
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _) rfl
    (perfectOpenScalarAcyclicConeRebase_zero j r q hq)
    (normalizedWeakTransformation hZ hC (perfectOpenScalarZeroToCone j r q hq))
    (perfectOpenScalarConeNormalizationIso j r q hq).hom
    (perfectOpenScalarZeroRebaseIso j).inv (perfectOpenScalarRebasedZeroToCone j r q hq)
    (normalizedWeakTransformation_weak hZ hC (perfectOpenScalarZeroToCone j r q hq)
      (perfectOpenScalarZeroToCone_weak j r q hq))
    (fun _ => (W).weq_iso _ inferInstance) (fun _ => (W).weq_iso _ inferInstance)
    (fun K => zeroToAcyclicInclusion_weak N ((Ar).obj K))
    (perfectOpenScalarZeroNormalizationSquare j r q hq)

/-- Rotation retains both normalization edges and reverses the canonical zero edge once. -/
def perfectOpenScalarCanonicalNullTriangle :
    ((perfectOpenScalarConeNormalizationHomotopy j r q hq).trans
      (perfectOpenScalarRebasedZeroToConeHomotopy j r q hq).symm).RelHomotopy
      ((perfectOpenScalarNormalizedZeroToConeHomotopy j r q hq).symm.trans
        (perfectOpenScalarZeroNormalizationHomotopy j)) :=
  (perfectOpenScalarZeroNormalizationTrack j r q hq).rotate.symm

/-- Normalizing a constant chosen-zero functor keeps zero at every input object. -/
theorem perfectOpenScalarZeroRebase_obj (K : Perfect X) :
    (Quillen.rebaseFunctor Z (V).zero (W).zero (((hZ).zero (V).isZero).iso (W).isZero)).obj K =
      (W).zero := by
  classical
  simp [Quillen.rebaseFunctor, Quillen.rebaseObj, zeroFunctor]

/-- The whole zero-normalization cylinder is the constant map, beyond its zero face. -/
theorem perfectOpenScalarZeroNormalizationCylinder_constant :
    weakNaturalTransformationCylinder V W (hZ).rebase (zeroFunctor_isExact V W)
        (perfectOpenScalarZeroRebaseIso j).inv (fun _ => (W).weq_iso _ inferInstance) =
      SSet.const (zeroSimplex (W).cof (W).weq (W).zero (W).isZero (Opposite.op ⦋0⦌)) := by
  ext n z
  apply Subtype.ext
  exact nerveCylinderDiagram_eq_const_of_zero _ (W).zero (W).isZero
    (fun p => perfectOpenScalarZeroRebase_obj j (z.1.val.obj p)) (fun _ => rfl) z.2.down

/-- Every ordinary input and every time gives the actual chosen zero. -/
theorem perfectOpenScalarZeroNormalizationRealization_constant
    (t : unitInterval) (x : (V).Delooping) :
    weakNaturalTransformationRealizationHomotopy V W (hZ).rebase (zeroFunctor_isExact V W)
        (perfectOpenScalarZeroRebaseIso j).inv (fun _ => (W).weq_iso _ inferInstance) (t, x) =
      (W).kBasepoint := by
  change SSet.toTop.map
    (weakNaturalTransformationCylinder V W (hZ).rebase (zeroFunctor_isExact V W)
      (perfectOpenScalarZeroRebaseIso j).inv (fun _ => (W).weq_iso _ inferInstance))
    ((realizationCylinderIso _).inv (x, ULift.up t)) = _
  rw [perfectOpenScalarZeroNormalizationCylinder_constant]
  exact realization_const_apply _ _

/-- The entire original canonical null is exactly the reversed whiskered cylinder on this rebase. -/
theorem perfectOpenScalarCanonicalNull_rebased_apply
    (t : unitInterval) (x : (V).Delooping) :
    acyclicNullhomotopy N (t, deloopingMap (hA).rebase x) =
      weakNaturalTransformationRealizationHomotopy V W
        ((hA).rebase.comp (zeroFunctor_isExact (acyclicStructure N) W)) hD
        (perfectOpenScalarRebasedZeroToCone j r q hq)
        (fun K => zeroToAcyclicInclusion_weak N ((Ar).obj K)) (unitInterval.symm t, x) := by
  have h := weakNaturalTransformationCylinder_precompose V (acyclicStructure N) W
    (zeroFunctor_isExact (acyclicStructure N) W) (acyclicInclusion_coarse_exact N)
    (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) (hA).rebase
  have h' := realizationSimplicialHomotopy_naturality
    (weakNaturalTransformationHomotopy (acyclicStructure N) W
      (zeroFunctor_isExact (acyclicStructure N) W) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N))
    (weakNaturalTransformationHomotopy V W
      ((hA).rebase.comp (zeroFunctor_isExact (acyclicStructure N) W)) hD
      (perfectOpenScalarRebasedZeroToCone j r q hq)
      (fun K => zeroToAcyclicInclusion_weak N ((Ar).obj K)))
    (sSetMap (hA).rebase) (𝟙 _) (by
      simpa only [Category.comp_id, weakNaturalTransformationHomotopy,
        perfectOpenScalarRebasedZeroToCone] using h)
    (unitInterval.symm t) x
  rw [SSet.toTop.map_id] at h'
  simp only [TopCat.id_app] at h'
  convert h' using 1 <;> rfl

end Quillen.PerfectComplexes
