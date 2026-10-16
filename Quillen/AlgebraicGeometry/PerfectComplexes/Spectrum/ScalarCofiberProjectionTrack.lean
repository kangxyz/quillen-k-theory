/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberSequenceMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarUnitTrackTransport
public import Quillen.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
public import Quillen.Topology.Realization.HomotopyNaturality

/-!
# The actual scalar inclusion/projection triangle

The original inclusion and fine weak projection retain exactly the coarse sequence's canonical
zero normalizations. Their actual composition triangle has the original scalar as its long edge.
The same normalized projection is fine weak before changing weak equivalences. No identity
additivity track, right-half summand, or canonical null is removed by these comparisons.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
open scoped Topology
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)

/-- The exact identity normalization used by the coarse scalar sequence. -/
def perfectOpenScalarIdentityRebaseIso :
    𝟭 (Perfect X) ≅ Quillen.rebaseFunctor (𝟭 (Perfect X)) (V).zero (W).zero
      (((hF).zero (V).isZero).iso (W).isZero) :=
  Quillen.rebaseFunctorIso _ _ _ _

variable (r : Γ(X, ⊤))
local notation "hM" =>
  Additivity.IsCofibrationSequence.exactG (perfectOpenScalarCofibrationSequence j r)

/-- The exact middle normalization used by the coarse scalar sequence. -/
def perfectOpenScalarMiddleRebaseIso :
    perfectScalarMiddleFunctor X r ≅
      Quillen.rebaseFunctor (perfectScalarMiddleFunctor X r) (V).zero (W).zero
        (((hM).zero (V).isZero).iso (W).isZero) :=
  Quillen.rebaseFunctorIso _ _ _ _

/-- The same coarse-normalized identity functor is fine exact, with no second rebasing. -/
theorem perfectOpenScalarIdentityRebase_fineExact :
    IsExact (V).cof (V).weq (V).cof (V).weq
      (Quillen.rebaseFunctor (𝟭 (Perfect X)) (V).zero (W).zero
        (((hF).zero (V).isZero).iso (W).isZero)) :=
  (IsExact.id (V).cof (V).weq).of_iso (perfectOpenScalarIdentityRebaseIso j)

/-- The same coarse-normalized middle functor is fine exact as well. -/
theorem perfectOpenScalarMiddleRebase_fineExact :
    IsExact (V).cof (V).weq (V).cof (V).weq
      (Quillen.rebaseFunctor (perfectScalarMiddleFunctor X r) (V).zero (W).zero
        (((hM).zero (V).isZero).iso (W).isZero)) :=
  (perfectScalarMiddleFunctor_waldhausenExact X r).of_iso
    (perfectOpenScalarMiddleRebaseIso j r)

/-- The unchanged projection, conjugated by exactly the two coarse endpoint normalizations. -/
theorem perfectOpenScalarNormalizedProjection_fineWeak (K : Perfect X) :
    (V).weq ((normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r)).app K) :=
  (V).weq.comp_mem _ _ ((V).weq_iso _ inferInstance)
    ((V).weq.comp_mem _ _ (perfectScalarProjectionNat_weak X r K)
      ((V).weq_iso _ inferInstance))

/-- The actual fine projection cylinder between the same two normalized functors. -/
def perfectOpenScalarProjectionFineRealizationHomotopy :
    (deloopingMap (perfectOpenScalarMiddleRebase_fineExact j r)).hom.Homotopy
      (deloopingMap (perfectOpenScalarIdentityRebase_fineExact j)).hom :=
  weakNaturalTransformationRealizationHomotopy V V
    (perfectOpenScalarMiddleRebase_fineExact j r)
    (perfectOpenScalarIdentityRebase_fineExact j)
    (normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r))
    (perfectOpenScalarNormalizedProjection_fineWeak j r)

/-- The coarse projection is the original weak cylinder with its actual canonical conjugation. -/
def perfectOpenScalarProjectionRealizationHomotopy :
    (deloopingMap (hM).rebase).hom.Homotopy (deloopingMap (hF).rebase).hom :=
  weakNaturalTransformationRealizationHomotopy V W (hM).rebase (hF).rebase
    (normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r))
    (normalizedWeakTransformation_weak hM hF (perfectScalarProjectionNat X r)
      (perfectScalarProjectionNat_openWeak j r))

/-- The original coarse prespectrum projection, retaining the full old fine projection. -/
def perfectOpenScalarProjectionHomotopy :
    Homotopy (exactOriginalPrespectrumMap V W hM) (exactOriginalPrespectrumMap V W hF) :=
  exactOriginalPrespectrumHomotopy V W hM hF (perfectScalarProjectionNat X r)
    (perfectScalarProjectionNat_openWeak j r)

/-- Every point of the projection's first level is the original ordinary cylinder. -/
theorem perfectOpenScalarProjectionHomotopy_level_one (t : unitInterval) (x : (V).Delooping) :
    (perfectOpenScalarProjectionHomotopy j r).level 1
        (t, (V).smallModelDeloopingHomeomorph x) =
      (W).smallModelDeloopingHomeomorph
        (perfectOpenScalarProjectionRealizationHomotopy j r (t, x)) :=
  originalPrespectrumTransformationHomotopy_level_one V W _ _ _ _ _ _ t x

/-- Fine-to-coarse transport preserves the whole projection cylinder, for all inputs and times. -/
theorem perfectOpenScalarProjectionRealizationHomotopy_changeWeak
    (t : unitInterval) (x : (V).Delooping) :
    changeWeakMap (perfectOpenNested j)
        (perfectOpenScalarProjectionFineRealizationHomotopy j r (t, x)) =
      perfectOpenScalarProjectionRealizationHomotopy j r (t, x) := by
  have h := realizationSimplicialHomotopy_naturality
    (weakNaturalTransformationHomotopy V V
      (perfectOpenScalarMiddleRebase_fineExact j r)
      (perfectOpenScalarIdentityRebase_fineExact j)
      (normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r))
      (perfectOpenScalarNormalizedProjection_fineWeak j r))
    (weakNaturalTransformationHomotopy V W (hM).rebase (hF).rebase
      (normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r))
      (normalizedWeakTransformation_weak hM hF (perfectScalarProjectionNat X r)
        (perfectScalarProjectionNat_openWeak j r)))
    (𝟙 _) (sSetMap hF) (by
      simp only [id_whiskerRight, Category.id_comp]
      ext n z : 4
      apply Subtype.ext
      rfl) t x
  rw [SSet.toTop.map_id] at h
  simp only [TopCat.id_app] at h
  convert h using 1 <;> rfl

variable (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The actual canonically rebased coarse inclusion cylinder. -/
def perfectOpenScalarInclusionRealizationHomotopy :
    (deloopingMap (hF).rebase).hom.Homotopy (deloopingMap (hM).rebase).hom :=
  weakNaturalTransformationRealizationHomotopy V W (hF).rebase (hM).rebase
    (normalizedWeakTransformation hF hM (perfectScalarInclusionNat X r))
    (normalizedWeakTransformation_weak hF hM (perfectScalarInclusionNat X r)
      (perfectScalarInclusionNat_openWeak j r q hq))

/-- The original inclusion at every prespectrum level, with those same endpoint normalizations. -/
def perfectOpenScalarInclusionHomotopy :
    Homotopy (exactOriginalPrespectrumMap V W hF) (exactOriginalPrespectrumMap V W hM) :=
  exactOriginalPrespectrumHomotopy V W hF hM (perfectScalarInclusionNat X r)
    (perfectScalarInclusionNat_openWeak j r q hq)

/-- Every point of the inclusion's first level is its entire original ordinary cylinder. -/
theorem perfectOpenScalarInclusionHomotopy_level_one (t : unitInterval) (x : (V).Delooping) :
    (perfectOpenScalarInclusionHomotopy j r q hq).level 1
        (t, (V).smallModelDeloopingHomeomorph x) =
      (W).smallModelDeloopingHomeomorph
        (perfectOpenScalarInclusionRealizationHomotopy j r q hq (t, x)) :=
  originalPrespectrumTransformationHomotopy_level_one V W _ _ _ _ _ _ t x

/-- The old composition triangle has the actual scalar as its long edge. -/
def perfectOpenScalarProjectionCompositionTrack :
    (perfectOpenScalarPrespectrumHomotopy j r q hq).RelHomotopy
      ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)) := by
  have J := exactOriginalPrespectrumCompositionHomotopy V W hF hM hF
    (perfectScalarInclusionNat X r) (perfectScalarProjectionNat X r)
    (perfectScalarInclusionNat_openWeak j r q hq) (perfectScalarProjectionNat_openWeak j r)
  convert J using 1 <;>
    simp only [perfectScalarInclusionNat_projection, perfectOpenScalarPrespectrumHomotopy,
      perfectOpenScalarInclusionHomotopy, perfectOpenScalarProjectionHomotopy]
  rfl

/-- The raw scalar retains the actual normalization prefix and the named association. -/
def perfectOpenScalarRawProjectionIntertwining :
    ((perfectOpenScalarOriginalHomotopy j r q hq).trans
      (perfectOpenChangeWeakNormalizationHomotopy j)).RelHomotopy
      ((perfectOpenChangeWeakNormalizationHomotopy j).trans
        ((perfectOpenScalarInclusionHomotopy j r q hq).trans
          (perfectOpenScalarProjectionHomotopy j r))) :=
  (perfectOpenScalarNormalizationTrack j r q hq).trans
    ((Homotopy.RelHomotopy.refl (perfectOpenChangeWeakNormalizationHomotopy j)).hcomp
      (perfectOpenScalarProjectionCompositionTrack j r q hq))

end Quillen.PerfectComplexes
