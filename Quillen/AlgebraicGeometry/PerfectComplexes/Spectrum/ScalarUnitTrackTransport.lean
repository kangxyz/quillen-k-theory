/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarUnitTrack
public import Quillen.Waldhausen.Fibration.Prespectrum
public import Quillen.Waldhausen.SConstruction.Iterated.HomotopyTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Raw scalar cylinders and their actual canonical normalization

The original change-weak map and its canonically rebased map are joined by the actual rebase
isomorphism track. Its whole relative pasting, followed by the unchanged restriction comparison,
intertwines the original raw scalar cylinder and actual flat-unit self-track at all levels.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The specified raw change-weak map is joined to its actual canonical zero rebase. -/
def perfectOpenChangeWeakNormalizationHomotopy :
    Homotopy (changeWeakPrespectrumMap (perfectOpenNested j))
      (exactOriginalPrespectrumMap _ _ (changeWeak_exact (perfectOpenNested j))) :=
  originalPrespectrumTransformationHomotopy _ _ (changeWeak_exact (perfectOpenNested j))
    (changeWeak_exact (perfectOpenNested j)).rebase
    (perfectOpenNested j).zero_eq.symm (Quillen.rebaseFunctor_obj_base _ _ _ _)
    (Quillen.rebaseFunctorIso (𝟭 (Perfect X)) (perfectWaldhausen X).zero
      (perfectOpenWeakWaldhausen j).zero
      (((changeWeak_exact (perfectOpenNested j)).zero (perfectWaldhausen X).isZero).iso
        (perfectOpenWeakWaldhausen j).isZero)).hom
    (fun _ => (perfectOpenWeakWaldhausen j).weq_iso _ inferInstance)

/-- The raw comparison retains B postcomposed by restriction, followed by C inverse then D. -/
def perfectOpenOriginalRestrictionFlatHomotopy :
    Homotopy
      (changeWeakPrespectrumMap (perfectOpenNested j) ≫ perfectOpenScalarRestrictionMap j)
      (perfectFlatPrespectrumMap j) :=
  ((perfectOpenChangeWeakNormalizationHomotopy j).postcomp
    (perfectOpenScalarRestrictionMap j)).trans (perfectOpenRestrictionFlatHomotopy j)

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The original scalar cylinder is used without any additional zero rebasing. -/
def perfectOpenScalarOriginalHomotopy :
    Homotopy (changeWeakPrespectrumMap (perfectOpenNested j))
      (changeWeakPrespectrumMap (perfectOpenNested j)) :=
  originalPrespectrumTransformationHomotopy _ _ (changeWeak_exact (perfectOpenNested j))
    (changeWeak_exact (perfectOpenNested j)) (perfectOpenNested j).zero_eq.symm
    (perfectOpenNested j).zero_eq.symm (perfectGlobalScalar X r)
    (perfectGlobalScalar_openWeak j r q hq)

/-- The full original raw and rebased scalar tracks intertwine along the actual rebase track. -/
def perfectOpenScalarNormalizationTrack :
    ((perfectOpenScalarOriginalHomotopy j r q hq).trans
      (perfectOpenChangeWeakNormalizationHomotopy j)).RelHomotopy
    ((perfectOpenChangeWeakNormalizationHomotopy j).trans
      (perfectOpenScalarPrespectrumHomotopy j r q hq)) := by
  let h := changeWeak_exact (perfectOpenNested j)
  let e := Quillen.rebaseFunctorIso (𝟭 (Perfect X)) (perfectWaldhausen X).zero
    (perfectOpenWeakWaldhausen j).zero
    ((h.zero (perfectWaldhausen X).isZero).iso (perfectOpenWeakWaldhausen j).isZero)
  let eta := perfectGlobalScalar X r
  let hEta := perfectGlobalScalar_openWeak j r q hq
  have he : eta ≫ e.hom = e.hom ≫ normalizedWeakTransformation h h eta := by
    change eta ≫ e.hom = e.hom ≫ (e.inv ≫ eta ≫ e.hom)
    simp only [Iso.hom_inv_id_assoc]
  exact originalPrespectrumPastingHomotopy _ _ h h h.rebase h.rebase
    (perfectOpenNested j).zero_eq.symm (perfectOpenNested j).zero_eq.symm
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
    eta e.hom e.hom (normalizedWeakTransformation h h eta) hEta
    (fun _ => (perfectOpenWeakWaldhausen j).weq_iso _ inferInstance)
    (fun _ => (perfectOpenWeakWaldhausen j).weq_iso _ inferInstance)
    (normalizedWeakTransformation_weak h h eta hEta) he

/-- Every point of the entire raw level-one scalar track is the old realization cylinder. -/
theorem perfectOpenScalarOriginalHomotopy_level_one (s : unitInterval)
    (x : (perfectWaldhausen X).Delooping) :
    (perfectOpenScalarOriginalHomotopy j r q hq).level 1
        (s, (perfectWaldhausen X).smallModelDeloopingHomeomorph x) =
      (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph
        (weakNaturalTransformationRealizationHomotopy (perfectWaldhausen X)
          (perfectOpenWeakWaldhausen j) (changeWeak_exact (perfectOpenNested j))
          (changeWeak_exact (perfectOpenNested j)) (perfectGlobalScalar X r)
          (perfectGlobalScalar_openWeak j r q hq) (s, x)) :=
  originalPrespectrumTransformationHomotopy_level_one _ _ _ _ _ _ _ _ s x

/-- The two original scalar routes intertwine along the entire specified raw-to-flat comparison. -/
def perfectOpenScalarOriginalRestrictionUnitTrack :
    (((perfectOpenScalarOriginalHomotopy j r q hq).postcomp
      (perfectOpenScalarRestrictionMap j)).trans
        (perfectOpenOriginalRestrictionFlatHomotopy j)).RelHomotopy
      ((perfectOpenOriginalRestrictionFlatHomotopy j).trans (perfectFlatUnitHomotopy j q)) := by
  let H0 := (perfectOpenScalarOriginalHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)
  let H1 := (perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)
  let B := (perfectOpenChangeWeakNormalizationHomotopy j).postcomp
    (perfectOpenScalarRestrictionMap j)
  let A := perfectOpenRestrictionFlatHomotopy j
  let Hq := perfectFlatUnitHomotopy j q
  have JB : (H0.trans B).RelHomotopy (B.trans H1) := by
    have J := (perfectOpenScalarNormalizationTrack j r q hq).postcomp
      (perfectOpenScalarRestrictionMap j)
    simpa only [Homotopy.postcomp_trans] using J
  have JA : (H1.trans A).RelHomotopy (A.trans Hq) :=
    perfectOpenScalarRestrictionUnitTrack j r q hq
  exact (Homotopy.RelHomotopy.transAssoc H0 B A).symm.trans
    ((JB.hcomp (Homotopy.RelHomotopy.refl A)).trans
      ((Homotopy.RelHomotopy.transAssoc B H1 A).trans
        (((Homotopy.RelHomotopy.refl B).hcomp JA).trans
          (Homotopy.RelHomotopy.transAssoc B A Hq).symm)))

end Quillen.PerfectComplexes
