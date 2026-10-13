/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionSpectrumComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.DerivedPullback
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Waldhausen.SmallModel.Whiskering

/-!
# Actual geometric comparison of the original joint coefficient evaluation

The original cocartesian evaluation transition, common-universe lifting and both
actual zero normalizations give a whole based prespectrum homotopy for every joint
scheme/coefficient arrow. Its image in the stable localization is a genuine natural
isomorphism of the original joint diagrams. Every native coefficient row is obtained
by restriction of that same family. Perfect comparison uses the original bounded-flat
inclusion and arbitrary derived pullback on a quasi-compact row; no flatness is needed.
These connective comparisons do not assert Laurent-seed or telescope compatibility.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation

/-- The original geometric pullback Model map, with its original canonical zero normalization. -/
def boundedFlatCoefficientOriginalModelMap {i k : Index R} (f : i ⟶ k) :
    modelOf (boundedFlatPerfectWaldhausen (space i)) ⟶
      modelOf (boundedFlatPerfectWaldhausen (space k)) :=
  modelMap _ _ (boundedFlatPerfectPullback_exact
    (Quillen.Scheme.CoefficientBaseChange.map f)).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

set_option maxHeartbeats 1200000 in
-- Elaborating both concrete lifted normalization composites exceeds the standard budget.
/-- The comparison retains the actual original evaluation transition and both chosen-zero paths. -/
def boundedFlatCoefficientSectionEvaluationIso {i k : Index R} (f : i ⟶ k) :
    (boundedFlatCoefficientSectionModelMap f ≫
      boundedFlatCoefficientSectionEvaluationModelMap k).functor ≅
      (boundedFlatCoefficientSectionEvaluationModelMap i ≫
        boundedFlatCoefficientOriginalModelMap f).functor := by
  let p := boundedFlatPerfectPullback (Quillen.Scheme.CoefficientBaseChange.map f)
  let h := boundedFlatPerfectPullback_exact (Quillen.Scheme.CoefficientBaseChange.map f)
  let z := Quillen.rebaseFunctorIso p
    (boundedFlatPerfectWaldhausen (space i)).zero
    (boundedFlatPerfectWaldhausen (space k)).zero
    ((h.zero (boundedFlatPerfectWaldhausen (space i)).isZero).iso
      (boundedFlatPerfectWaldhausen (space k)).isZero)
  let e := smallModelWhiskerIso
    (C := BoundedFlatCoefficientSections i)
    (D := BoundedFlatPerfect (space i)) (E := BoundedFlatPerfect (space k))
    (boundedFlatCoefficientOriginalEvaluation i)
    (boundedFlatCoefficientSectionsMap f ⋙ boundedFlatCoefficientOriginalEvaluation k)
    p _ (boundedFlatCoefficientSectionReindexIso f) z
  change (boundedFlatCoefficientSectionsMap f ⋙
      (boundedFlatCoefficientSectionEvaluationModelMap k).functor) ≅
    ((boundedFlatCoefficientSectionEvaluationModelMap i).functor ⋙
      (boundedFlatCoefficientOriginalModelMap f).functor)
  exact isoWhiskerLeft (boundedFlatCoefficientSectionsMap f)
      (boundedFlatCoefficientSectionEvaluationNormalizationIso k).symm ≪≫
    (Functor.associator (boundedFlatCoefficientSectionsMap f)
      (boundedFlatCoefficientOriginalEvaluation k) AsSmall.up).symm ≪≫ e ≪≫
    isoWhiskerRight (boundedFlatCoefficientSectionEvaluationNormalizationIso i) _

/-- The whole original coefficient/scheme comparison retains every original structure map. -/
def boundedFlatCoefficientSectionEvaluationHomotopy {i k : Index R} (f : i ⟶ k) :
    Homotopy
      ((boundedFlatCoefficientSectionPrespectrumFunctor R).map f ≫
        boundedFlatCoefficientSectionEvaluationPrespectrumMap k)
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap i ≫
        boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map f)) :=
  (prespectrumTransformationHomotopy
    (V := boundedFlatCoefficientSectionModel i)
    (W := modelOf (boundedFlatPerfectWaldhausen (space k)))
    (F := boundedFlatCoefficientSectionModelMap f ≫
      boundedFlatCoefficientSectionEvaluationModelMap k)
    (G := boundedFlatCoefficientSectionEvaluationModelMap i ≫
      boundedFlatCoefficientOriginalModelMap f)
    (boundedFlatCoefficientSectionEvaluationIso f).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_comp _ _)

/-- The same original joint section prespectra in the genuine stable localization. -/
def boundedFlatCoefficientSectionLocalizedSpectrumFunctor (R : CommRingCat.{u}) :
    Index R ⥤ StableLocalization.{u+1} :=
  boundedFlatCoefficientSectionPrespectrumFunctor R ⋙ toStableLocalization

/-- Actual evaluation is inverted only by its proved all-signed stable equivalence. -/
def boundedFlatCoefficientSectionEvaluationLocalizedIso (i : Index R) :
    (boundedFlatCoefficientSectionLocalizedSpectrumFunctor R).obj i ≅
      boundedFlatLocalizedSpectrum (space i) :=
  stableLocalizationIso (boundedFlatCoefficientSectionEvaluationPrespectrumMap i)
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap_isStableEquivalence i)

/-- The forward localized comparison is precisely the original normalized evaluation map. -/
@[simp] theorem boundedFlatCoefficientSectionEvaluationLocalizedIso_hom (i : Index R) :
    (boundedFlatCoefficientSectionEvaluationLocalizedIso i).hom =
      toStableLocalization.map (boundedFlatCoefficientSectionEvaluationPrespectrumMap i) := rfl

/-- Every joint square commutes in the localization by its actual whole comparison track. -/
theorem boundedFlatCoefficientSectionEvaluationLocalizedIso_naturality {i k : Index R}
    (f : i ⟶ k) :
    (boundedFlatCoefficientSectionLocalizedSpectrumFunctor R).map f ≫
        (boundedFlatCoefficientSectionEvaluationLocalizedIso k).hom =
      (boundedFlatCoefficientSectionEvaluationLocalizedIso i).hom ≫
        boundedFlatLocalizedPullback (Quillen.Scheme.CoefficientBaseChange.map f) := by
  change toStableLocalization.map
      ((boundedFlatCoefficientSectionPrespectrumFunctor R).map f) ≫
      toStableLocalization.map (boundedFlatCoefficientSectionEvaluationPrespectrumMap k) =
    toStableLocalization.map (boundedFlatCoefficientSectionEvaluationPrespectrumMap i) ≫
      toStableLocalization.map
        (boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map f))
  have h := toStableLocalization_map_eq_of_homotopy
    (boundedFlatCoefficientSectionEvaluationHomotopy f)
  simpa only [Functor.map_comp] using h

/-- The actual joint evaluation family is a genuine natural isomorphism. -/
def boundedFlatCoefficientSectionEvaluationLocalizedNatIso (R : CommRingCat.{u}) :
    boundedFlatCoefficientSectionLocalizedSpectrumFunctor R ≅
      Quillen.Scheme.CoefficientBaseChange.functor R ⋙ BoundedFlatLocalizedSpectrumFunctor :=
  NatIso.ofComponents boundedFlatCoefficientSectionEvaluationLocalizedIso
    boundedFlatCoefficientSectionEvaluationLocalizedIso_naturality

/-- The exact original forward evaluation is retained at every joint component. -/
@[simp] theorem boundedFlatCoefficientSectionEvaluationLocalizedNatIso_hom_app
    (i : Index R) :
    (boundedFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app i =
      toStableLocalization.map (boundedFlatCoefficientSectionEvaluationPrespectrumMap i) := rfl

/-- Restrict the same original family to an arbitrary actual coefficient row. -/
def boundedFlatCoefficientSectionRowEvaluationLocalizedNatIso (P : Over (Spec R)) :
    row P ⋙ boundedFlatCoefficientSectionLocalizedSpectrumFunctor R ≅
      row P ⋙ Quillen.Scheme.CoefficientBaseChange.functor R ⋙
        BoundedFlatLocalizedSpectrumFunctor :=
  isoWhiskerLeft (row P) (boundedFlatCoefficientSectionEvaluationLocalizedNatIso R)

/-- The unchanged native coefficient fibers as quasi-compact schemes with all original maps. -/
def boundedFlatCoefficientQuasiCompactRow (P : Over (Spec R)) [CompactSpace P.left] :
    Under R ⥤ Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ where
  obj a := op ⟨space (op P, a), compactSpace_space (op P, a)⟩
  map g := (ObjectProperty.homMk
    (Quillen.Scheme.CoefficientBaseChange.map (𝟙 (op P), g))).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact Quillen.Scheme.CoefficientBaseChange.map_id (op P, a)
  map_comp {a b c} g h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact Quillen.Scheme.CoefficientBaseChange.map_comp
      (i := (op P, a)) (k := (op P, b)) (l := (op P, c))
      (𝟙 (op P), g) (𝟙 (op P), h)

/-- The quasi-compact lift retains precisely the original native geometric row. -/
theorem boundedFlatCoefficientQuasiCompactRow_inclusion (P : Over (Spec R))
    [CompactSpace P.left] :
    boundedFlatCoefficientQuasiCompactRow P ⋙ Quillen.Scheme.quasiCompactSchemesInclusion.op =
      row P ⋙ Quillen.Scheme.CoefficientBaseChange.functor R := rfl

/-- Original perfect spectra and arbitrary derived pullbacks on the actual compact native row. -/
def boundedFlatCoefficientPerfectLocalizedSpectrumFunctor (P : Over (Spec R))
    [CompactSpace P.left] : Under R ⥤ StableLocalization.{u+1} :=
  boundedFlatCoefficientQuasiCompactRow P ⋙ PerfectLocalizedSpectrumFunctor

/-- The original bounded-flat inclusion is natural for arbitrary derived pullback. -/
def boundedFlatCoefficientPerfectInclusionLocalizedNatIso (P : Over (Spec R))
    [CompactSpace P.left] :
    row P ⋙ Quillen.Scheme.CoefficientBaseChange.functor R ⋙
        BoundedFlatLocalizedSpectrumFunctor ≅
      boundedFlatCoefficientPerfectLocalizedSpectrumFunctor P :=
  isoWhiskerLeft (boundedFlatCoefficientQuasiCompactRow P) boundedFlatPerfectSpectrumNatIso

/-- The same evaluation and literal inclusion compare perfect spectra on a quasi-compact row. -/
def boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso (P : Over (Spec R))
    [CompactSpace P.left] :
    row P ⋙ boundedFlatCoefficientSectionLocalizedSpectrumFunctor R ≅
      boundedFlatCoefficientPerfectLocalizedSpectrumFunctor P :=
  boundedFlatCoefficientSectionRowEvaluationLocalizedNatIso P ≪≫
    boundedFlatCoefficientPerfectInclusionLocalizedNatIso P

/-- Every perfect component is the same actual normalized evaluation followed by inclusion. -/
@[simp] theorem boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso_hom_app
    (P : Over (Spec R)) [CompactSpace P.left] (a : Under R) :
    (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P).hom.app a =
      toStableLocalization.map
        (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)) := by
  change toStableLocalization.map
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a)) ≫
    toStableLocalization.map (exactOriginalPrespectrumMap _ _
      (boundedFlatPerfectInclusion_exact (space (op P, a)))) = _
  rw [← Functor.map_comp]
  rfl

end Quillen.PerfectComplexes
