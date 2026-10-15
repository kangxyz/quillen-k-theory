/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassOriginalNegativeComparison
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.PolynomialLaurentSchemeNaturality
public import Quillen.KTheory.Bass.DiagramTransportNaturality

/-!
# Scheme restriction for the original finite native negative-group comparison

For an arbitrary scheme-over-base arrow with compact source and target, the
existing comparison preserves the actual original group pullback and the
original finite strict Model restriction. All transformations retain every
coefficient arrow. No supported, transition, seed or telescope assertion occurs.
-/

@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u w
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)

/-- Finite restriction is the iteration of the existing joint native Model map. -/
def boundedFlatCoefficientAmbientBassSchemeRestriction (i : ℕ) :
    boundedFlatCoefficientAmbientBassDiagram Q i ⟶
      boundedFlatCoefficientAmbientBassDiagram P i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (boundedFlatCoefficientSectionModelRestriction f) prespectrumFunctor)

/-- The bottom action applies the original signed stable homotopy functor. -/
def boundedFlatCoefficientAmbientBassBottomSchemeRestriction (i : ℕ) :
    boundedFlatCoefficientAmbientBassDiagram Q i ⋙ stableHomotopyFunctor (-(i : ℤ)) ⟶
      boundedFlatCoefficientAmbientBassDiagram P i ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  Functor.whiskerRight (boundedFlatCoefficientAmbientBassSchemeRestriction f i)
    (stableHomotopyFunctor (-(i : ℤ)))

/-- Degree zero is literally the original uniterated Model restriction. -/
theorem boundedFlatCoefficientAmbientBassBottomSchemeRestriction_zero (a : Under R) :
    (boundedFlatCoefficientAmbientBassBottomSchemeRestriction f 0).app a =
      (stableHomotopyFunctor 0).map
        (prespectrumFunctor.map ((boundedFlatCoefficientSectionModelRestriction f).app a)) := rfl

/-- The genuine signed bottom contraction preserves the original scheme restriction. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientBassBottomContractionIso_schemeRestriction
    (i : ℕ) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientAmbientBassBottomSchemeRestriction f i)).app a ≫
        (boundedFlatCoefficientAmbientBassBottomContractionIso P i).hom.app a =
    (boundedFlatCoefficientAmbientBassBottomContractionIso Q i).hom.app a ≫
      (boundedFlatCoefficientAmbientBassBottomSchemeRestriction f (i + 1)).app a :=
  modelDiagramBottomContractionIso_map
    (Functor.whiskerRight (boundedFlatCoefficientSectionModelRestriction f) prespectrumFunctor) i a

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The original native scheme pullback, lifted to the actual quasi-compact opposite rows. -/
def boundedFlatCoefficientQuasiCompactRowRestriction :
    boundedFlatCoefficientQuasiCompactRow Q ⟶ boundedFlatCoefficientQuasiCompactRow P where
  app a := (AlgebraicGeometry.Scheme.quasiCompactSchemeProperty.homMk (schemeMap f a)).op
  naturality {a b} g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact schemeMap_coefficientMap f g

/-- Every original group restriction is the already defined Bass functor on that scheme map. -/
def boundedFlatCoefficientOriginalNegativeKRestriction (i : ℕ) :
    boundedFlatCoefficientQuasiCompactRow Q ⋙ Bass.negativeKFunctor i ⟶
      boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i :=
  Functor.whiskerRight (boundedFlatCoefficientQuasiCompactRowRestriction f)
    (Bass.negativeKFunctor i)

/-- The true Laurent product identification retains the same original scheme pullback. -/
@[reassoc]
theorem boundedFlatCoefficientLaurentIso_schemeRestriction (a : Under R) :
    (boundedFlatCoefficientQuasiCompactRowRestriction f).app
        ((laurentUnderFunctor R).obj a) ≫
      (boundedFlatCoefficientLaurentIso P).hom.app a =
    (boundedFlatCoefficientLaurentIso Q).hom.app a ≫
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op.map
        ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentIso P a).inv ≫
      schemeMap f ((laurentUnderFunctor R).obj a) =
    (AlgebraicGeometry.Scheme.Products.baseProductFunctor
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)).map
        (schemeMap f a) ≫ (laurentIso Q a).inv
  apply (cancel_mono (laurentIso Q a).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [laurentIso_schemeMap f a, Iso.inv_hom_id_assoc]

/-- Original chart transport retains the actual restriction between compact native schemes. -/
@[reassoc]
theorem boundedFlatCoefficientContractionTransportIso_schemeRestriction
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedFlatCoefficientQuasiCompactRowRestriction f) F)).app a ≫
        (boundedFlatCoefficientContractionTransportIso P F).hom.app a =
    (boundedFlatCoefficientContractionTransportIso Q F).hom.app a ≫
      (Quillen.Bass.TwoChart.contraction (NatTrans.op
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
        (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F).map
          ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a) :=
  Quillen.Bass.TwoChart.contractionTransportIso_map
    (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientQuasiCompactRow Q) (boundedFlatCoefficientQuasiCompactRow P)
    (boundedFlatCoefficientPolynomialIso Q) (boundedFlatCoefficientLaurentIso Q)
    (boundedFlatCoefficientPolynomialIso P) (boundedFlatCoefficientLaurentIso P)
    (boundedFlatCoefficientPolynomialLaurentIso_plus Q)
    (boundedFlatCoefficientPolynomialLaurentIso_minus Q)
    (boundedFlatCoefficientPolynomialLaurentIso_plus P)
    (boundedFlatCoefficientPolynomialLaurentIso_minus P)
    (boundedFlatCoefficientQuasiCompactRowRestriction f)
    (boundedFlatCoefficientLaurentIso_schemeRestriction f) F a

/-- The inverse transport retains exactly the same original scheme restriction. -/
@[reassoc]
theorem boundedFlatCoefficientContractionTransportIso_schemeRestriction_inv
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (a : Under R) :
    (Quillen.Bass.TwoChart.contraction (NatTrans.op
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
      (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F).map
        ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a) ≫
      (boundedFlatCoefficientContractionTransportIso P F).inv.app a =
    (boundedFlatCoefficientContractionTransportIso Q F).inv.app a ≫
      (Quillen.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
        (Functor.whiskerRight (boundedFlatCoefficientQuasiCompactRowRestriction f) F)).app a := by
  apply (cancel_mono ((boundedFlatCoefficientContractionTransportIso P F).hom.app a)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [boundedFlatCoefficientContractionTransportIso_schemeRestriction, Iso.inv_hom_id_app_assoc]
  exact Category.comp_id _

/-- Joint normalized evaluation followed by the original inclusion preserves every scheme arrow. -/
@[reassoc]
theorem boundedFlatCoefficientSectionPerfectEvaluation_schemeRestriction (a : Under R) :
    toStableLocalization.map
        ((Functor.whiskerRight (boundedFlatCoefficientSectionModelRestriction f)
          prespectrumFunctor).app a) ≫
      (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P).hom.app a =
    (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso Q).hom.app a ≫
      PerfectLocalizedSpectrumFunctor.map
        ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a) := by
  have hE := (boundedFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.naturality
    (show (op Q, a) ⟶ (op P, a) from (f.op, 𝟙 a))
  have hI := boundedFlatPerfectSpectrumNatIso.hom.naturality
    ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a)
  change (boundedFlatCoefficientSectionLocalizedSpectrumFunctor R).map (f.op, 𝟙 a) ≫
      (boundedFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app (op P, a) =
    (boundedFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app (op Q, a) ≫
      boundedFlatLocalizedPullback (schemeMap f a) at hE
  change boundedFlatLocalizedPullback (schemeMap f a) ≫
      boundedFlatPerfectSpectrumNatIso.hom.app
        ((boundedFlatCoefficientQuasiCompactRow P).obj a) =
    boundedFlatPerfectSpectrumNatIso.hom.app
        ((boundedFlatCoefficientQuasiCompactRow Q).obj a) ≫
      PerfectLocalizedSpectrumFunctor.map
        ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a) at hI
  change (boundedFlatCoefficientSectionLocalizedSpectrumFunctor R).map (f.op, 𝟙 a) ≫
      ((boundedFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app (op P, a) ≫
        boundedFlatPerfectSpectrumNatIso.hom.app
          ((boundedFlatCoefficientQuasiCompactRow P).obj a)) =
    ((boundedFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app (op Q, a) ≫
      boundedFlatPerfectSpectrumNatIso.hom.app
        ((boundedFlatCoefficientQuasiCompactRow Q).obj a)) ≫ _
  rw [← Category.assoc, hE, Category.assoc, hI, ← Category.assoc]

/-- Original perfect K-zero and the actual degree-zero Model restriction commute. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientBassBottomZeroNatIso_schemeRestriction (a : Under R) :
    (boundedFlatCoefficientOriginalNegativeKRestriction f 0).app a ≫
      (boundedFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a =
    (boundedFlatCoefficientAmbientBassBottomZeroNatIso Q).hom.app a ≫
      (boundedFlatCoefficientAmbientBassBottomSchemeRestriction f 0).app a := by
  let Eₚ := Functor.isoWhiskerRight
    (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P)
    (localizedStableHomotopyFunctor 0)
  let Eᵩ := Functor.isoWhiskerRight
    (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso Q)
    (localizedStableHomotopyFunctor 0)
  have hE : (boundedFlatCoefficientAmbientBassBottomSchemeRestriction f 0).app a ≫
      Eₚ.hom.app a = Eᵩ.hom.app a ≫
        (PerfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor 0).map
          ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a) := by
    have h := congrArg ((localizedStableHomotopyFunctor 0).map)
      (boundedFlatCoefficientSectionPerfectEvaluation_schemeRestriction f a)
    simpa only [Functor.map_comp, localizedStableHomotopyFunctor_original_map,
      Functor.comp_map, Eₚ, Eᵩ, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      boundedFlatCoefficientAmbientBassBottomSchemeRestriction_zero]
      using h
  apply (cancel_mono (Eₚ.hom.app a)).mp
  change ((_ ≫ (perfectKZeroLocalizedStableIso
      ((boundedFlatCoefficientQuasiCompactRow P).obj a)).hom ≫ Eₚ.inv.app a) ≫
      Eₚ.hom.app a) =
    (((perfectKZeroLocalizedStableIso
      ((boundedFlatCoefficientQuasiCompactRow Q).obj a)).hom ≫ Eᵩ.inv.app a) ≫ _) ≫
      Eₚ.hom.app a
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hE, Iso.inv_hom_id_app_assoc]
  exact perfectKZeroLocalizedStableIso_naturality
    ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a)

/-- The existing assembled comparison retains original restriction in every finite degree. -/
theorem boundedFlatCoefficientAmbientNegativeKComparison_schemeRestriction (i : ℕ) :
    boundedFlatCoefficientOriginalNegativeKRestriction f i ≫
      (boundedFlatCoefficientAmbientNegativeKComparison P i).hom =
    (boundedFlatCoefficientAmbientNegativeKComparison Q i).hom ≫
      boundedFlatCoefficientAmbientBassBottomSchemeRestriction f i := by
  induction i with
  | zero =>
      apply NatTrans.ext
      funext a
      exact boundedFlatCoefficientAmbientBassBottomZeroNatIso_schemeRestriction f a
  | succ i ih =>
      apply NatTrans.ext
      funext a
      let τₚ := boundedFlatCoefficientContractionTransportIso P (Bass.negativeKFunctor i)
      let τᵩ := boundedFlatCoefficientContractionTransportIso Q (Bass.negativeKFunctor i)
      let γₚ := boundedFlatCoefficientAmbientNegativeKComparison P i
      let γᵩ := boundedFlatCoefficientAmbientNegativeKComparison Q i
      let βₚ := boundedFlatCoefficientAmbientBassBottomContractionIso P i
      let βᵩ := boundedFlatCoefficientAmbientBassBottomContractionIso Q i
      let C := Quillen.Bass.TwoChart.contractionFunctor
        (underToLaurent R) (underToLaurentInvert R)
      let r := (boundedFlatCoefficientOriginalNegativeKRestriction f (i + 1)).app a
      let k := (C.map (boundedFlatCoefficientOriginalNegativeKRestriction f i)).app a
      let gₚ := (C.map γₚ.hom).app a
      let gᵩ := (C.map γᵩ.hom).app a
      let s := (C.map (boundedFlatCoefficientAmbientBassBottomSchemeRestriction f i)).app a
      let t := (boundedFlatCoefficientAmbientBassBottomSchemeRestriction f (i + 1)).app a
      have hT : r ≫ τₚ.inv.app a = τᵩ.inv.app a ≫ k :=
        boundedFlatCoefficientContractionTransportIso_schemeRestriction_inv f
          (Bass.negativeKFunctor i) a
      have hC : k ≫ gₚ = gᵩ ≫ s := by
        have h := congrArg (fun η ↦ (C.map η).app a) ih
        simpa only [Functor.map_comp, NatTrans.comp_app] using h
      have hB : s ≫ βₚ.hom.app a = βᵩ.hom.app a ≫ t :=
        boundedFlatCoefficientAmbientBassBottomContractionIso_schemeRestriction f i a
      change r ≫ (τₚ.inv.app a ≫ gₚ ≫ βₚ.hom.app a) =
        (τᵩ.inv.app a ≫ gᵩ ≫ βᵩ.hom.app a) ≫ t
      calc
        r ≫ (τₚ.inv.app a ≫ gₚ ≫ βₚ.hom.app a) =
            (r ≫ τₚ.inv.app a) ≫ gₚ ≫ βₚ.hom.app a := by simp only [Category.assoc]
        _ = (τᵩ.inv.app a ≫ k) ≫ gₚ ≫ βₚ.hom.app a := by rw [hT]
        _ = τᵩ.inv.app a ≫ (k ≫ gₚ) ≫ βₚ.hom.app a := by simp only [Category.assoc]
        _ = τᵩ.inv.app a ≫ (gᵩ ≫ s) ≫ βₚ.hom.app a := by rw [hC]
        _ = τᵩ.inv.app a ≫ gᵩ ≫ (s ≫ βₚ.hom.app a) := by simp only [Category.assoc]
        _ = τᵩ.inv.app a ≫ gᵩ ≫ (βᵩ.hom.app a ≫ t) := by rw [hB]
        _ = (τᵩ.inv.app a ≫ gᵩ ≫ βᵩ.hom.app a) ≫ t := by simp only [Category.assoc]

/-- Component form keeps the original scheme pullback and actual finite spectral map explicit. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientNegativeKComparison_schemeRestriction_app
    (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).map
        (AlgebraicGeometry.Scheme.quasiCompactSchemeProperty.homMk (schemeMap f a)).op ≫
      (boundedFlatCoefficientAmbientNegativeKComparison P i).hom.app a =
    (boundedFlatCoefficientAmbientNegativeKComparison Q i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
          (Functor.whiskerRight (boundedFlatCoefficientSectionModelRestriction f)
            prespectrumFunctor)).app a) :=
  congrArg (fun η ↦ η.app a)
    (boundedFlatCoefficientAmbientNegativeKComparison_schemeRestriction f i)

end Quillen.PerfectComplexes
