/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSplitMaps
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationNaturality

/-!
# Original coefficient K-groups in the actual fine section spectrum

Every original nonnegative bounded-flat K-group is naturally the corresponding stable group
of the original fine section spectrum. The comparison uses the original normalized evaluation
and its actual stable inverse. Its representative equation retains the original K/stable map.
No compactness or flatness hypotheses are needed.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes

/-- The original bounded-flat K-group computes the same localized connective stable group. -/
def boundedFlatPerfectKLocalizedStableIso (n : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (boundedFlatPerfectKAddFunctor n).obj X ≅
      (BoundedFlatLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor (n : ℤ)).obj X :=
  (originalKStableEquiv (boundedFlatPerfectWaldhausen X.unop) n).toAddCommGrpIso

/-- Naturality retains every original bounded-flat pullback, including nonflat scheme maps. -/
@[reassoc]
theorem boundedFlatPerfectKLocalizedStableIso_naturality (n : ℕ)
    {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (boundedFlatPerfectKAddFunctor n).map f ≫ (boundedFlatPerfectKLocalizedStableIso n Y).hom =
      (boundedFlatPerfectKLocalizedStableIso n X).hom ≫
        (BoundedFlatLocalizedSpectrumFunctor ⋙
          localizedStableHomotopyFunctor (n : ℤ)).map f := by
  ext a
  exact localizedSpectrumMap_originalK_naturality _ _
    (boundedFlatPerfectPullback_exact f.unop) n a.toMul

/-- Original K-groups and original stable groups agree as actual functors. -/
def boundedFlatPerfectKLocalizedStableNatIso (n : ℕ) :
    boundedFlatPerfectKAddFunctor.{u} n ≅
      BoundedFlatLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor (n : ℤ) :=
  NatIso.ofComponents (boundedFlatPerfectKLocalizedStableIso n)
    (fun f => boundedFlatPerfectKLocalizedStableIso_naturality n f)

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The actual inverse of normalized evaluation gives the comparison with fine section groups. -/
def boundedFlatCoefficientSectionKStableNatIso (n : ℕ) :
    boundedFlatCoefficientKAddFunctor P n ≅
      row P ⋙ boundedFlatCoefficientSectionPrespectrumFunctor R ⋙
        stableHomotopyFunctor (n : ℤ) :=
  Functor.isoWhiskerLeft (row P ⋙ BaseChange.Coefficients.functor R)
      (boundedFlatPerfectKLocalizedStableNatIso n) ≪≫
    (Functor.isoWhiskerRight (boundedFlatCoefficientSectionRowEvaluationLocalizedNatIso P)
      (localizedStableHomotopyFunctor (n : ℤ))).symm

/-- Composing the comparison with original evaluation recovers the exact original K/stable map. -/
@[reassoc]
theorem boundedFlatCoefficientSectionKStableNatIso_evaluation (n : ℕ) (a : Under R) :
    (boundedFlatCoefficientSectionKStableNatIso P n).hom.app a ≫
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a)) =
      (originalKStableEquiv
        (boundedFlatPerfectWaldhausen (space (op P, a))) n).toAddCommGrpIso.hom := by
  let A := Functor.isoWhiskerLeft (row P ⋙ BaseChange.Coefficients.functor R)
    (boundedFlatPerfectKLocalizedStableNatIso n)
  let E := Functor.isoWhiskerRight (boundedFlatCoefficientSectionRowEvaluationLocalizedNatIso P)
    (localizedStableHomotopyFunctor (n : ℤ))
  have hE : E.hom.app a = (stableHomotopyFunctor (n : ℤ)).map
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a)) := rfl
  change (A.hom.app a ≫ E.inv.app a) ≫ _ = _
  rw [← hE, Category.assoc, ← NatTrans.comp_app, E.inv_hom_id, NatTrans.id_app]
  exact Category.comp_id (A.hom.app a)

end Quillen.PerfectComplexes
