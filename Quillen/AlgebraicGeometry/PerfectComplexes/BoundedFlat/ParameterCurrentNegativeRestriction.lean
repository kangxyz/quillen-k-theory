/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentNegativeComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterFullRestrictionSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterIteratedOpenIdentification
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalFullOpenTelescopeSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationTelescopeSquares
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFullOpenBassRestriction

/-!
# Original negative restriction in the current parameter telescope

The original scheme negative-group pullback is preserved by the actual finite
Spec-row comparisons and the independent current inclusion. The target arrow
is the original weak-change followed by full-open restriction. No inverse
localization or alternative group map is chosen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex SchemeNaturalSeed ParameterLaurentTrack

private theorem inverse_class_square {C : Type*} [Category C]
    {A B S T S' T' S'' T'' : C}
    (a : A ⟶ B) (g : A ⟶ S) (h : B ⟶ T) (f : S ⟶ T)
    (v : S' ⟶ S) (w : T' ⟶ T) (f' : S' ⟶ T')
    (e : S'' ⟶ S') (k : T'' ⟶ T') (f'' : S'' ⟶ T'')
    [IsIso v] [IsIso w] [IsIso e] [IsIso k]
    (h₀ : a ≫ h = g ≫ f) (h₁ : v ≫ f = f' ≫ w) (h₂ : e ≫ f' = f'' ≫ k) :
    a ≫ (h ≫ inv w ≫ inv k) = (g ≫ inv v ≫ inv e) ≫ f'' := by
  have hv : f ≫ inv w = inv v ≫ f' := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, h₁]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have he : f' ≫ inv k = inv e ≫ f'' := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, h₂]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  calc
    a ≫ (h ≫ inv w ≫ inv k) = g ≫ (f ≫ inv w) ≫ inv k := by
      rw [← Category.assoc a h, h₀]
      simp only [Category.assoc]
    _ = g ≫ (inv v ≫ f') ≫ inv k := by rw [hv]
    _ = (g ≫ inv v) ≫ (f' ≫ inv k) := by simp only [Category.assoc]
    _ = (g ≫ inv v) ≫ (inv e ≫ f'') := by rw [he]
    _ = (g ≫ inv v ≫ inv e) ≫ f'' := by simp only [Category.assoc]

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Both original global restriction factors retain the original finite scheme pullback. -/
theorem finite_fullRestriction_square (i : ℕ) :
    finiteRestriction Q i ≫
        (strictDiagramIterate (laurentUnderSquareFunctor _ ) i).map
          (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f) =
      (LocalizationTelescope.finiteOpen f i ≫ FullOpenTelescope.finiteRestriction f i) ≫
        finiteRestriction P i := by
  rw [Category.assoc, FullOpenTelescope.finiteRestriction_square,
    ← Category.assoc, LocalizationTelescope.finiteOpen_square, Category.assoc,
    boundedFlatCoefficientAmbientBassFullOpen_eq_original]
  rfl

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The unchanged finite negative comparison preserves the original scheme pullback. -/
@[reassoc]
theorem finiteNegativeKComparison_restriction (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (boundedFlatCoefficientOriginalNegativeKRestriction f i).app a ≫
      (finiteNegativeKComparison P i).hom.app a =
    (finiteNegativeKComparison Q i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((parameterFiniteRestriction f i).app (specUnder.obj a)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let : IsIso (H.map ((finiteRestriction Q i).app a)) :=
    finiteRestriction_isStableEquivalence Q i a (-(i : ℤ))
  let : IsIso (H.map ((finiteRestriction P i).app a)) :=
    finiteRestriction_isStableEquivalence P i a (-(i : ℤ))
  have h₁ := congrArg (fun η => H.map (η.app a)) (finite_fullRestriction_square f i)
  have h₂ := congrArg (fun η => H.map (η.app a)) (fullRestriction_finite_square f i)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp] at h₁ h₂
  rw [finiteNegativeKComparison_hom_app, finiteNegativeKComparison_hom_app]
  simpa only [← Functor.map_inv, NatIso.inv_hom_app] using
    inverse_class_square _ _ _ _ _ _ _ _ _ _
    (congrArg (fun η => η.app a)
      (boundedFlatCoefficientAmbientNegativeKComparison_schemeRestriction f i)) h₁ h₂.symm

omit [CompactSpace P.left] [CompactSpace Q.left] in
/-- The original current inclusion retains the actual full-open input map. -/
theorem currentStageInclusion_restriction (i : ℕ) :
    currentStageInclusion Q i ≫
      currentInputMap (ambientTrack Q.left) (ambientTrack P.left)
        (ParameterFullCurrentNull.fullMap f.left)
        (ParameterFullCurrentNull.fullMap_equivariant f.left) =
      parameterFiniteRestriction f i ≫ currentStageInclusion P i := by
  have h := Telescope.diagramInclusion_diagramMap
    (fun j => (strictDiagramIterate squareFunctor j).obj (parameterDiagram Q))
    (fun j => (strictDiagramIterate squareFunctor j).obj (parameterDiagram P))
    (currentTransition (ambientTrack Q.left)) (currentTransition (ambientTrack P.left))
    (fun j => (strictDiagramIterate squareFunctor j).map
      (ParameterFullCurrentNull.fullMap f.left))
    (currentInput_transition _ _ _ (ParameterFullCurrentNull.fullMap_equivariant f.left)) i
  simpa only [currentStageInclusion, currentInputMap, parameterFiniteRestriction,
    parameterRestrictionMap_eq_fullMap, parameterDiagram, currentTelescope] using h

variable [QuasiSeparatedSpace P.left] [QuasiSeparatedSpace Q.left]

/-- Every original negative pullback is the literal current full-open restriction. -/
@[reassoc]
theorem currentNegativeKComparison_restriction (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (boundedFlatCoefficientOriginalNegativeKRestriction f i).app a ≫
      (currentNegativeKComparison P i).hom.app a =
    (currentNegativeKComparison Q i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((currentInputMap (ambientTrack Q.left) (ambientTrack P.left)
          (ParameterFullCurrentNull.fullMap f.left)
          (ParameterFullCurrentNull.fullMap_equivariant f.left)).app (specUnder.obj a)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  have h := congrArg (fun η => H.map (η.app (specUnder.obj a)))
    (currentStageInclusion_restriction f i)
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  rw [currentNegativeKComparison_hom_app, currentNegativeKComparison_hom_app,
    ← Category.assoc, finiteNegativeKComparison_restriction]
  simpa only [Category.assoc] using
    congrArg (fun k => (finiteNegativeKComparison Q i).hom.app a ≫ k) h.symm

omit [QuasiSeparatedSpace P.left] in
/-- For an open immersion the ambient separation hypothesis supplies the open one. -/
@[reassoc]
theorem currentNegativeKComparison_openRestriction (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
    (boundedFlatCoefficientOriginalNegativeKRestriction f i).app a ≫
      (currentNegativeKComparison P i).hom.app a =
    (currentNegativeKComparison Q i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((currentInputMap (ambientTrack Q.left) (ambientTrack P.left)
          (ParameterFullCurrentNull.fullMap f.left)
          (ParameterFullCurrentNull.fullMap_equivariant f.left)).app (specUnder.obj a)) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact currentNegativeKComparison_restriction f i a

end Quillen.PerfectComplexes.GlobalParameterCoefficient
