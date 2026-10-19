/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentNegativeForget
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentNegativeRestriction

/-! # Inverse current negative-class maps and the unchanged two localization arrows -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open SchemeNaturalSeed ParameterLaurentTrack
universe u

/-- Inverting both fixed class isomorphisms preserves the exact original arrow. -/
theorem currentClassInverseSquare {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ A') (k : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ k.hom = e.hom ≫ g) : e.inv ≫ f = g ≫ k.inv := by
  apply (cancel_mono k.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

example {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison f i).inv.app a ≫
        (Bass.supportedNegativeKForgetNat i).app
          ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) =
      (stableHomotopyFunctor (-(i : ℤ))).map
          ((currentInputMap (supportedTrack f.left) (ambientTrack Q.left)
            (Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor)
            (forget_equivariant f.left)).app (specUnder.obj a)) ≫
        (GlobalParameterCoefficient.currentNegativeKComparison Q i).inv.app a :=
  currentClassInverseSquare
    ((GlobalSupportedParameterCoefficient.currentNegativeKComparison f i).app a)
    ((GlobalParameterCoefficient.currentNegativeKComparison Q i).app a) _ _
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison_forget f i a)

example {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace P.left] [QuasiSeparatedSpace Q.left]
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (GlobalParameterCoefficient.currentNegativeKComparison Q i).inv.app a ≫
        (boundedFlatCoefficientOriginalNegativeKRestriction f i).app a =
      (stableHomotopyFunctor (-(i : ℤ))).map
          ((currentInputMap (ambientTrack Q.left) (ambientTrack P.left)
            (ParameterFullCurrentNull.fullMap f.left)
            (ParameterFullCurrentNull.fullMap_equivariant f.left)).app (specUnder.obj a)) ≫
        (GlobalParameterCoefficient.currentNegativeKComparison P i).inv.app a :=
  currentClassInverseSquare
    ((GlobalParameterCoefficient.currentNegativeKComparison Q i).app a)
    ((GlobalParameterCoefficient.currentNegativeKComparison P i).app a) _ _
    (GlobalParameterCoefficient.currentNegativeKComparison_restriction f i a)

example (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    [CompactSpace P.left] [QuasiSeparatedSpace P.left]
    {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (GlobalParameterCoefficient.currentNegativeKComparison P 2).inv.app a ≫
        (Bass.negativeKFunctor 2).map ((boundedFlatCoefficientQuasiCompactRow P).map g) =
      (stableHomotopyFunctor (-((2 : ℕ) : ℤ))).map
          ((currentTelescope (ambientTrack P.left)).map (specUnder.map g)) ≫
        (GlobalParameterCoefficient.currentNegativeKComparison P 2).inv.app b :=
  ((GlobalParameterCoefficient.currentNegativeKComparison P 2).inv.naturality g).symm
