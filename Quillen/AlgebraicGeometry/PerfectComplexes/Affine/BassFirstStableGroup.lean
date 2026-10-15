/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassFirstCokernel
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSpanStableGroups
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStep
public import Quillen.KTheory.Bass.TwoChartStableCokernel

/-!
# The original first Bass step in degree minus one

The actual polynomial span, its genuine cone exact sequence, the signed parameter-loop shift
and the original perfect K-zero comparison identify degree minus one of the unchanged raw first
Bass step with the already-defined Bass cokernel of original perfect K-zero. Its Laurent map is
retained. No stabilization of later Bass stages is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The two unchanged polynomial inclusions induce the actual sum map onto the stable span. -/
def boundedFlatBassSpanStableSum (R : CommRingCat.{u}) :=
  biprod.desc
    ((stableHomotopyFunctor 0).map (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))))
    ((stableHomotopyFunctor 0).map (HomotopyPushout.inr
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))))

instance boundedFlatBassSpanStableSum_epi (R : CommRingCat.{u}) :
    Epi (boundedFlatBassSpanStableSum R) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro z
  obtain ⟨x, y, hxy⟩ := boundedFlatBassSpan_stable_zero_generate R z
  let P := (stableHomotopyFunctor 0).obj (originalPrespectrum
    (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R)))))
  refine ⟨(AddCommGrpCat.biprodIsoProd P P).inv (x, y), ?_⟩
  have h := ConcreteCategory.congr_hom (AddCommGrpCat.biprodIsoProd_inv_comp_desc
    ((stableHomotopyFunctor 0).map (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))))
    ((stableHomotopyFunctor 0).map (HomotopyPushout.inr
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))))) (x, y)
  exact h.trans hxy

/-- The original Bass comparison sends the two inclusions to the original two Laurent maps. -/
theorem boundedFlatBassSpanStableSum_comparison (R : CommRingCat.{u}) :
    boundedFlatBassSpanStableSum R ≫ (stableHomotopyFunctor 0).map
      (boundedFlatBassSquareComparison R) =
    biprod.desc
      ((stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (laurentPlus R)))
      ((stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (laurentMinus R))) := by
  apply biprod.hom_ext'
  · simp only [boundedFlatBassSpanStableSum, biprod.inl_desc_assoc, biprod.inl_desc,
      ← Functor.map_comp, boundedFlatBassSquareComparison, HomotopyPushout.inl_desc]
  · simp only [boundedFlatBassSpanStableSum, biprod.inr_desc_assoc, biprod.inr_desc,
      ← Functor.map_comp, boundedFlatBassSquareComparison, HomotopyPushout.inr_desc]

/-- The original perfect-K-zero Bass cokernel is the degree-minus-one group of the raw Bass step.
-/
def boundedFlatBassFirstStableGroupIso (R : CommRingCat.{u}) :
    Quillen.Bass.negativeK R 1 ≅ stableHomotopyGroup (boundedFlatAffineBassStep R) (-1) := by
  let := boundedFlatBassSpan_stable_neg_subsingleton R (-1) (by decide)
  exact boundedFlatBassKZeroCokernelIso R ≪≫
    Quillen.Bass.chartDifferenceLoopedConeIso (boundedFlatBassSquareComparison R)
      (boundedFlatBassSquareComparison_coneFiber_isStableEquivalence R)
      (boundedFlatBassSpanStableSum R)
      ((stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (laurentPlus R)))
      ((stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (laurentMinus R)))
      (boundedFlatBassSpanStableSum_comparison R)

/-- An original Laurent K-zero class enters the original cone, followed by the signed loop shift.
-/
def boundedFlatBassFirstLaurentMap (R : CommRingCat.{u}) :
    Quillen.Bass.affineKZeroFunctor.obj (.of (LaurentPolynomial R)) ⟶
      stableHomotopyGroup (boundedFlatAffineBassStep R) (-1) :=
  (boundedFlatAffineStableKZeroIso (.of (LaurentPolynomial R))).hom ≫
    (stableHomotopyFunctor 0).map (mappingConeInclusion (boundedFlatBassSquareComparison R)) ≫
      eqToHom (congrArg (stableHomotopyGroup (mappingCone (boundedFlatBassSquareComparison R)))
        (show (0 : ℤ) = -1 + 1 by decide)) ≫
        (parameterStableHomotopyIso (mappingCone (boundedFlatBassSquareComparison R)) (-1)).inv

/-- The original Laurent quotient map agrees with the unchanged spectral inclusion. -/
@[reassoc]
theorem boundedFlatBassFirstStableGroupIso_π (R : CommRingCat.{u}) :
    Quillen.Bass.negativeKπ R 0 ≫ (boundedFlatBassFirstStableGroupIso R).hom =
      boundedFlatBassFirstLaurentMap R := by
  let := boundedFlatBassSpan_stable_neg_subsingleton R (-1) (by decide)
  simp only [boundedFlatBassFirstStableGroupIso, Iso.trans_hom, ← Category.assoc]
  rw [boundedFlatBassKZeroCokernelIso_π]
  simp only [Category.assoc, boundedFlatBassStableDifference,
    Quillen.Bass.chartDifferenceLoopedConeIso_π, boundedFlatBassFirstLaurentMap]

/-- Every actual degree-minus-one first-step class comes from an original Laurent K-zero class. -/
theorem boundedFlatBassFirstLaurentMap_surjective (R : CommRingCat.{u}) :
    Function.Surjective (boundedFlatBassFirstLaurentMap R) := by
  intro z
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (boundedFlatBassFirstStableGroupIso R).hom).surjective z
  obtain ⟨x, rfl⟩ := Quillen.Bass.negativeKπ_surjective R 0 y
  exact ⟨x, (ConcreteCategory.congr_hom (boundedFlatBassFirstStableGroupIso_π R) x).symm⟩

/-- The literal polynomial difference is exactly the relation among original Laurent classes. -/
theorem boundedFlatBassFirstLaurentMap_eq_zero_iff (R : CommRingCat.{u})
    (x : Quillen.Bass.negativeK (Quillen.Bass.laurentFunctor.obj R) 0) :
    boundedFlatBassFirstLaurentMap R x = 0 ↔
      ∃ a b : Quillen.Bass.negativeK (Quillen.Bass.polynomialFunctor.obj R) 0,
        Quillen.Bass.negativeKMap (Quillen.Bass.plus.app R) 0 a -
          Quillen.Bass.negativeKMap (Quillen.Bass.minus.app R) 0 b = x := by
  rw [← Quillen.Bass.negativeKπ_eq_zero_iff]
  have h := ConcreteCategory.congr_hom (boundedFlatBassFirstStableGroupIso_π R) x
  constructor
  · intro hx
    apply (ConcreteCategory.bijective_of_isIso (boundedFlatBassFirstStableGroupIso R).hom).injective
    exact h.trans hx |>.trans (map_zero _).symm
  · intro hx
    exact h.symm.trans (by rw [ConcreteCategory.comp_apply, hx, map_zero])

end Quillen.PerfectComplexes
