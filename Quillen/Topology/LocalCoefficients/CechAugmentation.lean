/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CechBicomplex
public import Quillen.Algebra.Homology.TotalSingle

/-!
# The original Čech total augmentation to twisted singular chains

The total target supported in Čech degree zero identifies by an actual chain
isomorphism with the original small-chain complex. Composing gives the actual
augmentation to small and ambient twisted singular chains. This file does
not assume or assert that totalization preserves the proved row equivalences.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type u}
  (U : ι → Set X) (A : System.{u, u} X)

/-- Alternating singular faces commute with concentration in Čech degree zero. -/
def smallSingleBicomplexIso :
    HomologicalComplex₂.single₀Bicomplex (smallChainComplex U A) ≅ smallSingleBicomplex U A :=
  (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
    (ChainComplex.single₀ (ModuleCat.{u} ℤ))).app (smallSimplicialModule U A)

/-- The total complex concentrated in Čech degree zero is the actual small-chain complex. -/
def smallSingleTotalIso : smallSingleTotalComplex U A ≅ smallChainComplex U A :=
  HomologicalComplex₂.total.mapIso (smallSingleBicomplexIso U A).symm (ComplexShape.down ℕ) ≪≫
    (HomologicalComplex₂.single₀TotalIso (smallChainComplex U A)).symm

/-- Forget the Čech labels and identify the zero-th-row target with original small chains. -/
def cechSmallChainAugmentation : cechTotalComplex U A ⟶ smallChainComplex U A :=
  cechTotalAugmentation U A ≫ (smallSingleTotalIso U A).hom

/-- The original total augmentation to genuine twisted singular chains. -/
def cechSingularAugmentation : cechTotalComplex U A ⟶ singularChainComplex A :=
  cechSmallChainAugmentation U A ≫ smallChainComplexInclusion U A

/-- The zero-th Čech summand is unchanged by the target identification. -/
@[reassoc (attr := simp)]
theorem smallSingleTotalIso_zero (n : ℕ) :
    (smallSingleBicomplex U A).ιTotal (ComplexShape.down ℕ) n 0 n (Nat.add_zero n) ≫
      (smallSingleTotalIso U A).hom.f n = 𝟙 _ := by
  change _ ≫ ((HomologicalComplex₂.total.map (smallSingleBicomplexIso U A).inv
    (ComplexShape.down ℕ)).f n ≫ _) = _
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  change (𝟙 _) ≫ (HomologicalComplex₂.single₀TotalInclusion (smallChainComplex U A)).f n ≫
    (HomologicalComplex₂.single₀TotalIso (smallChainComplex U A)).inv.f n = _
  rw [Category.id_comp]
  exact congrArg (fun f ↦ f.f n)
    (HomologicalComplex₂.single₀TotalIso (smallChainComplex U A)).hom_inv_id

/-- On a genuine labeled simplex in Čech degree zero, augmentation is the original summand map. -/
@[reassoc]
theorem cechChainInclusion_totalAugmentation (n : ℕ) (t : CechSimplex U ⦋n⦌ ⦋0⦌) :
    cechChainInclusion U A t ≫
      (cechBicomplex U A).ιTotal (ComplexShape.down ℕ) n 0 n (Nat.add_zero n) ≫
        (cechSmallChainAugmentation U A).f n = smallChainInclusion U A t.1 := by
  change _ ≫ _ ≫ ((HomologicalComplex₂.total.map (cechBicomplexAugmentation U A)
    (ComplexShape.down ℕ)).f n ≫ _) = _
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  change _ ≫ (cechRowAugmentation U A ⦋n⦌).f 0 ≫ _ ≫ _ = _
  have ha : cechChainInclusion U A t ≫ cechModuleAugmentation U A ⦋n⦌ ⦋0⦌ =
      smallChainInclusion U A t.1 := Sigma.ι_comp_desc _ _
  change _ ≫ cechModuleAugmentation U A ⦋n⦌ ⦋0⦌ ≫ _ ≫ _ = _
  rw [← Category.assoc, ha, smallSingleTotalIso_zero]
  exact Category.comp_id _

/-- The same original summand is retained in ambient twisted singular chains. -/
@[reassoc]
theorem cechChainInclusion_singularAugmentation (n : ℕ) (t : CechSimplex U ⦋n⦌ ⦋0⦌) :
    cechChainInclusion U A t ≫
      (cechBicomplex U A).ιTotal (ComplexShape.down ℕ) n 0 n (Nat.add_zero n) ≫
        (cechSingularAugmentation U A).f n = chainInclusion A t.1.val := by
  change _ ≫ _ ≫ ((cechSmallChainAugmentation U A).f n ≫ smallModuleInclusion U A ⦋n⦌) = _
  rw [cechChainInclusion_totalAugmentation_assoc, smallChainInclusion_smallModuleInclusion]

end Quillen.LocalCoefficients
