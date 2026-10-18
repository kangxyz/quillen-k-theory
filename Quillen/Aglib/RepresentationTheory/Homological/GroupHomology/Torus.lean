/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.RepresentationTheory.Homological.GroupHomology.IntegralBar

/-!
# Original bar torus cycles, commutators, and simultaneous inversion

Intended upstream module: `Aglib.RepresentationTheory.Homological.GroupHomology.Torus`.
The original Mathlib bar complex uses a commutative coefficient ring and a group.
Chosen cocycles and extension perfectness retain their perfect-group hypotheses;
integral comparisons use `ULift ℤ`, and central lifts retain surjectivity and central kernel.
Current consumer: `Quillen.Algebra.Group.StableSteinbergSchur`.
-/
@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Finsupp
open scoped commutatorElement
namespace groupHomology.IntegralBar
section Bar
variable (k G : Type u) [CommRing k] [Group G] [Group.IsPerfect G]

/-- Commuting group elements give the literal original bar torus cycle [g|h]−[h|g]. -/
def torusCycle (g h : G) (hgh : Commute g h) : groupHomology.cycles₂ (coefficients k G) :=
  ⟨single (g, h) 1 - single (h, g) 1, by
    change groupHomology.d₂₁ (coefficients k G) _ = 0
    rw [map_sub]
    erw [dTwo_single, dTwo_single]
    rw [hgh.eq]
    abel⟩

/-- The actual filler cocycle difference is the NEGATIVE of that original torus homology class. -/
theorem barCocycle_sub_swap (g h : G) (hgh : Commute g h) :
    barCocycle k G g h - barCocycle k G h g =
      -groupHomology.H2π (coefficients k G) (torusCycle k G g h hgh) := by
  change groupHomology.H2π (coefficients k G) (fillerCycle k G g h) -
      groupHomology.H2π (coefficients k G) (fillerCycle k G h g) = _
  rw [← map_sub, ← map_neg]
  apply congrArg (groupHomology.H2π (coefficients k G))
  apply Subtype.ext
  change (_ + _ - _ - _) - (_ + _ - _ - _) = -(single (g, h) 1 - single (h, g) 1)
  rw [hgh.eq]
  abel

/-- Any two actual bar-extension lifts with commuting images have this exact commutator. -/
theorem barCommutator (a b : BarExtension k G) (hab : Commute a.base b.base) :
    ⁅a, b⁆ =
      (⟨-groupHomology.H2π (coefficients k G) (torusCycle k G a.base b.base hab), 1⟩ :
        BarExtension k G) := by
  let c : BarExtension k G :=
    ⟨barCocycle k G a.base b.base - barCocycle k G b.base a.base, 1⟩
  have hmul : a * b = c * (b * a) := by
    apply BarExtension.ext
    · change a.homology + b.homology + barCocycle k G a.base b.base =
        (barCocycle k G a.base b.base - barCocycle k G b.base a.base) +
          (b.homology + a.homology + barCocycle k G b.base a.base) +
            barCocycle k G 1 (b.base * a.base)
      rw [barCocycle_one_left]
      abel
    · change a.base * b.base = 1 * (b.base * a.base)
      rw [one_mul]
      exact hab.eq
  have hcomm : ⁅a, b⁆ = c := by
    rw [commutatorElement_def, hmul]
    group
  exact hcomm.trans (congrArg (fun h => (⟨h, 1⟩ : BarExtension k G))
    (barCocycle_sub_swap k G a.base b.base hab))
end Bar
end groupHomology.IntegralBar

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Finsupp
namespace groupHomology.IntegralBar
open groupHomology.IntegralBar
variable (G : Type u) [Group G]

/-- An explicit original three-chain comparing the two simultaneous-inverse torus cycles. -/
def torusInverseFiller (g h : G) : G × G × G →₀ ULift.{u} ℤ :=
  single (g, h, h⁻¹) 1 - single (h, g, h⁻¹) 1 + single (h, h⁻¹, g) 1 +
    (single (h⁻¹, g, g⁻¹) 1 - single (g, h⁻¹, g⁻¹) 1 + single (g, g⁻¹, h⁻¹) 1) +
      single (1, 1, g) 1 + single (g, 1, 1) 1 +
        single (1, 1, h⁻¹) 1 + single (h⁻¹, 1, 1) 1

/-- Its genuine native boundary is the difference of the original two torus chains. -/
theorem torusInverseFiller_boundary (g h : G) (hgh : Commute g h) :
    groupHomology.d₃₂ (coefficients (ULift.{u} ℤ) G) (torusInverseFiller G g h) =
      (torusCycle (ULift.{u} ℤ) G g⁻¹ h⁻¹ hgh.inv_inv).val -
        (torusCycle (ULift.{u} ℤ) G g h hgh).val := by
  simp only [torusInverseFiller, map_add, map_sub]
  erw [dThree_single, dThree_single, dThree_single, dThree_single, dThree_single,
    dThree_single, dThree_single, dThree_single, dThree_single, dThree_single]
  simp only [mul_inv_cancel, mul_one, one_mul, hgh.eq,
    hgh.inv_right.eq, hgh.inv_inv.eq, torusCycle]
  abel

/-- Simultaneous inversion has positive orientation on the original bar torus homology class. -/
theorem torusCycle_class_inv_inv (g h : G) (hgh : Commute g h) :
    integerBarCycleClass G (torusCycle (ULift.{u} ℤ) G g⁻¹ h⁻¹ hgh.inv_inv) =
      integerBarCycleClass G (torusCycle (ULift.{u} ℤ) G g h hgh) := by
  apply (integerBarH2AddEquiv G).injective
  change (integerBarH2Iso G).hom _ = (integerBarH2Iso G).hom _
  rw [integerBarH2Iso_cycleClass, integerBarH2Iso_cycleClass]
  apply (groupHomology.H2π_eq_iff _ _).mpr
  exact ⟨torusInverseFiller G g h, torusInverseFiller_boundary G g h hgh⟩
end groupHomology.IntegralBar

end
