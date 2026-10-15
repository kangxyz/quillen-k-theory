/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1SupportOrder

/-! Exact tagged original full nodes and the fifty proved boundary identifications. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes.BassH1Merged
abbrev Input := Fin 63 ⊕ Fin 31 ⊕ Fin 31 ⊕ Fin 25 ⊕ Fin 25

def oldInput (i : Fin 63) : Input := .inl i
def firstInput (i : Fin 31) : Input := .inr (.inl i)
def middleInput (i : Fin 31) : Input := .inr (.inr (.inl i))
def plusInput (i : Fin 25) : Input := .inr (.inr (.inr (.inl i)))
def minusInput (i : Fin 25) : Input := .inr (.inr (.inr (.inr i)))

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every tagged input retains its original whole functor and actual common reference iso. -/
def inputNode : Input → BassOverlap.Node P u v :=
  Sum.elim (BassH0Merged.nodes P u v)
    (Sum.elim (BassH1References.firstNodes P u v)
      (Sum.elim (BassH1References.middleNodes P u v)
        (Sum.elim
          (BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b))
          (BassH1References.chartNodes P u v (underToLaurentInvert R)
            (laurentMinus_projection P b)))))

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair0_nodes (i : Fin 5) :
    inputNode P u v (firstInput (![26, 27, 28, 29, 30] i)) =
      inputNode P u v (middleInput (![2, 3, 11, 14, 22] i)) := by
  fin_cases i
  · exact BassH1Join.middle_path_nodes P u v 0
  · exact BassH1Join.middle_path_nodes P u v 1
  · exact BassH1Join.middle_path_nodes P u v 2
  · exact BassH1Join.middle_path_nodes P u v 3
  · exact BassH1Join.middle_path_nodes P u v 4

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair1_nodes (i : Fin 5) :
    inputNode P u v (firstInput (![5, 6, 13, 7, 28] i)) =
      inputNode P u v (plusInput (![2, 7, 12, 17, 22] i)) := by
  fin_cases i
  · exact BassH1Join.plus_column_nodes P u v 0
  · exact BassH1Join.plus_column_nodes P u v 1
  · exact BassH1Join.plus_column_nodes P u v 2
  · exact BassH1Join.plus_column_nodes P u v 3
  · exact BassH1Join.plus_column_nodes P u v 4

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair2_nodes (i : Fin 5) :
    inputNode P u v (firstInput (![16, 17, 24, 18, 30] i)) =
      inputNode P u v (minusInput (![2, 7, 12, 17, 22] i)) := by
  fin_cases i
  · exact BassH1Join.minus_column_nodes P u v 0
  · exact BassH1Join.minus_column_nodes P u v 1
  · exact BassH1Join.minus_column_nodes P u v 2
  · exact BassH1Join.minus_column_nodes P u v 3
  · exact BassH1Join.minus_column_nodes P u v 4

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair3_nodes (i : Fin 5) :
    inputNode P u v (middleInput (![9, 10, 11, 12, 13] i)) =
      inputNode P u v (plusInput (![20, 21, 22, 23, 24] i)) := by
  fin_cases i
  · exact BassH1Join.plus_row_nodes P u v 0
  · exact BassH1Join.plus_row_nodes P u v 1
  · exact BassH1Join.plus_row_nodes P u v 2
  · exact BassH1Join.plus_row_nodes P u v 3
  · exact BassH1Join.plus_row_nodes P u v 4

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair4_nodes (i : Fin 5) :
    inputNode P u v (middleInput (![20, 21, 22, 23, 24] i)) =
      inputNode P u v (minusInput (![20, 21, 22, 23, 24] i)) := by
  fin_cases i
  · exact BassH1Join.minus_row_nodes P u v 0
  · exact BassH1Join.minus_row_nodes P u v 1
  · exact BassH1Join.minus_row_nodes P u v 2
  · exact BassH1Join.minus_row_nodes P u v 3
  · exact BassH1Join.minus_row_nodes P u v 4

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair5_nodes (i : Fin 5) :
    inputNode P u v (firstInput (![2, 3, 11, 14, 22] i)) =
      inputNode P u v (oldInput (![18, 37, 40, 59, 62] i)) := by
  fin_cases i
  · exact BassH1Join.first_old62_bottom_nodes P u v 0
  · exact BassH1Join.first_old62_bottom_nodes P u v 1
  · exact BassH1Join.first_old62_bottom_nodes P u v 2
  · exact BassH1Join.first_old62_bottom_nodes P u v 3
  · exact BassH1Join.first_old62_bottom_nodes P u v 4

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair6_nodes (i : Fin 5) :
    inputNode P u v (firstInput (![9, 10, 11, 12, 13] i)) =
      inputNode P u v (oldInput (![26, 28, 40, 27, 34] i)) := by
  fin_cases i
  · exact BassH1Join.first_old62_plus_nodes P u v 0
  · exact BassH1Join.first_old62_plus_nodes P u v 1
  · exact BassH1Join.first_old62_plus_nodes P u v 2
  · exact BassH1Join.first_old62_plus_nodes P u v 3
  · exact BassH1Join.first_old62_plus_nodes P u v 4

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair7_nodes (i : Fin 5) :
    inputNode P u v (firstInput (![20, 21, 22, 23, 24] i)) =
      inputNode P u v (oldInput (![48, 50, 62, 49, 56] i)) := by
  fin_cases i
  · exact BassH1Join.first_old62_minus_nodes P u v 0
  · exact BassH1Join.first_old62_minus_nodes P u v 1
  · exact BassH1Join.first_old62_minus_nodes P u v 2
  · exact BassH1Join.first_old62_minus_nodes P u v 3
  · exact BassH1Join.first_old62_minus_nodes P u v 4

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair8_nodes (i : Fin 5) :
    inputNode P u v (plusInput (![10, 11, 12, 13, 14] i)) =
      inputNode P u v (oldInput (![30, 33, 34, 31, 32] i)) := by
  fin_cases i
  · exact BassH1Join.product_old62_plus_nodes P u v 0
  · exact BassH1Join.product_old62_plus_nodes P u v 1
  · exact BassH1Join.product_old62_plus_nodes P u v 2
  · exact BassH1Join.product_old62_plus_nodes P u v 3
  · exact BassH1Join.product_old62_plus_nodes P u v 4

/-- Literal full-node boundary identities from the checked original families. -/
theorem pair9_nodes (i : Fin 5) :
    inputNode P u v (minusInput (![10, 11, 12, 13, 14] i)) =
      inputNode P u v (oldInput (![52, 55, 56, 53, 54] i)) := by
  fin_cases i
  · exact BassH1Join.product_old62_minus_nodes P u v 0
  · exact BassH1Join.product_old62_minus_nodes P u v 1
  · exact BassH1Join.product_old62_minus_nodes P u v 2
  · exact BassH1Join.product_old62_minus_nodes P u v 3
  · exact BassH1Join.product_old62_minus_nodes P u v 4

end Quillen.PerfectComplexes.BassH1Merged
