/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.SConstruction.WeakGridBasedHomotopy
public import Quillen.Waldhausen.Additivity.RealizationHomotopy
public import Quillen.Topology.HomotopyGroups.Equivalence

/-! # The actual based forward isomorphism of ordinary outer subdivision

Only the forward endpoint is required to preserve the displayed zero vertex.
The homotopy-group isomorphism is derived from the genuine unbased realization
equivalence, without assuming that its inverse or inverse homotopies are based.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u v

namespace Quillen.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- The original constant-zero grid in degrees (delta[0], [0]). -/
def subdivisionZeroVertex :
    (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)) _⦋0⦌ :=
  zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (OrdinalSubdivision.δ.obj ⦋0⦌)) (op ⦋0⦌)

/-- Its actual realization point, with no choice of path. -/
def subdivisionBasepoint :
    |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)| :=
  realizationPoint (subdivisionZeroVertex V)

/-- The original first-half endpoint takes the stated zero grid to the original zero grid. -/
@[simp]
theorem horizontalEndpoint_zeroVertex :
    (TheoremA.diagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))).app
      (op ⦋0⦌) (subdivisionZeroVertex V) = diagonalZeroVertex V := rfl

/-- The prescribed actual endpoint map preserves the displayed realization points. -/
@[simp]
theorem horizontalEndpoint_basepoint :
    realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))
      (subdivisionBasepoint V) = realizationPoint (diagonalZeroVertex V) := by
  rw [subdivisionBasepoint]
  exact realizationPoint_naturality _ _

/-- Ordinary outer subdivision induces an isomorphism by its actual based
forward map in every positive homotopy degree. -/
def subdivisionPiEquiv (n : ℕ) :
    HomotopyGroup.Pi (n + 1)
        |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
        (subdivisionBasepoint V) ≃*
      HomotopyGroup.Pi (n + 1) |TheoremA.diagonalSSet (bisimplicialSSet V)|
        (realizationPoint (diagonalZeroVertex V)) :=
  homotopyEquivPiEquiv (OrdinalSubdivision.horizontalRealizationHomotopyEquiv (bisimplicialSSet V))
    (horizontalEndpoint_basepoint V) n

/-- The forward homomorphism is exactly postcomposition by the original endpoint. -/
@[simp] theorem subdivisionPiEquiv_coe (n : ℕ) :
    (↑(subdivisionPiEquiv V n) : HomotopyGroup.Pi (n + 1)
        |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
        (subdivisionBasepoint V) →* HomotopyGroup.Pi (n + 1) |TheoremA.diagonalSSet
            (bisimplicialSSet V)|
        (realizationPoint (diagonalZeroVertex V))) =
      piMap n (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
        (horizontalEndpoint_basepoint V) := rfl


/-- Surjectivity of this original forward map is enough to cancel based precomposition. -/
theorem subdivisionPiMap_surjective (n : ℕ) :
    Function.Surjective (piMap n
      (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
      (horizontalEndpoint_basepoint V)) :=
  (subdivisionPiEquiv V n).surjective

end Quillen.Waldhausen.Additivity
