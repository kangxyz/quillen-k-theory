/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgePrecompBeta
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeCone

/-! The ordinary unreduced cone map induced by the proved whole Laurent-reference square. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {U V : Model.{u + 1}} (A : U ⟶ V)
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => normalizedMap (polynomialProjection P a)
local notation "F" => reference P a E
local notation "F'" => reference P a (A ≫ E)
local notation "β" => beta P a E
local notation "β'" => beta P a (A ≫ E)

/-- The cone coordinate is unchanged and the complete baseline is retained under its full map. -/
def coneMap : FourEdgeTree.cone E J F β ⟶ FourEdgeTree.cone (A ≫ E) J F' β' :=
  descend β (SSet.stdSimplex.isTerminalObj₀.from _)
    (onReference A F ≫ FourEdgeTree.coneLaurent (A ≫ E) J F' β')
    (FourEdgeTree.coneTip (A ≫ E) J F' β')
    (map P a A E ▷ Δ[1] ≫ FourEdgeTree.coneCylinder (A ≫ E) J F' β')
    (by
      rw [SSet.ι₀_comp_assoc, FourEdgeTree.coneCylinder_zero, ← Category.assoc,
        beta_naturality, Category.assoc])
    (by
      rw [SSet.ι₁_comp_assoc, FourEdgeTree.coneCylinder_one, ← Category.assoc]
      exact congrArg (fun f ↦ f ≫ FourEdgeTree.coneTip (A ≫ E) J F' β')
        (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _))

/-- The entire Laurent summand is transported by the actual source-domain reference map. -/
@[reassoc] theorem coneMap_laurent :
    FourEdgeTree.coneLaurent E J F β ≫ coneMap P a A E =
      onReference A F ≫ FourEdgeTree.coneLaurent (A ≫ E) J F' β' :=
  descend_left _ _ _ _ _ _ _

/-- The terminal tip is preserved without quotienting any baseline point. -/
@[reassoc] theorem coneMap_tip :
    FourEdgeTree.coneTip E J F β ≫ coneMap P a A E =
      FourEdgeTree.coneTip (A ≫ E) J F' β' :=
  descend_right _ _ _ _ _ _ _

/-- Every cone cylinder retains the same independent original cone coordinate. -/
@[reassoc] theorem coneMap_cylinder :
    FourEdgeTree.coneCylinder E J F β ≫ coneMap P a A E =
      map P a A E ▷ Δ[1] ≫ FourEdgeTree.coneCylinder (A ≫ E) J F' β' :=
  descend_cylinder _ _ _ _ _ _ _

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
