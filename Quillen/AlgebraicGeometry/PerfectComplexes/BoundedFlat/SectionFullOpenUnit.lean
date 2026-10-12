/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionFullOpenRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionUnitAction

/-!
# The actual scalar action under full-open restriction

The actual source scalar action is sent to the original inclusion-restricted target unit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSectionUnitIso boundedFlatPerfectGlobalUnitIso
  boundedFlatAffineFullOpenRestriction boundedFlatAffineSectionFullOpenRestriction

omit [IsOpenImmersion j] in
/-- The actual section action is sent to the precise original target unit. -/
theorem boundedFlatAffineSectionFullOpenRestriction_unit (a : Under R)
    (r : (Γ(Spec a.right, ⊤))ˣ) (s : BoundedFlatAffineSections a.right) :
    (boundedFlatAffineSectionFullOpenRestriction j a).map
        ((boundedFlatAffineSectionUnitIso a.right r).hom.app s) =
      (boundedFlatPerfectGlobalUnitIso (openSpace j a)
        (boundedFlatAffineFullOpenUnit j a r)).hom.app
          ((boundedFlatAffineSectionFullOpenRestriction j a).obj s) := by
  unfold boundedFlatAffineSectionFullOpenRestriction
  have h := congrArg ((boundedFlatAffineFullOpenRestriction j a).map)
    (boundedFlatAffineOriginalEvaluation_map_sectionUnitIso_hom a.right r s)
  change (boundedFlatAffineFullOpenRestriction j a).map
    ((boundedFlatAffineOriginalEvaluation a.right).map
      ((boundedFlatAffineSectionUnitIso a.right r).hom.app s)) = _
  exact h.trans (boundedFlatAffineFullOpenRestriction_unit j a r
    ((boundedFlatAffineOriginalEvaluation a.right).obj s))


end Quillen.PerfectComplexes
