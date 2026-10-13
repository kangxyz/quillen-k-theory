/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionFullOpenUnit

/-! The original ambient scalar survives actual full-open evaluation and coefficient change. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Scheme.AffineOpenPair Quillen.PerfectComplexes
universe u
namespace QuillenTest.FullOpenSectionUnit

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original full-open evaluation retains the entire inclusion-restricted unit automorphism. -/
theorem originalUnit_evaluation (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ)
    (s : BoundedFlatAffineFullOpenSections j a) :
    (boundedFlatAffineFullOpenOriginalEvaluation j a).mapIso
        ((boundedFlatAffineFullOpenSectionUnitIso j a
          (boundedFlatAffineFullOpenUnit j a r)).app s) =
      (boundedFlatPerfectGlobalUnitIso (openSpace j a)
        (boundedFlatAffineFullOpenUnit j a r)).app
          ((boundedFlatAffineFullOpenOriginalEvaluation j a).obj s) :=
  boundedFlatAffineFullOpenOriginalEvaluation_mapIso_sectionUnitIso j a
    (boundedFlatAffineFullOpenUnit j a r) s

/-- Every original coefficient arrow preserves the forward ambient unit after restriction. -/
theorem originalUnit_coefficient {a b : Under R} (f : a ⟶ b) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Functor.whiskerRight
        (boundedFlatAffineFullOpenSectionUnitIso j a (boundedFlatAffineFullOpenUnit j a r)).hom
        (boundedFlatAffineFullOpenSectionsMap j f) =
      Functor.whiskerLeft (boundedFlatAffineFullOpenSectionsMap j f)
        (boundedFlatAffineFullOpenSectionUnitIso j b (boundedFlatAffineFullOpenUnit j b
          (Units.map (Spec.map f.right).appTop.hom.toMonoidHom r))).hom :=
  boundedFlatAffineFullOpenSectionUnitIso_original_coefficient_hom j f r

/-- The forward section component multiplies every original complex term by the unit itself. -/
theorem originalUnit_hom_terms (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ)
    (s : BoundedFlatAffineFullOpenSections j a) (n : ℤ) :
    ((boundedFlatPerfect (openSpace j a)).ι.map
      ((boundedFlatAffineFullOpenOriginalEvaluation j a).map
        ((boundedFlatAffineFullOpenSectionUnitIso j a
          (boundedFlatAffineFullOpenUnit j a r)).hom.app s))).f n =
      (Quillen.SchemeSheaf.globalScalar (openSpace j a)
        (↑(boundedFlatAffineFullOpenUnit j a r))).app
          (((boundedFlatAffineFullOpenOriginalEvaluation j a).obj s).obj.X n) := by
  rw [boundedFlatAffineFullOpenOriginalEvaluation_map_sectionUnitIso_hom,
    boundedFlatPerfectGlobalUnitIso_hom_original, complexGlobalUnitIso_original_terms]
  dsimp only [Quillen.SchemeSheaf.globalUnitIso]

end QuillenTest.FullOpenSectionUnit
