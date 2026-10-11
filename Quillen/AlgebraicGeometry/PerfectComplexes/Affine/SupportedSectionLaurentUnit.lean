/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionUnitHomotopy
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentUnit

/-!
# The original Laurent coordinate on actual supported sections

Support restriction retains the full original forward and inverse Laurent section automorphisms.
The original target global-unit coordinate and inverse-coordinate formulas remain available from
the ambient owner. The direct, expanded equality on evaluated complex terms remains a separate
uncompleted proof. The original scalar coefficient equation supplies the supported action square,
and each specified original Laurent open-pair square has its genuine realized self-homotopy.
The fixed-open coefficient diagram is supplied by its separate diagram owner; constructing its
actual Bass seed remains separate.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.PolynomialBaseChange
open Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
attribute [local irreducible] boundedFlatAffineOriginalEvaluation boundedFlatAffineEvaluationAt
  boundedFlatPerfectGlobalUnitIso

/-- The supported action is the original Laurent global unit, with no replacement scalar. -/
def boundedFlatAffineSupportedSectionLaurentUnitIso
    (j : U ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion j] :
    𝟭 (BoundedFlatAffineSupportedSections j) ≅ 𝟭 (BoundedFlatAffineSupportedSections j) :=
  boundedFlatAffineSupportedSectionUnitIso j (laurentGlobalUnit R)

/-- Forgetting support retains the original forward Laurent automorphism on the entire section. -/
theorem boundedFlatAffineSupportedSectionLaurentUnitIso_hom_original
    (j : U ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion j]
    (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionLaurentUnitIso j).hom.app s).hom =
      (boundedFlatAffineSectionLaurentUnitIso R).hom.app s.obj :=
  boundedFlatAffineSupportedSectionUnitIso_hom j (laurentGlobalUnit R) s

/-- Forgetting support also retains the unchanged inverse Laurent automorphism. -/
theorem boundedFlatAffineSupportedSectionLaurentUnitIso_inv_original
    (j : U ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion j]
    (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionLaurentUnitIso j).inv.app s).hom =
      (boundedFlatAffineSectionLaurentUnitIso R).inv.app s.obj :=
  boundedFlatAffineSupportedSectionUnitIso_inv j (laurentGlobalUnit R) s

/-- Original Laurent coefficient maps preserve the exact supported target-unit action. -/
theorem boundedFlatAffineSupportedSectionLaurentUnitIso_coefficient
    (j : U ⟶ Spec (.of (LaurentPolynomial R)))
    (j' : V ⟶ Spec (.of (LaurentPolynomial S))) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map (laurentMap f)) :
    Functor.whiskerRight (boundedFlatAffineSupportedSectionLaurentUnitIso j).hom
        (boundedFlatAffineSupportedSectionsMap j j' (laurentMap f) l h) =
      Functor.whiskerLeft (boundedFlatAffineSupportedSectionsMap j j' (laurentMap f) l h)
        (boundedFlatAffineSupportedSectionLaurentUnitIso j').hom := by
  simpa only [boundedFlatAffineSupportedSectionLaurentUnitIso, laurentGlobalUnit_coefficient] using
    boundedFlatAffineSupportedSectionUnitIso_coefficient_hom
      j j' (laurentMap f) l h (laurentGlobalUnit R)

/-- The unchanged Laurent coordinate acts on the actual specified supported restriction map. -/
def boundedFlatAffineSupportedSectionLaurentUnitHomotopy
    (j : U ⟶ Spec R) (jL : V ⟶ Spec (.of (LaurentPolynomial R)))
    [IsOpenImmersion j] [IsOpenImmersion jL] (l : V ⟶ U)
    (h : l ≫ j = jL ≫ Spec.map (laurentCoefficient R)) :
    LoopPrespectrum.Homotopy
      (boundedFlatAffineSupportedSectionPrespectrumMap j jL (laurentCoefficient R) l h)
      (boundedFlatAffineSupportedSectionPrespectrumMap j jL (laurentCoefficient R) l h) :=
  boundedFlatAffineSupportedSectionUnitHomotopy
    j jL (laurentCoefficient R) l h (laurentGlobalUnit R)

end Quillen.PerfectComplexes
