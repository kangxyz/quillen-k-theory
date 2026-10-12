/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassDiagram
public import Quillen.KTheory.Bass.StrictUnderTransition

/-!
# Actual finite relative-open Bass diagrams and the original ambient restriction transport

The honest coarse relative-open Model diagram is iterated by the same Under-R Bass functor.
The original equality-induced restriction isomorphism retains the actual ambient ring stages.
Its inverse followed by the iterated original change of weak equivalences gives the matching
ambient-to-relative-open arrow. No seed, transition or telescope comparison is asserted here.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes

/-- The original Under restriction equality as an isomorphism of the actual ambient diagrams. -/
def boundedFlatAffineSectionBassRestrictionIso (R : CommRingCat.{u}) (n : ℕ) :
    (strictDiagramIterate (laurentUnderSquareFunctor R) n).obj
        (Under.forget R ⋙ boundedFlatAffineSectionPrespectrumFunctor) ≅
      Under.forget R ⋙ boundedFlatAffineSectionBassDiagram n :=
  eqToIso (Functor.congr_obj (strictRingDiagramRestriction_comp_iterate R n)
    boundedFlatAffineSectionPrespectrumFunctor)

/-- The forward map is exactly the already specified original restriction transport. -/
theorem boundedFlatAffineSectionBassRestrictionIso_hom (R : CommRingCat.{u}) (n : ℕ) :
    (boundedFlatAffineSectionBassRestrictionIso R n).hom =
      strictRingDiagramRestrictionIterateMap R n boundedFlatAffineSectionPrespectrumFunctor := rfl

variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Each finite relative-open stage iterates the original coarse Model diagram unchanged. -/
def boundedFlatAffineSectionOpenBassDiagram (n : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) n).obj
    (boundedFlatAffineSectionOpenPrespectrumFunctor j)

/-- The matching open arrow retains the original ambient stages and original change-weakness map. -/
def boundedFlatAffineSectionBassOpen (n : ℕ) :
    Under.forget R ⋙ boundedFlatAffineSectionBassDiagram n ⟶
      boundedFlatAffineSectionOpenBassDiagram j n :=
  (boundedFlatAffineSectionBassRestrictionIso R n).inv ≫
    (strictDiagramIterate (laurentUnderSquareFunctor R) n).map
      (boundedFlatAffineSectionOpenPrespectrumTransformation j)

/-- The original restriction transport cancels against exactly its original inverse. -/
theorem boundedFlatAffineSectionBassRestrictionIso_open (n : ℕ) :
    (boundedFlatAffineSectionBassRestrictionIso R n).hom ≫
        boundedFlatAffineSectionBassOpen j n =
      (strictDiagramIterate (laurentUnderSquareFunctor R) n).map
        (boundedFlatAffineSectionOpenPrespectrumTransformation j) := by
  exact (boundedFlatAffineSectionBassRestrictionIso R n).hom_inv_id_assoc
    ((strictDiagramIterate (laurentUnderSquareFunctor R) n).map
      (boundedFlatAffineSectionOpenPrespectrumTransformation j))

end Quillen.PerfectComplexes
