/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenScalarInterchange
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenNullCoefficient
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionDiagramLaurent
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenDiagramLaurent
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIdentityAction

/-!
# The original supported Laurent and relative-open null tracks commute

The two original coefficient actions are their literal target identity actions after the
unchanged Laurent coefficient maps. The proved whole scalar square and the actual coefficient
naturality of the reversed null track therefore give its exact Laurent square. Both times,
the fixed-open pullback, and the original target Laurent unit remain explicit.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The specified original Laurent loop commutes with the same reversed section null track at
both independent original parameters. No interchange or seed-compatibility premise is supplied. -/
theorem boundedFlatAffineSupportedSectionOpenNullHomotopy_laurent_apply
    (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSupportedSectionOpenNullHomotopy
        (inclusion j ((laurentUnderFunctor R).obj a))).level n
        (s, (boundedFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n
        (t, (boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).level n
          (s, x)) := by
  have hS := prespectrumIsoHomotopy_onFunctor_apply
    ((boundedFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineSupportedSectionUnitIso
      (inclusion j ((laurentUnderFunctor R).obj a)) (laurentGlobalUnit a.right)) n t x
  have hC := prespectrumIsoHomotopy_onFunctor_apply
    ((boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineSectionLaurentUnitIso a.right) n t
    ((boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).level n (s, x))
  have hN := boundedFlatAffineSupportedSectionOpenNullHomotopy_coefficient
    (inclusion j a) (inclusion j ((laurentUnderFunctor R).obj a))
    ((laurentUnderCoefficient R).app a).right
    (openMap j ((laurentUnderCoefficient R).app a))
    (openMap_inclusion j ((laurentUnderCoefficient R).app a)) n s x
  have hU := boundedFlatAffineSupportedSectionOpenNullHomotopy_unit_apply
    (inclusion j ((laurentUnderFunctor R).obj a)) (laurentGlobalUnit a.right) n s t
    ((prespectrumMap ((boundedFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))).map n x)
  exact (congrArg (fun y => (boundedFlatAffineSupportedSectionOpenNullHomotopy
    (inclusion j ((laurentUnderFunctor R).obj a))).level n (s, y)) hS).trans
    (hU.trans ((congrArg (fun y => (prespectrumIsoHomotopy
      (𝟙 (boundedFlatAffineSectionOpenModel (inclusion j ((laurentUnderFunctor R).obj a))))
      (boundedFlatAffineSectionLaurentUnitIso a.right)).level n (t, y)) hN.symm).trans hC.symm))

end Quillen.PerfectComplexes
