/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionOpenLaurentInterchange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassSeed
public import Quillen.KTheory.Bass.StrictDiagramHomotopy
public import Quillen.Topology.Prespectrum.StrictSquareSeedHomotopy

/-!
# The original supported seed commutes with the whole relative-open null track

The Bass image is the actual moving-span, cone and parameter-loop image of the original null
family. The genuine Laurent scalar square supplies the scalar input to original source-seed
naturality. Consequently the two unchanged seed/null composites agree as full continuous tracks,
with the original reversed null parameter and output-loop coordinate retained. No seed-relative
compatibility is supplied, and no relative-open endpoint is replaced by a full-open spectrum.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual Bass action on the original coefficient-natural support/open null family. -/
def boundedFlatAffineSupportedSectionOpenBassNullHomotopy (a : Under R) :
    Homotopy
      (((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j)).app a ≫
      ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatAffineSectionOpenPrespectrumTransformation j)).app a)
      (zeroHom
        (((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
          (boundedFlatAffineSupportedSectionPrespectrumFunctor j)).obj a)
        (((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
          (boundedFlatAffineSectionOpenPrespectrumFunctor j)).obj a)) :=
  strictDiagramNullHomotopy
    (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j)
    (boundedFlatAffineSectionOpenPrespectrumTransformation j)
    (fun a => boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a))
    (fun {a b} f => boundedFlatAffineSupportedSectionOpenNullHomotopy_coefficient
      (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f))
    (laurentUnderSquareFunctor R) a

/-- The unchanged original seeds commute with the full Bass null family, not just its endpoints. -/
theorem boundedFlatAffineSupportedSectionOpenBassNullHomotopy_seed_level
    (a : Under R) (n : ℕ) :
    ((boundedFlatAffineSupportedSectionOpenBassNullHomotopy j a).precomp
        (boundedFlatAffineSupportedSectionBassSeedMap j a)).level n =
      ((boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).postcomp
        (boundedFlatAffineSectionOpenBassSeedMap j a)).level n := by
  let H := diagramSquareMapHomotopy
    (η := boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
      boundedFlatAffineSectionOpenPrespectrumTransformation j)
    (θ := diagramZeroMap (boundedFlatAffineSupportedSectionPrespectrumFunctor j)
      (boundedFlatAffineSectionOpenPrespectrumFunctor j))
    (fun a => boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a))
    (fun {a b} f => boundedFlatAffineSupportedSectionOpenNullHomotopy_coefficient
      (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f))
    (laurentUnderSquare R a)
  let P := (boundedFlatAffineSupportedDiagramLaurentHomotopy j a).cast
    (boundedFlatAffineSupportedSectionBassSquare_source j a).symm
    (boundedFlatAffineSupportedSectionBassSquare_source j a).symm
  let Q := (boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).cast
    (boundedFlatAffineSectionOpenBassSquare_source j a).symm
    (boundedFlatAffineSectionOpenBassSquare_source j a).symm
  have hU : ∀ m r s x, H.target.level m (r, P.level m (s, x)) =
      Q.level m (s, H.source.level m (r, x)) := by
    intro m r s x
    exact boundedFlatAffineSupportedSectionOpenNullHomotopy_laurent_apply j a m r s x
  apply ContinuousMap.ext
  rintro ⟨r, x⟩
  apply Path.ext
  funext t
  exact H.sourceSeed_apply P Q hU n r t x

/-- Both original null and output-loop coordinates survive the same exact seed comparison. -/
theorem boundedFlatAffineSupportedSectionOpenBassNullHomotopy_seed_apply
    (a : Under R) (n : ℕ) (r t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
        ((boundedFlatAffineSupportedSectionOpenBassNullHomotopy j a).level n
          (r, (boundedFlatAffineSupportedSectionBassSeedMap j a).map n x)) t =
      Path.toContinuousMap
        ((boundedFlatAffineSectionOpenBassSeedMap j a).map n
          ((boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).level n
            (r, x))) t :=
  congrArg (fun H => Path.toContinuousMap (H (r, x)) t)
    (boundedFlatAffineSupportedSectionOpenBassNullHomotopy_seed_level j a n)

/-- Each original null time gives the actual strict coefficient-natural transformation. -/
def boundedFlatAffineSupportedSectionOpenNullTimeSlice (r : unitInterval) :
    boundedFlatAffineSupportedSectionPrespectrumFunctor j ⟶
      boundedFlatAffineSectionOpenPrespectrumFunctor j :=
  diagramHomotopyAt
    (η := boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
      boundedFlatAffineSectionOpenPrespectrumTransformation j)
    (θ := diagramZeroMap (boundedFlatAffineSupportedSectionPrespectrumFunctor j)
      (boundedFlatAffineSectionOpenPrespectrumFunctor j))
    (fun a => boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a))
    (fun {a b} f => boundedFlatAffineSupportedSectionOpenNullHomotopy_coefficient
      (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f)) r

/-- The original whole null square is a literal seed square at every original time slice. -/
theorem boundedFlatAffineSupportedSectionOpenNullTimeSlice_seed (r : unitInterval) :
    boundedFlatAffineSupportedSectionBassSeed j ≫
        (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSupportedSectionOpenNullTimeSlice j r) =
      boundedFlatAffineSupportedSectionOpenNullTimeSlice j r ≫
        boundedFlatAffineSectionOpenBassSeed j := by
  apply NatTrans.ext
  funext a
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  have ht := strictDiagramMapHomotopy_at
    (η := boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
      boundedFlatAffineSectionOpenPrespectrumTransformation j)
    (θ := diagramZeroMap (boundedFlatAffineSupportedSectionPrespectrumFunctor j)
      (boundedFlatAffineSectionOpenPrespectrumFunctor j))
    (fun a => boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a))
    (fun {a b} f => boundedFlatAffineSupportedSectionOpenNullHomotopy_coefficient
      (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f))
    (laurentUnderSquareFunctor R) a r
  change (((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
      (boundedFlatAffineSupportedSectionOpenNullTimeSlice j r)).app a).map n
      ((boundedFlatAffineSupportedSectionBassSeedMap j a).map n x) =
    (boundedFlatAffineSectionOpenBassSeedMap j a).map n
      ((boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).level n (r, x))
  exact (congrArg (fun f => f.map n
    ((boundedFlatAffineSupportedSectionBassSeedMap j a).map n x)) ht.symm).trans
    (congrArg (fun H => H (r, x))
      (boundedFlatAffineSupportedSectionOpenBassNullHomotopy_seed_level j a n))

end Quillen.PerfectComplexes
