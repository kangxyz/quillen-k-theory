/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassSeedChangeWeak
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescope
public import Quillen.Topology.Prespectrum.TelescopeDiagramMap

/-!
# Original ambient-to-relative-open maps through the Bass tower

The proved original seed square is iterated unchanged. Cancelling the actual Under-restriction
isomorphism gives a square against the existing ambient ring transitions, so their original
quotient telescopes receive an actual map with unchanged cylinder coordinates. No stability
of the change of weaknesses or replacement by a full-open endpoint is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Stage zero is the unchanged original fine-to-coarse section transformation. -/
theorem boundedFlatAffineSectionBassOpen_zero :
    boundedFlatAffineSectionBassOpen j 0 =
      boundedFlatAffineSectionOpenPrespectrumTransformation j := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The actual original ring-stage maps commute with the actual relative-open seed transitions. -/
theorem boundedFlatAffineSectionBassOpen_transition (n : ℕ) :
    boundedFlatAffineSectionBassOpen j n ≫ boundedFlatAffineSectionOpenBassTransition j n =
      Functor.whiskerLeft (Under.forget R) (boundedFlatAffineSectionBassTransition n) ≫
        boundedFlatAffineSectionBassOpen j (n + 1) := by
  apply (cancel_epi (boundedFlatAffineSectionBassRestrictionIso R n).hom).1
  rw [← Category.assoc, boundedFlatAffineSectionBassRestrictionIso_open]
  have ht :
      (strictDiagramIterate (laurentUnderSquareFunctor R) n).map
          (boundedFlatAffineSectionOpenPrespectrumTransformation j) ≫
          boundedFlatAffineSectionOpenBassTransition j n =
        strictDiagramTransition (laurentUnderSquareFunctor R)
            (boundedFlatAffineSectionBassUnderSeed R) n ≫
          (strictDiagramIterate (laurentUnderSquareFunctor R) (n + 1)).map
            (boundedFlatAffineSectionOpenPrespectrumTransformation j) :=
    (strictDiagramTransition_map (laurentUnderSquareFunctor R)
      (boundedFlatAffineSectionBassUnderSeed R) (boundedFlatAffineSectionOpenBassSeed j)
      (boundedFlatAffineSectionOpenPrespectrumTransformation j)
      (boundedFlatAffineSectionOpenBassSeed_changeWeak j) n).symm
  have hr :
      strictDiagramTransition (laurentUnderSquareFunctor R)
          (boundedFlatAffineSectionBassUnderSeed R) n ≫
          (boundedFlatAffineSectionBassRestrictionIso R (n + 1)).hom =
        (boundedFlatAffineSectionBassRestrictionIso R n).hom ≫
          Functor.whiskerLeft (Under.forget R) (boundedFlatAffineSectionBassTransition n) :=
    strictRingDiagramRestrictionIterateMap_transition R n boundedFlatAffineSectionBassSeed
  exact ht.trans
    ((congrArg (fun f => strictDiagramTransition (laurentUnderSquareFunctor R)
      (boundedFlatAffineSectionBassUnderSeed R) n ≫ f)
      (boundedFlatAffineSectionBassRestrictionIso_open j (n + 1)).symm).trans
      ((Category.assoc
        (strictDiagramTransition (laurentUnderSquareFunctor R)
          (boundedFlatAffineSectionBassUnderSeed R) n)
        (boundedFlatAffineSectionBassRestrictionIso R (n + 1)).hom
        (boundedFlatAffineSectionBassOpen j (n + 1))).symm.trans
        ((congrArg (fun f => f ≫ boundedFlatAffineSectionBassOpen j (n + 1)) hr).trans
          (Category.assoc _ _ _))))

/-- The actual original finite maps induce the unchanged quotient telescope map. -/
def boundedFlatAffineSectionBassTelescopeOpen :
    Under.forget R ⋙ boundedFlatAffineSectionBassTelescopeFunctor ⟶
      boundedFlatAffineSectionOpenBassTelescopeFunctor j :=
  Telescope.diagramMap (fun n ↦ Under.forget R ⋙ boundedFlatAffineSectionBassDiagram n)
    (boundedFlatAffineSectionOpenBassDiagram j)
    (fun n ↦ Functor.whiskerLeft (Under.forget R) (boundedFlatAffineSectionBassTransition n))
    (boundedFlatAffineSectionOpenBassTransition j)
    (boundedFlatAffineSectionBassOpen j) (boundedFlatAffineSectionBassOpen_transition j)

/-- Every original ambient cylinder keeps its height under the relative-open telescope map. -/
theorem boundedFlatAffineSectionBassTelescopeOpen_cylinder
    (a : Under R) (k i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj a.right).space k) :
    ((boundedFlatAffineSectionBassTelescopeOpen j).app a).map k
        (Telescope.cylinder (fun n ↦ (boundedFlatAffineSectionBassDiagram n).obj a.right)
          (fun n ↦ (boundedFlatAffineSectionBassTransition n).app a.right) k i (s, x)) =
      Telescope.cylinder (fun n ↦ (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
        (fun n ↦ (boundedFlatAffineSectionOpenBassTransition j n).app a) k i
          (s, ((boundedFlatAffineSectionBassOpen j i).app a).map k x) := rfl

/-- Every original stage inclusion commutes with the actual ambient-to-relative-open map. -/
theorem boundedFlatAffineSectionBassTelescopeInclusion_open (n : ℕ) :
    Functor.whiskerLeft (Under.forget R) (boundedFlatAffineSectionBassTelescopeInclusion n) ≫
        boundedFlatAffineSectionBassTelescopeOpen j =
      boundedFlatAffineSectionBassOpen j n ≫
        boundedFlatAffineSectionOpenBassTelescopeInclusion j n :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ n

/-- The original section map is retained on the exact initial telescope faces. -/
theorem boundedFlatAffineSectionBassTelescopeInitial_open :
    Functor.whiskerLeft (Under.forget R) boundedFlatAffineSectionBassTelescopeInitial ≫
        boundedFlatAffineSectionBassTelescopeOpen j =
      boundedFlatAffineSectionOpenPrespectrumTransformation j ≫
        boundedFlatAffineSectionOpenBassTelescopeInitial j := by
  exact (boundedFlatAffineSectionBassTelescopeInclusion_open j 0).trans
    (congrArg (fun f => f ≫ boundedFlatAffineSectionOpenBassTelescopeInclusion j 0)
      (boundedFlatAffineSectionBassOpen_zero j))

end Quillen.PerfectComplexes
