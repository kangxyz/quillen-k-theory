/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassSeed
public import Quillen.Topology.Prespectrum.TelescopeDiagram

/-!
# The actual supported Bass tower and telescope

Every transition is the existing Bass functor's iterated image of the constructed original
supported Laurent seed. The actual quotient telescope preserves each coefficient map and
entire cylinder coordinate. Its identity-algebra source remains the specified pullback of j.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual finite Bass diagram of the original supported Model prespectrum. -/
def boundedFlatAffineSupportedSectionBassDiagram (n : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (KTheory.Bass.strictDiagramIterate (laurentUnderSquareFunctor R) n).obj
    (boundedFlatAffineSupportedSectionPrespectrumFunctor j)

/-- The original constructed seed is iterated unchanged at every finite stage. -/
def boundedFlatAffineSupportedSectionBassTransition (n : ℕ) :
    boundedFlatAffineSupportedSectionBassDiagram j n ⟶
      boundedFlatAffineSupportedSectionBassDiagram j (n + 1) :=
  KTheory.Bass.strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatAffineSupportedSectionBassSeed j) n

/-- The actual reduced quotient telescope of the original supported Bass tower. -/
def boundedFlatAffineSupportedSectionBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatAffineSupportedSectionBassDiagram j)
    (boundedFlatAffineSupportedSectionBassTransition j)

/-- Original supported stages include at their actual cylinder faces. -/
def boundedFlatAffineSupportedSectionBassTelescopeInclusion (n : ℕ) :
    boundedFlatAffineSupportedSectionBassDiagram j n ⟶
      boundedFlatAffineSupportedSectionBassTelescopeFunctor j :=
  Telescope.diagramInclusion (boundedFlatAffineSupportedSectionBassDiagram j)
    (boundedFlatAffineSupportedSectionBassTransition j) n

/-- The original supported prespectrum enters at the actual stage-zero cylinder face. -/
def boundedFlatAffineSupportedSectionBassTelescopeInitial :
    boundedFlatAffineSupportedSectionPrespectrumFunctor j ⟶
      boundedFlatAffineSupportedSectionBassTelescopeFunctor j :=
  boundedFlatAffineSupportedSectionBassTelescopeInclusion j 0

/-- The original coefficient and telescope height are unchanged on every supported cylinder. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeFunctor_map_cylinder
    {a b : Under R} (f : a ⟶ b) (k i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :
    ((boundedFlatAffineSupportedSectionBassTelescopeFunctor j).map f).map k
        (Telescope.cylinder (fun n ↦ (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
          (fun n ↦ (boundedFlatAffineSupportedSectionBassTransition j n).app a) k i (s, x)) =
      Telescope.cylinder (fun n ↦ (boundedFlatAffineSupportedSectionBassDiagram j n).obj b)
        (fun n ↦ (boundedFlatAffineSupportedSectionBassTransition j n).app b) k i
          (s, ((boundedFlatAffineSupportedSectionBassDiagram j i).map f).map k x) := rfl

end Quillen.PerfectComplexes
