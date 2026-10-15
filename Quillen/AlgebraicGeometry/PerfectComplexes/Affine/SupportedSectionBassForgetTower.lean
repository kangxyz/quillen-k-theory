/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionForgetSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescope
public import Quillen.KTheory.Bass.StrictUnderTransition
public import Quillen.Topology.Prespectrum.TelescopeDiagramMap

/-!
# Actual support inclusion through every Bass stage and its original telescope

The proved original seed square is iterated by the same Bass endofunctor. The actual
Under-restriction comparison retains the original ambient ring stages and their transitions.
The resulting telescope arrow uses the original stage maps at the identical cylinder height.
No equivalence of support inclusion or negative localization statement is asserted.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineSectionPrespectrumFunctor
  boundedFlatAffineSupportedSectionPrespectrumFunctor

/-- The unchanged iterated support inclusion enters the original ambient ring Bass stage. -/
def boundedFlatAffineSupportedSectionBassForget (n : ℕ) :
    boundedFlatAffineSupportedSectionBassDiagram j n ⟶
      Under.forget R ⋙ boundedFlatAffineSectionBassDiagram n :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) n).map
      (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j) ≫
    strictRingDiagramRestrictionIterateMap R n boundedFlatAffineSectionPrespectrumFunctor

/-- Stage zero retains the literal original support-forgetting prespectrum transformation. -/
theorem boundedFlatAffineSupportedSectionBassForget_zero :
    boundedFlatAffineSupportedSectionBassForget j 0 =
      boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j := by
  change boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The first finite support inclusion is the original parameter-looped comparison cone map. -/
theorem boundedFlatAffineSupportedSectionBassForget_one_app (a : Under R) :
    (boundedFlatAffineSupportedSectionBassForget j 1).app a =
      parameterLoopingMap (boundedFlatAffineSupportedSectionBassConeForget j a) := rfl

/-- Every original iterated transition commutes with these actual finite support inclusions. -/
theorem boundedFlatAffineSupportedSectionBassForget_transition (n : ℕ) :
    boundedFlatAffineSupportedSectionBassForget j n ≫
        Functor.whiskerLeft (Under.forget R) (boundedFlatAffineSectionBassTransition n) =
      boundedFlatAffineSupportedSectionBassTransition j n ≫
        boundedFlatAffineSupportedSectionBassForget j (n + 1) := by
  exact strictRingDiagramRestrictionIterateArrow_transition R n
    (boundedFlatAffineSupportedSectionBassSeed j) boundedFlatAffineSectionBassSeed
    (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j)
    (boundedFlatAffineSupportedSectionBassSeed_forget j)

/-- The actual quotient telescope map is induced by the unchanged finite support inclusions. -/
def boundedFlatAffineSupportedSectionBassTelescopeForget :
    boundedFlatAffineSupportedSectionBassTelescopeFunctor j ⟶
      Under.forget R ⋙ boundedFlatAffineSectionBassTelescopeFunctor :=
  Telescope.diagramMap (boundedFlatAffineSupportedSectionBassDiagram j)
    (fun n ↦ Under.forget R ⋙ boundedFlatAffineSectionBassDiagram n)
    (boundedFlatAffineSupportedSectionBassTransition j)
    (fun n ↦ Functor.whiskerLeft (Under.forget R) (boundedFlatAffineSectionBassTransition n))
    (boundedFlatAffineSupportedSectionBassForget j)
    (boundedFlatAffineSupportedSectionBassForget_transition j)

/-- The support-forgetting telescope map preserves the entire original cylinder coordinate. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeForget_cylinder
    (a : Under R) (k i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :
    ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a).map k
        (Telescope.cylinder (fun n ↦ (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
          (fun n ↦ (boundedFlatAffineSupportedSectionBassTransition j n).app a) k i (s, x)) =
      Telescope.cylinder (fun n ↦ (boundedFlatAffineSectionBassDiagram n).obj a.right)
        (fun n ↦ (boundedFlatAffineSectionBassTransition n).app a.right) k i
          (s, ((boundedFlatAffineSupportedSectionBassForget j i).app a).map k x) := rfl

/-- Every original stage inclusion commutes with the actual support-forgetting telescope map. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeInclusion_forget (n : ℕ) :
    boundedFlatAffineSupportedSectionBassTelescopeInclusion j n ≫
        boundedFlatAffineSupportedSectionBassTelescopeForget j =
      boundedFlatAffineSupportedSectionBassForget j n ≫
        Functor.whiskerLeft (Under.forget R) (boundedFlatAffineSectionBassTelescopeInclusion n) :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ n

/-- The original initial support inclusion commutes with the constructed telescope arrow. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeInitial_forget :
    boundedFlatAffineSupportedSectionBassTelescopeInitial j ≫
        boundedFlatAffineSupportedSectionBassTelescopeForget j =
      boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
        Functor.whiskerLeft (Under.forget R) boundedFlatAffineSectionBassTelescopeInitial :=
  boundedFlatAffineSupportedSectionBassTelescopeInclusion_forget j 0

end Quillen.PerfectComplexes
