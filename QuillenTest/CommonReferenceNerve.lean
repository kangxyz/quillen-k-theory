/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerve

/-! Exact original diamond-family consumers of the common-reference nerve factorization. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace QuillenTest.CommonReferenceNerve
variable {V W : Model.{u}} {F₀ F₁ F₂ F₃ : V ⟶ W}
  (η : F₀.functor ≅ F₁.functor) (θ : F₁.functor ≅ F₃.functor)
  (η' : F₀.functor ≅ F₂.functor)

/-- The original diamond's exact nodes and reference isomorphisms. -/
def diamondNodes : Fin 4 → CommonReferenceNerve.Node F₀ := fun i ↦
  ⟨![F₀, F₁, F₂, F₃] i,
    (show ∀ j : Fin 4, F₀.functor ≅ (![F₀, F₁, F₂, F₃] j).functor from
      Fin.cases (Iso.refl _) (Fin.cases η (Fin.cases η'
        (Fin.cases (η ≪≫ θ) (fun j ↦ Fin.elim0 j))))) i⟩

/-- The whole existing geometric diamond is unchanged at every original level and parameter. -/
theorem original_diamond_family (n : ℕ) (z : StdSimplex ℝ (Fin 4))
    (x : (prespectrum V).space n) :
    CommonReferenceNerve.prespectrumFamily F₀ (diamondNodes η θ η') n (z, x) =
      prespectrumSimplexFamily (ModelSimplex.diamond η θ η') n (z, x) :=
  congrArg (fun f ↦ f (z, x))
    (CommonReferenceNerve.prespectrumFamily_eq F₀ (diamondNodes η θ η') n)

/-- The original level-zero loop time is independent of the whole diamond parameter. -/
theorem original_diamond_level_zero (z : StdSimplex ℝ (Fin 4))
    (x : Path (stagePoint 0 V) (stagePoint 0 V)) (t : unitInterval) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      CommonReferenceNerve.prespectrumFamily F₀ (diamondNodes η θ η') 0 (z, x)) t =
      stageSimplexBarycentric (ModelSimplex.diamond η θ η') 0 (z, x t) := by
  rw [original_diamond_family]
  exact prespectrumSimplexFamily_zero_apply _ z x t

/-- The original structure time is retained at every level of the exact diamond. -/
theorem original_diamond_structure_time (n : ℕ) (z : StdSimplex ℝ (Fin 4))
    (x : (prespectrum V).space n) (t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily F₀ (diamondNodes η θ η') (n + 1)
        (z, (prespectrum V).structureMap n x t) =
      (prespectrum W).structureMap n
        (prespectrumSimplexFamily (ModelSimplex.diamond η θ η') n (z, x)) t := by
  rw [original_diamond_family]
  exact prespectrumSimplexFamily_structure _ n z x t

end QuillenTest.CommonReferenceNerve
