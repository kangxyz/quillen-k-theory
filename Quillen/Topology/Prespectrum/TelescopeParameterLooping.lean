/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.Telescope
public import Quillen.Topology.Prespectrum.ParameterLooping

/-!
# Actual telescope-to-parameter-loop comparison

The unchanged telescope cylinder moves whole original loops into the original telescope.
Its height, loop parameter and prespectrum structure time remain independent. Continuity is
proved into the actual compact-open path space before descending the original quotient.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The original cylinder moves an entire loop without changing either time coordinate. -/
def parameterLoopingInclusionTrack (i : ℕ) :
    Homotopy (parameterLoopingMap (inclusion E f i))
      (parameterLoopingMap (f i) ≫ parameterLoopingMap (inclusion E f (i + 1))) where
  level k := {
    toFun (z : unitInterval × Path ((E i).point k) ((E i).point k)) := {
      toFun t := cylinder E f k i (z.1, z.2 t)
      continuous_toFun := by fun_prop
      source' := by rw [z.2.source]; exact cylinder_point E f k i z.1
      target' := by rw [z.2.target]; exact cylinder_point E f k i z.1 }
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun z : (unitInterval × Path ((E i).point k) ((E i).point k)) ×
        unitInterval => cylinder E f k i (z.1.1, z.1.2 z.2))
      fun_prop }
  at_zero _k _x := by apply Path.ext; funext t; rfl
  at_one k x := by
    change Path ((E i).point k) ((E i).point k) at x
    apply Path.ext
    funext t
    exact cylinder_one E f k i (x t)
  at_point k s := by apply Path.ext; funext t; exact cylinder_point E f k i s
  comm _k _s _x _t := by apply Path.ext; funext r; rfl

/-- Descend the actual looped-stage cylinders into parameter looping of the original telescope. -/
def parameterLoopingComparison :
    prespectrum (fun i => parameterLooping (E i)) (fun i => parameterLoopingMap (f i)) ⟶
      parameterLooping (prespectrum E f) :=
  desc (fun i => parameterLooping (E i)) (fun i => parameterLoopingMap (f i))
    (fun i => parameterLoopingMap (inclusion E f i)) (parameterLoopingInclusionTrack E f)

/-- The original telescope height and independent loop time are retained literally. -/
theorem parameterLoopingComparison_cylinder (k i : ℕ) (s t : unitInterval)
    (x : Path ((E i).point k) ((E i).point k)) :
    Path.toContinuousMap ((parameterLoopingComparison E f).map k
      (cylinder (fun i => parameterLooping (E i)) (fun i => parameterLoopingMap (f i)) k i
        (s, x))) t = cylinder E f k i (s, x t) := rfl

/-- Every unchanged stage inclusion is sent to the actual loop of the original inclusion. -/
theorem inclusion_parameterLoopingComparison (i : ℕ) :
    inclusion (fun i => parameterLooping (E i)) (fun i => parameterLoopingMap (f i)) i ≫
        parameterLoopingComparison E f = parameterLoopingMap (inclusion E f i) :=
  inclusion_desc _ _ _ _ i

variable (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))

include ha in
/-- The exact looped original maps form the corresponding strict telescope map. -/
theorem parameterLoopingMapCompatibility (i : ℕ) :
    parameterLoopingMap (a i) ≫ parameterLoopingMap (g i) =
      parameterLoopingMap (f i) ≫ parameterLoopingMap (a (i + 1)) := by
  exact (parameterLoopingFunctor.map_comp (a i) (g i)).symm.trans
    ((congrArg parameterLoopingFunctor.map (ha i)).trans
      (parameterLoopingFunctor.map_comp (f i) (a (i + 1))))

/-- Naturality keeps the original strict tower map, without changing any cylinder track. -/
theorem parameterLoopingComparison_naturality :
    map (fun i => parameterLooping (E i)) (fun i => parameterLoopingMap (f i))
        (fun i => parameterLooping (F i)) (fun i => parameterLoopingMap (g i))
        (fun i => parameterLoopingMap (a i)) (parameterLoopingMapCompatibility E f F g a ha) ≫
        parameterLoopingComparison F g =
      parameterLoopingComparison E f ≫ parameterLoopingMap (map E f F g a ha) := by
  apply hom_ext
  intro k i s x
  apply Path.ext
  funext t
  rfl

end Quillen.LoopPrespectrum.Telescope
