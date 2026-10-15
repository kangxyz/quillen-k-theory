/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.CWComplex.Whitehead

/-! # QuillenTest of original-map classical CW Whitehead -/
@[expose] public section

open Topology

open Quillen.ClassicalCW

noncomputable section
open Set
open scoped unitInterval
universe u
namespace QuillenTest.ClassicalCWWhitehead

open Quillen
open ClassicalCW
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [T2Space X] [T2Space Y]
variable (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D]
variable (f : C(C, D)) (hf : IsWeakHomotopyEquivalence f)

/-- The forward map is exactly f, rather than a map with the same homotopy class. -/
theorem originalForwardMap :
    (homotopyEquivOfWeakHomotopyEquivalence C D f hf).toFun = f := rfl

/-- The inverse projects the actual constructed mapping-path section. -/
theorem actualInverseMap :
    (homotopyEquivOfWeakHomotopyEquivalence C D f hf).invFun =
      (MappingPath.source f).comp (mappingPathSection C D f hf) := rfl

omit [T2Space X] [CWComplex C] in
/-- The actual section lies over each original target point strictly. -/
theorem originalSectionEquation (y : D) :
    MappingPath.endpoint f (mappingPathSection C D f hf y) = y :=
  ContinuousMap.congr_fun (mappingPathSection_endpoint C D f hf) y

/-- Both endpoints of the original-source inverse homotopy are preserved. -/
theorem leftHomotopyEndpoints (x : C) :
    weakMapLeftHomotopy C D f hf (0, x) = weakMapInverse C D f hf (f x) ∧
      weakMapLeftHomotopy C D f hf (1, x) = x :=
  ⟨(weakMapLeftHomotopy C D f hf).map_zero_left x,
    (weakMapLeftHomotopy C D f hf).map_one_left x⟩

omit [T2Space X] [CWComplex C] in
/-- Both endpoints of the original-target inverse homotopy are preserved. -/
theorem rightHomotopyEndpoints (y : D) :
    weakMapRightHomotopy C D f hf (0, y) = f (weakMapInverse C D f hf y) ∧
      weakMapRightHomotopy C D f hf (1, y) = y :=
  ⟨(weakMapRightHomotopy C D f hf).map_zero_left y,
    (weakMapRightHomotopy C D f hf).map_one_left y⟩

omit [T2Space X] [CWComplex C] in
/-- The right homotopy keeps the full section path, not a reparametrized surrogate. -/
theorem originalStoredRightPath (t : I) (y : D) :
    weakMapRightHomotopy C D f hf (t, y) = (mappingPathSection C D f hf y).val.2 t := rfl

/-- The CW parameter lift retains the entire prescribed base homotopy. -/
theorem fullPrescribedHomotopy {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : CubicalSubdivision.BoundaryLifting p)
    (a₀ a₁ : C(C, E)) (H : (p.comp a₀).Homotopy (p.comp a₁)) (t : I) (x : C) :
    p (homotopyLift C p hp a₀ a₁ H (t, x)) = H (t, x) :=
  homotopyLift_project C p hp a₀ a₁ H t x

end QuillenTest.ClassicalCWWhitehead
