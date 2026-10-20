/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenRelativeExtension
public import Mathlib.Topology.Homotopy.Path

/-! Construct and extend the six literal null-comparison faces, with arbitrary fixed source and
target. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
open Quillen.SimplexCubeExtension
variable {V W T : Model.{u}} (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε₀ ε₁ : G.functor ≅ (F ≫ J).functor)

/-- Two complete route surfaces share whole endpoint paths and retain their actual fixed
endpoints. -/
structure ChosenNullSurfaces where
  /-- The actual fixed source point. -/
  startPoint : space F J G ε₀ ε₁
  /-- The actual fixed terminal point. -/
  endPoint : space F J G ε₀ ε₁
  /-- The left route surface, with route time first and seed time second. -/
  left : C(I × I, space F J G ε₀ ε₁)
  /-- The right route surface, with route time first and seed time second. -/
  right : C(I × I, space F J G ε₀ ε₁)
  /-- The shared seed path at route time zero. -/
  start : C(I, space F J G ε₀ ε₁)
  /-- The shared seed path at route time one. -/
  finish : C(I, space F J G ε₀ ε₁)
  left_start (t : I) : left (0, t) = start t
  left_finish (t : I) : left (1, t) = finish t
  right_start (t : I) : right (0, t) = start t
  right_finish (t : I) : right (1, t) = finish t
  left_zero (s : I) : left (s, 0) = startPoint
  left_one (s : I) : left (s, 1) = endPoint
  right_zero (s : I) : right (s, 0) = startPoint
  right_one (s : I) : right (s, 1) = endPoint

namespace ChosenNullSurfaces
variable {F J G ε₀ ε₁} (S : ChosenNullSurfaces F J G ε₀ ε₁)

/-- The two route surfaces, fixed endpoint paths, and actual constant endpoint faces. -/
def faces (a : Fin 3 × Bool) : C(face a, space F J G ε₀ ε₁) :=
  if a.1 = 0 then
    ⟨fun z ↦ (if a.2 then S.right else S.left) (z.val.val 1, z.val.val 2), by
      exact (if a.2 then S.right else S.left).continuous.comp
        (((continuous_apply 1).comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_apply 2).comp (continuous_subtype_val.comp continuous_subtype_val)))⟩
  else if a.1 = 1 then
    ⟨fun z ↦ (if a.2 then S.finish else S.start) (z.val.val 2), by
      exact (if a.2 then S.finish else S.start).continuous.comp
        ((continuous_apply 2).comp (continuous_subtype_val.comp continuous_subtype_val))⟩
  else ContinuousMap.const _ (if a.2 then S.endPoint else S.startPoint)

/-- All twelve whole edges agree; endpoint-path tip values follow from the left surface. -/
theorem compatible : EdgeCompatible (fun a ↦ S.faces a) := by
  have hs0 : S.start 0 = S.startPoint :=
    (S.left_start 0).symm.trans (S.left_zero 0)
  have hs1 : S.start 1 = S.endPoint :=
    (S.left_start 1).symm.trans (S.left_one 0)
  have hf0 : S.finish 0 = S.startPoint :=
    (S.left_finish 0).symm.trans (S.left_zero 1)
  have hf1 : S.finish 1 = S.endPoint :=
    (S.left_finish 1).symm.trans (S.left_one 1)
  intro i j hij a b x hi hj
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    cases a <;> cases b <;>
      simp only [face, Set.mem_ofPred_eq, endpoint, Bool.false_eq_true, ↓reduceIte] at hj
  all_goals
    dsimp [faces]
    first
    | change x.val (1 : Fin 3) = _ at hj
    | change x.val (2 : Fin 3) = _ at hj
    rw [hj]
    first
    | exact S.left_start _
    | exact S.left_finish _
    | exact S.right_start _
    | exact S.right_finish _
    | exact S.left_zero _
    | exact S.left_one _
    | exact S.right_zero _
    | exact S.right_one _
    | exact hs0
    | exact hs1
    | exact hf0
    | exact hf1

/-- Glue the six literal null-comparison faces at their proved whole edges. -/
def boundaryMap : C(boundary, space F J G ε₀ ε₁) :=
  glueClosedCover face isClosed_face faces_cover S.faces
    (edgeCompatible_pairwise (fun a ↦ S.faces a) S.compatible)

/-- Extend in the actual contractible carrier, preserving every supplied boundary point. -/
def extension : C(Fin 3 → I, space F J G ε₀ ε₁) :=
  cubeExtension F J G ε₀ ε₁ 3 S.boundaryMap

/-- The extension restricts to every point of each supplied face. -/
theorem extension_face (a : Fin 3 × Bool) (z : face a) :
    S.extension z.val.val = S.faces a z := by
  exact (DFunLike.congr_fun
    (cubeExtension_restrict F J G ε₀ ε₁ 3 S.boundaryMap) z.val).trans
      (glueClosedCover_apply face isClosed_face faces_cover S.faces
        (edgeCompatible_pairwise (fun a ↦ S.faces a) S.compatible) a z)

/-- Product coordinates keep filling, comparison and path time separate. -/
def carrier : C((I × I) × I, space F J G ε₀ ε₁) :=
  S.extension.comp ⟨fun z ↦ RelativeBoundary.coordinates z.1.1 z.1.2 z.2, by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [RelativeBoundary.coordinates] <;> fun_prop⟩

/-- The entire first comparison face is unchanged. -/
theorem carrier_left (r s : I) : S.carrier ((0,r),s) = S.left (r,s) := by
  exact S.extension_face (0, false)
    (RelativeBoundary.onFace (0, false) (RelativeBoundary.coordinates 0 r s) rfl)

/-- The entire second comparison face is unchanged. -/
theorem carrier_right (r s : I) : S.carrier ((1,r),s) = S.right (r,s) := by
  exact S.extension_face (0, true)
    (RelativeBoundary.onFace (0, true) (RelativeBoundary.coordinates 1 r s) rfl)

/-- The original source path is fixed independently of filling time. -/
theorem carrier_start (q s : I) : S.carrier ((q,0),s) = S.start s := by
  exact S.extension_face (1, false)
    (RelativeBoundary.onFace (1, false) (RelativeBoundary.coordinates q 0 s) rfl)

/-- The original target path is fixed independently of filling time. -/
theorem carrier_finish (q s : I) : S.carrier ((q,1),s) = S.finish s := by
  exact S.extension_face (1, true)
    (RelativeBoundary.onFace (1, true) (RelativeBoundary.coordinates q 1 s) rfl)

/-- The actual source endpoint is fixed, without replacing it by a tip. -/
theorem carrier_zero (q r : I) : S.carrier ((q,r),0) = S.startPoint := by
  exact S.extension_face (2, false)
    (RelativeBoundary.onFace (2, false) (RelativeBoundary.coordinates q r 0) rfl)

/-- The actual terminal endpoint is fixed. -/
theorem carrier_one (q r : I) : S.carrier ((q,r),1) = S.endPoint := by
  exact S.extension_face (2, true)
    (RelativeBoundary.onFace (2, true) (RelativeBoundary.coordinates q r 1) rfl)

/-- Compact joint native evaluation retains all three parameters and the original input. -/
def joint (n : ℕ) : C(((I × I) × I) × (prespectrum V).space n, (nativeCone J).space n) :=
  compactNativeFamily F J G ε₀ ε₁ S.carrier n

/-- The point condition holds throughout the cube, not only at its boundary. -/
theorem joint_point (n : ℕ) (z : (I × I) × I) :
    S.joint n (z, (prespectrum V).point n) = (nativeCone J).point n :=
  nativeEval_point F J G ε₀ ε₁ n (S.carrier z)

/-- Structure time stays independent of every one of the three filling coordinates. -/
theorem joint_structure (n : ℕ) (z : (I × I) × I)
    (x : (prespectrum V).space n) (t : I) :
    S.joint (n+1) (z, (prespectrum V).structureMap n x t) =
      (nativeCone J).structureMap n (S.joint n (z,x)) t :=
  nativeEval_structure F J G ε₀ ε₁ n (S.carrier z) x t

end ChosenNullSurfaces

/-- Two literal path homotopies supply a six-face null boundary with their actual endpoints. -/
def chosenNullSurfaces {a b : space F J G ε₀ ε₁} {p q : Path a b}
    (L R : p.Homotopy q) : ChosenNullSurfaces F J G ε₀ ε₁ where
  startPoint := a
  endPoint := b
  left := L.toContinuousMap
  right := R.toContinuousMap
  start := p.toContinuousMap
  finish := q.toContinuousMap
  left_start := L.map_zero_left
  left_finish := L.map_one_left
  right_start := R.map_zero_left
  right_finish := R.map_one_left
  left_zero := L.source
  left_one := L.target
  right_zero := R.source
  right_one := R.target

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
