/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Prespectrum.StableShift

/-!
Consumers retain the original coordinate sign, corrected indexing arrows, both colimit inclusion
directions, the negative-one and zero degree boundaries, the odd-stage factor and original
stable-map naturality.
-/
@[expose] public section

open CategoryTheory.Limits.SequentialSystem


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u v w
namespace QuillenTest.CoordinateSign

open Quillen

lemma actual_boundary_homotopy {N : Type v} [DecidableEq N]
    {X : Type u} [TopologicalSpace X] {x : X} (i j : N) (hij : i ≠ j)
    (p : GenLoop N X x) (s : unitInterval) (z : N → unitInterval) (hz : z ∈ Cube.boundary N) :
    transposeGenLoopHomotopy i j hij p (s,z) = x :=
  (transposeGenLoopHomotopy i j hij p).eq_fst s hz |>.trans
    ((transposeGenLoop i j hij p).property z hz)

lemma actual_swap_twice_class {N : Type v} [DecidableEq N] [Nonempty N]
    {X : Type u} [TopologicalSpace X] {x : X} (i j : N) (hij : i ≠ j)
    (p : GenLoop N X x) :
    (Quotient.mk' (transposeGenLoop i j hij (transposeGenLoop i j hij p)) : HomotopyGroup N X x) =
      Quotient.mk' p := by
  exact (transposeGenLoop_class i j hij _).trans
    ((congrArg (fun a : HomotopyGroup N X x ↦ a⁻¹) (transposeGenLoop_class i j hij p)).trans
      (inv_inv _))

lemma degree_zero_double_loop_sign {X : Type u} [TopologicalSpace X] {x : X}
    (f : C(Path (Path.refl x) (Path.refl x),Path (Path.refl x) (Path.refl x)))
    (hf : f (Path.refl (Path.refl x)) = Path.refl (Path.refl x))
    (hc : ∀ γ s t, f γ s t = γ t s)
    (a : HomotopyGroup.Pi 0 (Path (Path.refl x) (Path.refl x)) (Path.refl (Path.refl x))) :
    (loopShiftEquiv (x := x) 1).symm
      ((loopShiftEquiv (x := Path.refl x) 0).symm (homotopyGroupMap f hf a)) =
      ((loopShiftEquiv (x := x) 1).symm ((loopShiftEquiv (x := Path.refl x) 0).symm a))⁻¹ :=
  loopShiftEquiv_twice_coordinateSwap 0 f hf hc a

lemma original_tail_inclusions {C : Type u} [Category.{v} C]
    (F : ℕ ⥤ C) [HasColimit F] (t n : ℕ) :
    colimit.ι (shiftFunctor t ⋙ F) n ≫ (tailColimitIso F t).hom = colimit.ι F
      (t+n) ∧
    colimit.ι F (t+n) ≫ (tailColimitIso F t).inv = colimit.ι (shiftFunctor t ⋙
      F) n :=
  ⟨tailColimitIso_ι_hom F t n,tailColimitIso_ι_inv F t n⟩

lemma original_corrected_square {C : Type u} [Category.{v} C] [Preadditive C]
    {F G : ℕ ⥤ C} (e : ∀ n, F.obj n ≅ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ (e (n+1)).hom =
      -((e n).hom ≫ G.map (homOfLE (Nat.le_succ n)))) (m n : ℕ) (f : m ⟶ n) :
    F.map f ≫ (signCorrectionIso e h).hom.app n =
      (signCorrectionIso e h).hom.app m ≫ G.map f :=
  (signCorrectionIso e h).hom.naturality f

end QuillenTest.CoordinateSign

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace QuillenTest.StableShift

open Quillen
open Quillen.LoopPrespectrum

lemma original_negative_one_stage (E : LoopPrespectrum.{u}) :
    stableHomotopyι (parameterLooping E) (-1) 0 ≫ (parameterStableHomotopyIso E (-1)).hom =
      (parameterStableStageIso E (-1) 0).hom ≫ (shiftedStableReindexIso E (-1) 0).hom ≫
        stableHomotopyι E 0 1 := by
  simpa [parameterStableOffset] using parameterStableHomotopyIso_ι_hom E (-1) 0

lemma original_zero_stage (E : LoopPrespectrum.{u}) :
    stableHomotopyι (parameterLooping E) 0 0 ≫ (parameterStableHomotopyIso E 0).hom =
      (parameterStableStageIso E 0 0).hom ≫ (shiftedStableReindexIso E 0 0).hom ≫
        stableHomotopyι E 1 0 := by
  simpa [parameterStableOffset] using parameterStableHomotopyIso_ι_hom E 0 0

lemma original_odd_stage_sign (E : LoopPrespectrum.{u}) (d : ℤ) :
    stableHomotopyι (parameterLooping E) d 1 ≫ (parameterStableHomotopyIso E d).hom =
      (-(parameterStableStageIso E d 1).hom) ≫ (shiftedStableReindexIso E d 1).hom ≫
        stableHomotopyι E (d+1) (parameterStableOffset d+1) := by
  simpa only [alternatingIso_succ, alternatingIso_zero, Preadditive.neg_iso_hom] using
    parameterStableHomotopyIso_ι_hom E d 1

lemma original_stage_inverse (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    (alternatingIso n (parameterStableStageIso E d n)).hom ≫
      (shiftedStableReindexIso E d n).hom ≫ stableHomotopyι E (d+1) (parameterStableOffset d+n) ≫
        (parameterStableHomotopyIso E d).inv = stableHomotopyι (parameterLooping E) d n :=
  parameterStableHomotopyIso_ι_inv E d n

lemma original_map_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) :
    (stableHomotopyFunctor d).map (parameterLoopingMap f) ≫ (parameterStableHomotopyIso F d).hom =
      (parameterStableHomotopyIso E d).hom ≫ (stableHomotopyFunctor (d+1)).map f :=
  parameterStableHomotopyIso_naturality f d

lemma original_inverse_map_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) :
    (parameterStableHomotopyIso E d).inv ≫ (stableHomotopyFunctor d).map (parameterLoopingMap f) =
      (stableHomotopyFunctor (d+1)).map f ≫ (parameterStableHomotopyIso F d).inv :=
  parameterStableHomotopyIso_inv_naturality f d

end QuillenTest.StableShift
