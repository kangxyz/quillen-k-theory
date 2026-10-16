/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.StableHomotopy

/-! Semantic consumers of the original stable transition, colimit and K-map normalizations. -/
@[expose] public section

open CategoryTheory.Limits.SequentialSystem

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Quillen Quillen.LoopPrespectrum
universe u v w
namespace QuillenTest.StableHomotopyGroups

open Quillen

/-- Every actual stable stage has the requested integer degree. -/
theorem degree_bookkeeping (d : ℤ) (n : ℕ) :
    (d.toNat+n+2 : ℤ) - ((-d).toNat+n+2) = d := stableStage_degree d n

/-- The transition retains the whole original structure homomorphism and inverse shift. -/
theorem original_transition (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ)
    (a : stableStage E d n) :
    stableTransition E d n a =
      (loopShiftMulEquiv (x := E.point (((-d).toNat+n+2)+1)) (d.toNat+n+1)).symm
        (homotopyGroupMap (E.structureMap ((-d).toNat+n+2)) (E.map_point ((-d).toNat+n+2)) a) := rfl

/-- The actual stable colimit maps compose on the original stage inclusions. -/
theorem colimit_composition {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) (g : F ⟶ G)
    (d : ℤ) (n : ℕ) :
    stableHomotopyι E d n ≫ (stableHomotopyFunctor d).map f ≫ (stableHomotopyFunctor d).map g =
      (stableSystemMap (f ≫ g) d).app n ≫ stableHomotopyι G d n := by
  rw [← Functor.map_comp, stableHomotopyι_naturality]

/-- A genuine coherent homotopy identifies the original colimit maps in every integer degree. -/
theorem whole_homotopy {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : LoopPrespectrum.Homotopy f g) (d : ℤ) :
    (stableHomotopyFunctor d).map f = (stableHomotopyFunctor d).map g := H.stableHomotopyMap_eq d

/-- The generic comparison uses the actual inverses, with independent categorical universes. -/
theorem original_sequential_comparison {C : Type u} [Category.{v} C] (F : ℕ ⥤ C)
    [HasColimit F] [∀ n, IsIso (F.map (homOfLE (Nat.le_succ n)))] (n : ℕ) :
    colimit.ι F n ≫ (colimitIsoOfSucc F).hom =
      (toZeroIso (fun n ↦ F.map (homOfLE (Nat.le_succ n))) n).hom :=
  ι_colimitIsoOfSucc_hom F n

/-- Both inverse orders use the literal stage-zero inclusion, even in degree minus one. -/
theorem negative_stage_inverse (E : LoopPrespectrum.{u}) (hE : E.IsOmega) :
    stableHomotopyι E (-1) 0 ≫ (stableHomotopyStageZeroIso E hE (-1)).hom = 𝟙 _ ∧
      (stableHomotopyStageZeroIso E hE (-1)).hom ≫ stableHomotopyι E (-1) 0 = 𝟙 _ := by
  constructor
  · exact stableHomotopyι_zero_hom E hE (-1)
  · rw [← stableHomotopyStageZeroIso_inv E hE (-1), Iso.hom_inv_id]

/-- The same original inverse is retained in stable degree zero. -/
theorem zero_stage_inverse (E : LoopPrespectrum.{u}) (hE : E.IsOmega) :
    (stableHomotopyStageZeroIso E hE 0).inv = stableHomotopyι E 0 0 :=
  stableHomotopyStageZeroIso_inv E hE 0

open Quillen.Waldhausen.IteratedS

/-- Original K-zero is identified as a group, retaining its actual multiplication. -/
theorem original_Kzero_group {C : Type u} [Category.{v} C] (W : Structure C) (a b : W.K 0) :
    originalKStableEquiv W 0 (Additive.ofMul (a*b)) =
      originalKStableEquiv W 0 (Additive.ofMul a) + originalKStableEquiv W 0 (Additive.ofMul b) :=
  (originalKStableEquiv W 0).map_add _ _

/-- Every original K-group comparison has both actual inverse laws. -/
theorem original_K_inverse {C : Type u} [Category.{v} C] (W : Structure C) (n : ℕ)
    (a : Additive (W.K n)) (b : stableHomotopyGroup (originalPrespectrum W) (n : ℤ)) :
    (originalKStableEquiv W n).symm (originalKStableEquiv W n a) = a ∧
      originalKStableEquiv W n ((originalKStableEquiv W n).symm b) = b :=
  ⟨(originalKStableEquiv W n).symm_apply_apply a, (originalKStableEquiv W n).apply_symm_apply b⟩

/-- Original exact K-maps, including K-zero, agree with the actual stable colimit maps. -/
theorem original_K_map {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    (W : Structure C) (V : Structure D) {F : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F) (h₀ : F.obj W.zero = V.zero)
    (n : ℕ) (a : W.K n) :
    originalKStableEquiv V n (Additive.ofMul (KMap hF n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (originalPrespectrumMap W V hF h₀)
        (originalKStableEquiv W n (Additive.ofMul a)) :=
  originalKStableEquiv_naturality W V hF h₀ n a

/-- The comparison uses exactly the displayed original stage inclusion. -/
theorem original_K_inclusion {C : Type u} [Category.{v} C] (W : Structure C) (n : ℕ)
    (a : Additive (W.K n)) :
    originalKStableEquiv W n a =
      stableHomotopyι (originalPrespectrum W) (n : ℤ) 0 (originalKStableStageEquiv W n a) :=
  originalKStableEquiv_apply W n a

/-- The constructed connective spectrum has zero negative stable elements. -/
theorem original_negative_zero {C : Type u} [Category.{v} C] (W : Structure C)
    (d : ℤ) (hd : d < 0) (a : stableHomotopyGroup (originalPrespectrum W) d) : a = 0 := by
  let := originalStableHomotopyGroup_neg_subsingleton W d hd
  exact Subsingleton.elim _ _

end QuillenTest.StableHomotopyGroups
