/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.Looping
public import Quillen.Topology.Prespectrum.StableEquivalence
public import Quillen.Aglib.CategoryTheory.Limits.Shapes.SequentialSystem.Interleaving

/-!
# The original loop-tail stabilization preserves stable groups

The unchanged structure maps give the existing strict map `E ⟶ looping (tail E)`. The actual
loop-degree shift returns each target stable stage to the next original source stage. Both
successor-interleaving identities are proved, so the original stabilization map is a stable
equivalence in every integer degree without any point-set, Omega, or connectivity assumptions.

This uses the existing `looping` structure, not the transposed `parameterLooping` construction.
It does not assert that iterated loop-tail replacement is an Omega spectrum or that it preserves
mapping cones; those require further approximation and excision theorems.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

namespace Quillen.LoopPrespectrum

variable (E : LoopPrespectrum.{u}) (d : ℤ)

/-- The genuine loop shift returns the stabilized stage to the next original stable stage. -/
def stabilizationStageReturn (n : ℕ) :
    (stableSystem (looping (tail E)) d).obj n ⟶ (stableSystem E d).obj (n + 1) :=
  AddCommGrpCat.ofHom (loopShiftMulEquiv (x := E.point (((-d).toNat + n + 2) + 1))
    (d.toNat + n + 1)).symm.toAdditive.toAddMonoidHom

/-- The original structure map followed by the return map is the original stable successor. -/
theorem stabilizationStageMap_return (n : ℕ) :
    (stableSystemMap (stabilizationMap E) d).app n ≫ stabilizationStageReturn E d n =
      (stableSystem E d).map (homOfLE (Nat.le_succ n)) := by
  simp only [stableSystem, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
  rfl

/-- Returning and applying the next original structure map gives the loop-tail stable successor. -/
theorem stabilizationStageReturn_map (n : ℕ) :
    stabilizationStageReturn E d n ≫ (stableSystemMap (stabilizationMap E) d).app (n + 1) =
      (stableSystem (looping (tail E)) d).map (homOfLE (Nat.le_succ n)) := by
  simp only [stableSystem, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
  apply AddCommGrpCat.ext
  intro a
  change Additive.ofMul (piMap (d.toNat + n + 2)
      (E.structureMap (((-d).toNat + n + 2) + 1))
      (E.map_point (((-d).toNat + n + 2) + 1))
      ((loopShiftMulEquiv (x := E.point (((-d).toNat + n + 2) + 1))
        (d.toNat + n + 1)).symm a.toMul)) = _
  apply congrArg Additive.ofMul
  apply (loopShiftMulEquiv (x := Path.refl (E.point (((-d).toNat + n + 2) + 1 + 1)))
    (d.toNat + n + 1)).injective
  change _ = (loopShiftMulEquiv (x := Path.refl
    (E.point (((-d).toNat + n + 2) + 1 + 1))) (d.toNat + n + 1))
      ((loopShiftMulEquiv (x := Path.refl
        (E.point (((-d).toNat + n + 2) + 1 + 1))) (d.toNat + n + 1)).symm
          (piMap (d.toNat + n + 1)
            (basedLoopMap (E.structureMap (((-d).toNat + n + 2) + 1))
              (E.map_point (((-d).toNat + n + 2) + 1)))
            (basedLoopMap_refl _ _) a.toMul))
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun k ↦ k ((loopShiftMulEquiv
    (x := E.point (((-d).toNat + n + 2) + 1)) (d.toNat + n + 1)).symm a.toMul))
    (loopShiftMulEquiv_natural (d.toNat + n + 1)
      (E.structureMap (((-d).toNat + n + 2) + 1))
      (E.map_point (((-d).toNat + n + 2) + 1)))
  simpa only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulEquiv.apply_symm_apply] using h.symm

/-- The actual stable-group isomorphism has the unchanged stabilization map as its forward map. -/
def stabilizationStableHomotopyIso :
    stableHomotopyGroup E d ≅ stableHomotopyGroup (looping (tail E)) d :=
  SequentialInterleaving.colimitIso (stableSystemMap (stabilizationMap E) d)
    (stabilizationStageReturn E d) (stabilizationStageMap_return E d)
    (stabilizationStageReturn_map E d)

@[simp]
theorem stabilizationStableHomotopyIso_hom :
    (stabilizationStableHomotopyIso E d).hom = (stableHomotopyFunctor d).map (stabilizationMap E) :=
  rfl

/-- The inverse keeps the original loop shift and precisely one original stable successor. -/
@[reassoc (attr := simp)]
theorem stabilizationStableHomotopyIso_ι_inv (n : ℕ) :
    stableHomotopyι (looping (tail E)) d n ≫ (stabilizationStableHomotopyIso E d).inv =
      stabilizationStageReturn E d n ≫ stableHomotopyι E d (n + 1) :=
  SequentialInterleaving.ι_inverse _ _ _ _ n

/-- Every original loop-tail stabilization map is a stable equivalence in all integer degrees. -/
theorem stabilizationMap_isStableEquivalence : IsStableEquivalence (stabilizationMap E) := by
  intro k
  exact (stabilizationStableHomotopyIso E k).isIso_hom

end Quillen.LoopPrespectrum
