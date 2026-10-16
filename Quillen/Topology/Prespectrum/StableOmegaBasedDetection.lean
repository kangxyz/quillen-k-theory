/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.SequentialSystem.IsoColimit
public import Quillen.Topology.Prespectrum.StableOmega
public import Quillen.Topology.Prespectrum.StableEquivalence
public import Quillen.Topology.Prespectrum.HomotopyStructure

/-!
# Signed stable detection at every chosen Omega-spectrum point

Every original stable-stage inclusion of an Omega-prespectrum is invertible. Naturality of
these inclusions detects the original map in every signed stable stage. The actual structure
maps then give bijectivity at every original level in every finite degree, including degree
zero. No connectedness, separation, or connectivity growth is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

namespace Quillen.LoopPrespectrum

/-- Every original stable-stage inclusion of a genuine Omega-prespectrum is invertible. -/
theorem stableHomotopyι_isIso_of_isOmega (E : LoopPrespectrum.{u}) (hE : E.IsOmega)
    (d : ℤ) (i : ℕ) : IsIso (stableHomotopyι E d i) := by
  let (n : ℕ) : IsIso ((stableSystem E d).map (homOfLE (Nat.le_succ n))) :=
    stableSystem_succ_isIso E hE d n
  have he : stableHomotopyι E d i =
      (SequentialSystem.toZeroIso
        (fun n ↦ (stableSystem E d).map (homOfLE (Nat.le_succ n))) i).hom ≫
          (stableHomotopyStageZeroIso E hE d).inv := by
    apply (cancel_mono (stableHomotopyStageZeroIso E hE d).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact SequentialSystem.ι_colimitIsoOfSucc_hom (stableSystem E d) i
  rw [he]
  infer_instance

variable {E F : LoopPrespectrum.{u}} (hE : E.IsOmega) (hF : F.IsOmega) (f : E ⟶ F)
include hE hF

/-- A stable equivalence between genuine Omega-prespectra gives bijections on each unchanged
signed stable stage, through the original colimit-inclusion naturality square. -/
theorem stableSystemMap_app_bijective_of_isStableEquivalence (hf : IsStableEquivalence f)
    (d : ℤ) (i : ℕ) : Function.Bijective ((stableSystemMap f d).app i) := by
  have := stableHomotopyι_isIso_of_isOmega E hE d i
  have := stableHomotopyι_isIso_of_isOmega F hF d i
  have := hf d
  have he : (stableSystemMap f d).app i =
      stableHomotopyι E d i ≫ (stableHomotopyFunctor d).map f ≫
        inv (stableHomotopyι F d i) := by
    apply (cancel_mono (stableHomotopyι F d i)).mp
    rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (stableHomotopyι_naturality f d i).symm
  apply (ConcreteCategory.isIso_iff_bijective _).mp
  rw [he]
  infer_instance

/-- Bijectivity of the original next-level map descends through the original Omega structure
maps, retaining both the level and finite homotopy degree. -/
theorem homotopyGroupMap_bijective_of_succ (k n : ℕ)
    (hf : Function.Bijective (homotopyGroupMap (N := Fin (n + 1))
      (f.map (k + 1)) (f.map_point (k + 1)))) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (f.map k) (f.map_point k)) := by
  have he : structureHomotopyMap F k n ∘ homotopyGroupMap (f.map k) (f.map_point k) =
      homotopyGroupMap (f.map (k + 1)) (f.map_point (k + 1)) ∘ structureHomotopyMap E k n :=
    funext (structureHomotopyMap_naturality f k n)
  have hb := hf.comp (structureHomotopyEquiv E hE k n).bijective
  change Function.Bijective
    (homotopyGroupMap (f.map (k + 1)) (f.map_point (k + 1)) ∘ structureHomotopyMap E k n) at hb
  rw [← he] at hb
  exact (Function.Bijective.of_comp_iff' (structureHomotopyEquiv F hF k n).bijective _).mp hb

/-- Signed stable equivalence detects the original map at every chosen level point in every
finite homotopy degree, including zero and levels zero and one. -/
theorem homotopyGroupMap_bijective_of_isStableEquivalence (hf : IsStableEquivalence f)
    (k n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (f.map k) (f.map_point k)) := by
  have hb := stableSystemMap_app_bijective_of_isStableEquivalence hE hF f hf
    ((n : ℤ) - (k : ℤ)) (min n k)
  have hd : ((n : ℤ) - (k : ℤ)).toNat + min n k + 2 = n + 2 := by omega
  have hl : (-((n : ℤ) - (k : ℤ))).toNat + min n k + 2 = k + 2 := by omega
  change Function.Bijective (homotopyGroupMap
    (N := Fin (((n : ℤ) - (k : ℤ)).toNat + min n k + 2))
    (f.map ((-((n : ℤ) - (k : ℤ))).toNat + min n k + 2))
    (f.map_point ((-((n : ℤ) - (k : ℤ))).toNat + min n k + 2))) at hb
  rw [hd, hl] at hb
  exact homotopyGroupMap_bijective_of_succ hE hF f k n
    (homotopyGroupMap_bijective_of_succ hE hF f (k + 1) (n + 1) hb)

end Quillen.LoopPrespectrum
