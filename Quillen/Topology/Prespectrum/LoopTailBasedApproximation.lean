/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.LoopTailHomotopyShift

/-!
# The original loop-tail replacement structure at its chosen points

The canonical telescope homotopy-colimit comparisons identify the previously constructed
interleaving isomorphism with the unchanged structure map on actual homotopy sets. For original
T1 levels this proves bijectivity in every finite degree, including zero, at the displayed chosen
point. The zero-degree result also supplies actual coverage of all target components.

Higher homotopy groups at other source components are not asserted here. In particular this
module does not claim the complete weak-equivalence property or an Omega-spectrum theorem.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

variable (E : LoopPrespectrum.{u}) [∀ k, T1Space (E.space k)] (k n : ℕ)

/-- The actual telescope colimit comparison retains the original structure-induced function. -/
@[reassoc]
theorem loopTailHomotopyColimit_structure :
    (Telescope.homotopyColimitIso (loopTailIterate E) (loopTailTransition E) k n).hom ≫
      TypeCat.ofHom (structureHomotopyMap (loopTailReplacement E) k n) =
        (loopTailHomotopyColimitIso E k n).hom ≫
          (Telescope.homotopyColimitIso (loopTailIterate E) (loopTailTransition E)
            (k + 1) (n + 1)).hom := by
  apply colimit.hom_ext
  intro i
  change colimit.ι _ i ≫
    ((Telescope.homotopyColimitIso (loopTailIterate E) (loopTailTransition E) k n).hom ≫ _) =
      colimit.ι _ i ≫ (colimMap (loopTailHomotopyStructureMap E k n) ≫ _)
  rw [Telescope.homotopyColimitIso_ι_hom_assoc, ι_colimMap_assoc,
    Telescope.homotopyColimitIso_ι_hom]
  ext a
  exact structureHomotopyMap_naturality
    (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) i) k n a

/-- The original structure-induced function is a bijection on all finite homotopy sets based at
the chosen point, without an increasing-connectivity assumption. -/
theorem loopTailReplacement_structureHomotopyMap_bijective :
    Function.Bijective (structureHomotopyMap (loopTailReplacement E) k n) := by
  let a := Telescope.homotopyColimitIso (loopTailIterate E) (loopTailTransition E) k n
  let b := loopTailHomotopyColimitIso E k n
  let c := Telescope.homotopyColimitIso (loopTailIterate E) (loopTailTransition E)
    (k + 1) (n + 1)
  let e := a.symm ≪≫ b ≪≫ c
  have he : e.hom = TypeCat.ofHom (structureHomotopyMap (loopTailReplacement E) k n) := by
    apply (cancel_epi a.hom).mp
    change a.hom ≫ (a.inv ≫ b.hom ≫ c.hom) = _
    rw [Iso.hom_inv_id_assoc]
    exact (loopTailHomotopyColimit_structure E k n).symm
  have hb := (ConcreteCategory.isIso_iff_bijective e.hom).mp e.isIso_hom
  rw [he] at hb
  exact hb

/-- The unchanged structure adjoint is bijective at its chosen basepoint in every finite degree. -/
theorem loopTailReplacement_structureMap_homotopy_bijective :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      ((loopTailReplacement E).structureMap k) ((loopTailReplacement E).map_point k)) := by
  have h := loopTailReplacement_structureHomotopyMap_bijective E k n
  constructor
  · intro a b hab
    exact h.injective (congrArg (loopShiftEquiv n).symm hab)
  · intro a
    obtain ⟨b, hb⟩ := h.surjective ((loopShiftEquiv n).symm a)
    exact ⟨b, (loopShiftEquiv n).symm.injective hb⟩

/-- Degree zero supplies actual paths from images of the original structure map to every target
loop, including nonconstant-loop components. -/
theorem loopTailReplacement_structureMap_component_surjective
    (γ : Path ((loopTailReplacement E).point (k + 1))
      ((loopTailReplacement E).point (k + 1))) :
    ∃ x : (loopTailReplacement E).space k,
      Joined ((loopTailReplacement E).structureMap k x) γ := by
  let q : GenLoop (Fin 0)
      (Path ((loopTailReplacement E).point (k + 1)) ((loopTailReplacement E).point (k + 1)))
      (Path.refl ((loopTailReplacement E).point (k + 1))) :=
    ⟨ContinuousMap.const _ γ, by rintro t ⟨i, _⟩; exact Fin.elim0 i⟩
  obtain ⟨a, ha⟩ := (loopTailReplacement_structureMap_homotopy_bijective E k 0).surjective
    (Quotient.mk' q)
  induction a using Quotient.inductionOn with
  | h p =>
    obtain ⟨H⟩ := Quotient.exact ha
    exact ⟨p 0, ⟨H.toHomotopy.evalAt 0⟩⟩

end Quillen.LoopPrespectrum
