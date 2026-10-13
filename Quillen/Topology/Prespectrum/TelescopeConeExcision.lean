/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopeConeExactness

/-!
# Genuine excision for the original cone of a strict telescope map

The exact stage-compatible signed boundary followed by the original canonical source-to-fiber
comparison is the original fiber boundary. The actual two exact sequences prove that comparison
bijective on every signed stable group. Thus the telescope boundary agrees with the original
cone boundary defined by that same comparison. Only stage T1 and proved finite-stage excision
enter; no connectivity or excision of the whole telescope is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))
    [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((F i).space k)]
    (h : ∀ i, IsStableEquivalence (mappingConeFiberComparison (a i)))

/-- The original comparison carries the actual colimit boundary to the original fiber boundary.
-/
theorem coneStableConnecting_comparison (d : ℤ) :
    coneStableConnecting E f F g a ha h d ≫
      (stableHomotopyFunctor d).map (mappingConeFiberComparison (map E f F g a ha)) =
        stableFiberConnecting (mappingConeInclusion (map E f F g a ha)) d := by
  apply (cancel_epi (coneStableColimitIso E f F g a ha (d + 1)).hom).mp
  apply colimit.hom_ext
  intro i
  rw [coneStableColimitIso_ι_hom_assoc, coneStableColimitIso_ι_hom_assoc]
  rw [← Category.assoc, coneStableConnecting_stage, Category.assoc]
  have hn := congrArg ((stableHomotopyFunctor d).map)
    (mappingConeFiberComparison_naturality (coneStageSquare E f F g a ha i))
  rw [Functor.map_comp, Functor.map_comp] at hn
  let v := (stableHomotopyFunctor d).map
    (homotopyFiberMap (mappingConeInclusionSquare (coneStageSquare E f F g a ha i)))
  calc
    _ = stableMappingConeConnecting (a i) (h i) d ≫
        ((stableHomotopyFunctor d).map (mappingConeFiberComparison (a i)) ≫ v) :=
      congrArg (fun b ↦ stableMappingConeConnecting (a i) (h i) d ≫ b) hn
    _ = (stableMappingConeConnecting (a i) (h i) d ≫
        (stableHomotopyFunctor d).map (mappingConeFiberComparison (a i))) ≫ v :=
      (Category.assoc _ _ _).symm
    _ = stableFiberConnecting (mappingConeInclusion (a i)) d ≫ v :=
      congrArg (fun b ↦ b ≫ v) (stableMappingConeConnecting_comparison (a i) (h i) d)
    _ = _ := (stableFiberConnecting_naturality
      (mappingConeInclusionSquare (coneStageSquare E f F g a ha i)) d).symm

include h in
/-- Actual finite-stage excision passes to the same original telescope cone-to-fiber comparison.
-/
theorem coneFiberComparison_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (map E f F g a ha)) := by
  intro d
  let b := map E f F g a ha
  let j : stableHomotopyGroup (prespectrum E f) d ⟶
      stableHomotopyGroup (homotopyFiber (mappingConeInclusion b)) d :=
    (stableHomotopyFunctor d).map (mappingConeFiberComparison b)
  let p : stableHomotopyGroup (homotopyFiber (mappingConeInclusion b)) d ⟶
      stableHomotopyGroup (prespectrum F g) d :=
    (stableHomotopyFunctor d).map (homotopyFiberProjection (mappingConeInclusion b))
  let δ : stableHomotopyGroup (mappingCone b) (d + 1) ⟶
      stableHomotopyGroup (prespectrum E f) d := coneStableConnecting E f F g a ha h d
  have hp (x : stableHomotopyGroup (prespectrum E f) d) :
      p (j x) = (stableHomotopyFunctor d).map b x :=
    ConcreteCategory.congr_hom (stableMappingConeComparison_projection b d) x
  have hδ (y : stableHomotopyGroup (mappingCone b) (d + 1)) :
      j (δ y) = stableFiberConnecting (mappingConeInclusion b) d y :=
    ConcreteCategory.congr_hom (coneStableConnecting_comparison E f F g a ha h d) y
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective j.hom
  constructor
  · apply (injective_iff_map_eq_zero j.hom).mpr
    intro x hx
    have hb : (stableHomotopyFunctor d).map b x = 0 := by
      rw [← hp x, hx, map_zero]
    obtain ⟨y, hy⟩ := (coneStableConnecting_exact_source E f F g a ha h d x).mp hb
    have hz : stableFiberConnecting (mappingConeInclusion b) d y = 0 :=
      (hδ y).symm.trans ((congrArg j hy).trans hx)
    obtain ⟨z, hz⟩ := (stableFiberConnecting_exact_target (mappingConeInclusion b) d y).mp hz
    exact hy.symm.trans
      ((coneStableConnecting_exact_cone E f F g a ha h d y).mpr ⟨z, hz⟩)
  · intro z
    have hpz : (stableHomotopyFunctor d).map (mappingConeInclusion b) (p z) = 0 :=
      (stableHomotopyFiber_exact_source (mappingConeInclusion b) d (p z)).mpr ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := (cone_stable_exact_target E f F g a ha h d (p z)).mp hpz
    have hw : p (z - j x) = 0 := by
      rw [map_sub, hp, hx, sub_self]
    obtain ⟨y, hy⟩ :=
      (stableFiberConnecting_exact_fiber (mappingConeInclusion b) d (z - j x)).mp hw
    let x' : stableHomotopyGroup (prespectrum E f) d := x
    refine ⟨x' + δ y, ?_⟩
    rw [map_add, hδ, hy]
    dsimp [x']
    abel

/-- The stage-colimit boundary is precisely the original signed cone boundary of this comparison.
-/
theorem coneStableConnecting_eq_original (d : ℤ) :
    coneStableConnecting E f F g a ha h d =
      stableMappingConeConnecting (map E f F g a ha)
        (coneFiberComparison_isStableEquivalence E f F g a ha h) d := by
  let := coneFiberComparison_isStableEquivalence E f F g a ha h d
  apply (cancel_mono ((stableHomotopyFunctor d).map
    (mappingConeFiberComparison (map E f F g a ha)))).mp
  rw [coneStableConnecting_comparison, stableMappingConeConnecting_comparison]

end Quillen.LoopPrespectrum.Telescope
