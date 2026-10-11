/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.TelescopeConeIso
public import Quillen.Topology.Prespectrum.TelescopeStableColimit
public import Quillen.Topology.Prespectrum.ConeLoopSeparation

/-!
# Actual stable groups of the cone of a telescope map

For T1 source and target stages, the original cone-stage inclusions induce a canonical signed
stable-group colimit isomorphism onto the cone of the unchanged telescope map. The proof uses
the strict two-coordinate cone/telescope interchange and accepted compact representability;
no uniform connectivity of the telescope or stable cone exactness premise is used.
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

/-- The actual stage-cone stable colimit is the signed stable group of the original telescope cone.
-/
def coneStableColimitIso (d : ℤ) :
    colimit (stageStableDiagram (fun i ↦ mappingCone (a i))
      (coneTransition E f F g a ha) d) ≅ stableHomotopyGroup (mappingCone (map E f F g a ha)) d :=
  (stableColimitIso (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) d).trans
    ((stableHomotopyFunctor d).mapIso (coneIso E f F g a ha).symm)

/-- The isomorphism is induced by the unchanged original stage-cone maps, in every signed degree.
-/
@[reassoc] theorem coneStableColimitIso_ι_hom (d : ℤ) (i : ℕ) :
    colimit.ι (stageStableDiagram (fun i ↦ mappingCone (a i))
        (coneTransition E f F g a ha) d) i ≫ (coneStableColimitIso E f F g a ha d).hom =
      (stableHomotopyFunctor d).map (coneStageMap E f F g a ha i) := by
  change colimit.ι _ i ≫ stableColimitComparison _ _ d ≫
    (stableHomotopyFunctor d).map (coneFromTelescope E f F g a ha) = _
  rw [← Category.assoc, stableColimitComparison_ι, ← Functor.map_comp]
  exact congrArg ((stableHomotopyFunctor d).map)
    (inclusion_desc (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha)
      (coneStageMap E f F g a ha) (coneStageTrack E f F g a ha) i)

end Quillen.LoopPrespectrum.Telescope
