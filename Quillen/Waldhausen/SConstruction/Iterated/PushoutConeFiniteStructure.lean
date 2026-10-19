/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.PushoutFiniteStructure
public import Quillen.Waldhausen.SConstruction.Iterated.FiniteConnectivity
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP
public import Quillen.Waldhausen.SConstruction.Iterated.OmegaSpectrum

/-!
# Finite structure range of a genuine model pushout cone

All four corners are the original Waldhausen prespectra. The attaching map is arbitrary;
the statement therefore applies to the prescribed raw Bass comparison without strictifying
its comparison homotopy. Only chosen-point groups in degrees at least two are used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology
universe u
namespace Quillen.Waldhausen.IteratedS

/-- The exact original model growth, with no auxiliary connectivity assumption. -/
theorem model_growth_zero (W : Model.{u}) (n : ℕ) (x) (j : ℕ) (hj : j < n + 2) :
    Subsingleton (HomotopyGroup.Pi j ((prespectrum W).space (n + 0 + 2)) x) :=
  prespectrum_positiveLevel_homotopyGroup_subsingleton_at W (n + 1) j (by omega) x

/-- The original cone over a model-span comparison has a finite linear structure range. -/
theorem pushoutCone_structure_bijective {A B C D : Model.{u}}
    (f : prespectrum A ⟶ prespectrum B) (g : prespectrum A ⟶ prespectrum C)
    (d : HomotopyPushout.prespectrum f g ⟶ prespectrum D) (n k : ℕ)
    (hk : k + 2 < 2 * n + 2) :
    Function.Bijective (homotopyGroupMap (N := Fin (k + 2))
      ((mappingCone d).structureMap (n + 3)) ((mappingCone d).map_point (n + 3))) := by
  have hA := prespectrum_point_homotopyExtensionProperty A
  have hB := prespectrum_point_homotopyExtensionProperty B
  have hC := prespectrum_point_homotopyExtensionProperty C
  have hD := prespectrum_point_homotopyExtensionProperty D
  have hP (m : ℕ) := HomotopyPushout.point_homotopyExtensionProperty f g m
    (hA m) (hB m) (hC m)
  have hπP (m : ℕ) (x) (j : ℕ) (hj : j < m + 2) :=
    HomotopyPushout.homotopyGroup_subsingleton f g (m + 0 + 2) m
      (hA _) (hB _) (hC _) (model_growth_zero A m)
      (model_growth_zero B m) (model_growth_zero C m) x j hj
  change Function.Bijective (homotopyGroupMap (N := Fin (k + 2))
    ((mappingCone d).structureMap ((n + 1) + 0 + 2))
    ((mappingCone d).map_point ((n + 1) + 0 + 2)))
  apply mappingCone_structure_bijective d 0 (fun m => hP _) (fun m => hD _)
    hπP (model_growth_zero D) (n + 1) k (2 * (n + 1) + 1) (by omega) (by omega)
  · intro j hj hr
    exact HomotopyPushout.structure_bijective_of_omega_corners f g 0 hA hB hC
      (model_growth_zero A) (model_growth_zero B) (model_growth_zero C)
      (prespectrum_isOmega A) (prespectrum_isOmega B) (prespectrum_isOmega C)
      (n + 1) j hj hr
  · intro j _ _
    exact based_bijective_of_weak _ _ (prespectrum_isOmega D _) j

end Quillen.Waldhausen.IteratedS
