/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.OmegaSpectrum
public import Quillen.Topology.Prespectrum.StableLevelOne
public import Quillen.Waldhausen.Functoriality.KMap

/-!
# Original K-maps on the actual Model prespectra

The level-one Omega comparison identifies the unchanged K-map of a Model arrow with its
nonnegative stable map. Injectivity and surjectivity transport through this same comparison.
Negative stable groups of the actual Models vanish by their positive-level connectivity.
No normalization through a different small model or replacement spectrum is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u
namespace Quillen.Waldhausen.IteratedS

/-- The original K-map and actual Model prespectrum map use the same level-one comparison. -/
theorem prespectrumMap_KMap_stable_naturality {W V : Model.{u}} (f : W ⟶ V)
    (n : ℕ) (x : W.waldhausen.K n) :
    levelOneStableEquiv (prespectrum V) (prespectrum_isOmega V) n
        (Additive.ofMul (KMap f.exact n x)) =
      (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)
        (levelOneStableEquiv (prespectrum W) (prespectrum_isOmega W) n
          (Additive.ofMul x)) := by
  rw [KMap_eq_piMap_of_zeroEq f.exact f.zero]
  exact levelOneStableEquiv_naturality (prespectrum_isOmega W) (prespectrum_isOmega V)
    (prespectrumMap f) n x

/-- Injectivity of the unchanged K-map gives injectivity of the actual nonnegative stable map. -/
theorem prespectrumMap_stable_nonnegative_injective {W V : Model.{u}} (f : W ⟶ V)
    (n : ℕ) (hf : Function.Injective (KMap f.exact n)) :
    Function.Injective ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)) := by
  let eW := levelOneStableEquiv (prespectrum W) (prespectrum_isOmega W) n
  let eV := levelOneStableEquiv (prespectrum V) (prespectrum_isOmega V) n
  intro x y hxy
  obtain ⟨a, rfl⟩ := eW.surjective x
  obtain ⟨b, rfl⟩ := eW.surjective y
  have h := (prespectrumMap_KMap_stable_naturality f n a.toMul).trans
    (hxy.trans (prespectrumMap_KMap_stable_naturality f n b.toMul).symm)
  have hab := hf (congrArg Additive.toMul (eV.injective h))
  exact congrArg eW (congrArg Additive.ofMul hab)

/-- Surjectivity transports through the same original K-to-stable comparison. -/
theorem prespectrumMap_stable_nonnegative_surjective {W V : Model.{u}} (f : W ⟶ V)
    (n : ℕ) (hf : Function.Surjective (KMap f.exact n)) :
    Function.Surjective ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)) := by
  let eW := levelOneStableEquiv (prespectrum W) (prespectrum_isOmega W) n
  let eV := levelOneStableEquiv (prespectrum V) (prespectrum_isOmega V) n
  intro y
  obtain ⟨b, rfl⟩ := eV.surjective y
  obtain ⟨a, ha⟩ := hf b.toMul
  exact ⟨eW (Additive.ofMul a),
    (prespectrumMap_KMap_stable_naturality f n a).symm.trans
      (congrArg eV (congrArg Additive.ofMul ha))⟩

/-- Connectivity of the actual positive Model levels gives all negative stable vanishing. -/
theorem prespectrum_stableHomotopyGroup_neg_subsingleton (W : Model.{u})
    (d : ℤ) (hd : d < 0) : Subsingleton (stableHomotopyGroup (prespectrum W) d) :=
  stableHomotopyGroup_subsingleton_of_neg (prespectrum W) (prespectrum_isOmega W)
    (fun n ↦ stageSpace_pathConnected n W) d hd

end Quillen.Waldhausen.IteratedS
