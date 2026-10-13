/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.StableLevelOne
public import Quillen.Topology.Prespectrum.StableEquivalence

/-!
# Positive-level detection of stable equivalences between connective Omega-spectra

For Omega-prespectra with path-connected positive levels, an original stable equivalence is a
complete weak homotopy equivalence at every original positive level. The actual structure maps
transport the positive-degree tests, and connectivity supplies both degree zero and component
coverage. No continuous inverse, cofiber exactness, or basepoint cofibration is assumed.
-/
@[expose] public section
noncomputable section

open CategoryTheory
open scoped Topology
universe u
namespace Quillen.LoopPrespectrum

variable {E F : LoopPrespectrum.{u}} (hE : E.IsOmega) (hF : F.IsOmega)
  (f : E ⟶ F) (hf : IsStableEquivalence f)
include hE hF hf

/-- A stable equivalence between Omega-spectra gives the original positive homotopy bijections
at level one, by naturality of the actual stable-colimit comparison. -/
theorem levelOne_piMap_bijective_of_isStableEquivalence (k : ℕ) :
    Function.Bijective (piMap k (f.map 1) (f.map_point 1)) := by
  let eE := levelOneStableEquiv E hE k
  let eF := levelOneStableEquiv F hF k
  have he : (fun a : Additive (HomotopyGroup.Pi (k + 1) (E.space 1) (E.point 1)) ↦
      eF (Additive.ofMul (piMap k (f.map 1) (f.map_point 1) a.toMul))) =
      (stableHomotopyFunctor (k : ℤ)).map f ∘ eE := by
    funext a
    exact levelOneStableEquiv_naturality hE hF f k a.toMul
  have hb := ((ConcreteCategory.isIso_iff_bijective _).mp (hf (k : ℤ))).comp eE.bijective
  rw [← he] at hb
  exact (eF.bijective.of_comp_iff' _).mp hb

variable (hcE : ∀ n, PathConnectedSpace (E.space (n + 1)))
  (hcF : ∀ n, PathConnectedSpace (F.space (n + 1)))
include hcE hcF

/-- Every unchanged positive-level positive-degree map is bijective. Below the level,
connectivity is derived from the original Omega maps; above it, their actual naturality applies. -/
theorem positiveLevel_piMap_bijective_of_isStableEquivalence (n k : ℕ) :
    Function.Bijective (piMap k (f.map (n + 1)) (f.map_point (n + 1))) := by
  induction n generalizing k with
  | zero => exact levelOne_piMap_bijective_of_isStableEquivalence hE hF f hf k
  | succ n ih =>
    cases k with
    | zero =>
      let := homotopyGroup_subsingleton_of_lt E hE hcE 1 (n + 2) (by omega)
      let := homotopyGroup_subsingleton_of_lt F hF hcF 1 (n + 2) (by omega)
      exact Function.bijective_of_subsingleton' _
    | succ k =>
      have hb := (structurePiMap_bijective F hF (n + 1) k).comp (ih k)
      have he := DFunLike.congr_fun (structurePiMap_naturality f (n + 1) k)
      have hw : (structurePiMap F (n + 1) k) ∘
          piMap k (f.map (n + 1)) (f.map_point (n + 1)) =
          (piMap (k + 1) (f.map (n + 2)) (f.map_point (n + 2))) ∘
            structurePiMap E (n + 1) k := funext he
      rw [hw] at hb
      exact (Function.Bijective.of_comp_iff _
        (structurePiMap_bijective E hE (n + 1) k)).mp hb

/-- Stable equivalence on connected Omega-spectra gives complete weakness on each original
positive level, including the actual component-surjectivity clause. -/
theorem positiveLevel_isWeakHomotopyEquivalence_of_isStableEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence (f.map (n + 1)) := by
  let := hcE n
  let := hcF n
  apply isWeakHomotopyEquivalence_of_connected (f.map (n + 1)) (E.point (n + 1))
  intro k
  have transfer {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      (g : C(X, Y)) (x : X) (y : Y) (h : g x = y)
      (hb : Function.Bijective (piMap k g h)) :
      Function.Bijective (piMap k g (x := x) rfl) := by
    cases h
    exact hb
  exact transfer (f.map (n + 1)) (E.point (n + 1)) (F.point (n + 1))
    (f.map_point (n + 1))
    (positiveLevel_piMap_bijective_of_isStableEquivalence hE hF f hf hcE hcF n k)

end Quillen.LoopPrespectrum
