/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.ConeFiniteStructure
public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeVanishing

/-!
# The original cone growth and its degree-one structure map

Only the degree-one corner needed by the finite abelian ladder is supplied by vanishing.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology
universe u
namespace Quillen.LoopPrespectrum

/-- Weak equivalence at the actual named basepoints gives the chosen-point group bijection. -/
theorem based_bijective_of_weak {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (hf : IsWeakHomotopyEquivalence f) (j : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin j) f h) := by
  cases h
  exact hf.homotopy_bijective x j

/-- The actual cone retains all-point linear vanishing. -/
theorem mappingCone_growth {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (c : ℕ)
    (hE : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point (n + c + 2)))))
    (hF : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point (n + c + 2)))))
    (hπE : ∀ n x j, j < n + 2 →
      Subsingleton (HomotopyGroup.Pi j (E.space (n + c + 2)) x))
    (hπF : ∀ n x j, j < n + 2 →
      Subsingleton (HomotopyGroup.Pi j (F.space (n + c + 2)) x))
    (n : ℕ) (x : (mappingCone f).space (n + c + 2)) (j : ℕ) (hj : j < n + 2) :
    Subsingleton (HomotopyGroup.Pi j ((mappingCone f).space (n + c + 2)) x) :=
  ReducedMappingCone.homotopyGroup_subsingleton _ _ (f.map _) (f.map_point _)
    (hE n) (hF n) n (hπE n) (hπF n) x j hj

/-- Linear vanishing suffices for the one-dimensional chosen-point structure corner. -/
theorem structure_one_bijective_of_growth (E : LoopPrespectrum.{u}) (c : ℕ)
    (hπ : ∀ n x j, j < n + 2 →
      Subsingleton (HomotopyGroup.Pi j (E.space (n + c + 2)) x)) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin 1)
      (E.structureMap (n + c + 2)) (E.map_point (n + c + 2))) := by
  let := hπ n (E.point _) 1 (by omega)
  have hh := hπ (n + 1) (E.point ((n + 1) + c + 2)) 2 (by omega)
  have hh' : Subsingleton (HomotopyGroup.Pi 2 (E.space (n + c + 2 + 1))
      (E.point (n + c + 2 + 1))) := by
    rw [show n + c + 2 + 1 = (n + 1) + c + 2 by omega]
    exact hh
  let := subsingleton_pi_loop_of_succ (E.point (n + c + 2 + 1)) 1 hh'
    (Path.refl _)
  exact Function.bijective_of_subsingleton' _

end Quillen.LoopPrespectrum
