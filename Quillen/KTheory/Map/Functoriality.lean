/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.KTheory.Map.CoherenceData
public import Quillen.Topology.Realization.HomotopyBridge

/-!
# Functoriality of genuine Quillen K-group maps

The comparison between normalized composite Q-functors is the identity at the
zero base object. Its nerve homotopy realizes to a continuous homotopy fixed at
that basepoint. Homotopy invariance of actual homotopy-group maps therefore
proves the composition law for the zero-based Quillen K-group homomorphisms.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactFunctor
open Quillen

variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  [Preadditive T] [HasFiniteBiproducts T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}

/-- Realization of the normalized Q-functor preserves the chosen K-space points. -/
theorem normalizedQ_map_point (F : ExactFunctor EC ED) :
    classifyingSpaceMap F.normalizedQ EC.kBasepoint = ED.kBasepoint :=
  rebaseFunctor_map_point F.mapQ (Q.of EC.deflation EC.inflation (0 : C))
    (Q.of ED.deflation ED.inflation (0 : D)) (ED.qIsoOfIso F.toFunctor.mapZeroObject)

/-- The original K-map is definitionally induced by the normalized Q-functor. -/
theorem KMap_eq_piMap (F : ExactFunctor EC ED) (n : ℕ) :
    F.KMap n = piMap n (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact functor composition is respected by all genuine zero-based Quillen
K-group homomorphisms. The proof uses a continuous homotopy fixed at zero. -/
@[simp]
theorem KMap_comp (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) (n : ℕ) :
    (F.comp G).KMap n = (G.KMap n).comp (F.KMap n) := by
  let H := classifyingSpaceNaturalTransformationBasedHomotopy
    (F.normalizedQCompIso G).hom (Q.of EC.deflation EC.inflation (0 : C))
    (F.normalizedQCompIso_obj_base G) (F.normalizedQCompIso_hom_base G)
  have hcomp : classifyingSpaceMap (F.normalizedQ ⋙ G.normalizedQ) EC.kBasepoint =
      ET.kBasepoint := by
    rw [classifyingSpaceMap_comp, TopCat.comp_app, F.normalizedQ_map_point,
      G.normalizedQ_map_point]
  have hH : ∀ t, H.toHomotopy (t, EC.kBasepoint) = ET.kBasepoint := by
    intro t
    exact (H.prop t EC.kBasepoint (Set.mem_singleton _)).trans
      (F.comp G).normalizedQ_map_point
  have hmap := piMap_eq_of_based_homotopy n
    (F.comp G).normalizedQ_map_point hcomp H.toHomotopy hH
  calc
    (F.comp G).KMap n =
        piMap n (classifyingSpaceMap (F.normalizedQ ⋙ G.normalizedQ)).hom hcomp := hmap
    _ = (G.KMap n).comp (F.KMap n) := by
      apply MonoidHom.ext
      intro a
      change homotopyGroupMap (classifyingSpaceMap (F.normalizedQ ⋙ G.normalizedQ)).hom
        hcomp a = homotopyGroupMap (classifyingSpaceMap G.normalizedQ).hom
          G.normalizedQ_map_point
          (homotopyGroupMap (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point a)
      simp only [classifyingSpaceMap_comp, TopCat.hom_comp]
      exact homotopyGroupMap_comp _ _ _ _ a

end CategoryTheory.ExactCategory.ExactFunctor
