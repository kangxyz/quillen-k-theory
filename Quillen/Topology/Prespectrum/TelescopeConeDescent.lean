/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.TelescopeConeIso
public import Quillen.Topology.Prespectrum.ConeDescNaturality

/-!
# Original cone descents and strictly compatible telescope null tracks

The original telescope homotopy of a compatible stage null family descends from the cone of
the unchanged telescope map. This descent factors through the actual telescope-cone isomorphism
and the telescope of the original stage descents. All cylinder and homotopy times are literal;
no point-set separation, excision or stable-equivalence premise is used for this equality.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
    (a : ∀ i, E i ⟶ F i) (b : ∀ i, F i ⟶ G i)
    (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))
    (hb : ∀ i, b i ≫ h i = g i ≫ b (i + 1))
    (N : ∀ i, Homotopy (a i ≫ b i) (zeroHom (E i) (G i)))
    (hN : ∀ i k r x, (h i).map k ((N i).level k (r, x)) =
      (N (i + 1)).level k (r, (f i).map k x))

/-- The literal original telescope homotopy, with only its proven composite/zero endpoints cast. -/
def mapNullHomotopy :
    Homotopy (map E f F g a ha ≫ map F g G h b hb)
      (zeroHom (prespectrum E f) (prespectrum G h)) :=
  (mapHomotopy E f G h (fun i ↦ a i ≫ b i) (fun i ↦ zeroHom (E i) (G i))
    (by intro i; rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc])
    (by
      intro i
      apply Hom.ext
      funext k
      ext x
      exact (h i).map_point k)
    N hN).cast (by apply hom_ext; intros; rfl) (by
      apply hom_ext
      intro k i t x
      exact cylinder_point G h k i t)

/-- The original null time and original telescope height are retained independently. -/
theorem mapNullHomotopy_cylinder (k i : ℕ) (r t : unitInterval) (x : (E i).space k) :
    (mapNullHomotopy E f F g G h a b ha hb N hN).level k
        (r, cylinder E f k i (t, x)) =
      cylinder G h k i (t, (N i).level k (r, x)) := rfl

include hb hN in
/-- The prescribed full stage-null square makes the original stage cone descents compatible. -/
theorem coneDesc_transition (i : ℕ) :
    mappingConeDesc (a i) (b i) (N i) ≫ h i =
      coneTransition E f F g a ha i ≫ mappingConeDesc (a (i + 1)) (b (i + 1)) (N (i + 1)) :=
  (mappingConeDesc_naturality (coneTransitionSquare E f F g a ha i)
    (b i) (b (i + 1)) (h i) (N i) (N (i + 1)) (hb i).symm (hN i)).symm

/-- The unchanged telescope of the original cone descents. -/
def coneDescMap :
    prespectrum (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) ⟶ prespectrum G h :=
  map (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) G h
    (fun i ↦ mappingConeDesc (a i) (b i) (N i))
    (coneDesc_transition E f F g G h a b ha hb N hN)

/-- The actual telescope-cone isomorphism factors the specified original null descent literally. -/
theorem coneIso_desc :
    (coneIso E f F g a ha).hom ≫ coneDescMap E f F g G h a b ha hb N hN =
      mappingConeDesc (map E f F g a ha) (map F g G h b hb)
        (mapNullHomotopy E f F g G h a b ha hb N hN) := by
  apply mappingCone_hom_ext
  · apply hom_ext
    intros
    rfl
  · intro k r q
    induction q using Quot.inductionOn with
    | h z => rfl

/-- The original telescope-of-cones cylinder retains its height after descent. -/
theorem coneDescMap_cylinder (k i : ℕ) (t : unitInterval)
    (q : (mappingCone (a i)).space k) :
    (coneDescMap E f F g G h a b ha hb N hN).map k
        (cylinder (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) k i (t, q)) =
      cylinder G h k i (t, (mappingConeDesc (a i) (b i) (N i)).map k q) := rfl

end Quillen.LoopPrespectrum.Telescope
