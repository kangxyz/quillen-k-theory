/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopeConeDescentStable

/-!
# Original telescope cone-descent consumers

The actual initial target face, full null/telescope cylinder, independent structure time,
negative stable degrees and signed boundary are retained. Stable transfer uses original stage
T1 and stage descent stability; the boundary uses genuine original finite-stage excision.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.Telescope
universe u
namespace QuillenTest.TelescopeConeDescent

open Quillen
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
    (a : ∀ i, E i ⟶ F i) (b : ∀ i, F i ⟶ G i)
    (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))
    (hb : ∀ i, b i ≫ h i = g i ≫ b (i + 1))
    (N : ∀ i, Homotopy (a i ≫ b i) (zeroHom (E i) (G i)))
    (hN : ∀ i k r x, (h i).map k ((N i).level k (r, x)) =
      (N (i + 1)).level k (r, (f i).map k x))

/-- The original stage-zero target inclusion is preserved by the exact telescope cone descent. -/
theorem originalInitialTarget :
    inclusion F g 0 ≫ mappingConeInclusion (map E f F g a ha) ≫
      mappingConeDesc (map E f F g a ha) (map F g G h b hb)
        (mapNullHomotopy E f F g G h a b ha hb N hN) = b 0 ≫ inclusion G h 0 := by
  rw [mappingConeInclusion_desc, inclusion_map]

/-- The original cone and telescope cylinders keep their two independent coordinates. -/
theorem originalTwoCylinders (k i : ℕ) (r t : unitInterval) (x : (E i).space k) :
    (mappingConeDesc (map E f F g a ha) (map F g G h b hb)
      (mapNullHomotopy E f F g G h a b ha hb N hN)).map k
        (ReducedMappingCone.cylinder ((prespectrum E f).point k) ((prespectrum F g).point k)
          ((map E f F g a ha).map k) (r, cylinder E f k i (t, x))) =
      cylinder G h k i (t, (N i).level k (r, x)) := rfl

/-- The source structure time remains independent of both original cylinder coordinates. -/
theorem originalThreeTimes (k i : ℕ) (r t s : unitInterval) (x : (E i).space k) :
    (mapNullHomotopy E f F g G h a b ha hb N hN).level (k + 1)
      (r, (prespectrum E f).structureMap k (cylinder E f k i (t, x)) s) =
      cylinder G h (k + 1) i (t, (G i).structureMap k ((N i).level k (r, x)) s) := by
  change cylinder G h (k + 1) i (t, (N i).level (k + 1)
    (r, (E i).structureMap k x s)) = _
  rw [(N i).comm]

/-- Each actual time slice is the original telescope map of the original time-slice maps. -/
theorem originalTimeSlice (r : unitInterval) :
    (mapNullHomotopy E f F g G h a b ha hb N hN).at r =
      map E f G h (fun i ↦ (N i).at r) (by
        intro i
        apply Hom.ext
        funext k
        ext x
        exact hN i k r x) := by
  apply hom_ext
  intros
  rfl

variable [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((F i).space k)]
    [∀ i k, T1Space ((G i).space k)]

/-- Every negative signed degree uses the same original cone descent and same entire null track. -/
theorem originalNegativeBijective
    (hdesc : ∀ i, IsStableEquivalence (mappingConeDesc (a i) (b i) (N i))) (q : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-((q : ℤ) + 1))).map
      (mappingConeDesc (map E f F g a ha) (map F g G h b hb)
        (mapNullHomotopy E f F g G h a b ha hb N hN))) := by
  let := coneDesc_isStableEquivalence E f F g G h a b ha hb N hN hdesc (-((q : ℤ) + 1))
  exact ConcreteCategory.bijective_of_isIso _

omit [∀ i k, T1Space ((G i).space k)] in
/-- The original signed boundary retains the actual telescope fiber lift on each stable class. -/
theorem originalSignedBoundary
    (he : ∀ i, IsStableEquivalence (mappingConeFiberComparison (a i))) (d : ℤ)
    (x : stableHomotopyGroup (mappingCone (map E f F g a ha)) (d + 1)) :
    stableFiberConnecting (map F g G h b hb) d
      ((stableHomotopyFunctor (d + 1)).map
        (mappingConeDesc (map E f F g a ha) (map F g G h b hb)
          (mapNullHomotopy E f F g G h a b ha hb N hN)) x) =
      (stableHomotopyFunctor d).map (homotopyFiberLift (map F g G h b hb)
        (map E f F g a ha) (mapNullHomotopy E f F g G h a b ha hb N hN))
        (stableMappingConeConnecting (map E f F g a ha)
          (coneFiberComparison_isStableEquivalence E f F g a ha he) d x) :=
  ConcreteCategory.congr_hom (coneDesc_connecting E f F g G h a b ha hb N hN he d) x

end QuillenTest.TelescopeConeDescent
