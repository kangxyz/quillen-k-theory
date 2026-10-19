/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.FiberHomotopySquare
public import Quillen.Topology.Prespectrum.FiberLiftConnecting
public import Quillen.Topology.Prespectrum.HomotopySquare
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# Homotopy-compatible naturality of specified fiber lifts

Two specified arrow homotopies and a whole square comparing their specified null tracks give
an actual homotopy between the original fiber lifts. The square retains comparison time,
null time, and prespectrum structure time independently. Stable comparisons then transport
stability of the original lifts and their original signed connecting maps.

The null square is an explicit input. These generic consumers do not construct that square
for a geometric sequence or replace either specified nullhomotopy.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

variable {S A O S' A' O' : LoopPrespectrum.{u}}
    (f : S ⟶ A) (r : A ⟶ O) (f' : S' ⟶ A') (r' : A' ⟶ O')
    (N : Homotopy (f ≫ r) (zeroHom S O))
    (N' : Homotopy (f' ≫ r') (zeroHom S' O'))
    (s : S ⟶ S') (a : A ⟶ A') (o : O ⟶ O')
    (Hf : Homotopy (f ≫ a) (s ≫ f'))
    (Hr : Homotopy (a ≫ r') (r ≫ o))

/-- The supplied second-arrow track followed by the original postcomposed null, with its
original half clocks and only endpoint-arrow casts. -/
def homotopyFiberLiftSquareNullHomotopy :
    Homotopy ((f ≫ a) ≫ r') (zeroHom S O') :=
  ((Homotopy.precomp f Hr).cast (Category.assoc f a r').symm
    (Category.assoc f r o).symm).trans
      ((N.postcomp o).cast rfl (zeroHom_comp o))

/-- The target specified null is precomposed by the source comparison without changing its time. -/
def homotopyFiberLiftTargetNullHomotopy :
    Homotopy ((s ≫ f') ≫ r') (zeroHom S O') :=
  (Homotopy.precomp s N').cast (Category.assoc s f' r').symm (comp_zeroHom s)

variable (Q : (homotopyFiberLiftSquareNullHomotopy f r r' N a o Hr).Square
    (homotopyFiberLiftTargetNullHomotopy f' r' N' s)
    (Hf.postcomp r') (Homotopy.refl (zeroHom S O')))

/-- A whole specified null square lifts to an actual coherent homotopy of the original
fiber-lift composites. Its two coordinates are exactly the first-arrow track and the square. -/
def homotopyFiberLiftNaturalityHomotopy :
    Homotopy (homotopyFiberLift r f N ≫ homotopyFiberSquareMap r r' a o Hr)
      (s ≫ homotopyFiberLift r' f' N') where
  level n :=
    { toFun z := ⟨(Hf.level n z,
        ⟨fun t ↦ Q.level n (z.1, (t, z.2)), by fun_prop⟩),
        Q.left n z.1 z.2, Q.right n z.1 z.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.prodMk
        · exact (Hf.level n).continuous
        · apply ContinuousMap.continuous_of_continuous_uncurry
          change Continuous (fun z : (unitInterval × S.space n) × unitInterval ↦
            Q.level n (z.1.1, (z.2, z.1.2)))
          fun_prop }
  at_zero n x := by
    apply Subtype.ext
    apply Prod.ext
    · exact Hf.at_zero n x
    · apply ContinuousMap.ext
      intro t
      change Q.level n (0, (t, x)) = _
      rw [Q.at_zero]
      rfl
  at_one n x := by
    apply Subtype.ext
    apply Prod.ext
    · exact Hf.at_one n x
    · apply ContinuousMap.ext
      intro t
      exact Q.at_one n t x
  at_point n c := by
    apply Subtype.ext
    apply Prod.ext
    · exact Hf.at_point n c
    · apply ContinuousMap.ext
      intro t
      exact Q.at_point n c t
  comm n c x t := by
    apply Subtype.ext
    apply Prod.ext
    · exact Hf.comm n c x t
    · apply ContinuousMap.ext
      intro v
      exact Q.comm n c v x t

/-- The actual lifted homotopy retains every value of the first-arrow track. -/
@[simp] theorem homotopyFiberLiftNaturalityHomotopy_source
    (n : ℕ) (c : unitInterval) (x : S.space n) :
    ((homotopyFiberLiftNaturalityHomotopy f r f' r' N N' s a o Hf Hr Q).level n
      (c, x)).1.1 = Hf.level n (c, x) := rfl

/-- The actual lifted homotopy retains the entire null square with independent times. -/
@[simp] theorem homotopyFiberLiftNaturalityHomotopy_path
    (n : ℕ) (c t : unitInterval) (x : S.space n) :
    ((homotopyFiberLiftNaturalityHomotopy f r f' r' N N' s a o Hf Hr Q).level n
      (c, x)).1.2 t = Q.level n (c, (t, x)) := rfl

include Hf Hr Q in
/-- Stable comparisons and a whole compatible null square transport stability of the
specified fiber lifts in both directions, without choosing inverse comparison tracks. -/
theorem homotopyFiberLift_homotopySquare_isStableEquivalence_iff
    (hs : IsStableEquivalence s) (ha : IsStableEquivalence a)
    (ho : IsStableEquivalence o) :
    IsStableEquivalence (homotopyFiberLift r f N) ↔
      IsStableEquivalence (homotopyFiberLift r' f' N') := by
  have hsq := homotopyFiberSquareMap_isStableEquivalence r r' a o Hr ha ho
  have hn := homotopyFiberLiftNaturalityHomotopy f r f' r' N N' s a o Hf Hr Q
  constructor
  · intro h d
    let := hs d
    apply (isIso_comp_left_iff ((stableHomotopyFunctor d).map s)
      ((stableHomotopyFunctor d).map (homotopyFiberLift r' f' N'))).mp
    rw [← Functor.map_comp, ← hn.stableHomotopyMap_eq d]
    exact (h.comp hsq) d
  · intro h d
    let := hsq d
    apply (isIso_comp_right_iff
      ((stableHomotopyFunctor d).map (homotopyFiberLift r f N))
      ((stableHomotopyFunctor d).map (homotopyFiberSquareMap r r' a o Hr))).mp
    rw [← Functor.map_comp, hn.stableHomotopyMap_eq d]
    exact (hs.comp h) d

include Hf Hr Q in
/-- The original signed connecting maps are natural under the supplied arrow tracks and
whole null square. Only the two original lift maps in this degree need to be invertible. -/
theorem stableFiberLiftConnecting_homotopySquare (d : ℤ)
    [IsIso ((stableHomotopyFunctor d).map (homotopyFiberLift r f N))]
    [IsIso ((stableHomotopyFunctor d).map (homotopyFiberLift r' f' N'))] :
    stableFiberLiftConnecting f r N d ≫ (stableHomotopyFunctor d).map s =
      (stableHomotopyFunctor (d + 1)).map o ≫
        stableFiberLiftConnecting f' r' N' d := by
  have hL :
      (stableHomotopyFunctor d).map s ≫
          (stableHomotopyFunctor d).map (homotopyFiberLift r' f' N') =
        (stableHomotopyFunctor d).map (homotopyFiberLift r f N) ≫
          (stableHomotopyFunctor d).map (homotopyFiberSquareMap r r' a o Hr) := by
    simpa only [Functor.map_comp] using
      (homotopyFiberLiftNaturalityHomotopy f r f' r' N N' s a o Hf Hr Q).stableHomotopyMap_eq d
        |>.symm
  apply (cancel_mono ((stableHomotopyFunctor d).map (homotopyFiberLift r' f' N'))).1
  calc
    (stableFiberLiftConnecting f r N d ≫ (stableHomotopyFunctor d).map s) ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift r' f' N') =
      stableFiberLiftConnecting f r N d ≫
        ((stableHomotopyFunctor d).map s ≫
          (stableHomotopyFunctor d).map (homotopyFiberLift r' f' N')) :=
      Category.assoc _ _ _
    _ = stableFiberConnecting r d ≫
        (stableHomotopyFunctor d).map (homotopyFiberSquareMap r r' a o Hr) := by
      rw [hL, ← Category.assoc, stableFiberLiftConnecting_comp_lift]
    _ = (stableHomotopyFunctor (d + 1)).map o ≫ stableFiberConnecting r' d :=
      (stableFiberConnecting_homotopySquare r r' a o Hr d).symm
    _ = ((stableHomotopyFunctor (d + 1)).map o ≫
        stableFiberLiftConnecting f' r' N' d) ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift r' f' N') := by
      rw [Category.assoc, stableFiberLiftConnecting_comp_lift]

end Quillen.LoopPrespectrum
