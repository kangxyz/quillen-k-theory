/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackNullEvaluation
public import Quillen.Topology.Prespectrum.SelfTrackStableNaturality

/-!
# Stable evaluation of the original null-conjugated self-track map

The original null-loop map, followed by the existing integer-graded loop
shift, is the self-track operation. The comparison retains the same original
finite stage, alternating sign, integer reindexing, and canonical stage leg.
Postcomposition therefore gives the factorization of the original supplied
null-loop map, including the original mapping-cone loop transition.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- The original stable stage map followed by actual loop uncurrying is the same stage operation. -/
theorem Homotopy.nullLoopMap_stableStage (H : Homotopy f f)
    (N : Homotopy f (zeroHom E F)) (d : ℤ) (n : ℕ) :
    (stableSystemMap (H.nullLoopMap N) d).app n ≫ (parameterStableStageIso F d n).hom =
      H.stableStageOperation d n := by
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (H.nullLoopMap_piMap N ((-d).toNat + n + 2) (d.toNat + n + 1) (Additive.toMul a))

/-- The exact original stage evaluation retains its common sign and integer reindexing. -/
@[reassoc] theorem Homotopy.nullLoopMap_correctedStableStage (H : Homotopy f f)
    (N : Homotopy f (zeroHom E F)) (d : ℤ) (n : ℕ) :
    (stableSystemMap (H.nullLoopMap N) d).app n ≫
        (CategoryTheory.Limits.SequentialSystem.alternatingIso n
          (parameterStableStageIso F d n)).hom ≫
          (shiftedStableReindexIso F d n).hom =
      ((-1 : ℤ) ^ n • H.stableStageOperation d n) ≫
        (shiftedStableReindexIso F d n).hom := by
  rw [CategoryTheory.Limits.SequentialSystem.alternatingIso_hom, ← Category.assoc,
    Preadditive.comp_zsmul, H.nullLoopMap_stableStage]

/-- The original supplied-null map evaluates to the actual integer-graded self-track operation. -/
theorem Homotopy.nullLoopMap_stableHomotopy (H : Homotopy f f)
    (N : Homotopy f (zeroHom E F)) (d : ℤ) :
    (stableHomotopyFunctor d).map (H.nullLoopMap N) ≫ (parameterStableHomotopyIso F d).hom =
      H.stableOperation d := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι E d n ≫
      ((stableHomotopyFunctor d).map (H.nullLoopMap N) ≫ (parameterStableHomotopyIso F d).hom) =
    stableHomotopyι E d n ≫ H.stableOperation d
  rw [← Category.assoc, stableHomotopyι_naturality, Category.assoc,
    parameterStableHomotopyIso_ι_hom, H.nullLoopMap_correctedStableStage_assoc,
    H.stableOperation_ι]

/-- Postcomposition retains the original target map and the specified original nullhomotopy. -/
theorem Homotopy.nullLoopMap_stableHomotopy_postcomp (H : Homotopy f f) (j : F ⟶ G)
    (N : Homotopy (f ≫ j) (zeroHom E G)) (d : ℤ) :
    (stableHomotopyFunctor d).map ((H.postcomp j).nullLoopMap N) ≫
        (parameterStableHomotopyIso G d).hom =
      H.stableOperation d ≫ (stableHomotopyFunctor (d + 1)).map j :=
  ((H.postcomp j).nullLoopMap_stableHomotopy N d).trans (H.stableOperation_postcomp j d)

/-- The original mapping-cone loop transition has the original stable inclusion factorization. -/
theorem mappingConeLoopTransition_stableHomotopy (f : E ⟶ F) (H : Homotopy f f) (d : ℤ) :
    (stableHomotopyFunctor d).map (mappingConeLoopTransition f H) ≫
        (parameterStableHomotopyIso (mappingCone f) d).hom =
      H.stableOperation d ≫ (stableHomotopyFunctor (d + 1)).map (mappingConeInclusion f) :=
  H.nullLoopMap_stableHomotopy_postcomp (mappingConeInclusion f) (mappingConeHomotopy f) d

end Quillen.LoopPrespectrum
