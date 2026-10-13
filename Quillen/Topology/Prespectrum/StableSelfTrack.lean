/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackRepresentative
public import Quillen.Topology.Prespectrum.LoopTailOmega
public import Quillen.Topology.Prespectrum.LoopTailReplacementFunctor
public import Quillen.Topology.Prespectrum.StableOmegaBasedDetection
public import Quillen.Topology.Prespectrum.ParameterLoopingStableEquivalence
public import Quillen.Topology.Prespectrum.NullLoopNaturality
public import Quillen.Topology.Prespectrum.FiberHomotopySquare
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# Vanishing of the original null-conjugated self-track on stable degree zero

Only the specified sphere representative is contracted. The original Laurent self-track and
both occurrences of its prescribed chart null path are retained. The actual loop-tail initial
inclusions detect the result: their strict naturality identifies the postcomposed original
track, and the parameter-looped original inclusion is a stable equivalence. No replacement
seed, global relative homotopy, coefficient coherence, or later Bass-iterate conclusion is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- The one-higher obstruction vanishes at each original degree-zero stable stage. Each
representative is contracted separately, with the unchanged null-conjugated loop map. -/
theorem Homotopy.nullLoopMap_stableMap_zero_of_level
    (H : Homotopy f f) (j : F ⟶ G) (N : Homotopy (f ≫ j) (zeroHom E G))
    (hF : ∀ i, Subsingleton (HomotopyGroup.Pi (i + 3) (F.space (i + 2))
      (F.point (i + 2)))) :
    (stableHomotopyFunctor 0).map ((H.postcomp j).nullLoopMap N) = 0 := by
  let a := (H.postcomp j).nullLoopMap N
  change colimMap (stableSystemMap a 0) = 0
  apply colimit.hom_ext
  intro i
  rw [ι_colimMap, comp_zero]
  have hz : (stableSystemMap a 0).app i = 0 := by
    apply AddCommGrpCat.ext
    intro x
    change Additive.ofMul (piMap ((0 : ℤ).toNat + i + 1)
      (a.map ((-(0 : ℤ)).toNat + i + 2))
      (a.map_point ((-(0 : ℤ)).toNat + i + 2)) x.toMul) = 0
    induction x.toMul using Quotient.inductionOn with
    | h p =>
      have hi : Subsingleton (HomotopyGroup.Pi ((0 : ℤ).toNat + i + 1 + 2)
          (F.space ((-(0 : ℤ)).toNat + i + 2))
          (F.point ((-(0 : ℤ)).toNat + i + 2))) := by
        have hd : (0 : ℤ).toNat + i + 1 + 2 = i + 3 := by omega
        have hl : (-(0 : ℤ)).toNat + i + 2 = i + 2 := by omega
        rw [hd, hl]
        exact hF i
      exact congrArg Additive.ofMul (Quotient.sound
        (H.nullLoopMap_genLoop_homotopic_const j N
          ((-(0 : ℤ)).toNat + i + 2) ((0 : ℤ).toNat + i + 1) hi p))
  rw [hz, zero_comp]

/-- The actual stable-equivalent Omega replacement has precisely the one-higher finite
vanishing required for degree-zero sphere self-tracks. -/
theorem loopTailReplacement_selfTrack_obstruction_subsingleton
    (F : LoopPrespectrum.{u}) [∀ n, T1Space (F.space n)]
    (hF : Subsingleton (stableHomotopyGroup F 1)) (i : ℕ) :
    Subsingleton (HomotopyGroup.Pi (i + 3) ((loopTailReplacement F).space (i + 2))
      ((loopTailReplacement F).point (i + 2))) := by
  let := hF
  let : Subsingleton (stableHomotopyGroup (loopTailReplacement F) 1) :=
    (loopTailReplacementStableHomotopyIso F 1).addCommGroupIsoToAddEquiv.symm.injective.subsingleton
  let := stableHomotopyι_isIso_of_isOmega (loopTailReplacement F)
    (loopTailReplacement_isOmega F) 1 i
  have hstage : Subsingleton ((stableSystem (loopTailReplacement F) 1).obj i) :=
    (ConcreteCategory.bijective_of_isIso
      (stableHomotopyι (loopTailReplacement F) 1 i)).injective.subsingleton
  have hd : (1 : ℤ).toNat + i + 2 = i + 3 := by omega
  have hl : (-(1 : ℤ)).toNat + i + 2 = i + 2 := by omega
  change Subsingleton (Additive (HomotopyGroup.Pi ((1 : ℤ).toNat + i + 2)
    ((loopTailReplacement F).space ((-(1 : ℤ)).toNat + i + 2))
    ((loopTailReplacement F).point ((-(1 : ℤ)).toNat + i + 2)))) at hstage
  rw [hd, hl] at hstage
  let := hstage
  refine ⟨fun a b => ?_⟩
  exact congrArg Additive.toMul (Subsingleton.elim (Additive.ofMul a) (Additive.ofMul b))

/-- The original null-conjugated self-track induces zero on stable degree zero if the original
intermediate spectrum has zero stable degree one. The supplied null path is not replaced;
levelwise T1 is used only for the actual stable-equivalent Omega replacements. -/
theorem Homotopy.nullLoopMap_stableMap_zero
    (H : Homotopy f f) (j : F ⟶ G) (N : Homotopy (f ≫ j) (zeroHom E G))
    [∀ n, T1Space (F.space n)] [∀ n, T1Space (G.space n)]
    (hF : Subsingleton (stableHomotopyGroup F 1)) :
    (stableHomotopyFunctor 0).map ((H.postcomp j).nullLoopMap N) = 0 := by
  let α := loopTailReplacementInclusion F
  let β := loopTailReplacementInclusion G
  let j' := loopTailReplacementMap j
  have hs : (f ≫ j) ≫ β = (f ≫ α) ≫ j' := by
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun k => f ≫ k) (loopTailReplacementInclusion_naturality j).symm
  let N' : Homotopy ((f ≫ α) ≫ j') (zeroHom E (loopTailReplacement G)) :=
    (N.postcomp β).cast hs (zeroHom_comp β)
  have he : (H.postcomp j).nullLoopMap N ≫ parameterLoopingMap β =
      ((H.postcomp α).postcomp j').nullLoopMap N' := by
    have h := Homotopy.nullLoopMap_naturality (𝟙 E) β (H.postcomp j)
      ((H.postcomp α).postcomp j') N N' ?_ ?_
    · simpa only [Category.id_comp] using h
    · intro n
      ext z
      exact congrArg (fun k => k.map n (H.level n z))
        (loopTailReplacementInclusion_naturality j).symm
    · intro n
      rfl
  have hz := (H.postcomp α).nullLoopMap_stableMap_zero_of_level j' N'
    (loopTailReplacement_selfTrack_obstruction_subsingleton F hF)
  let := parameterLoopingMap_isStableEquivalence β
    (loopTailReplacementInclusion_isStableEquivalence G) 0
  apply (cancel_mono ((stableHomotopyFunctor 0).map (parameterLoopingMap β))).mp
  rw [← Functor.map_comp, he, hz, zero_comp]

end Quillen.LoopPrespectrum
