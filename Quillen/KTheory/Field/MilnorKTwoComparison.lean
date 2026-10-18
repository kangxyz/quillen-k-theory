/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Algebra.Group.StableSteinbergRankTwo
public import Quillen.KTheory.Field.SteinbergFiberNaturality
public import Quillen.KTheory.Field.SteinbergFiberSurjectivity
public import Quillen.KTheory.Field.ScalarExtensionComparison
public import Quillen.Aglib.KTheory.MilnorK.K2.FiniteField

/-!
# Canonical Milnor K2 maps to the original Quillen groups

The supplied uniform Milnor group maps through its existing ordered
Steinberg-kernel map and the original stable-fiber comparison to Quillen K2
of finite projective right modules. The actual upper finite-module map then
uses the original right-projective-to-upper-module equivalence explicitly.
Ordered tuples retain the original torus defects, and the original field
extension maps commute with both comparisons in the stated common universe.

Surjectivity is stated here with two explicit hypotheses: perfectness of the
actual stable-fiber fundamental group and containment of the full Steinberg
kernel in its original rank-two stage. Under those hypotheses, the supplied
finite-field Milnor vanishing makes the actual right-projective and upper
finite-module K2 groups subsingleton. The subsequent `MilnorKTwoSurjectivity`
module discharges stage containment using actual all-rank kernel generation;
fiber perfectness remains an explicit input. No unconditional finite-field
Quillen vanishing, injectivity, Matsumoto equivalence, or positive unit-product
marking is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory

namespace Quillen.Field
open FiniteProjectiveModule.StableCompletion
attribute [local instance] StableSteinberg.kernelCommGroup
variable (F : Type u) [Field F]

/-- The existing uniform Milnor map followed by the original right-projective K2 map. -/
def milnorToRightProjectiveKTwo : MilnorK.K F 2 →+
    Additive ((FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 2) :=
  (steinbergKernelToRightProjectiveKTwo F).toAdditive.comp (StableSteinberg.milnorToKernel F)

/-- The upper finite-module map explicitly uses the original projective/module equivalence. -/
def milnorToUpperModuleKTwo : MilnorK.K F 2 →+
    Additive ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2) :=
  (rightProjectiveUpperModuleKEquiv F 2).toMonoidHom.toAdditive.comp
    (milnorToRightProjectiveKTwo F)

/-- The projective map retains exactly its two original composed maps. -/
theorem milnorToRightProjectiveKTwo_apply (a : MilnorK.K F 2) :
    milnorToRightProjectiveKTwo F a = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.milnorToKernel F a).toMul) := rfl

/-- The finite-module map retains the explicit upper-model equivalence. -/
theorem milnorToUpperModuleKTwo_apply (a : MilnorK.K F 2) :
    milnorToUpperModuleKTwo F a = Additive.ofMul
      (rightProjectiveUpperModuleKEquiv F 2 (milnorToRightProjectiveKTwo F a).toMul) := rfl

/-- Every ordered tuple maps to the original kernel-valued ordered torus defect. -/
theorem milnorToRightProjectiveKTwo_symbol (a : MilnorK.SymbolTuple F 2) :
    milnorToRightProjectiveKTwo F (MilnorK.symbol a) = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F
        (StableSteinberg.torusDefectKernel (a 0) (a 1))) := by
  rw [milnorToRightProjectiveKTwo_apply, StableSteinberg.milnorToKernel_symbol]
  rfl

/-- The ordered pair has its literal original torus-defect value in right-projective K2. -/
theorem milnorToRightProjectiveKTwo_pair (a b : Fˣ) :
    milnorToRightProjectiveKTwo F (MilnorK.symbol ![a, b]) = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) :=
  milnorToRightProjectiveKTwo_symbol F ![a, b]

/-- The actual upper-model value is the original ordered defect under the explicit equivalence. -/
theorem milnorToUpperModuleKTwo_symbol (a : MilnorK.SymbolTuple F 2) :
    milnorToUpperModuleKTwo F (MilnorK.symbol a) = Additive.ofMul
      (rightProjectiveUpperModuleKEquiv F 2
        (steinbergKernelToRightProjectiveKTwo F
          (StableSteinberg.torusDefectKernel (a 0) (a 1)))) := by
  rw [milnorToUpperModuleKTwo_apply, milnorToRightProjectiveKTwo_symbol]
  rfl

/-- The ordered upper-model pair retains the same original torus defect and equivalence. -/
theorem milnorToUpperModuleKTwo_pair (a b : Fˣ) :
    milnorToUpperModuleKTwo F (MilnorK.symbol ![a, b]) = Additive.ofMul
      (rightProjectiveUpperModuleKEquiv F 2
        (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b))) :=
  milnorToUpperModuleKTwo_symbol F ![a, b]

/-- Undoing the upper model exposes the original inclusion and opposite-ring restriction maps. -/
theorem milnorToUpperModuleKTwo_toOriginal (a : MilnorK.K F 2) :
    ExactFunctor.commonAmbientKMap
      ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallModelToOriginal.{u + 1})
      2 (milnorToUpperModuleKTwo F a).toMul =
      (finiteModuleRingExact (RingEquiv.toOpposite F)).KMap 2
        ((FiniteProjectiveModule.toFiniteModuleExact Fᵐᵒᵖ).KMap 2
          (milnorToRightProjectiveKTwo F a).toMul) :=
  rightProjectiveUpperModuleKEquiv_toOriginal F 2 _

variable {F} {L : Type u} [Field L] (f : F →+* L)

/-- The two existing kernel field maps are the same restriction of the original Steinberg map. -/
theorem steinbergKernelMap_eq_toElementaryKernelMap :
    steinbergKernelMap f = StableSteinberg.toElementaryKernelMap f := by
  ext a
  rfl

/-- The original right-projective scalar extension commutes with the canonical Milnor map. -/
theorem milnorToRightProjectiveKTwo_naturality (a : MilnorK.K F 2) :
    ((FiniteProjectiveModule.rightBaseChangeExact f).KMap 2).toAdditive
        (milnorToRightProjectiveKTwo F a) =
      milnorToRightProjectiveKTwo L (MilnorK.mapAdd 2 f a) := by
  have hk : (steinbergKernelMap f).toAdditive (StableSteinberg.milnorToKernel F a) =
      StableSteinberg.milnorToKernel L (MilnorK.mapAdd 2 f a) := by
    rw [steinbergKernelMap_eq_toElementaryKernelMap]
    exact DFunLike.congr_fun (StableSteinberg.milnorToKernel_naturality f) a
  change ((FiniteProjectiveModule.rightBaseChangeExact f).KMap 2).toAdditive
      ((steinbergKernelToRightProjectiveKTwo F).toAdditive
        (StableSteinberg.milnorToKernel F a)) =
    (steinbergKernelToRightProjectiveKTwo L).toAdditive
      (StableSteinberg.milnorToKernel L (MilnorK.mapAdd 2 f a))
  calc
    _ = (steinbergKernelToRightProjectiveKTwo L).toAdditive
        ((steinbergKernelMap f).toAdditive (StableSteinberg.milnorToKernel F a)) :=
      congrArg Additive.ofMul (steinbergKernelToRightProjectiveKTwo_naturality f
        (StableSteinberg.milnorToKernel F a).toMul)
    _ = _ := congrArg (steinbergKernelToRightProjectiveKTwo L).toAdditive hk

/-- Homomorphism form of the original right-projective field-extension square. -/
theorem milnorToRightProjectiveKTwo_naturality_hom :
    (((FiniteProjectiveModule.rightBaseChangeExact f).KMap 2).toAdditive).comp
        (milnorToRightProjectiveKTwo F) =
      (milnorToRightProjectiveKTwo L).comp (MilnorK.mapAdd 2 f) := by
  apply AddMonoidHom.ext
  intro a
  exact milnorToRightProjectiveKTwo_naturality f a

/-- Literal tensor extension and the original upper-model transport give the actual
finite-module square. -/
theorem milnorToUpperModuleKTwo_naturality (a : MilnorK.K F 2) :
    ((finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive
        (milnorToUpperModuleKTwo F a) =
      milnorToUpperModuleKTwo L (MilnorK.mapAdd 2 f a) := by
  have h := congrArg Additive.toMul (milnorToRightProjectiveKTwo_naturality f a)
  change (FiniteProjectiveModule.rightBaseChangeExact f).KMap 2
      (milnorToRightProjectiveKTwo F a).toMul =
    (milnorToRightProjectiveKTwo L (MilnorK.mapAdd 2 f a)).toMul at h
  exact congrArg Additive.ofMul
    ((rightProjectiveUpperModuleKEquiv_baseChange f 2
      (milnorToRightProjectiveKTwo F a).toMul).symm.trans
      (congrArg (rightProjectiveUpperModuleKEquiv L 2) h))

/-- Homomorphism form of the original upper finite-module field-extension square. -/
theorem milnorToUpperModuleKTwo_naturality_hom :
    (((finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive).comp
        (milnorToUpperModuleKTwo F) =
      (milnorToUpperModuleKTwo L).comp (MilnorK.mapAdd 2 f) := by
  apply AddMonoidHom.ext
  intro a
  exact milnorToUpperModuleKTwo_naturality f a

variable (F)

/-- Explicit perfectness and stage containment imply surjectivity of the original projective map. -/
theorem milnorToRightProjectiveKTwo_surjective [Group.IsPerfect (StableFiberPiOne F)]
    (hstage : (StableSteinberg.toElementary F).ker ≤ StableSteinberg.stage F 2) :
    Function.Surjective (milnorToRightProjectiveKTwo F) := by
  have hs : Function.Surjective (steinbergKernelToRightProjectiveKTwo F).toAdditive := by
    intro a
    obtain ⟨b, hb⟩ := steinbergKernelToRightProjectiveKTwo_surjective F a.toMul
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  exact hs.comp
    ((StableSteinberg.KernelGeneration.milnorToKernel_surjective_iff_kernel_le_stage_two).2 hstage)

/-- The same two hypotheses give surjectivity after the explicit actual upper-module equivalence. -/
theorem milnorToUpperModuleKTwo_surjective [Group.IsPerfect (StableFiberPiOne F)]
    (hstage : (StableSteinberg.toElementary F).ker ≤ StableSteinberg.stage F 2) :
    Function.Surjective (milnorToUpperModuleKTwo F) := by
  intro a
  obtain ⟨b, hb⟩ := milnorToRightProjectiveKTwo_surjective F hstage
    (Additive.ofMul ((rightProjectiveUpperModuleKEquiv F 2).symm a.toMul))
  refine ⟨b, ?_⟩
  rw [milnorToUpperModuleKTwo_apply, hb]
  exact congrArg Additive.ofMul ((rightProjectiveUpperModuleKEquiv F 2).apply_symm_apply a.toMul)

/-- Finite Milnor vanishing gives actual right-projective K2 triviality under BOTH hypotheses. -/
theorem rightProjectiveKTwo_subsingleton_of_finite [Finite F]
    [Group.IsPerfect (StableFiberPiOne F)]
    (hstage : (StableSteinberg.toElementary F).ker ≤ StableSteinberg.stage F 2) :
    Subsingleton ((FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 2) := by
  constructor
  intro a b
  obtain ⟨x, hx⟩ := milnorToRightProjectiveKTwo_surjective F hstage (Additive.ofMul a)
  obtain ⟨y, hy⟩ := milnorToRightProjectiveKTwo_surjective F hstage (Additive.ofMul b)
  exact congrArg Additive.toMul (hx.symm.trans
    ((congrArg (milnorToRightProjectiveKTwo F) (Subsingleton.elim x y)).trans hy))

/-- The actual upper finite-module K2 group is likewise trivial under the same TWO hypotheses. -/
theorem upperModuleKTwo_subsingleton_of_finite [Finite F]
    [Group.IsPerfect (StableFiberPiOne F)]
    (hstage : (StableSteinberg.toElementary F).ker ≤ StableSteinberg.stage F 2) :
    Subsingleton ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2) := by
  constructor
  intro a b
  apply (rightProjectiveUpperModuleKEquiv F 2).symm.injective
  exact @Subsingleton.elim _ (rightProjectiveKTwo_subsingleton_of_finite F hstage) _ _

end Quillen.Field
