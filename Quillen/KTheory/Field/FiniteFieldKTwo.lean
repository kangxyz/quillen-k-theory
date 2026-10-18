/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Field.MilnorKTwoSurjectivity
public import Quillen.KTheory.Plus.StableFiberPerfectness
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.UniverseComparison

/-!
# Actual Quillen K2 and coherent G2 of finite fields

Proved perfectness of the actual stable completion fiber supplies a local
instance to the original Milnor-to-Quillen comparison. The existing all-rank
kernel generation and finite-field Milnor vanishing then make the original
right-projective and upper finite-module K2 groups trivial.

The native lower group uses the canonical smallKUniverseEquiv for the SAME
finite-module category with carrier universe u. The literal public coherent
group on Spec F then uses publicSpecGRingEquiv into that original lower group,
retaining original global-sections and model-comparison maps. No larger-carrier
module category or replacement group is used. Every finite field is covered,
including F2 and F3. No external perfectness or generation hypothesis, Matsumoto
injectivity, or positive scalar-product marking is required here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Field
open FiniteProjectiveModule.StableCompletion
variable (F : Type u) [Field F] [Finite F]

/-- The original right-projective Quillen K2 group of every finite field has one element. -/
theorem rightProjectiveKTwo_subsingleton :
    Subsingleton ((FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 2) := by
  let : Group.IsPerfect (StableFiberPiOne F) := stableFiberPiOne_isPerfect F
  exact rightProjectiveKTwo_subsingleton_of_finite_of_fiberPerfect F

/-- Every class in the original right-projective K2 group is neutral. -/
theorem rightProjectiveKTwo_eq_one
    (a : (FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 2) : a = 1 :=
  @Subsingleton.elim _ (rightProjectiveKTwo_subsingleton F) a 1

/-- The actual upper finite-module K2 group of every finite field has one element. -/
theorem upperModuleKTwo_subsingleton :
    Subsingleton ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2) := by
  let : Group.IsPerfect (StableFiberPiOne F) := stableFiberPiOne_isPerfect F
  exact upperModuleKTwo_subsingleton_of_finite_of_fiberPerfect F

/-- Every class in the actual upper finite-module K2 group is neutral. -/
theorem upperModuleKTwo_eq_one
    (a : (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2) : a = 1 :=
  @Subsingleton.elim _ (upperModuleKTwo_subsingleton F) a 1

/-- The original lower finite-module G2 group is trivial via its canonical upper-model map. -/
theorem finiteModuleGTwo_subsingleton :
    Subsingleton (FiniteModuleLocalization.G F 2) := by
  constructor
  intro a b
  apply ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallKUniverseEquiv.{u, u + 1} 2).injective
  exact @Subsingleton.elim _ (upperModuleKTwo_subsingleton F) _ _

/-- Every class in the original native lower finite-module G2 group is neutral. -/
theorem finiteModuleGTwo_eq_one (a : FiniteModuleLocalization.G F 2) : a = 1 :=
  @Subsingleton.elim _ (finiteModuleGTwo_subsingleton F) a 1

/-- The literal public coherent G2 group on Spec F is trivial via the original affine map. -/
theorem specGTwo_subsingleton :
    Subsingleton (Scheme.Modules.Coherent.G (Spec (CommRingCat.of F)) 2) := by
  constructor
  intro a b
  apply (Scheme.Modules.Coherent.publicSpecGRingEquiv (CommRingCat.of F) 2).injective
  exact @Subsingleton.elim _ (finiteModuleGTwo_subsingleton F) _ _

/-- Every class in the literal public coherent G2 group of Spec F is neutral. -/
theorem specGTwo_eq_one
    (a : Scheme.Modules.Coherent.G (Spec (CommRingCat.of F)) 2) : a = 1 :=
  @Subsingleton.elim _ (specGTwo_subsingleton F) a 1

end Quillen.Field
