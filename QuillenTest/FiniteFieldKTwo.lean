/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Quillen.KTheory.Field.FiniteFieldKTwo
import Mathlib.Algebra.Field.ZMod

/-! Actual finite-field Quillen endpoints, including the smallest fields and public scheme G2. -/

noncomputable section
open CategoryTheory CategoryTheory.ExactCategory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace QuillenTest.FiniteFieldKTwo

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Every original native lower-module endpoint is trivial over F2, F3 and F5. -/
theorem smallFieldsLowerGTwo :
    Subsingleton (Quillen.FiniteModuleLocalization.G (ZMod 2) 2) ∧
      Subsingleton (Quillen.FiniteModuleLocalization.G (ZMod 3) 2) ∧
        Subsingleton (Quillen.FiniteModuleLocalization.G (ZMod 5) 2) :=
  ⟨Quillen.Field.finiteModuleGTwo_subsingleton (ZMod 2),
    Quillen.Field.finiteModuleGTwo_subsingleton (ZMod 3),
    Quillen.Field.finiteModuleGTwo_subsingleton (ZMod 5)⟩

/-- The literal public coherent groups vanish over each of the same three fields. -/
theorem smallFieldsPublicGTwo
    (a : Scheme.Modules.Coherent.G (Spec (CommRingCat.of (ZMod 2))) 2)
    (b : Scheme.Modules.Coherent.G (Spec (CommRingCat.of (ZMod 3))) 2)
    (c : Scheme.Modules.Coherent.G (Spec (CommRingCat.of (ZMod 5))) 2) :
    a = 1 ∧ b = 1 ∧ c = 1 :=
  ⟨Quillen.Field.specGTwo_eq_one (ZMod 2) a,
    Quillen.Field.specGTwo_eq_one (ZMod 3) b,
    Quillen.Field.specGTwo_eq_one (ZMod 5) c⟩

/-- The general finite-field interface requires neither fiber perfectness nor a stage premise. -/
theorem generalFiniteField (F : Type u) [Field F] [Finite F] :
    Subsingleton ((Quillen.FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 2) ∧
      Subsingleton ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2) ∧
        Subsingleton (Quillen.FiniteModuleLocalization.G F 2) ∧
          Subsingleton (Scheme.Modules.Coherent.G (Spec (CommRingCat.of F)) 2) :=
  ⟨Quillen.Field.rightProjectiveKTwo_subsingleton F,
    Quillen.Field.upperModuleKTwo_subsingleton F,
    Quillen.Field.finiteModuleGTwo_subsingleton F,
    Quillen.Field.specGTwo_subsingleton F⟩

end QuillenTest.FiniteFieldKTwo
