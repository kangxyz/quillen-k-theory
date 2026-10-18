/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Field.FiniteFieldKTwo
public import Mathlib.Algebra.Field.ZMod

/-!
# Finite-field Quillen G2 clients at the original native and public scheme endpoints

The source field and both chosen-model universes remain explicit. No external
perfectness, kernel-generation, symbol-marking or Matsumoto premise is supplied.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace Consumer.FiniteFieldKTwo

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A public coherent class maps to the neutral native lower class by the original affine map. -/
theorem originalAffineCoordinates (F : Type u) [Field F] [Finite F]
    (a : Scheme.Modules.Coherent.G (Spec (CommRingCat.of F)) 2) :
    Scheme.Modules.Coherent.publicSpecGRingEquiv (CommRingCat.of F) 2 a = 1 ∧ a = 1 :=
  ⟨Quillen.Field.finiteModuleGTwo_eq_one F _, Quillen.Field.specGTwo_eq_one F a⟩

/-- The literal lower and public G2 groups vanish for an arbitrary finite field. -/
theorem generalFiniteField (F : Type u) [Field F] [Finite F]
    (a : Quillen.FiniteModuleLocalization.G F 2)
    (b : Scheme.Modules.Coherent.G (Spec (CommRingCat.of F)) 2) : a = 1 ∧ b = 1 :=
  ⟨Quillen.Field.finiteModuleGTwo_eq_one F a, Quillen.Field.specGTwo_eq_one F b⟩

/-- The smallest two fields have the original lower G2 endpoint, without auxiliary premises. -/
theorem smallFieldsLower :
    Subsingleton (Quillen.FiniteModuleLocalization.G (ZMod 2) 2) ∧
      Subsingleton (Quillen.FiniteModuleLocalization.G (ZMod 3) 2) :=
  ⟨Quillen.Field.finiteModuleGTwo_subsingleton (ZMod 2),
    Quillen.Field.finiteModuleGTwo_subsingleton (ZMod 3)⟩

/-- The field with five elements uses the actual public coherent group on its spectrum. -/
theorem fiveElementPublic
    (a : Scheme.Modules.Coherent.G (Spec (CommRingCat.of (ZMod 5))) 2) : a = 1 :=
  Quillen.Field.specGTwo_eq_one (ZMod 5) a

end Consumer.FiniteFieldKTwo
