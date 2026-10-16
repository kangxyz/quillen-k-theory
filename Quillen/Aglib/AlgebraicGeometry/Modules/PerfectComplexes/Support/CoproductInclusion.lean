/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Strict
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Perfect

/-!
# Forgetting support and binary coproducts

The actual supported full-subcategory inclusion retains its underlying complexes, chain maps and selected coproduct comparison.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.OpenFunctorNaturality
open Waldhausen 

variable {U X V Y : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The actual full-subcategory inclusion forgetting support. -/
def supportInclusion : (perfectSupported j).FullSubcategory ⥤ Perfect X :=
  ObjectProperty.ιOfLE (show perfectSupported j ≤ locallyPerfect X from fun _ h => h.1)

instance supportInclusion_additive : (supportInclusion j).Additive := by
  unfold supportInclusion
  infer_instance

instance supportInclusion_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (supportInclusion j) := by
  let : PreservesBinaryBiproducts (supportInclusion j) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact preservesBinaryCoproducts_of_preservesBinaryBiproducts _

end Quillen.PerfectComplexes.OpenFunctorNaturality

end

end
