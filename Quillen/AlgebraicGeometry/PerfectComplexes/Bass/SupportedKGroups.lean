/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedGroups

/-!
# Original nonnegative supported K-groups as additive pair functors

The original supported K-groups and arbitrary commutative open-pair pullbacks form additive
functors in every nonnegative degree. The zero-degree functor is the unchanged original base
of the supported Bass recursion. Only ambient quasi-compactness is built into the pair category;
no compactness of the removed open is imposed by this functor construction.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.Bass
attribute [local instance] Waldhausen.Additivity.KCommGroup

/-- Original supported K-groups with their actual arbitrary pair pullback maps. -/
def supportedKAddFunctor (n : ℕ) :
    Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj A := AddCommGrpCat.of (Additive (PerfectSupportedK A.unop.obj.obj.hom n))
  map f := AddCommGrpCat.ofHom (perfectSupportedKPullback f.unop n).toAdditive
  map_id A := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive (perfectSupportedKPullback_id A.unop n)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive (perfectSupportedKPullback_comp g.unop f.unop n)

/-- Degree zero retains the original supported Bass recursion base, with every original map. -/
def supportedKAddFunctorZeroIso : supportedKAddFunctor.{u} 0 ≅ supportedKZeroFunctor :=
  Iso.refl _

end Quillen.PerfectComplexes.Bass
