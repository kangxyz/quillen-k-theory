/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Additivity.BasedAdditivity
public import Quillen.Waldhausen.QuillenComparison.ExactNaturality
public import Quillen.Waldhausen.GilletWaldhausen.AdjacentTruncation
public import Quillen.Waldhausen.GilletWaldhausen.FixedBounds
public import Quillen.Waldhausen.ExtensionCategory.KEquivalence

/-! Downstream contracts for the actual additivity and acyclic-filtration interfaces. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.Additivity Quillen.Waldhausen.GilletWaldhausen
universe u v
namespace Consumer

section Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
  {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- Both endpoints are the original realization maps. This is explicitly unbased. -/
def actual_additivity_homotopy :
    (deloopingMap hs.exactG).hom.Homotopy
      (deloopingMap (sumFunctor_isExact V W hs.exactH hs.exactF)).hom :=
  additivityHomotopy V W a b hs
/-- The based result retains both original canonical K-maps, including n=0. -/
theorem actual_canonical_K_additivity (n : ℕ) :
    Waldhausen.KMap hs.exactG n =
      Waldhausen.KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n :=
  KMap_additivity V W a b hs n
end Additivity

section ExactNaturality
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- Canonical Q/S naturality uses both original K-map APIs. -/
theorem canonical_QS_naturality (n : ℕ) :
    (QuillenComparison.comparisonKEquiv ED n).toMonoidHom.comp (Waldhausen.KMap F.waldhausenExact n)
      =
      (F.KMap n).comp (QuillenComparison.comparisonKEquiv EC n).toMonoidHom :=
  QuillenComparison.comparisonKEquiv_exactFunctor_naturality F n
end ExactNaturality

section AcyclicFiltration
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The adjacent truncation sequence has a derived genuine relative condition. -/
theorem actual_adjacent_cofibration_sequence (n : ℤ) :
    IsCofibrationSequence (complexSubcategory (boundedAcyclic P))
      (complexSubcategory (boundedAcyclic P))
      (adjacentTruncationInclusion P n) (adjacentTruncationProjection P n) :=
  adjacentTruncation_isCofibrationSequence_quasiIso P n

/-- The upper endpoint is a natural iso whose forward map remains the actual inclusion. -/
def actual_fixed_bound_endpoint (a b n : ℤ) (hn : b ≤ n) :
    (fixedAcyclicBounds P a b).ι ⋙ boundedAcyclicTruncLEFunctor P n ≅
      (fixedAcyclicBounds P a b).ι := fixedBoundsTruncLEIdentityIso P a b n hn
end AcyclicFiltration

section ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)
/-- The actual extension category requires only the original Waldhausen structure. -/
def genuine_extension_structure : Structure (ExtensionCategory.Obj W) :=
  ExtensionCategory.waldhausenStructure W
/-- Exactness and the cofiber squares are derived, not supplied by the downstream user. -/
theorem genuine_extension_sequence :
    IsCofibrationSequence (ExtensionCategory.waldhausenStructure W) W
      (ExtensionCategory.inclusion W) (ExtensionCategory.quotient W) :=
  ExtensionCategory.isCofibrationSequence W
end ExtensionCategory

section ExtensionRealization
variable {C : Type u} [Category.{u} C] (W : Structure C)
/-- The target is the actual product-category S-model in the honest universe scope. -/
def actual_extension_realization_equivalence : ContinuousMap.HomotopyEquiv
    (ExtensionCategory.waldhausenStructure W).Delooping
      (ExtensionCategory.productStructure W W).Delooping :=
  ExtensionCategory.realizationHomotopyEquiv W
/-- The forward map is literally the prescribed source/cofiber map. -/
theorem actual_extension_realization_forward :
    (actual_extension_realization_equivalence W).toFun =
      (deloopingMap (ExtensionCategory.sourceCofiber_exact W)).hom := rfl
/-- Original source/cofiber and split K-maps are the exact two directions. -/
def actual_extension_K_equivalence (n : ℕ) :
    (ExtensionCategory.waldhausenStructure W).K n ≃*
      (ExtensionCategory.productStructure W W).K n := ExtensionCategory.KEquiv W n

theorem actual_extension_K_forward (n : ℕ) :
    (actual_extension_K_equivalence W n).toMonoidHom =
      Waldhausen.KMap (ExtensionCategory.sourceCofiber_exact W) n := rfl

theorem actual_extension_K_inverse (n : ℕ) :
    (actual_extension_K_equivalence W n).symm.toMonoidHom = ExtensionCategory.splitKMap W n :=
  ExtensionCategory.KEquiv_symm_toMonoidHom W n
end ExtensionRealization

end Consumer
