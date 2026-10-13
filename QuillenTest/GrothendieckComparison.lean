/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.GrothendieckComparison.Functor

/-! Consumers of the genuine natural comparison, on arbitrary homotopical K₀
classes and the original object generators and conflation relations. -/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Quillen
namespace QuillenTest.GrothendieckComparison

open Quillen
variable {C D : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
  (E : ExactStructure C) (ED : ExactStructure D)

/-- Every actual topological K₀ class has exactly one classical Grothendieck class. -/
theorem unique_classical_representative (x : E.K 0) :
    ∃! a : Multiplicative E.GrothendieckGroup, E.grothendieckToKZero a = x := by
  obtain ⟨a, ha⟩ := E.grothendieckToKZero_surjective x
  exact ⟨a, ha, fun b hb ↦ E.grothendieckToKZero_injective (hb.trans ha.symm)⟩

/-- The inverse naturality square now applies to every actual K₀ class. -/
theorem inverse_naturality_on_all_classes (F : ExactFunctor E ED) (x : E.K 0) :
    ED.kZeroToGrothendieck (F.KMap 0 x) =
      F.grothendieckMap.toMultiplicative (E.kZeroToGrothendieck x) :=
  (DFunLike.congr_fun F.kZeroToGrothendieck_naturality x).symm

/-- The actual inverse retains the sign of every original conflation relation. -/
theorem inverse_conflation_difference {S : ShortComplex C} (hS : E.conflation S) :
    E.grothendieckKZeroEquiv.symm
      (E.kZeroObjectClass S.X₂ * (E.kZeroObjectClass S.X₁)⁻¹) =
        Multiplicative.ofAdd (E.grothendieckClass S.X₃) := by
  change E.kZeroToGrothendieck _ = _
  simp only [map_mul, map_inv, E.kZeroToGrothendieck_objectClass]
  rw [E.grothendieckClass_additive hS]
  change Multiplicative.ofAdd
    (E.grothendieckClass S.X₁ + E.grothendieckClass S.X₃ - E.grothendieckClass S.X₁) = _
  congr 1
  abel

/-- Homomorphisms out of genuine K₀ are determined by the original object loops. -/
theorem actual_kZero_hom_ext {A : Type*} [Group A] (f g : E.K 0 →* A)
    (h : ∀ X : C, f (E.kZeroObjectClass X) = g (E.kZeroObjectClass X)) : f = g := by
  have he : f.comp E.grothendieckToKZero = g.comp E.grothendieckToKZero := by
    apply E.grothendieck_mulHom_ext
    intro X
    simpa using h X
  apply MonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := E.grothendieckToKZero_surjective x
  exact DFunLike.congr_fun he a

/-- The bundled natural-isomorphism triangle holds on arbitrary genuine K₀ elements. -/
theorem bundled_inverse_triangle (B : SmallExactCategory.{u}) (x : B.exactStructure.K 0) :
    (SmallExactCategory.grothendieckKZeroIso.hom.app B)
      ((SmallExactCategory.grothendieckKZeroIso.inv.app B) x) = x := by
  exact DFunLike.congr_fun B.exactStructure.grothendieckToKZero_comp_retraction x

end QuillenTest.GrothendieckComparison
