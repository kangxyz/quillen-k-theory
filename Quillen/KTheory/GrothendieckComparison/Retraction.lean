/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.KTheory.GrothendieckComparison.Factorization
public import Quillen.Topology.ClassifyingSpace.CompletionRetraction

/-!
# A retraction from genuine Quillen K₀ to the Grothendieck group

Realizing the localization functor from Q to its actual groupoid completion
and using the fundamental-group theorem for groupoids constructs a retraction
of the original Grothendieck comparison. In particular, distinct Grothendieck
classes remain distinct in the actual homotopical K₀. Surjectivity of the
original comparison is a separate edge-path generation theorem.
-/
@[expose] public section

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Apply the generic topological retraction to the Q-category, with the
original genuine K₀/fundamental-group identification. -/
def kZeroToQGroupoid : E.K 0 →* E.qGroupoidZeroGroup :=
  (classifyingGroupoidCompletionRetraction E.QCategory E.qZero).comp
    E.kZeroFundamentalGroupEquiv.toMonoidHom

/-- The generic retraction is a left inverse to the original completed-Q-loop map. -/
@[simp] theorem kZeroToQGroupoid_comp :
    E.kZeroToQGroupoid.comp E.qGroupoidToKZero = MonoidHom.id E.qGroupoidZeroGroup := by
  apply MonoidHom.ext
  intro a
  change classifyingGroupoidCompletionRetraction E.QCategory E.qZero
    (E.kZeroFundamentalGroupEquiv
      (E.kZeroFundamentalGroupEquiv.symm
        (classifyingGroupoidCompletionMap E.QCategory E.qZero a))) = a
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (classifyingGroupoidCompletionRetraction_comp E.QCategory E.qZero) a

/-- The topological retraction preserves the original canonical object loops. -/
@[simp] lemma kZeroToQGroupoid_objectClass (X : C) :
    E.kZeroToQGroupoid (E.kZeroObjectClass X) = E.qObjectClass E.toQGroupoid X := by
  rw [← E.qGroupoidToKZero_objectClass]
  exact DFunLike.congr_fun E.kZeroToQGroupoid_comp _

/-- The original classical Grothendieck group is a retract of actual Quillen K₀. -/
def kZeroToGrothendieck : E.K 0 →* Multiplicative E.GrothendieckGroup :=
  E.grothendieckQGroupoidEquiv.symm.toMonoidHom.comp E.kZeroToQGroupoid

@[simp] lemma kZeroToGrothendieck_objectClass (X : C) :
    E.kZeroToGrothendieck (E.kZeroObjectClass X) =
      Multiplicative.ofAdd (E.grothendieckClass X) := by
  change E.qGroupoidToGrothendieck (E.kZeroToQGroupoid (E.kZeroObjectClass X)) = _
  simp

/-- The topological-to-classical map is a left inverse to the original canonical comparison. -/
@[simp] theorem kZeroToGrothendieck_comp :
    E.kZeroToGrothendieck.comp E.grothendieckToKZero =
      MonoidHom.id (Multiplicative E.GrothendieckGroup) := by
  apply E.grothendieck_mulHom_ext
  intro X
  simp

/-- The original comparison into actual homotopical K₀ is injective. -/
theorem grothendieckToKZero_injective : Function.Injective E.grothendieckToKZero := by
  intro a b h
  have hab := congrArg E.kZeroToGrothendieck h
  simpa only [← MonoidHom.comp_apply, E.kZeroToGrothendieck_comp, MonoidHom.id_apply] using hab

/-- Every classical class is attained by the topological-to-classical retraction. -/
theorem kZeroToGrothendieck_surjective : Function.Surjective E.kZeroToGrothendieck := by
  intro a
  exact ⟨E.grothendieckToKZero a, DFunLike.congr_fun E.kZeroToGrothendieck_comp a⟩

/-- No additional equality between canonical object classes arises in genuine K₀. -/
@[simp] theorem kZeroObjectClass_eq_iff (X Y : C) :
    E.kZeroObjectClass X = E.kZeroObjectClass Y ↔
      E.grothendieckClass X = E.grothendieckClass Y := by
  constructor
  · intro h
    have he := congrArg E.kZeroToGrothendieck h
    exact Multiplicative.ofAdd.injective (by
      simpa only [E.kZeroToGrothendieck_objectClass] using he)
  · intro h
    have he := congrArg E.grothendieckToKZero (congrArg Multiplicative.ofAdd h)
    simpa using he

/-- Realizing completed Q-loops does not identify distinct completion classes. -/
theorem qGroupoidToKZero_injective : Function.Injective E.qGroupoidToKZero :=
  E.grothendieckToKZero_injective_iff.mp E.grothendieckToKZero_injective

end Quillen.ExactStructure
