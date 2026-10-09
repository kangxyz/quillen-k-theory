import Quillen.KTheory.GrothendieckComparison.Groupoid
import Quillen.KTheory.FundamentalGroup.Completion

/-!
# The canonical comparison factors through actual groupoid completion

The Q-specific algebraic calculation and the continuous-path construction
meet in an exact equality of homomorphisms. The only remaining general
presentation question is bijectivity of the canonical realized completion map.
-/

noncomputable section
universe v u
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The canonical homomorphism from completed Q-edge loops to the genuine K₀. -/
def qGroupoidToKZero : E.qGroupoidZeroGroup →* E.K 0 :=
  E.kZeroFundamentalGroupEquiv.symm.toMonoidHom.comp
    (classifyingGroupoidCompletionMap E.QCategory E.qZero)

/-- The completion comparison takes each formal object loop to precisely
its continuous realized counterpart. -/
@[simp] lemma qGroupoidToKZero_objectClass (X : C) :
    E.qGroupoidToKZero (E.qObjectClass E.toQGroupoid X) = E.kZeroObjectClass X := by
  apply E.kZeroFundamentalGroupEquiv.injective
  change E.kZeroFundamentalGroupEquiv
    (E.kZeroFundamentalGroupEquiv.symm
      ((classifyingGroupoidCompletionFunctor E.QCategory).map
        (E.qObjectClass E.toQGroupoid X))) = _
  erw [MulEquiv.apply_symm_apply, ← E.qObjectClass_comp]
  rw [E.kZeroFundamentalGroupEquiv_objectClass, E.kZeroObjectLoop_eq_qObjectClass]
  have h : HEq
      (E.qObjectClass (E.toQGroupoid ⋙ classifyingGroupoidCompletionFunctor E.QCategory) X)
      (E.qObjectClass (classifyingFundamentalGroupoidFunctor E.QCategory) X) := by
    rw [toClassifyingGroupoidCompletionFunctor]
  exact eq_of_heq h

/-- The canonical algebraic-to-topological comparison is exactly the proved
Grothendieck/groupoid equivalence followed by realization of completed paths. -/
theorem grothendieckToKZero_factorization :
    E.qGroupoidToKZero.comp E.grothendieckQGroupoidEquiv.toMonoidHom =
      E.grothendieckToKZero := by
  apply E.grothendieck_mulHom_ext
  intro X
  change E.qGroupoidToKZero (E.grothendieckToQGroupoid
    (Multiplicative.ofAdd (E.grothendieckClass X))) = _
  simp

/-- Surjectivity of the K₀ comparison is precisely topological edge-loop generation. -/
theorem grothendieckToKZero_surjective_iff :
    Function.Surjective E.grothendieckToKZero ↔ Function.Surjective E.qGroupoidToKZero := by
  rw [← E.grothendieckToKZero_factorization]
  constructor
  · intro h y
    obtain ⟨a, ha⟩ := h y
    exact ⟨E.grothendieckQGroupoidEquiv a, ha⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    obtain ⟨a, rfl⟩ := E.grothendieckQGroupoidEquiv.surjective x
    exact ⟨a, hx⟩

/-- Injectivity of the K₀ comparison is precisely injectivity of the canonical
completed-edge-loop realization map. -/
theorem grothendieckToKZero_injective_iff :
    Function.Injective E.grothendieckToKZero ↔ Function.Injective E.qGroupoidToKZero := by
  rw [← E.grothendieckToKZero_factorization]
  constructor
  · intro h x y hxy
    obtain ⟨a, rfl⟩ := E.grothendieckQGroupoidEquiv.surjective x
    obtain ⟨b, rfl⟩ := E.grothendieckQGroupoidEquiv.surjective y
    exact congrArg E.grothendieckQGroupoidEquiv (h hxy)
  · intro h x y hxy
    exact E.grothendieckQGroupoidEquiv.injective (h hxy)

end Quillen.ExactStructure
