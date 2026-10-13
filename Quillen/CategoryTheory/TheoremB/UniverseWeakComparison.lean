/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.TheoremB.FullWeakComparison
public import Quillen.CategoryTheory.Comma.UniverseLift

/-!
# Actual comma projections in independent category universes

Weak equivalences of the original comma transition maps and weak contractibility
of the actual base imply that the original comma projection is a weak equivalence.
The proof transports the common-universe theorem through strict comma-lifting
squares and homeomorphisms, without choosing a substitute forward map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u₁ v₁ u₂ v₂ w
namespace Quillen.TheoremB

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Every original comma transition is a weak equivalence, with no universe restrictions. -/
def TransitionWeakEquivalencesUniversal (F : C ⥤ D) : Prop :=
  ∀ ⦃d e : D⦄ (f : d ⟶ e),
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (CostructuredArrow.map (S := F) f))

/-- The original weak transition hypothesis passes to the common-universe lift. -/
theorem transitionWeakEquivalences_universeLift (F : C ⥤ D)
    (h : TransitionWeakEquivalencesUniversal F) :
    TransitionWeakEquivalences (universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F) := by
  intro d e f
  have hu := isWeakHomotopyEquivalence_of_homotopyEquiv
    (costructuredArrowUniverseHomeomorph.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂}
      F (ULift.down d)).toHomotopyEquiv
  have hv := isWeakHomotopyEquivalence_of_homotopyEquiv
    (costructuredArrowUniverseHomeomorph.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂}
      F (ULift.down e)).toHomotopyEquiv
  have ht := hv.comp (h (ULift.down f))
  change IsWeakHomotopyEquivalence
    ((classifyingSpaceMapUniversal (costructuredArrowUniverseUp F (ULift.down e))).comp
      (classifyingSpaceMapUniversal (CostructuredArrow.map (ULift.down f)))) at ht
  rw [← classifyingSpaceMapUniversal_comp, ← costructuredArrowUniverseUp_map,
    classifyingSpaceMapUniversal_comp] at ht
  have he := ht.of_comp_left hu
  change IsWeakHomotopyEquivalence (classifyingSpaceMap (CostructuredArrow.map f)).hom
  simpa only [classifyingSpaceMapUniversal_eq, AsSmall.up, ULift.up_down] using he

/-- Weak contractibility of the actual base suffices for the actual comma projection
in independent object and morphism universes. The point target may be in any universe. -/
theorem commaProjectionUniversal_isWeakHomotopyEquivalence_of_weakBase
    (F : C ⥤ D) (h : TransitionWeakEquivalencesUniversal F) (d : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const (ClassifyingSpace D)
      (PUnit.unit : PUnit.{w + 1}))) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (CostructuredArrow.proj F d)) := by
  let F' := universeLiftFunctor.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F
  let eP : PUnit.{w + 1} ≃ₜ PUnit.{max u₁ v₁ u₂ v₂ + 1} :=
    { toEquiv := Equiv.punitEquivPUnit
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  have hD' := ((isWeakHomotopyEquivalence_of_homotopyEquiv eP.toHomotopyEquiv).comp hD).comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (classifyingSpaceUniverseHomeomorph.{u₂, v₂, max u₁ v₁ u₂ v₂} D).symm.toHomotopyEquiv)
  have hp := commaProjection_isWeakHomotopyEquivalence_of_weakBase F'
    (transitionWeakEquivalences_universeLift F h) (AsSmall.up.obj d) hD'
  have hu := isWeakHomotopyEquivalence_of_homotopyEquiv
    (costructuredArrowUniverseHomeomorph.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂} F d).toHomotopyEquiv
  have hs := hp.comp hu
  change IsWeakHomotopyEquivalence
    ((classifyingSpaceMap (CostructuredArrow.proj F' (AsSmall.up.obj d))).hom.comp
      (classifyingSpaceMapUniversal (costructuredArrowUniverseUp F d))) at hs
  rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp,
    costructuredArrowUniverseUp_proj, classifyingSpaceMapUniversal_comp] at hs
  exact hs.of_comp_right (isWeakHomotopyEquivalence_of_homotopyEquiv
    (classifyingSpaceUniverseHomeomorph.{u₁, v₁, max u₁ v₁ u₂ v₂} C).toHomotopyEquiv)

end Quillen.TheoremB
