/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletionKernel
public import Quillen.Topology.ClassifyingSpace.GroupHom
public import Quillen.KTheory.Plus.ProjectiveCompletionPositiveKNaturality
public import Quillen.KTheory.Plus.StableCompletionBasedRingNaturality

/-!
# The stable elementary quotient and original projective K₁

The comparison is the composite of the original stable-completion equivalence
with the standard completion-to-Q equivalence. It therefore keeps the original
stable matrix map, its basepoint tracks, and the inner-loop reversal already
present in that comparison. Its target is the actual Q-construction of finite
projective right modules. Ring naturality uses the original scalar-extension
exact functor. `Field.StableMatrixMarking` and `Field.MatrixCubeComparison`
identify its finite-matrix values with the literal positive matrix cubes.
-/
@[expose] public section

noncomputable section
universe u

namespace Quillen.FiniteProjectiveModule.StableCompletion

variable (R : Type u) [Ring R]

/-- The canonical stable-quotient comparison to the original projective Q-group. -/
def elementaryProjectiveKOneEquiv : StableGeneralLinear.ElementaryQuotient R ≃*
    (exactStructure Rᵐᵒᵖ).K 1 :=
  (elementaryPiOneEquiv R).trans (zeroCompletionPositiveKEquiv R 0)

/-- The comparison retains the actual original stable matrix class. -/
theorem elementaryProjectiveKOneEquiv_quotientMap (g : StableGeneralLinear.Group R) :
    elementaryProjectiveKOneEquiv R (StableGeneralLinear.quotientMap R g) =
      zeroCompletionPositiveKEquiv R 0 (stableGroupPiOneMap R g) := rfl

variable {R} {S : Type u} [Ring S]

/-- Change of rings on the actual stable matrix class uses the prescribed track. -/
theorem stableGroupPiOneMap_ringMap (f : R →+* S) (g : StableGeneralLinear.Group R) :
    pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) 0
      (homotopyGroupMapHom (N := Fin 1) (zeroCompletionBaseChangeMap f) rfl
        (stableGroupPiOneMap R g)) =
      stableGroupPiOneMap S (StableGeneralLinear.map f g) := by
  have h := DFunLike.congr_fun (stablePiOneMap_ringMap f)
    (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R) g)
  change _ = stablePiOneMap S
    (GroupoidClassifying.piOneMap (StableGeneralLinear.map f)
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R) g)) at h
  rw [GroupoidClassifying.piOneMap_equiv] at h
  exact h

/-- The original elementary-quotient equivalence is natural for actual ring maps. -/
theorem elementaryPiOneEquiv_ringMap (f : R →+* S)
    (a : StableGeneralLinear.ElementaryQuotient R) :
    pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) 0
      (homotopyGroupMapHom (N := Fin 1) (zeroCompletionBaseChangeMap f) rfl
        (elementaryPiOneEquiv R a)) =
      elementaryPiOneEquiv S (StableGeneralLinear.quotientRingMap f a) := by
  obtain ⟨g, rfl⟩ := StableGeneralLinear.quotientMap_surjective R a
  exact stableGroupPiOneMap_ringMap f g

/-- The canonical quotient-to-Q comparison commutes with literal scalar extension. -/
theorem elementaryProjectiveKOneEquiv_ringMap (f : R →+* S)
    (a : StableGeneralLinear.ElementaryQuotient R) :
    elementaryProjectiveKOneEquiv S (StableGeneralLinear.quotientRingMap f a) =
      (rightBaseChangeExact f).KMap 1 (elementaryProjectiveKOneEquiv R a) := by
  change zeroCompletionPositiveKEquiv S 0
    (elementaryPiOneEquiv S (StableGeneralLinear.quotientRingMap f a)) = _
  rw [← elementaryPiOneEquiv_ringMap]
  exact zeroCompletionPositiveKEquiv_baseChange f 0 (elementaryPiOneEquiv R a)

/-- The same actual ring-change square as an equality of group homomorphisms. -/
theorem elementaryProjectiveKOneEquiv_ringMap_hom (f : R →+* S) :
    (elementaryProjectiveKOneEquiv S).toMonoidHom.comp
        (StableGeneralLinear.quotientRingMap f) =
      ((rightBaseChangeExact f).KMap 1).comp
        (elementaryProjectiveKOneEquiv R).toMonoidHom := by
  exact MonoidHom.ext (elementaryProjectiveKOneEquiv_ringMap f)

/-- The inverse of the same comparison is natural, by its proved forward square. -/
theorem elementaryProjectiveKOneEquiv_symm_baseChange (f : R →+* S)
    (a : (exactStructure Rᵐᵒᵖ).K 1) :
    (elementaryProjectiveKOneEquiv S).symm ((rightBaseChangeExact f).KMap 1 a) =
      StableGeneralLinear.quotientRingMap f ((elementaryProjectiveKOneEquiv R).symm a) := by
  apply (elementaryProjectiveKOneEquiv S).injective
  rw [MulEquiv.apply_symm_apply, elementaryProjectiveKOneEquiv_ringMap,
    MulEquiv.apply_symm_apply]

end Quillen.FiniteProjectiveModule.StableCompletion
