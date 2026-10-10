/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Localization.Serre.FiberComparison
public import Quillen.KTheory.Map.Functoriality

/-! # A basepoint-compatible Serre-localization fiber comparison

This uses exactly the normalized Q-functors underlying the defined K-group
maps. The comparison fixes the original chosen zero basepoints. The assertion
that this comparison is a homotopy equivalence remains the localization theorem.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject unitInterval

namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The Q-functor induced by the exact inclusion of the Serre subcategory into `C`, normalized
to send the chosen Q-zero object exactly to the ambient Q-zero object. -/
abbrev inclusionNormalizedQ := (Devissage.exactInclusion P).normalizedQ
/-- The Q-functor induced by the exact Serre quotient functor, normalized to send the ambient
chosen Q-zero object exactly to the quotient Q-zero object. -/
abbrev quotientNormalizedQ := (quotientExactFunctor P).normalizedQ

/-- The normalized quotient/inclusion composite is naturally isomorphic to zero. -/
def normalizedQuotientInclusionZeroIso :
    inclusionNormalizedQ P ⋙ quotientNormalizedQ P ≅
      (Functor.const (Devissage.subcategoryExactStructure P).QCategory).obj
        (quotientExactStructure P).qZero :=
  (rebaseFunctorCompRightIso (Devissage.mapQ P) (quotientMapQ P)
    (Devissage.subcategoryExactStructure P).qZero (abelianExactStructure C).qZero
    (quotientExactStructure P).qZero
    ((abelianExactStructure C).qIsoOfIso (Devissage.exactInclusion P).toFunctor.mapZeroObject)
    ((quotientExactStructure P).qIsoOfIso (quotientExactFunctor P).toFunctor.mapZeroObject)).symm ≪≫
      quotientInclusionZeroIso P

/-- The normalized composite sends the source zero exactly to the target zero. -/
theorem normalizedComposite_obj_zero :
    (inclusionNormalizedQ P ⋙ quotientNormalizedQ P).obj
      (Devissage.subcategoryExactStructure P).qZero = (quotientExactStructure P).qZero :=
  rebaseFunctor_comp_obj_base _ _ _ _ _ _ _

/-- Its comparison at zero is the identity after the exact displayed equality. -/
theorem normalizedZeroIso_hom_base :
    (normalizedQuotientInclusionZeroIso P).hom.app
      (Devissage.subcategoryExactStructure P).qZero =
        eqToHom (normalizedComposite_obj_zero P) :=
  ((quotientExactStructure P).qHom_subsingleton_of_isZero _ _
    (isZero_zero (Quotient P))).elim _ _

/-- The actual relative topological nullhomotopy for the normalized maps. -/
def normalizedQuotientInclusionHomotopy :
    ((classifyingSpaceMap (quotientNormalizedQ P)).hom.comp
      (classifyingSpaceMap (inclusionNormalizedQ P)).hom).HomotopyRel
      (ContinuousMap.const _ (quotientExactStructure P).kBasepoint)
      {(Devissage.subcategoryExactStructure P).kBasepoint} :=
  (classifyingSpaceNaturalTransformationBasedHomotopy
    (normalizedQuotientInclusionZeroIso P).hom
    (Devissage.subcategoryExactStructure P).qZero
    (normalizedComposite_obj_zero P) (normalizedZeroIso_hom_base P)).cast
      (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
      (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- The nullhomotopy stays at the target's actual chosen basepoint. -/
theorem normalizedQuotientInclusionHomotopy_based (t : I) :
    normalizedQuotientInclusionHomotopy P
      (t, (Devissage.subcategoryExactStructure P).kBasepoint) =
        (quotientExactStructure P).kBasepoint := by
  have hh := (normalizedQuotientInclusionHomotopy P).prop t
    (Devissage.subcategoryExactStructure P).kBasepoint (Set.mem_singleton _)
  exact hh.trans (by
    change classifyingSpaceMap (quotientNormalizedQ P)
      (classifyingSpaceMap (inclusionNormalizedQ P)
        (Devissage.subcategoryExactStructure P).kBasepoint) = _
    rw [(Devissage.exactInclusion P).normalizedQ_map_point,
      (quotientExactFunctor P).normalizedQ_map_point])

/-- The localization comparison into the fiber of precisely the normalized
map that defines the quotient's K-group homomorphisms. -/
def basedLocalizationFiberComparison :
    C((Devissage.subcategoryExactStructure P).KSpace,
      HomotopyFiber (classifyingSpaceMap (quotientNormalizedQ P)).hom
        (quotientExactStructure P).kBasepoint) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMap (inclusionNormalizedQ P)).hom
    (normalizedQuotientInclusionHomotopy P).toHomotopy

/-- The comparison preserves the chosen zero/constant-path basepoint. -/
theorem basedLocalizationFiberComparison_basepoint :
    basedLocalizationFiberComparison P (Devissage.subcategoryExactStructure P).kBasepoint =
      HomotopyFiber.basepoint (classifyingSpaceMap (quotientNormalizedQ P)).hom
        (quotientExactStructure P).kBasepoint (abelianExactStructure C).kBasepoint
        (quotientExactFunctor P).normalizedQ_map_point := by
  apply Subtype.ext
  apply Prod.ext
  · exact (Devissage.exactInclusion P).normalizedQ_map_point
  · apply ContinuousMap.ext
    intro t
    exact normalizedQuotientInclusionHomotopy_based P t

/-- The normalized path-space fiber used by the canonical K-map. -/
abbrev NormalizedLocalizationFiber :=
  HomotopyFiber (classifyingSpaceMap (quotientNormalizedQ P)).hom
    (quotientExactStructure P).kBasepoint

/-- Its chosen constant-path basepoint. -/
def normalizedFiberBasepoint : NormalizedLocalizationFiber P :=
  HomotopyFiber.basepoint _ _ (abelianExactStructure C).kBasepoint
    (quotientExactFunctor P).normalizedQ_map_point

/-- The based comparison induces a genuine homomorphism into the fiber's
homotopy groups. No assertion that it is an isomorphism is made. -/
def localizationFiberComparisonHom (n : ℕ) :
    (Devissage.subcategoryExactStructure P).K n →*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P) :=
  piMap n (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P)

/-- Fiber projection on the same homotopy groups. -/
def localizationFiberProjectionHom (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P) →*
      (abelianExactStructure C).K n :=
  piMap n (HomotopyFiber.projection _ _)
    (show HomotopyFiber.projection _ _ (normalizedFiberBasepoint P) =
      (abelianExactStructure C).kBasepoint from rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The based comparison is compatible with the actual inclusion K-map. -/
theorem localizationFiberComparisonHom_projection (n : ℕ) :
    (localizationFiberProjectionHom P n).comp (localizationFiberComparisonHom P n) =
      Devissage.KMap P n := by
  change (piMap n _ _).comp (piMap n _ _) = _
  rw [← homotopyGroupMapHom_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical inclusion and quotient K-maps have trivial composite.
This follows from the actual based nullhomotopy, not the still-open fiber-equivalence theorem. -/
theorem quotientKMap_comp_inclusion (n : ℕ) :
    (quotientKMap P n).comp (Devissage.KMap P n) = 1 := by
  change ((quotientExactFunctor P).KMap n).comp ((Devissage.exactInclusion P).KMap n) = 1
  rw [ExactFunctor.KMap_eq_piMap, ExactFunctor.KMap_eq_piMap,
    ← homotopyGroupMapHom_comp]
  exact piMap_eq_one_of_based_nullhomotopy n _
    (normalizedQuotientInclusionHomotopy P).toHomotopy
    (normalizedQuotientInclusionHomotopy_based P)

end Quillen.SerreLocalization
