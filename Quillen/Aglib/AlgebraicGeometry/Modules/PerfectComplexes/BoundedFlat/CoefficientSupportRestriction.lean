/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportedSections
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientOpenRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SupportUnion
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Pairs
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.PairSquares
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SupportedRestriction
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Basic

/-!
# Actual auxiliary support and joint coefficient restriction

The specified support opens, inverse-image pair maps, supported section restrictions and literal
coefficient square are preserved. The fiber support is precisely the intersection of the original
auxiliary closed support and localization complement.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

/-- The auxiliary open on a native fiber is its actual original projection preimage. -/
def boundedFlatCoefficientSupportOpen (Q : Over (Spec R)) (T : Q.left.Opens) (a : Under R) :
    (space (op Q, a)).Opens := projection (op Q, a) ⁻¹ᵁ T

/-- Arbitrary coefficient change retains the exact original support preimage. -/
theorem boundedFlatCoefficientSupportOpen_preimage
    (Q : Over (Spec R)) (T : Q.left.Opens) {a b : Under R} (g : a ⟶ b) :
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
        (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g) ⁻¹ᵁ
          boundedFlatCoefficientSupportOpen Q T a = boundedFlatCoefficientSupportOpen Q T b := by
  change (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g) ≫ projection (op Q, a)) ⁻¹ᵁ T = _
  rw [map_projection]
  rfl

/-- The auxiliary support complement stays quasi-compact under native coefficient base change. -/
theorem boundedFlatCoefficientSupportOpen_compactSpace
    (Q : Over (Spec R)) (T : Q.left.Opens) [CompactSpace T] (a : Under R) :
    CompactSpace (boundedFlatCoefficientSupportOpen Q T a) := by
  apply isCompact_iff_compactSpace.mp
  have hT : IsCompact (T : Set Q.left) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace T from inferInstance)
  exact (projection (op Q, a)).isCompact_preimage hT

/-- The actual coefficient square between the native auxiliary support opens. -/
def boundedFlatCoefficientSupportPairMap
    (Q : Over (Spec R)) (T : Q.left.Opens) {a b : Under R} (g : a ⟶ b) :
    supportOpenPair (boundedFlatCoefficientSupportOpen Q T b) ⟶
      supportOpenPair (boundedFlatCoefficientSupportOpen Q T a) :=
  let m := AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
  let h := (boundedFlatCoefficientSupportOpen_preimage Q T g).symm.le
  ObjectProperty.homMk (Arrow.homMk
    (m.resLE (boundedFlatCoefficientSupportOpen Q T a)
      (boundedFlatCoefficientSupportOpen Q T b) h) m (m.resLE_comp_ι h))

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The open-side auxiliary support complement is the literal native inverse image. -/
def boundedFlatCoefficientOpenSupportOpen (a : Under R) : (space (op P, a)).Opens :=
  schemeMap f a ⁻¹ᵁ boundedFlatCoefficientSupportOpen Q T a

omit [IsOpenImmersion f.left] in
/-- The native open support is the projection preimage of the original open support. -/
theorem boundedFlatCoefficientOpenSupportOpen_eq (a : Under R) :
    boundedFlatCoefficientOpenSupportOpen f T a =
      projection (op P, a) ⁻¹ᵁ (f.left ⁻¹ᵁ T) := by
  change (schemeMap f a ≫ projection (op Q, a)) ⁻¹ᵁ T = _
  rw [schemeMap_projection]
  rfl

/-- The actual coefficient square on the open-side intersection with auxiliary support. -/
def boundedFlatCoefficientOpenSupportPairMap {a b : Under R} (g : a ⟶ b) :
    supportOpenPair (boundedFlatCoefficientOpenSupportOpen f T b) ⟶
      supportOpenPair (boundedFlatCoefficientOpenSupportOpen f T a) :=
  supportedPairTargetSquare (schemeMap f b) (schemeMap f a)
    (boundedFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedFlatCoefficientOpenSquare f g).symm

/-- Native relative support on the ambient fiber is the original intersection with the closed
complement of the localization open. -/
def boundedFlatCoefficientFiberSupportOpen (a : Under R) : (space (op Q, a)).Opens :=
  boundedFlatCoefficientSupportOpen Q T a ⊔ (schemeMap f a).opensRange

/-- Every native coefficient map preserves this actual intersection support. -/
def boundedFlatCoefficientFiberSupportPairMap {a b : Under R} (g : a ⟶ b) :
    supportOpenPair (boundedFlatCoefficientFiberSupportOpen f T b) ⟶
      supportOpenPair (boundedFlatCoefficientFiberSupportOpen f T a) :=
  supportedPairUnionSquare (schemeMap f b) (schemeMap f a)
    (boundedFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedFlatCoefficientOpenSquare f g).symm

/-- Fine native ambient sections with their original auxiliary closed support. -/
abbrev BoundedFlatCoefficientSupportedAmbientSections (a : Under R) :=
  BoundedFlatCoefficientSupportedSections (boundedFlatCoefficientSupportOpen Q T a).ι

/-- Fine native open sections with support precisely on the actual intersection. -/
abbrev BoundedFlatCoefficientSupportedOpenSections (a : Under R) :=
  BoundedFlatCoefficientSupportedSections (boundedFlatCoefficientOpenSupportOpen f T a).ι

/-- The unchanged actual coefficient functor on supported ambient native sections. -/
def boundedFlatCoefficientSupportedAmbientMap {a b : Under R} (g : a ⟶ b) :
    BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a ⥤
      BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T b :=
  boundedFlatCoefficientSupportedSectionsMap
    (boundedFlatCoefficientSupportOpen Q T a).ι (boundedFlatCoefficientSupportOpen Q T b).ι
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (boundedFlatCoefficientSupportPairMap Q T g).hom.left
    (Arrow.w (boundedFlatCoefficientSupportPairMap Q T g).hom)

/-- The unchanged actual coefficient functor on the supported native open sections. -/
def boundedFlatCoefficientSupportedOpenMap {a b : Under R} (g : a ⟶ b) :
    BoundedFlatCoefficientSupportedOpenSections f T a ⥤
      BoundedFlatCoefficientSupportedOpenSections f T b :=
  boundedFlatCoefficientSupportedSectionsMap
    (boundedFlatCoefficientOpenSupportOpen f T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T b).ι
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
    (boundedFlatCoefficientOpenSupportPairMap f T g).hom.left
    (by
      dsimp only [boundedFlatCoefficientOpenSupportPairMap, supportedPairTargetSquare,
        supportOpenPair, ObjectProperty.homMk, Arrow.homMk]
      exact Scheme.Hom.resLE_comp_ι _ _)

/-- Restriction uses original joint reindexing with the literal inverse-image support square. -/
def boundedFlatCoefficientSupportedOpenRestriction (a : Under R) :
    BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a ⥤
      BoundedFlatCoefficientSupportedOpenSections f T a :=
  boundedFlatCoefficientSupportedSectionsMap
    (boundedFlatCoefficientSupportOpen Q T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T a).ι
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)).hom.left
    (Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)).hom)

/-- The original supported restriction intertwines actual native evaluation and geometric pullback.
-/
def boundedFlatCoefficientSupportedOpenRestrictionEvaluationIso (a : Under R) :
    boundedFlatCoefficientSupportedOpenRestriction f T a ⋙
        boundedFlatCoefficientSupportedEvaluation (i := (op P, a))
          (boundedFlatCoefficientOpenSupportOpen f T a).ι ≅
      boundedFlatCoefficientSupportedEvaluation (i := (op Q, a))
        (boundedFlatCoefficientSupportOpen Q T a).ι ⋙
        boundedFlatPerfectSupportedPullback
          (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)) :=
  boundedFlatCoefficientSupportedSectionReindexIso
    (boundedFlatCoefficientSupportOpen Q T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T a).ι
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)).hom.left
    (Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)).hom)

omit [IsOpenImmersion f.left] in
/-- The actual coefficient and restriction functors form a strict supported section square. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_square {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientSupportedAmbientMap T g ⋙
        boundedFlatCoefficientSupportedOpenRestriction f T b =
      boundedFlatCoefficientSupportedOpenRestriction f T a ⋙
        boundedFlatCoefficientSupportedOpenMap f T g :=
  boundedFlatCoefficientSupportedSectionsMap_square
    (boundedFlatCoefficientSupportOpen Q T a).ι
    (boundedFlatCoefficientSupportOpen Q T b).ι
    (boundedFlatCoefficientOpenSupportOpen f T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T b).ι
    (i := (op Q, a)) (k := (op Q, b)) (k' := (op P, a)) (t := (op P, b))
    (𝟙 (op Q), g) (f.op, 𝟙 b) (f.op, 𝟙 a) (𝟙 (op P), g)
    (boundedFlatCoefficientSupportPairMap Q T g).hom.left
    (supportRestrictionPair (schemeMap f b) (boundedFlatCoefficientSupportOpen Q T b)).hom.left
    (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)).hom.left
    (boundedFlatCoefficientOpenSupportPairMap f T g).hom.left
    (Arrow.w (boundedFlatCoefficientSupportPairMap Q T g).hom)
    (Arrow.w (supportRestrictionPair (schemeMap f b)
      (boundedFlatCoefficientSupportOpen Q T b)).hom)
    (Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)).hom)
    (by
      dsimp only [boundedFlatCoefficientOpenSupportPairMap, supportedPairTargetSquare,
        supportOpenPair, ObjectProperty.homMk, Arrow.homMk]
      exact Scheme.Hom.resLE_comp_ι _ _)
    ((rowTransformation f).naturality g)

omit [IsOpenImmersion f.left] in
/-- The actual open-side support preimage is preserved by every coefficient map. -/
theorem boundedFlatCoefficientOpenSupportOpen_preimage {a b : Under R} (g : a ⟶ b) :
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
        (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g) ⁻¹ᵁ
          boundedFlatCoefficientOpenSupportOpen f T a =
        boundedFlatCoefficientOpenSupportOpen f T b := by
  rw [boundedFlatCoefficientOpenSupportOpen_eq, boundedFlatCoefficientOpenSupportOpen_eq]
  exact boundedFlatCoefficientSupportOpen_preimage P (f.left ⁻¹ᵁ T) g

/-- The auxiliary support and the localization complement are the actual two closed factors. -/
theorem boundedFlatCoefficientFiberSupportOpen_not_mem (a : Under R) (x : space (op Q, a)) :
    x ∉ boundedFlatCoefficientFiberSupportOpen f T a ↔
      x ∉ boundedFlatCoefficientSupportOpen Q T a ∧ x ∉ (schemeMap f a).opensRange :=
  not_or

/-- The actual native section category on the intersection of the two closed supports. -/
abbrev BoundedFlatCoefficientSupportedFiberSections (a : Under R) :=
  BoundedFlatCoefficientSupportedSections (boundedFlatCoefficientFiberSupportOpen f T a).ι

/-- Inside auxiliary support, the original closed fiber support is exactly open acyclicity. -/
theorem boundedFlatCoefficientFiberSupported_iff (a : Under R)
    (S : BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι S.obj ↔
      ((restrict (schemeMap f a)).obj
        ((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).obj).Acyclic := by
  have h := boundedFlatPerfectSupported_sup_opensRange_iff
    (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)
    ((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).obj
  constructor
  · intro hS
    exact (h.mp ⟨((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).property, hS⟩).2
  · intro hS
    exact (h.mpr
      ⟨⟨((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).property,
        S.property⟩, hS⟩).2

end Quillen.PerfectComplexes

end

end
