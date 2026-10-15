/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedOpenNaturality

/-!
# Native coefficient Models with auxiliary closed support

For an original open arrow and an auxiliary open `T`, support on every native
ambient fiber is the complement of the actual inverse image of `T` under the
original projection. The open-side support is its actual inverse image under
the native open arrow. Thus it is precisely the original support intersected
with the original open. Relative acyclicity also retains the intersection of
the auxiliary support with the complement of the localization open.

The actual supported fine and coarse Models use the same original joint zero.
Coefficient reindexing and restriction are exact and preserve this zero
literally. The strict original index squares give the coefficient-natural
restriction. No supported quotient grading, cofinality, seed or telescope
statement is asserted by these Model constructions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.CoefficientBaseChange
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
    (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T g).hom)

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

omit [IsOpenImmersion f.left] in
/-- The same supported restriction is exact for both original fine structures. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_fine_exact (a : Under R) :
    IsExact
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientSupportOpen Q T a).ι).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientSupportOpen Q T a).ι).weq
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι).weq
      (boundedFlatCoefficientSupportedOpenRestriction f T a) :=
  boundedFlatCoefficientSupportedSectionsMap_exact
    (boundedFlatCoefficientSupportOpen Q T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T a).ι
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)).hom.left
    (Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)).hom)

/-- Actual supported ambient coefficient change is exact for the fine structures. -/
theorem boundedFlatCoefficientSupportedAmbientMap_fine_exact {a b : Under R} (g : a ⟶ b) :
    IsExact
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientSupportOpen Q T a).ι).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientSupportOpen Q T a).ι).weq
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientSupportOpen Q T b).ι).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientSupportOpen Q T b).ι).weq
      (boundedFlatCoefficientSupportedAmbientMap T g) :=
  boundedFlatCoefficientSupportedSectionsMap_exact
    (boundedFlatCoefficientSupportOpen Q T a).ι (boundedFlatCoefficientSupportOpen Q T b).ι
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (boundedFlatCoefficientSupportPairMap Q T g).hom.left
    (Arrow.w (boundedFlatCoefficientSupportPairMap Q T g).hom)

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

/-- Coarse supported weakness is detected by the actual original section restriction. -/
def boundedFlatCoefficientSupportedOpenWaldhausen (a : Under R) :
    Structure (BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a) :=
  Structure.withInverseImageWeak (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a)

/-- The same native fine weak class is contained in the restriction-detected coarse class. -/
def boundedFlatCoefficientSupportedOpenNested (a : Under R) :
    Fibration.NestedWeakEquivalences
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientSupportOpen Q T a).ι) :=
  Structure.inverseImageWeakNested (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a)

omit [IsOpenImmersion f.left] in
/-- Original supported coarse-to-fine restriction preserves all Waldhausen structure. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι).weq
      (boundedFlatCoefficientSupportedOpenRestriction f T a) :=
  Structure.withInverseImageWeak_exact
    (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a)

omit [IsOpenImmersion f.left] in
/-- Original supported open-side coefficient change is exact for the fine structures. -/
theorem boundedFlatCoefficientSupportedOpenMap_fine_exact {a b : Under R} (g : a ⟶ b) :
    IsExact
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι).weq
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T b).ι).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T b).ι).weq
      (boundedFlatCoefficientSupportedOpenMap f T g) :=
  boundedFlatCoefficientSupportedSectionsMap_exact
    (boundedFlatCoefficientOpenSupportOpen f T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T b).ι
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
    (boundedFlatCoefficientOpenSupportPairMap f T g).hom.left
    (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T g).hom)

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
    (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T g).hom)
    ((rowTransformation f).naturality g)

private theorem inverseImageSquare_exact {C C' D D' : Type*}
    [Category* C] [Category* C'] [Category* D] [Category* D']
    {V : Structure C} {V' : Structure C'} {W : Structure D} {W' : Structure D'}
    {r : C ⥤ D} {r' : C' ⥤ D'} {S : C ⥤ C'} {J : D ⥤ D'}
    (hr : IsExact V.cof V.weq W.cof W.weq r)
    (hr' : IsExact V'.cof V'.weq W'.cof W'.weq r')
    (hS : IsExact V.cof V.weq V'.cof V'.weq S)
    (hJ : IsExact W.cof W.weq W'.cof W'.weq J) (h : S ⋙ r' = r ⋙ J) :
    IsExact (Structure.withInverseImageWeak hr).cof (Structure.withInverseImageWeak hr).weq
      (Structure.withInverseImageWeak hr').cof (Structure.withInverseImageWeak hr').weq S where
  zero := hS.zero
  cofibration := hS.cofibration
  pushout := hS.pushout
  weak g hg := by
    have hcomp := (Structure.withInverseImageWeak_exact hr).comp hJ
    rw [← h] at hcomp
    exact hcomp.weak g hg

omit [IsOpenImmersion f.left] in
/-- Coefficient exactness for the coarse structure follows from the same strict restriction square.
-/
theorem boundedFlatCoefficientSupportedAmbientMap_coarse_exact {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedFlatCoefficientSupportedOpenWaldhausen f T a).cof
      (boundedFlatCoefficientSupportedOpenWaldhausen f T a).weq
      (boundedFlatCoefficientSupportedOpenWaldhausen f T b).cof
      (boundedFlatCoefficientSupportedOpenWaldhausen f T b).weq
      (boundedFlatCoefficientSupportedAmbientMap T g) :=
  inverseImageSquare_exact
    (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a)
    (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T b)
    (boundedFlatCoefficientSupportedAmbientMap_fine_exact T g)
    (boundedFlatCoefficientSupportedOpenMap_fine_exact f T g)
    (boundedFlatCoefficientSupportedOpenRestriction_square f T g)

/-- Actual fine ambient Models on the original auxiliary support. -/
def boundedFlatCoefficientSupportedAmbientModel (a : Under R) : Model.{u+1} :=
  boundedFlatCoefficientSupportedSectionModel (i := (op Q, a))
    (boundedFlatCoefficientSupportOpen Q T a).ι

/-- Original coefficient reindexing is an exact, zero-preserving fine ambient Model map. -/
def boundedFlatCoefficientSupportedAmbientModelMap {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientSupportedAmbientModel T a ⟶
      boundedFlatCoefficientSupportedAmbientModel T b :=
  boundedFlatCoefficientSupportedSectionModelMap
    (boundedFlatCoefficientSupportOpen Q T a).ι (boundedFlatCoefficientSupportOpen Q T b).ι
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (boundedFlatCoefficientSupportPairMap Q T g).hom.left
    (Arrow.w (boundedFlatCoefficientSupportPairMap Q T g).hom)

/-- The original fine ambient support Models form a strict coefficient diagram. -/
def boundedFlatCoefficientSupportedAmbientModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatCoefficientSupportedAmbientModel T
  map := boundedFlatCoefficientSupportedAmbientModelMap T
  map_id a := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_id
      (boundedFlatCoefficientSupportOpen Q T a).ι
      (boundedFlatCoefficientSupportPairMap Q T (𝟙 a)).hom.left
      (Arrow.w (boundedFlatCoefficientSupportPairMap Q T (𝟙 a)).hom)
  map_comp {a b c} g h := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_comp
      (boundedFlatCoefficientSupportOpen Q T a).ι (boundedFlatCoefficientSupportOpen Q T b).ι
      (boundedFlatCoefficientSupportOpen Q T c).ι
      (i := (op Q, a)) (k := (op Q, b)) (t := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)
      (boundedFlatCoefficientSupportPairMap Q T g).hom.left
      (boundedFlatCoefficientSupportPairMap Q T h).hom.left
      (boundedFlatCoefficientSupportPairMap Q T (g ≫ h)).hom.left
      (Arrow.w (boundedFlatCoefficientSupportPairMap Q T g).hom)
      (Arrow.w (boundedFlatCoefficientSupportPairMap Q T h).hom)
      (Arrow.w (boundedFlatCoefficientSupportPairMap Q T (g ≫ h)).hom)

/-- The actual fine native open Model retains the original intersection support. -/
def boundedFlatCoefficientSupportedFullOpenModel (a : Under R) : Model.{u+1} :=
  boundedFlatCoefficientSupportedSectionModel (i := (op P, a))
    (boundedFlatCoefficientOpenSupportOpen f T a).ι

/-- Original open-side coefficient maps preserve all fine structure and the shared joint zero. -/
def boundedFlatCoefficientSupportedFullOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientSupportedFullOpenModel f T a ⟶
      boundedFlatCoefficientSupportedFullOpenModel f T b :=
  boundedFlatCoefficientSupportedSectionModelMap
    (boundedFlatCoefficientOpenSupportOpen f T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T b).ι
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
    (boundedFlatCoefficientOpenSupportPairMap f T g).hom.left
    (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T g).hom)

/-- The fine supported native open Models form the strict coefficient diagram F_Z. -/
def boundedFlatCoefficientSupportedFullOpenModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatCoefficientSupportedFullOpenModel f T
  map := boundedFlatCoefficientSupportedFullOpenModelMap f T
  map_id a := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_id
      (boundedFlatCoefficientOpenSupportOpen f T a).ι
      (boundedFlatCoefficientOpenSupportPairMap f T (𝟙 a)).hom.left
      (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T (𝟙 a)).hom)
  map_comp {a b c} g h := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_comp
      (boundedFlatCoefficientOpenSupportOpen f T a).ι
      (boundedFlatCoefficientOpenSupportOpen f T b).ι
      (boundedFlatCoefficientOpenSupportOpen f T c).ι
      (i := (op P, a)) (k := (op P, b)) (t := (op P, c))
      (𝟙 (op P), g) (𝟙 (op P), h)
      (boundedFlatCoefficientOpenSupportPairMap f T g).hom.left
      (boundedFlatCoefficientOpenSupportPairMap f T h).hom.left
      (boundedFlatCoefficientOpenSupportPairMap f T (g ≫ h)).hom.left
      (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T g).hom)
      (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T h).hom)
      (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T (g ≫ h)).hom)

/-- The actual supported coarse Model retains the original ambient sections and shared zero. -/
def boundedFlatCoefficientSupportedOpenModel (a : Under R) : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a),
    boundedFlatCoefficientSupportedOpenWaldhausen f T a⟩

/-- Coarse coefficient change is the same original supported functor and preserves its zero. -/
def boundedFlatCoefficientSupportedOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientSupportedOpenModel f T a ⟶
      boundedFlatCoefficientSupportedOpenModel f T b where
  functor := boundedFlatCoefficientSupportedAmbientMap T g
  exact := boundedFlatCoefficientSupportedAmbientMap_coarse_exact f T g
  zero := (boundedFlatCoefficientSupportedAmbientModelMap T g).zero

/-- The coarse supported native ambient Models form the strict coefficient diagram C_Z. -/
def boundedFlatCoefficientSupportedOpenModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatCoefficientSupportedOpenModel f T
  map := boundedFlatCoefficientSupportedOpenModelMap f T
  map_id a := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_id
      (boundedFlatCoefficientSupportOpen Q T a).ι
      (boundedFlatCoefficientSupportPairMap Q T (𝟙 a)).hom.left
      (Arrow.w (boundedFlatCoefficientSupportPairMap Q T (𝟙 a)).hom)
  map_comp {a b c} g h := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_comp
      (boundedFlatCoefficientSupportOpen Q T a).ι (boundedFlatCoefficientSupportOpen Q T b).ι
      (boundedFlatCoefficientSupportOpen Q T c).ι
      (i := (op Q, a)) (k := (op Q, b)) (t := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)
      (boundedFlatCoefficientSupportPairMap Q T g).hom.left
      (boundedFlatCoefficientSupportPairMap Q T h).hom.left
      (boundedFlatCoefficientSupportPairMap Q T (g ≫ h)).hom.left
      (Arrow.w (boundedFlatCoefficientSupportPairMap Q T g).hom)
      (Arrow.w (boundedFlatCoefficientSupportPairMap Q T h).hom)
      (Arrow.w (boundedFlatCoefficientSupportPairMap Q T (g ≫ h)).hom)

/-- The same original supported restriction is a coarse-to-fine Model map r_Z. -/
def boundedFlatCoefficientSupportedOpenRestrictionModelMap (a : Under R) :
    boundedFlatCoefficientSupportedOpenModel f T a ⟶
      boundedFlatCoefficientSupportedFullOpenModel f T a where
  functor := boundedFlatCoefficientSupportedOpenRestriction f T a
  exact := boundedFlatCoefficientSupportedOpenRestriction_exact f T a
  zero := boundedFlatCoefficientSupportedSectionsMap_sectionZero
    (boundedFlatCoefficientSupportOpen Q T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T a).ι
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)).hom.left
    (Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)).hom)

/-- The actual supported restriction is natural in the original coefficient Model diagrams. -/
def boundedFlatCoefficientSupportedOpenRestrictionModelTransformation :
    boundedFlatCoefficientSupportedOpenModelFunctor f T ⟶
      boundedFlatCoefficientSupportedFullOpenModelFunctor f T where
  app := boundedFlatCoefficientSupportedOpenRestrictionModelMap f T
  naturality a b g := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedOpenRestriction_square f T g

/-- The fine-to-coarse Model map preserves the supported category and original joint zero. -/
def boundedFlatCoefficientSupportedOpenChangeWeakModelMap (a : Under R) :
    boundedFlatCoefficientSupportedAmbientModel T a ⟶
      boundedFlatCoefficientSupportedOpenModel f T a where
  functor := 𝟭 (BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a)
  exact := Fibration.changeWeak_exact (boundedFlatCoefficientSupportedOpenNested f T a)
  zero := rfl

/-- Fine-to-coarse change of weakness is natural under every original coefficient map. -/
def boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation :
    boundedFlatCoefficientSupportedAmbientModelFunctor T ⟶
      boundedFlatCoefficientSupportedOpenModelFunctor f T where
  app := boundedFlatCoefficientSupportedOpenChangeWeakModelMap f T
  naturality a b g := by
    apply Model.Hom.ext
    change boundedFlatCoefficientSupportedAmbientMap T g ⋙ 𝟭 _ =
      𝟭 _ ⋙ boundedFlatCoefficientSupportedAmbientMap T g
    simp only [Functor.comp_id, Functor.id_comp]

/-- Original iterated-S realization of the actual supported coarse coefficient diagram. -/
def boundedFlatCoefficientSupportedOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientSupportedOpenModelFunctor f T ⋙ prespectrumFunctor

/-- Original iterated-S realization of the actual supported fine open coefficient diagram. -/
def boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientSupportedFullOpenModelFunctor f T ⋙ prespectrumFunctor

/-- Actual supported native restriction on the same coefficient prespectrum diagrams. -/
def boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation :
    boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T ⟶
      boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T :=
  Functor.whiskerRight (boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T)
    prespectrumFunctor


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

/-- The actual fine Model on the original intersection of the closed supports. -/
def boundedFlatCoefficientSupportedFiberModel (a : Under R) : Model.{u+1} :=
  boundedFlatCoefficientSupportedSectionModel (i := (op Q, a))
    (boundedFlatCoefficientFiberSupportOpen f T a).ι

/-- Every coefficient arrow gives exact, zero-preserving reindexing on the same closed fiber. -/
def boundedFlatCoefficientSupportedFiberModelMap {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientSupportedFiberModel f T a ⟶
      boundedFlatCoefficientSupportedFiberModel f T b :=
  boundedFlatCoefficientSupportedSectionModelMap
    (boundedFlatCoefficientFiberSupportOpen f T a).ι
    (boundedFlatCoefficientFiberSupportOpen f T b).ι
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (boundedFlatCoefficientFiberSupportPairMap f T g).hom.left
    (Arrow.w (boundedFlatCoefficientFiberSupportPairMap f T g).hom)

/-- Actual closed fiber Models form a strict coefficient diagram with the same joint zero. -/
def boundedFlatCoefficientSupportedFiberModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatCoefficientSupportedFiberModel f T
  map := boundedFlatCoefficientSupportedFiberModelMap f T
  map_id a := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_id
      (boundedFlatCoefficientFiberSupportOpen f T a).ι
      (boundedFlatCoefficientFiberSupportPairMap f T (𝟙 a)).hom.left
      (Arrow.w (boundedFlatCoefficientFiberSupportPairMap f T (𝟙 a)).hom)
  map_comp {a b c} g h := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_comp
      (boundedFlatCoefficientFiberSupportOpen f T a).ι
      (boundedFlatCoefficientFiberSupportOpen f T b).ι
      (boundedFlatCoefficientFiberSupportOpen f T c).ι
      (i := (op Q, a)) (k := (op Q, b)) (t := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)
      (boundedFlatCoefficientFiberSupportPairMap f T g).hom.left
      (boundedFlatCoefficientFiberSupportPairMap f T h).hom.left
      (boundedFlatCoefficientFiberSupportPairMap f T (g ≫ h)).hom.left
      (Arrow.w (boundedFlatCoefficientFiberSupportPairMap f T g).hom)
      (Arrow.w (boundedFlatCoefficientFiberSupportPairMap f T h).hom)
      (Arrow.w (boundedFlatCoefficientFiberSupportPairMap f T (g ≫ h)).hom)

private theorem restrictionWeak_iff {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (A : X.Opens)
    {K L : (boundedFlatPerfectSupported A.ι).FullSubcategory} (p : K ⟶ L) :
    (boundedFlatPerfectSupportedWaldhausen (j ⁻¹ᵁ A).ι).weq
        ((boundedFlatPerfectSupportedPullback (supportRestrictionPair j A)).map p) ↔
      (boundedFlatPerfectSupportedOpenWaldhausen j A).weq p := by
  let e := restrictIsoPullbackComplex j
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app K.obj) (e.app L.obj) (e.hom.naturality p.hom).symm)).symm

-- Factor the comparison over the original joint indices before specializing a native fiber.
private theorem supportedSectionRestrictionWeak_iff {i k : Index R}
    (η : i ⟶ k) [IsOpenImmersion (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η)]
    (A : (space i).Opens) {S V : BoundedFlatCoefficientSupportedSections A.ι} (p : S ⟶ V) :
    (boundedFlatCoefficientSupportedSectionWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η ⁻¹ᵁ A).ι).weq
      ((boundedFlatCoefficientSupportedSectionsMap A.ι
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η ⁻¹ᵁ A).ι η
        (supportRestrictionPair (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A).hom.left
        (Arrow.w (supportRestrictionPair
          (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A).hom)).map p) ↔
      (boundedFlatPerfectSupportedOpenWaldhausen
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A).weq
        ((boundedFlatCoefficientSupportedEvaluation A.ι).map p) :=
  (boundedFlatCoefficientSupportedSectionsMap_weq_iff A.ι
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η ⁻¹ᵁ A).ι η
    (supportRestrictionPair (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A).hom.left
    (Arrow.w (supportRestrictionPair (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η)
      A).hom) p).trans
    (restrictionWeak_iff (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map η) A
      ((boundedFlatCoefficientSupportedEvaluation A.ι).map p))
/-- Coarse section weakness is exactly the original geometric supported relative-open weak class. -/
theorem boundedFlatCoefficientSupportedOpenWaldhausen_weq_iff (a : Under R)
    {S V : BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a} (p : S ⟶ V) :
    (boundedFlatCoefficientSupportedOpenWaldhausen f T a).weq p ↔
      (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).weq
        ((boundedFlatCoefficientSupportedEvaluation
          (i := (op Q, a)) (boundedFlatCoefficientSupportOpen Q T a).ι).map p) := by
  let : IsOpenImmersion (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)) :=
    (show IsOpenImmersion (schemeMap f a) from inferInstance)
  exact (Structure.withInverseImageWeak_weq_iff
    (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a) p).trans
    (supportedSectionRestrictionWeak_iff
      (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
      (boundedFlatCoefficientSupportOpen Q T a) p)

end Quillen.PerfectComplexes
