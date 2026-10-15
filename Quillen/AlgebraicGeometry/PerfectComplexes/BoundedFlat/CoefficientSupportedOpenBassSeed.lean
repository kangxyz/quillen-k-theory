/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionUnits
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenGrading
public import Quillen.KTheory.Bass.StrictLaurentSeedContraction

/-!
# Original auxiliary-supported coefficient Laurent actions and Bass seeds

Forward native coefficient units lift through the actual supported section
inclusions. Their original coefficient and restriction equations prove the
supported C_Z/F_Z/G_Z action tracks and seeds with the same square, joint zero,
source-leg cylinder and scalar/null concatenation. Equal endpoint grades make
the actual graded zero endomorphism weak and construct the complete graded
seed contraction. Only the G_Z coefficient diagram requires compact P and Q.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso boundedFlatCoefficientSectionLaurentUnitIso

/-- The actual coefficient unit restricted through the original supported section inclusion. -/
def boundedFlatCoefficientSupportSectionUnitIso {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] (r : (Γ(Spec i.2.right, ⊤))ˣ) :
    𝟭 (BoundedFlatCoefficientSupportedSections j) ≅
      𝟭 (BoundedFlatCoefficientSupportedSections j) :=
  lift (boundedFlatCoefficientSectionSupported j).ι
    (boundedFlatCoefficientSectionUnitIso i (boundedFlatCoefficientUnit i r))

/-- Forgetting support retains exactly the original forward coefficient-unit component. -/
theorem boundedFlatCoefficientSupportSectionUnitIso_hom {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] (r : (Γ(Spec i.2.right, ⊤))ˣ)
    (S : BoundedFlatCoefficientSupportedSections j) :
    ((boundedFlatCoefficientSupportSectionUnitIso j r).hom.app S).hom =
      (boundedFlatCoefficientSectionUnitIso i (boundedFlatCoefficientUnit i r)).hom.app S.obj :=
  map_lift_hom (boundedFlatCoefficientSectionSupported j).ι _ S

private theorem supportMap_preserves_lift {i k : Index R} {U V : Scheme.{u}}
    (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
    (η : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      η)
    (α : 𝟭 (BoundedFlatCoefficientSections i) ≅ 𝟭 (BoundedFlatCoefficientSections i))
    (β : 𝟭 (BoundedFlatCoefficientSections k) ≅ 𝟭 (BoundedFlatCoefficientSections k))
    (hαβ : Preserves (boundedFlatCoefficientSectionsMap η) α β) :
    Preserves (boundedFlatCoefficientSupportedSectionsMap j j' η l h)
      (lift (boundedFlatCoefficientSectionSupported j).ι α)
      (lift (boundedFlatCoefficientSectionSupported j').ι β) := by
  intro S
  apply ObjectProperty.hom_ext
  change (boundedFlatCoefficientSectionsMap η).map
    ((lift (boundedFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    ((lift (boundedFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom
  rw [show ((lift (boundedFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    α.hom.app S.obj from map_lift_hom (boundedFlatCoefficientSectionSupported j).ι α S,
    show ((lift (boundedFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom =
      β.hom.app ((boundedFlatCoefficientSectionsMap η).obj S.obj) from
      map_lift_hom (boundedFlatCoefficientSectionSupported j').ι β _]
  exact hαβ S.obj

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original ambient Laurent unit on its actual auxiliary-supported native fiber. -/
def boundedFlatCoefficientSupportedAmbientLaurentUnitIso (Q : Over (Spec R))
    (T : Q.left.Opens) (a : Under R) :=
  lift (boundedFlatCoefficientSectionSupported
    (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a)).ι).ι
    (boundedFlatCoefficientSectionLaurentUnitIso Q a)

/-- The original restricted Laurent unit on the true open-side auxiliary support. -/
def boundedFlatCoefficientSupportedFullOpenLaurentUnitIso (a : Under R) :=
  lift (boundedFlatCoefficientSectionSupported
    (boundedFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj a)).ι).ι
    (boundedFlatCoefficientSectionLaurentUnitIso P a)

omit [IsOpenImmersion f.left] in
/-- Actual ambient supported coefficient reindexing preserves the original Laurent coordinate. -/
theorem boundedFlatCoefficientSupportedAmbientLaurentUnitIso_coefficient
    (Q : Over (Spec R)) (T : Q.left.Opens) {a b : Under R} (g : a ⟶ b) :
    Preserves (boundedFlatCoefficientSupportedAmbientMap T ((laurentUnderFunctor R).map g))
      (boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T a)
      (boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T b) :=
  supportMap_preserves_lift
    (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a)).ι
    (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj b)).ι
    (𝟙 (op Q), (laurentUnderFunctor R).map g)
    (boundedFlatCoefficientSupportPairMap Q T ((laurentUnderFunctor R).map g)).hom.left
    (Arrow.w (boundedFlatCoefficientSupportPairMap Q T ((laurentUnderFunctor R).map g)).hom)
    _ _ (boundedFlatCoefficientSectionLaurentUnitIso_coefficient Q g)

omit [IsOpenImmersion f.left] in
/-- Actual open-side supported coefficient reindexing preserves the same Laurent coordinate. -/
theorem boundedFlatCoefficientSupportedFullOpenLaurentUnitIso_coefficient
    {a b : Under R} (g : a ⟶ b) :
    Preserves (boundedFlatCoefficientSupportedOpenMap f T ((laurentUnderFunctor R).map g))
      (boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T a)
      (boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T b) :=
  supportMap_preserves_lift
    (boundedFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj a)).ι
    (boundedFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj b)).ι
    (𝟙 (op P), (laurentUnderFunctor R).map g)
    (boundedFlatCoefficientOpenSupportPairMap f T ((laurentUnderFunctor R).map g)).hom.left
    (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T ((laurentUnderFunctor R).map g)).hom)
    _ _ (boundedFlatCoefficientSectionLaurentUnitIso_coefficient P g)

omit [IsOpenImmersion f.left] in
/-- The actual supported restriction preserves each forward Laurent-unit component. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_laurentUnit_preserves (a : Under R) :
    Preserves (boundedFlatCoefficientSupportedOpenRestriction f T
      ((laurentUnderFunctor R).obj a))
      (boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T a)
      (boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T a) :=
  supportMap_preserves_lift
    (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a)).ι
    (boundedFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj a)).ι
    (f.op, 𝟙 ((laurentUnderFunctor R).obj a))
    (supportRestrictionPair (schemeMap f ((laurentUnderFunctor R).obj a))
      (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a))).hom.left
    (Arrow.w (supportRestrictionPair (schemeMap f ((laurentUnderFunctor R).obj a))
      (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a))).hom)
    _ _ (boundedFlatCoefficientSectionLaurentUnitIso_restriction f a)

omit [IsOpenImmersion f.left] in
/-- Supported restriction retains every original coefficient scalar through its actual map. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_coefficientUnit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedFlatCoefficientSupportedOpenRestriction f T a)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientSupportOpen Q T a).ι r)
      (boundedFlatCoefficientSupportSectionUnitIso
        (boundedFlatCoefficientOpenSupportOpen f T a).ι r) :=
  supportMap_preserves_lift (boundedFlatCoefficientSupportOpen Q T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T a).ι (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)).hom.left
    (Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)).hom)
    _ _ (boundedFlatCoefficientSectionsRestriction_unit_preserves f a r)

/-- The original ambient forward Laurent unit, with its proved coefficient naturality. -/
def boundedFlatCoefficientSupportedOpenLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedOpenModelFunctor f T) where
  unit a := boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T a
  naturality g := boundedFlatCoefficientSupportedAmbientLaurentUnitIso_coefficient Q T g

/-- The original restricted forward Laurent unit on the actual native fine open row. -/
def boundedFlatCoefficientSupportedFullOpenLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedFullOpenModelFunctor f T) where
  unit a := boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T a
  naturality g := boundedFlatCoefficientSupportedFullOpenLaurentUnitIso_coefficient f T g

/-- The entire original ambient Laurent action track on the unchanged coefficient Model map. -/
def boundedFlatCoefficientSupportedOpenLaurentHomotopy (a : Under R) :=
  (boundedFlatCoefficientSupportedOpenLaurentAction f T).track.homotopy a

/-- The entire original restricted Laurent action track on the actual fine open Model map. -/
def boundedFlatCoefficientSupportedFullOpenLaurentHomotopy (a : Under R) :=
  (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track.homotopy a

/-- All four original ambient native corners with their original positive and inverse charts. -/
def boundedFlatCoefficientSupportedOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T) a

/-- All four original fine open corners with the same coefficient charts. -/
def boundedFlatCoefficientSupportedFullOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) a

/-- The actual mapping cone of the original ambient square comparison. -/
def boundedFlatCoefficientSupportedOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T) a

/-- The actual mapping cone of the original fine open square comparison. -/
def boundedFlatCoefficientSupportedFullOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) a

/-- The original ambient source-leg cylinder; it is not a localization-null substitution. -/
def boundedFlatCoefficientSupportedOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T) a

/-- The original fine open source-leg cylinder on its unchanged native square. -/
def boundedFlatCoefficientSupportedFullOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) a

/-- The original ambient pointwise seed retains the prescribed scalar/null concatenation. -/
def boundedFlatCoefficientSupportedOpenBassSeedMap (a : Under R) :=
  (boundedFlatCoefficientSupportedOpenLaurentAction f T).track.seedMap a

/-- The original fine open pointwise seed retains that same prescribed concatenation. -/
def boundedFlatCoefficientSupportedFullOpenBassSeedMap (a : Under R) :=
  (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track.seedMap a

/-- The constructed coefficient-natural original ambient Bass seed. -/
def boundedFlatCoefficientSupportedOpenBassSeed :
    boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T) :=
  (boundedFlatCoefficientSupportedOpenLaurentAction f T).track.seed

/-- The constructed coefficient-natural original fine open Bass seed. -/
def boundedFlatCoefficientSupportedFullOpenBassSeed :
    boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) :=
  (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track.seed

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The same actual open unit acts on the original graded Model; only weakness changes. -/
def boundedFlatCoefficientSupportedGradedOpenLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedGradedOpenModelFunctor f T) where
  unit a := boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T a
  naturality g := boundedFlatCoefficientSupportedFullOpenLaurentUnitIso_coefficient f T g

/-- The unchanged forward Laurent unit realized in the original graded coefficient diagram. -/
def boundedFlatCoefficientSupportedGradedOpenLaurentHomotopy (a : Under R) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).track.homotopy a

/-- The original graded native four-corner square. -/
def boundedFlatCoefficientSupportedGradedOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) a

/-- The actual mapping cone of the original graded comparison map. -/
def boundedFlatCoefficientSupportedGradedOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) a

/-- The original graded source-leg cylinder, with every time parameter unchanged. -/
def boundedFlatCoefficientSupportedGradedOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) a

/-- The graded pointwise seed uses that original source-leg null and forward scalar action. -/
def boundedFlatCoefficientSupportedGradedOpenBassSeedMap (a : Under R) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).track.seedMap a

/-- The constructed coefficient-natural original graded Bass seed. -/
def boundedFlatCoefficientSupportedGradedOpenBassSeed :
    boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).track.seed

/-- The actual chosen-zero endomorphism has equal original quotient grades. -/
theorem boundedFlatCoefficientSupportedGradedLaurentZero_weak (a : Under R)
    (S : (boundedFlatCoefficientSupportedGradedOpenModelFunctor f T).obj a) :
    ((boundedFlatCoefficientSupportedGradedOpenModelFunctor f T).obj
      ((laurentUnderFunctor R).obj a)).waldhausen.weq
      ((modelZeroEndotransformation ((boundedFlatCoefficientSupportedGradedOpenModelFunctor f T).map
        ((laurentUnderCoefficient R).app a))).app S) := rfl

/-- The whole original Laurent-action contraction has its same scalar and point endpoints. -/
def boundedFlatCoefficientSupportedGradedLaurentContraction (a : Under R) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).contraction
    (boundedFlatCoefficientSupportedGradedLaurentZero_weak f T) a

/-- The same chosen contraction preserves both independent times under every coefficient map. -/
theorem boundedFlatCoefficientSupportedGradedLaurentContraction_naturality
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (r t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map
      ((laurentUnderFunctor R).map g)).map n
        ((boundedFlatCoefficientSupportedGradedLaurentContraction f T a).level n (r, (t, x))) =
      (boundedFlatCoefficientSupportedGradedLaurentContraction f T b).level n
        (r, (t, ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map g).map n
          x)) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).contraction_naturality
    (boundedFlatCoefficientSupportedGradedLaurentZero_weak f T) g n r t x

/-- The original graded seed is null through its prescribed original source-leg conjugation. -/
def boundedFlatCoefficientSupportedGradedOpenBassSeedNull (a : Under R) :
    LoopPrespectrum.Homotopy (boundedFlatCoefficientSupportedGradedOpenBassSeedMap f T a)
      (zeroHom ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a)
        (parameterLooping (boundedFlatCoefficientSupportedGradedOpenBassCone f T a))) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).seedNullHomotopy
    (boundedFlatCoefficientSupportedGradedLaurentZero_weak f T) a

/-- The whole original graded seed null is coefficient-natural, with its actual Bass target. -/
def boundedFlatCoefficientSupportedGradedOpenBassSeedDiagramNull :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedGradedOpenBassSeed f T)
      (𝟙 ((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T))) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).seedDiagramNull
    (boundedFlatCoefficientSupportedGradedLaurentZero_weak f T)

/-- The endpoint cast retains the same original graded seed-null time and loop value. -/
theorem boundedFlatCoefficientSupportedGradedOpenBassSeedDiagramNull_level (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedFlatCoefficientSupportedGradedOpenBassSeedDiagramNull f T).homotopy a).level n (r, x) =
      (boundedFlatCoefficientSupportedGradedOpenBassSeedNull f T a).level n (r, x) := rfl

end Quillen.PerfectComplexes
