/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.CoefficientBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurentBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Affine.LaurentUnitNaturality
public import Quillen.Algebra.Polynomial.LaurentUnderSquare

/-!
# Original native coefficient Laurent geometry

The fixed native pullbacks give the original two polynomial charts and Laurent corner.
Actual pullback isomorphisms compare these corners with the common integer-base products;
the chosen pullbacks are never equated. The original coefficient projections identify the
forward Laurent unit on the native fiber with the same integer-coordinate unit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.Bass
universe u
namespace Quillen.Scheme.CoefficientBaseChange
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- Original native coefficient reindexing as a scheme map. -/
def coefficientMap {a b : Under R} (g : a ⟶ b) : space (op P, b) ⟶ space (op P, a) :=
  map (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)

/-- Its square with the actual coefficient projections is cartesian. -/
theorem coefficientMap_isPullback {a b : Under R} (g : a ⟶ b) :
    IsPullback (coefficientMap P g) (coefficientProjection (op P, b))
      (coefficientProjection (op P, a)) (Spec.map g.right) := by
  apply IsPullback.of_right (h₁₂ := projection (op P, a)) (h₂₂ := Spec.map a.hom)
  · have hp : coefficientMap P g ≫ projection (op P, a) = projection (op P, b) := by
      rw [coefficientMap, map_projection]
      exact Category.comp_id _
    rw [hp, ← Spec.map_comp, Under.w g]
    exact IsPullback.of_hasPullback P.hom (Spec.map b.hom)
  · exact map_coefficientProjection (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
  · exact IsPullback.of_hasPullback P.hom (Spec.map a.hom)

/-- Original native coefficient maps compose on the same fixed fibers. -/
theorem coefficientMap_comp {a b c : Under R} (g : a ⟶ b) (h : b ⟶ c) :
    coefficientMap P (g ≫ h) = coefficientMap P h ≫ coefficientMap P g := by
  have hc := map_comp (i := (op P, a)) (k := (op P, b)) (l := (op P, c))
    (𝟙 (op P), g) (𝟙 (op P), h)
  change map (i := (op P, a)) (k := (op P, c))
    (𝟙 (op P) ≫ 𝟙 (op P), g ≫ h) = _ at hc
  simpa only [Category.id_comp, coefficientMap] using hc

/-- Every coefficient arrow retains the original native coefficient projection square. -/
@[reassoc] theorem coefficientMap_coefficientProjection {a b : Under R} (g : a ⟶ b) :
    coefficientMap P g ≫ coefficientProjection (op P, a) =
      coefficientProjection (op P, b) ≫ Spec.map g.right :=
  map_coefficientProjection (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)

/-- All four original native corners and their actual geometric maps. -/
def laurentSquare (a : Under R) : Arrow (Arrow AlgebraicGeometry.Scheme.{u}ᵒᵖ) :=
  (row P ⋙ functor R).mapArrow.mapArrow.obj (laurentUnderSquare R a)

/-- Original positive-chart projection from the fixed polynomial coefficient fiber. -/
def polynomialProjection (a : Under R) :
    space (op P, (polynomialUnderFunctor R).obj a) ⟶ space (op P, a) :=
  coefficientMap P ((polynomialUnderCoefficient R).app a)

/-- Original projection from the fixed Laurent coefficient fiber. -/
def laurentProjection (a : Under R) :
    space (op P, (laurentUnderFunctor R).obj a) ⟶ space (op P, a) :=
  coefficientMap P ((laurentUnderCoefficient R).app a)

/-- The original positive-coordinate chart on the fixed native coefficient fibers. -/
def laurentPlus (a : Under R) :
    space (op P, (laurentUnderFunctor R).obj a) ⟶
      space (op P, (polynomialUnderFunctor R).obj a) :=
  coefficientMap P ((underToLaurent R).app a)

/-- The original inverse-coordinate chart; its source still carries the forward unit. -/
def laurentMinus (a : Under R) :
    space (op P, (laurentUnderFunctor R).obj a) ⟶
      space (op P, (polynomialUnderFunctor R).obj a) :=
  coefficientMap P ((underToLaurentInvert R).app a)

/-- Both original positive source legs have the same actual native coefficient composite. -/
@[reassoc] theorem laurentPlus_projection (a : Under R) :
    laurentPlus P a ≫ polynomialProjection P a = laurentProjection P a := by
  change coefficientMap P ((underToLaurent R).app a) ≫
    coefficientMap P ((polynomialUnderCoefficient R).app a) = _
  rw [← coefficientMap_comp, polynomialUnderCoefficient_toLaurent]
  rfl

/-- The original inverse chart has precisely that same actual native coefficient composite. -/
@[reassoc] theorem laurentMinus_projection (a : Under R) :
    laurentMinus P a ≫ polynomialProjection P a = laurentProjection P a := by
  change coefficientMap P ((underToLaurentInvert R).app a) ≫
    coefficientMap P ((polynomialUnderCoefficient R).app a) = _
  rw [← coefficientMap_comp, polynomialUnderCoefficient_toLaurentInvert]
  rfl

/-- The native polynomial fiber is the actual product over the common integral base. -/
theorem polynomial_isPullback (a : Under R) :
    IsPullback (polynomialProjection P a)
      (coefficientProjection (op P, (polynomialUnderFunctor R).obj a) ≫
        Spec.map (polynomialMap (Bass.integerMap a.right)))
      (toIntegerBase (space (op P, a)))
      (PolynomialLaurent.polynomialProjection Bass.integerRing) := by
  have h := (coefficientMap_isPullback P ((polynomialUnderCoefficient R).app a)).paste_vert
    (Bass.polynomialSpec_isPullback a.right)
  simpa only [Functor.id_obj, toIntegerBase_naturality, polynomialProjection] using h

/-- The native Laurent fiber is the actual product over the same integral base. -/
theorem laurent_isPullback (a : Under R) :
    IsPullback (laurentProjection P a)
      (coefficientProjection (op P, (laurentUnderFunctor R).obj a) ≫
        Spec.map (laurentMap (Bass.integerMap a.right)))
      (toIntegerBase (space (op P, a)))
      (PolynomialLaurent.laurentProjection Bass.integerRing) := by
  have h := (coefficientMap_isPullback P ((laurentUnderCoefficient R).app a)).paste_vert
    (Bass.laurentSpec_isPullback a.right)
  simpa only [Functor.id_obj, toIntegerBase_naturality, laurentProjection] using h

/-- Actual comparison with the specified polynomial product, preserving its projections. -/
def polynomialIso (a : Under R) :
    space (op P, (polynomialUnderFunctor R).obj a) ≅
      (baseProductFunctor (PolynomialLaurent.polynomialProjection Bass.integerRing)).obj
        (space (op P, a)) := (polynomial_isPullback P a).isoPullback

/-- Actual comparison with the specified Laurent product, preserving its projections. -/
def laurentIso (a : Under R) :
    space (op P, (laurentUnderFunctor R).obj a) ≅
      (baseProductFunctor (PolynomialLaurent.laurentProjection Bass.integerRing)).obj
        (space (op P, a)) := (laurent_isPullback P a).isoPullback

/-- The native polynomial comparison keeps the original source projection. -/
@[reassoc] theorem polynomialIso_hom_fst (a : Under R) :
    (polynomialIso P a).hom ≫ pullback.fst _ _ = polynomialProjection P a :=
  (polynomial_isPullback P a).isoPullback_hom_fst

/-- The native polynomial comparison keeps its exact integer coefficient leg. -/
@[reassoc] theorem polynomialIso_hom_snd (a : Under R) :
    (polynomialIso P a).hom ≫ pullback.snd _ _ =
      coefficientProjection (op P, (polynomialUnderFunctor R).obj a) ≫
        Spec.map (polynomialMap (Bass.integerMap a.right)) :=
  (polynomial_isPullback P a).isoPullback_hom_snd

/-- The native Laurent comparison keeps the original source projection. -/
@[reassoc] theorem laurentIso_hom_fst (a : Under R) :
    (laurentIso P a).hom ≫ pullback.fst _ _ = laurentProjection P a :=
  (laurent_isPullback P a).isoPullback_hom_fst

/-- The native Laurent comparison keeps its exact integer coefficient leg. -/
@[reassoc] theorem laurentIso_hom_snd (a : Under R) :
    (laurentIso P a).hom ≫ pullback.snd _ _ =
      coefficientProjection (op P, (laurentUnderFunctor R).obj a) ≫
        Spec.map (laurentMap (Bass.integerMap a.right)) :=
  (laurent_isPullback P a).isoPullback_hom_snd

/-- The actual positive chart agrees under the original native/product isomorphisms. -/
@[reassoc] theorem polynomialLaurentIso_plus (a : Under R) :
    laurentPlus P a ≫ (polynomialIso P a).hom =
      (laurentIso P a).hom ≫
        (baseProductTransformation _ _ (PolynomialLaurent.laurentPlus Bass.integerRing)
          (PolynomialLaurent.laurentPlus_projection Bass.integerRing)).app (space (op P, a)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, polynomialIso_hom_fst, baseProductTransformation,
      pullback.lift_fst, Category.comp_id, laurentIso_hom_fst, laurentPlus_projection]
  · simp only [Category.assoc, polynomialIso_hom_snd, baseProductTransformation,
      pullback.lift_snd, laurentIso_hom_snd_assoc]
    change coefficientMap P ((underToLaurent R).app a) ≫
      coefficientProjection (op P, (polynomialUnderFunctor R).obj a) ≫ _ = _
    rw [coefficientMap_coefficientProjection_assoc]
    change coefficientProjection (op P, (laurentUnderFunctor R).obj a) ≫
      PolynomialLaurent.laurentPlus a.right ≫ Spec.map (polynomialMap (Bass.integerMap a.right)) = _
    rw [PolynomialLaurent.laurentPlus, PolynomialLaurent.laurentPlus,
      ← Spec.map_comp, ← Spec.map_comp, toLaurent_naturality]

/-- The inverse-coordinate chart agrees as well, retaining its original inversion. -/
@[reassoc] theorem polynomialLaurentIso_minus (a : Under R) :
    laurentMinus P a ≫ (polynomialIso P a).hom =
      (laurentIso P a).hom ≫
        (baseProductTransformation _ _ (PolynomialLaurent.laurentMinus Bass.integerRing)
          (PolynomialLaurent.laurentMinus_projection Bass.integerRing)).app (space (op P, a)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, polynomialIso_hom_fst, baseProductTransformation,
      pullback.lift_fst, Category.comp_id, laurentIso_hom_fst, laurentMinus_projection]
  · simp only [Category.assoc, polynomialIso_hom_snd, baseProductTransformation,
      pullback.lift_snd, laurentIso_hom_snd_assoc]
    change coefficientMap P ((underToLaurentInvert R).app a) ≫
      coefficientProjection (op P, (polynomialUnderFunctor R).obj a) ≫ _ = _
    rw [coefficientMap_coefficientProjection_assoc]
    change coefficientProjection (op P, (laurentUnderFunctor R).obj a) ≫
      PolynomialLaurent.laurentMinus a.right ≫
        Spec.map (polynomialMap (Bass.integerMap a.right)) = _
    rw [PolynomialLaurent.laurentMinus, PolynomialLaurent.laurentMinus,
      ← Spec.map_comp, ← Spec.map_comp, minus_naturality]

/-- The common integer-coordinate unit pulls back to the original native forward unit. -/
theorem laurentIso_globalUnit (a : Under R) :
    Units.map (laurentIso P a).hom.appTop.hom.toMonoidHom
      (Units.map (pullback.snd (toIntegerBase (space (op P, a)))
        (PolynomialLaurent.laurentProjection Bass.integerRing)).appTop.hom.toMonoidHom
          (PolynomialLaurent.laurentGlobalUnit Bass.integerRing)) =
      Units.map (coefficientProjection (op P, (laurentUnderFunctor R).obj a)).appTop.hom.toMonoidHom
        (PolynomialLaurent.laurentGlobalUnit a.right) := by
  have hu := PolynomialLaurent.laurentGlobalUnit_coefficient (Bass.integerMap a.right)
  rw [← hu]
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (laurentIso_hom_snd P a)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑(PolynomialLaurent.laurentGlobalUnit Bass.integerRing))

end Quillen.Scheme.CoefficientBaseChange
