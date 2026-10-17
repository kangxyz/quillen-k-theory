/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentKOperation
public import Quillen.Aglib.Algebra.Polynomial.Laurent.UnderZero
public import Quillen.KTheory.Bass.TwoChartAdditive
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Natural maps splitting the original coefficient Bass row

The original bounded-flat K-groups form an additive-group-valued coefficient functor under
all coefficient maps. Literal zero evaluation retracts the common-corner map naturally, and
the literal inverse Laurent-unit operation is a natural degree-raising transformation.
These constructions require no flatness or compactness assumptions on the coefficient maps.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Bass.TwoChart
universe u
namespace Quillen.PerfectComplexes

attribute [local instance] Waldhausen.Additivity.KCommGroup

/-- The original bounded-flat K-functor with its actual abelian group structure. -/
def boundedFlatPerfectKAddFunctor (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj X := AddCommGrpCat.of (Additive (BoundedFlatPerfectK X.unop n))
  map f := AddCommGrpCat.ofHom (boundedFlatPerfectKPullback f.unop n).toAdditive
  map_id X := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive (boundedFlatPerfectKPullback_id X.unop n)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive
      (boundedFlatPerfectKPullback_comp g.unop f.unop n)

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The original chosen coefficient fibers and pullbacks, with no replaced K-group. -/
def boundedFlatCoefficientKAddFunctor (n : ℕ) : Under R ⥤ AddCommGrpCat.{u + 1} :=
  row P ⋙ BaseChange.Coefficients.functor R ⋙ boundedFlatPerfectKAddFunctor n

/-- The actual source functor of the original two-chart difference. -/
def boundedFlatCoefficientPolynomialPairFunctor (n : ℕ) :
    Under R ⥤ AddCommGrpCat.{u + 1} :=
  polynomialDifferenceDiagram (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientKAddFunctor P n) ⋙ Arrow.leftFunc

/-- Both actual coefficient inclusions, as a natural common-corner homomorphism. -/
def boundedFlatCoefficientCorner (n : ℕ) :
    boundedFlatCoefficientKAddFunctor P n ⟶ boundedFlatCoefficientPolynomialPairFunctor P n where
  app a := biprod.lift
    ((boundedFlatCoefficientKAddFunctor P n).map ((polynomialUnderCoefficient R).app a))
    ((boundedFlatCoefficientKAddFunctor P n).map ((polynomialUnderCoefficient R).app a))
  naturality {a b} f := by
    have h := congrArg (boundedFlatCoefficientKAddFunctor P n).map
      ((polynomialUnderCoefficient R).naturality f)
    apply biprod.hom_ext <;>
      simpa [boundedFlatCoefficientPolynomialPairFunctor, polynomialDifferenceDiagram,
        ← CategoryTheory.Functor.map_comp] using h

/-- Literal zero evaluation on the first chart, natural under every coefficient map. -/
def boundedFlatCoefficientCornerRetraction (n : ℕ) :
    boundedFlatCoefficientPolynomialPairFunctor P n ⟶ boundedFlatCoefficientKAddFunctor P n where
  app a := biprod.fst ≫
    (boundedFlatCoefficientKAddFunctor P n).map (polynomialUnderZero R a)
  naturality {a b} f := by
    change biprod.map _ _ ≫ biprod.fst ≫ _ = (biprod.fst ≫ _) ≫ _
    rw [biprod.map_fst_assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      polynomialUnderZero_naturality]

/-- The first splitting is an equality of original natural transformations. -/
@[reassoc (attr := simp)]
theorem boundedFlatCoefficientCorner_retraction (n : ℕ) :
    boundedFlatCoefficientCorner P n ≫ boundedFlatCoefficientCornerRetraction P n =
      𝟙 (boundedFlatCoefficientKAddFunctor P n) := by
  apply NatTrans.ext
  funext a
  change biprod.lift _ _ ≫ biprod.fst ≫ _ = _
  rw [biprod.lift_fst_assoc, ← CategoryTheory.Functor.map_comp,
    polynomialUnderCoefficient_zero]
  exact (boundedFlatCoefficientKAddFunctor P n).map_id a

/-- The actual first short row uses the categorical cokernel of the original common corner. -/
def boundedFlatCoefficientCornerSequence (n : ℕ) :
    ShortComplex (Under R ⥤ AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (boundedFlatCoefficientCorner P n)
    (cokernel.π (boundedFlatCoefficientCorner P n)) (cokernel.condition _)

/-- The original first short row is split as functors, using actual zero evaluation. -/
def boundedFlatCoefficientCornerSplitting (n : ℕ) :
    (boundedFlatCoefficientCornerSequence P n).Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    (ShortComplex.cokernelSequence_exact (boundedFlatCoefficientCorner P n))
    (boundedFlatCoefficientCornerRetraction P n)
    (boundedFlatCoefficientCorner_retraction P n) (by
      change Epi (cokernel.π (boundedFlatCoefficientCorner P n))
      infer_instance)

/-- The actual Bass contraction preserves this constructed splitting without an epimorphic
chart-difference assumption. -/
def boundedFlatCoefficientContractedCornerSplitting (n : ℕ) :
    ((boundedFlatCoefficientCornerSequence P n).map
      (contractionFunctor (underToLaurent R) (underToLaurentInvert R))).Splitting :=
  (boundedFlatCoefficientCornerSplitting P n).map
    (contractionFunctor (underToLaurent R) (underToLaurentInvert R))

/-- The literal inverse Laurent-unit operation is natural in the original coefficient row. -/
def boundedFlatCoefficientInverseUnitSection (n : ℕ) :
    boundedFlatCoefficientKAddFunctor P n ⟶
      laurentUnderFunctor R ⋙ boundedFlatCoefficientKAddFunctor P (n + 1) where
  app a := AddCommGrpCat.ofHom
    (boundedFlatCoefficientInverseLaurentKOperation P a n).toAdditive
  naturality {a b} f := by
    apply AddCommGrpCat.hom_ext
    exact (congrArg MonoidHom.toAdditive
      (boundedFlatCoefficientInverseLaurentKOperation_naturality P f n)).symm

end Quillen.PerfectComplexes
