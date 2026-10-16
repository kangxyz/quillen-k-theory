/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Relative
public import Quillen.KTheory.Bass.TwoChart
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPullbackFunctor
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
Genuine group-level Bass recursion on all quasi-compact schemes with arbitrary pullback maps. The
natural-number index n means K_{-n}; degree zero retains the original perfect K0 group and maps.
Representatives, exactness and unique descent use the displayed relative polynomial/Laurent schemes.
Geometric affine comparison, supported variants, spectral comparison and negative TT localization
are separate bridges.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.Bass
open AlgebraicGeometry.Scheme

/-- The commutative group structure on original perfect K0 supplied by additivity. -/
local instance perfectKZeroCommGroup (X : QuasiCompactSchemes.{u}) : CommGroup (PerfectK X.obj 0) :=
  Quillen.Waldhausen.Additivity.KCommGroup (perfectWaldhausen X.obj) 0

/-- The unchanged perfect K0 groups and original arbitrary pullbacks on all qc schemes. -/
def perfectKZeroMultiplicativeFunctor : QuasiCompactSchemes.{u}ᵒᵖ ⥤ CommGrpCat.{u+1} where
  obj X := .of (PerfectK X.unop.obj 0)
  map f := CommGrpCat.ofHom (perfectKPullback f.unop.hom 0)
  map_id X := by apply CommGrpCat.hom_ext; exact perfectKPullback_id X.unop.obj 0
  map_comp f g := by apply CommGrpCat.hom_ext; exact perfectKPullback_comp g.unop.hom f.unop.hom 0

/-- Original scheme K0 in additive notation, without changing its maps or group law. -/
def perfectKZeroFunctor : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u+1} :=
  perfectKZeroMultiplicativeFunctor ⋙ CommGrpCat.toAddCommGrp

/-- Genuine group-level Bass recursion on qc schemes. Index n denotes K_{-n}. -/
def negativeKFunctor : ℕ → QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u+1}
  | 0 => perfectKZeroFunctor
  | n+1 => Quillen.Bass.TwoChart.contraction (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
      (negativeKFunctor n)

/-- The Bass group K_{-n} of an actual quasi-compact scheme. -/
abbrev negativeK (X : QuasiCompactSchemes.{u}) (n : ℕ) : AddCommGrpCat.{u+1} :=
  (negativeKFunctor n).obj (op X)

/-- Genuine contravariant maps for arbitrary morphisms of qc schemes. -/
abbrev negativeKPullback {X Y : QuasiCompactSchemes.{u}} (f : X ⟶ Y) (n : ℕ) :
    negativeK Y n ⟶ negativeK X n := (negativeKFunctor n).map f.op

@[simp] lemma negativeKPullback_id (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    negativeKPullback (𝟙 X) n = 𝟙 (negativeK X n) := (negativeKFunctor n).map_id _

@[simp] lemma negativeKPullback_comp {X Y Z : QuasiCompactSchemes.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    negativeKPullback (f ≫ g) n = negativeKPullback g n ≫ negativeKPullback f n :=
  (negativeKFunctor n).map_comp g.op f.op

@[simp] lemma negativeKPullback_zero {X Y : QuasiCompactSchemes.{u}}
    (f : X ⟶ Y) (a : PerfectK Y.obj 0) :
    negativeKPullback f 0 (Additive.ofMul a) = Additive.ofMul (perfectKPullback f.hom 0 a) := rfl

/-- The actual Laurent quotient arrow in each successive negative degree. -/
def negativeKπ (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    negativeK (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X) n ⟶
      negativeK X (n+1) :=
  (Quillen.Bass.TwoChart.contractionπ (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (negativeKFunctor n)).app (op X)

@[reassoc] lemma negativeKπ_naturality {X Y : QuasiCompactSchemes.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.map f) n ≫
      negativeKπ X n =
      negativeKπ Y n ≫ negativeKPullback f (n+1) :=
  (Quillen.Bass.TwoChart.contractionπ (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (negativeKFunctor n)).naturality f.op

lemma negativeKπ_surjective (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    Function.Surjective (negativeKπ X n) :=
  Quillen.Bass.TwoChart.contractionπ_surjective _ _ _ _

/-- The literal two-chart relation on the actual relative polynomial/Laurent schemes. -/
lemma negativeKπ_eq_zero_iff (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (x : negativeK (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X) n) :
    negativeKπ X n x = 0 ↔ ∃ a b : negativeK
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.obj X) n,
      negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X) n a -
        negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X) n b = x
          :=
  Quillen.Bass.TwoChart.contractionπ_eq_zero_iff _ _ _ _ _

/-- The exact categorical Bass presentation of each successor degree. -/
lemma negativeK_exact (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (ShortComplex.mk
      (Quillen.Bass.TwoChart.polynomialDifference (NatTrans.op
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
        (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) (negativeKFunctor n)
          (op X)) (negativeKπ X n)
      (Quillen.Bass.TwoChart.polynomialDifference_contractionπ _ _ _ _)).Exact :=
  Quillen.Bass.TwoChart.contraction_exact _ _ _ _

instance negativeKπ_epi (X : QuasiCompactSchemes.{u}) (n : ℕ) : Epi (negativeKπ X n) :=
  Quillen.Bass.TwoChart.contractionπ_epi _ _ _ _

/-- On any actual flat morphism the original degree-zero map is the exact flat-pullback map. -/
lemma negativeKPullback_flat {X Y : QuasiCompactSchemes.{u}}
    (f : X ⟶ Y) [Flat f.hom] (a : PerfectK Y.obj 0) :
    negativeKPullback f 0 (Additive.ofMul a) = Additive.ofMul (perfectKFlatPullback f.hom 0 a) := by
  rw [negativeKPullback_zero,perfectKPullback_eq_flatPullback]

/-- Descent of a prescribed Laurent homomorphism annihilating both original chart pullbacks. -/
def negativeKDesc (X : QuasiCompactSchemes.{u}) (n : ℕ) {A : AddCommGrpCat.{u + 1}}
    (f : negativeK (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X) n ⟶ A)
    (hp : negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X) n ≫ f =
      0)
    (hm : negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X) n ≫ f
      = 0) :
    negativeK X (n+1) ⟶ A :=
  Quillen.Bass.TwoChart.contractionDescOfCharts (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
    (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) (negativeKFunctor n) (op
      X) f hp hm

@[reassoc (attr := simp)] lemma negativeKπ_desc (X : QuasiCompactSchemes.{u}) (n : ℕ)
    {A : AddCommGrpCat.{u + 1}} (f : negativeK
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X) n ⟶ A)
    (hp : negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X) n ≫ f =
      0)
    (hm : negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X) n ≫ f
      = 0) :
    negativeKπ X n ≫ negativeKDesc X n f hp hm = f :=
  Quillen.Bass.TwoChart.contractionπ_descOfCharts (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
    (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) (negativeKFunctor n) (op
      X) f hp hm

lemma negativeKDesc_unique (X : QuasiCompactSchemes.{u}) (n : ℕ)
    {A : AddCommGrpCat.{u + 1}} (f : negativeK
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.obj X) n ⟶ A)
    (hp : negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus.app X) n ≫ f =
      0)
    (hm : negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus.app X) n ≫ f
      = 0)
    (g : negativeK X (n + 1) ⟶ A) (hg : negativeKπ X n ≫ g = f) :
    g = negativeKDesc X n f hp hm := by
  exact (cancel_epi (negativeKπ X n)).mp (hg.trans (negativeKπ_desc X n f hp hm).symm)

end Quillen.PerfectComplexes.Bass

end
