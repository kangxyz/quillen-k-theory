/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare

/-!
# Natural zero evaluation in the original coefficient category

Literal polynomial evaluation at zero is natural over the fixed coefficient ring and splits
the original polynomial inclusion as a natural transformation, before passing to any K-group.

This general candidate is intended for `Aglib.Algebra.Polynomial.Laurent.UnderZero`. It uses
arbitrary commutative rings, with no additional hypotheses. Its current consumer is the
original coefficient Bass common-corner retraction.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace CommRingCat.PolynomialLaurent

variable (R : CommRingCat.{u})

/-- The original zero evaluation retains the actual structure map from the fixed ring. -/
def polynomialUnderZero (a : Under R) : (polynomialUnderFunctor R).obj a ⟶ a :=
  Under.homMk (CommRingCat.ofHom (Polynomial.evalRingHom (0 : a.right))) (by
    change (a.hom ≫ coefficient a.right) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : a.right)) = a.hom
    have hc : coefficient a.right ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : a.right)) = 𝟙 a.right := by
      apply CommRingCat.hom_ext
      ext x
      change Polynomial.eval 0 (Polynomial.C x) = x
      simp
    rw [Category.assoc, hc, Category.comp_id])

/-- The actual zero evaluation commutes with every original coefficient-ring map. -/
@[reassoc]
theorem polynomialUnderZero_naturality {a b : Under R} (f : a ⟶ b) :
    (polynomialUnderFunctor R).map f ≫ polynomialUnderZero R b =
      polynomialUnderZero R a ≫ f := by
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext p
  change (Polynomial.map f.right.hom p).eval 0 = f.right.hom (p.eval 0)
  simpa only [map_zero] using Polynomial.eval_map_apply (p := p) f.right.hom 0

/-- Zero evaluation is an actual natural transformation on the fixed coefficient category. -/
def polynomialUnderZeroNat : polynomialUnderFunctor R ⟶ 𝟭 (Under R) where
  app := polynomialUnderZero R
  naturality _ _ f := polynomialUnderZero_naturality R f

/-- Original inclusion followed by original evaluation is literally the identity. -/
@[reassoc (attr := simp)]
theorem polynomialUnderCoefficient_zero (a : Under R) :
    (polynomialUnderCoefficient R).app a ≫ polynomialUnderZero R a = 𝟙 a := by
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext x
  change Polynomial.eval 0 (Polynomial.C x) = x
  simp

/-- The polynomial inclusion is split naturally, not only object by object. -/
@[reassoc (attr := simp)]
theorem polynomialUnderCoefficient_zeroNat :
    polynomialUnderCoefficient R ≫ polynomialUnderZeroNat R = 𝟙 (𝟭 (Under R)) := by
  apply NatTrans.ext
  funext a
  exact polynomialUnderCoefficient_zero R a

end CommRingCat.PolynomialLaurent
