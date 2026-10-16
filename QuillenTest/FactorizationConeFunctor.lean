/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Waldhausen.SplitComplexes.FactorizationConeFunctor
/-! Original signed quotient and exactness clients. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen.Waldhausen.SplitFactorization
universe u v u' v'
namespace QuillenTest.FactorizationConeFunctor
variable {A : Type u} [Category.{v} A] [Abelian A]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  {F G : D ⥤ CochainComplex A ℤ} [F.Additive] [G.Additive] (α : F ⟶ G)

omit [Preadditive D] [F.Additive] [G.Additive] in
/-- No original quotient coordinate is replaced by an arbitrary cofiber map. -/
theorem original_quotient (X : D) : (quotientToConeNatTrans α).app X =
    quotientMap (α.app X) ≫ (Quillen.CochainComplex.mappingConeNegIso (α.app X)).hom := rfl

/-- The input sequence may be any inherited short exact sequence. -/
theorem arbitrary_short_exact (S : ShortComplex D) (hF : (S.map F).ShortExact)
    (hG : (S.map G).ShortExact) : (S.map (middleNatTransFunctor α)).ShortExact :=
  middleNatTransFunctor_shortExact α S hF hG

omit [Preadditive D] [F.Additive] [G.Additive] in
/-- The original projection factors the same original transformation. -/
theorem original_factorization : inclusionNatTrans α ≫ projectionNatTrans α = α :=
  inclusionNatTrans_projection α

end QuillenTest.FactorizationConeFunctor
