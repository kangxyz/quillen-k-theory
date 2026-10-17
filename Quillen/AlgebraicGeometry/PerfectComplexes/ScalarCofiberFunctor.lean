/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarConeFunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberPrism
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationConeFunctor
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# The original scalar cylinder as a genuine cofibration sequence of exact functors

The original inclusion, middle object and projection retain their actual factorization maps.
The third functor is the literal signed scalar cone, with the original quotientToCone. Genuine
inherited conflations and quotient exactness give the relative cofibration condition. The original
zero-corner pushout proves a cofibration sequence without replacing the inherited exact structure
by split cofibrations or choosing a categorical-cofiber substitute.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization
open Quillen.Waldhausen.Fibration Quillen.Waldhausen.GilletWaldhausen
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Abelian.hasFiniteBiproducts
variable (X : Scheme.{u}) (r : Γ(X, ⊤))

/-- The original cylinder middle object and maps for the actual scalar transformation. -/
def perfectScalarMiddleFunctor : Perfect X ⥤ Perfect X :=
  (locallyPerfect X).lift
    (middleNatTransFunctor (Functor.whiskerRight (perfectGlobalScalar X r) (locallyPerfect X).ι))
    (fun K => middle_property (locallyPerfect X)
      (fun hA hB f => locallyPerfect_mappingCone hA hB f)
      K.property K.property ((complexGlobalScalar X r).app K.obj))

/-- The same original first factor, now as a natural transformation. -/
def perfectScalarInclusionNat : 𝟭 (Perfect X) ⟶ perfectScalarMiddleFunctor X r where
  app K := perfectScalarInclusion X r K
  naturality _ _ g := ObjectProperty.hom_ext _
    ((inclusionNatTrans (Functor.whiskerRight (perfectGlobalScalar X r)
      (locallyPerfect X).ι)).naturality g)

/-- The same original weak projection, now as a natural transformation. -/
def perfectScalarProjectionNat : perfectScalarMiddleFunctor X r ⟶ 𝟭 (Perfect X) where
  app K := perfectScalarProjection X r K
  naturality _ _ g := ObjectProperty.hom_ext _
    ((projectionNatTrans (Functor.whiskerRight (perfectGlobalScalar X r)
      (locallyPerfect X).ι)).naturality g)

/-- The original signed quotient, naturally into the literal scalar cone. -/
def perfectScalarConeProjectionNat :
    perfectScalarMiddleFunctor X r ⟶ perfectScalarConeFunctor X r where
  app K := (locallyPerfect X).homMk (quotientToCone ((complexGlobalScalar X r).app K.obj))
  naturality _ _ g := ObjectProperty.hom_ext _
    ((quotientToConeNatTrans (Functor.whiskerRight (perfectGlobalScalar X r)
      (locallyPerfect X).ι)).naturality g)

/-- The actual two factors still compose to the original scalar. -/
theorem perfectScalarInclusionNat_projection :
    perfectScalarInclusionNat X r ≫ perfectScalarProjectionNat X r = perfectGlobalScalar X r := by
  apply NatTrans.ext
  funext K
  exact perfectScalarInclusion_projection X r K

/-- The actual first factor and signed quotient compose to zero. -/
theorem perfectScalarInclusionNat_quotient :
    perfectScalarInclusionNat X r ≫ perfectScalarConeProjectionNat X r = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _ (inclusion_quotientToCone ((complexGlobalScalar X r).app K.obj))

instance perfectScalarMiddleFunctor_additive : (perfectScalarMiddleFunctor X r).Additive := by
  unfold perfectScalarMiddleFunctor
  infer_instance

/-- The original middle functor preserves arbitrary inherited abelian conflations. -/
def perfectScalarMiddleExactFunctor :
    ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (locallyPerfect X))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (locallyPerfect X)) where
  toFunctor := perfectScalarMiddleFunctor X r
  map_conflation S hS := middleNatTransFunctor_shortExact
    (Functor.whiskerRight (perfectGlobalScalar X r) (locallyPerfect X).ι) S hS hS

/-- Its original fine weak maps and pushouts are preserved as well. -/
theorem perfectScalarMiddleFunctor_waldhausenExact :
    IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (perfectScalarMiddleFunctor X r) where
  zero h := (perfectScalarMiddleFunctor X r).map_isZero h
  cofibration g hg := (perfectScalarMiddleExactFunctor X r).map_inflation g hg
  weak {K L} g hg := by
    let φ := Arrow.homMk (f := Arrow.mk ((complexGlobalScalar X r).app K.obj))
      (g := Arrow.mk ((complexGlobalScalar X r).app L.obj))
      g.hom g.hom ((complexGlobalScalar X r).naturality g.hom)
    let : QuasiIso φ.right := hg
    exact middleFunctor_map_quasiIso φ
  pushout hi h := (perfectScalarMiddleExactFunctor X r).map_isPushout hi h

/-- The pointwise short complex keeps all three original objects and signed arrows. -/
def perfectScalarConeSequence (K : Perfect X) : ShortComplex (Perfect X) :=
  exactFunctorSequenceAt (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
    (perfectScalarInclusionNat_quotient X r) K

/-- The actual signed quotient sequence is a genuine inherited conflation. -/
theorem perfectScalarConeSequence_conflation (K : Perfect X) :
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (locallyPerfect X)).conflation (perfectScalarConeSequence X r K) :=
  quotientToConeSequence_shortExact ((complexGlobalScalar X r).app K.obj)

/-- Quotient exactness forces the genuine relative cofibration for every inherited cofibration. -/
theorem perfectScalarInclusionNat_cofibration :
    Additivity.IsCofibrationTransformation (perfectWaldhausen X)
      (perfectScalarInclusionNat X r) (perfectWaldhausen X) where
  app_cof K := ExtensionCategory.inclusion_cof (perfectWaldhausen X) (perfectScalarExtension X r K)
  relative_cof {K L} g hg := by
    let E := ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (locallyPerfect X)
    let : HasPushout
        (exactFunctorSequenceAt (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
          (perfectScalarInclusionNat_quotient X r) K).f
        (exactFunctorSequenceMap (perfectScalarInclusionNat X r)
          (perfectScalarConeProjectionNat X r) (perfectScalarInclusionNat_quotient X r) g).τ₁ :=
      Additivity.hasPushout (perfectWaldhausen X) (perfectScalarInclusionNat X r)
        (fun K => ExtensionCategory.inclusion_cof (perfectWaldhausen X)
          (perfectScalarExtension X r K)) g
    exact relativePushout_inflation E
      (exactFunctorSequenceMap (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
        (perfectScalarInclusionNat_quotient X r) g)
      (perfectScalarConeSequence_conflation X r K) (perfectScalarConeSequence_conflation X r L)
      ((perfectScalarConeExactFunctor X r).map_inflation g hg)

/-- The original scalar cylinder and signed cone form an actual cofibration sequence. -/
theorem perfectScalarCofibrationSequence :
    Additivity.IsCofibrationSequence (perfectWaldhausen X) (perfectWaldhausen X)
      (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r) where
  exactF := IsExact.id _ _
  exactG := perfectScalarMiddleFunctor_waldhausenExact X r
  exactH := perfectScalarConeFunctor_waldhausenExact X r
  cofibration := perfectScalarInclusionNat_cofibration X r
  cofiber K := subcategoryCone_isPushout (locallyPerfect X)
    (fun hA hB f => locallyPerfect_mappingCone hA hB f) ((perfectGlobalScalar X r).app K)

/-- Every original projection component is already weak before open restriction. -/
theorem perfectScalarProjectionNat_weak (K : Perfect X) :
    (perfectWaldhausen X).weq ((perfectScalarProjectionNat X r).app K) :=
  perfectScalarProjection_weak X r K

end Quillen.PerfectComplexes
