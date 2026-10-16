/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberSumNormalization

/-! Actual functor data, complete normalization components and the original categorical square. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.ExtensionCategory
universe u
namespace QuillenTest.ScalarCofiberSumNormalization
local instance (X : Scheme.{u}) : HasBinaryCoproducts (Perfect X) :=
  Additivity.hasBinaryCoproducts (perfectWaldhausen X)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "Z" => zeroFunctor (C := Perfect X) W
local notation "h0" => perfectScalarIdentityFineCofibrationSequence (X := X)
local notation "h1" => perfectScalarCofibrationSequence X r
local notation "Fbar" => Quillen.rebaseFunctor (𝟭 (Perfect X)) (Structure.zero V)
  (Structure.zero W) (Limits.IsZero.iso
    (IsExact.zero (changeWeak_exact (perfectOpenNested j)) (Structure.isZero V))
    (Structure.isZero W))
local notation "A" => perfectOpenScalarConeFunctor j r q hq
local notation "hA" => perfectOpenScalarConeFunctor_waldhausenExact j r q hq
local notation "Ar" => Quillen.rebaseFunctor A (Structure.zero V)
  (Structure.zero (acyclicStructure (perfectOpenNested j)))
  (Limits.IsZero.iso (IsExact.zero hA (Structure.isZero V))
    (Structure.isZero (acyclicStructure (perfectOpenNested j))))
local notation "D" => Ar ⋙ acyclicInclusion (perfectOpenNested j)

/-- The actual two normalized coproduct functors, not just their induced maps, agree. -/
theorem original_functor_data : coproductRebasedFunctor V = coproductRebasedFunctor W :=
  perfectOpenScalarCoproductRebase_eq j

/-- Both directions of every actual coproduct normalization component retain their transports. -/
theorem original_rebase_components (K L : Perfect X) :
    (coproductRebaseIso V).hom.app (K, L) ≫
        eqToHom (congrArg (fun F => F.obj (K, L)) (perfectOpenScalarCoproductRebase_eq j)) =
      (coproductRebaseIso W).hom.app (K, L) ∧
    eqToHom (congrArg (fun F => F.obj (K, L))
        (perfectOpenScalarCoproductRebase_eq j).symm) ≫
        (coproductRebaseIso V).inv.app (K, L) =
      (coproductRebaseIso W).inv.app (K, L) :=
  ⟨perfectOpenScalarCoproductRebaseIso_hom j K L,
    perfectOpenScalarCoproductRebaseIso_inv j K L⟩

/-- The original identity quotient functor and its actual arrow have the same chosen zero. -/
theorem original_identity_zero_data :
    zeroFunctor (C := Perfect X) V = Z ∧
      QuotientRows.oneIdToZero V = QuotientRows.oneIdToZero W :=
  ⟨perfectOpenScalarIdentityQuotient_eq j, perfectOpenScalarIdentityQuotientArrow_eq j⟩

/-- Both separated endpoint data retain their literal fine/coarse normalizations. -/
theorem original_split_data :
    normalizedSplitEndpoint V V (h0).exactH (h0).exactF =
      normalizedSplitEndpoint V W (perfectOpenScalarIdentityCofibrationSequence j).exactH
        (perfectOpenScalarIdentityCofibrationSequence j).exactF ∧
    normalizedSplitEndpoint V V (h1).exactH (h1).exactF =
      normalizedSplitEndpoint V W (perfectOpenScalarCofibrationSequence j r).exactH
        (perfectOpenScalarCofibrationSequence j r).exactF :=
  ⟨perfectOpenScalarIdentitySplitEndpoint_eq j, perfectOpenScalarConeSplitEndpoint_eq j r⟩

/-- The zero target is genuinely fine exact on the actual componentwise product structure. -/
theorem original_zero_target_exact :
    IsExact (productStructure V V).cof (productStructure V V).weq (V).cof (V).weq
      (perfectOpenScalarZeroPairTarget j) :=
  perfectOpenScalarZeroPairTarget_exact j

/-- The public acyclic cone target is fine exact with its inherited inclusion. -/
theorem original_cone_target_exact :
    IsExact (productStructure V V).cof (productStructure V V).weq (V).cof (V).weq
      (perfectOpenScalarConePairTarget j r q hq) :=
  perfectOpenScalarConePairTarget_exact j r q hq

/-- Every original identity Theta factor is retained on independently varying inputs. -/
theorem original_zero_theta (K L : Perfect X) :
    (perfectOpenScalarZeroSumNormalizationIso j).hom.app (K, L) =
      (normalizedSplitIso V V (h0).exactH (h0).exactF).inv.app (K, L) ≫
        coprod.map ((perfectOpenScalarZeroRebaseIso j).hom.app K)
          ((perfectOpenScalarIdentityRebaseIso j).hom.app L) ≫
        coprod.map ((perfectOpenScalarZeroRebaseIso j).inv.app K) (𝟙 ((Fbar).obj L)) ≫
        (coproductRebaseIso V).hom.app ((Z).obj K, (Fbar).obj L) :=
  perfectOpenScalarZeroSumNormalizationIso_hom j K L

/-- Every cone Theta factor retains the actual beta and original coproduct normalization. -/
theorem original_cone_theta (K L : Perfect X) :
    (perfectOpenScalarConeSumNormalizationIso j r q hq).hom.app (K, L) =
      (normalizedSplitIso V V (h1).exactH (h1).exactF).inv.app (K, L) ≫
        coprod.map ((perfectOpenScalarConeRebaseIso j r).hom.app K)
          ((perfectOpenScalarIdentityRebaseIso j).hom.app L) ≫
        coprod.map ((perfectOpenScalarConeNormalizationIso j r q hq).hom.app K)
          (𝟙 ((Fbar).obj L)) ≫
        (coproductRebaseIso V).hom.app ((D).obj K, (Fbar).obj L) :=
  perfectOpenScalarConeSumNormalizationIso_hom j r q hq K L

/-- Both whole normalization isomorphisms are fine weak. -/
theorem original_theta_weak (K L : Perfect X) :
    (V).weq ((perfectOpenScalarZeroSumNormalizationIso j).hom.app (K, L)) ∧
      (V).weq ((perfectOpenScalarConeSumNormalizationIso j r q hq).hom.app (K, L)) :=
  ⟨perfectOpenScalarZeroSumNormalizationIso_weak j K L,
    perfectOpenScalarConeSumNormalizationIso_weak j r q hq K L⟩

/-- Both Theta zero components use the actual source and target transports. -/
theorem original_theta_zero :
    eqToHom (normalizedSplitEndpoint_obj_zero V V (h0).exactH (h0).exactF).symm ≫
        (perfectOpenScalarZeroSumNormalizationIso j).hom.app ((V).zero, (V).zero) ≫
        eqToHom (perfectOpenScalarZeroPairTarget_zero j) = 𝟙 (V).zero ∧
    eqToHom (normalizedSplitEndpoint_obj_zero V V (h1).exactH (h1).exactF).symm ≫
        (perfectOpenScalarConeSumNormalizationIso j r q hq).hom.app ((V).zero, (V).zero) ≫
        eqToHom (perfectOpenScalarConePairTarget_zero j r q hq) = 𝟙 (V).zero :=
  ⟨perfectOpenScalarZeroSumNormalizationIso_zero j,
    perfectOpenScalarConeSumNormalizationIso_zero j r q hq⟩

/-- The canonical pair keeps the zero-to-inclusion first and literal identity second. -/
theorem original_pair_component (K L : Perfect X) :
    (perfectOpenScalarCanonicalPairTransformation j r q hq).app (K, L) =
      ((perfectOpenScalarRebasedZeroToCone j r q hq).app K, 𝟙 ((Fbar).obj L)) :=
  perfectOpenScalarCanonicalPairTransformation_app j r q hq K L

/-- The entire canonical sum arrow is the actual coarse normalized coproduct map. -/
theorem original_sum_component (K L : Perfect X) :
    (perfectOpenScalarCanonicalSumTransformation j r q hq).app (K, L) =
      (coproductRebasedFunctor W).map
        ((perfectOpenScalarRebasedZeroToCone j r q hq).app K, 𝟙 ((Fbar).obj L)) :=
  perfectOpenScalarCanonicalSumTransformation_app j r q hq K L

/-- Both canonical arrows keep the supplied original coarse weakness witnesses. -/
theorem original_canonical_weak (K L : Perfect X) :
    (productStructure W W).weq
        ((perfectOpenScalarCanonicalPairTransformation j r q hq).app (K, L)) ∧
      (W).weq ((perfectOpenScalarCanonicalSumTransformation j r q hq).app (K, L)) :=
  ⟨perfectOpenScalarCanonicalPairTransformation_weak j r q hq K L,
    perfectOpenScalarCanonicalSumTransformation_weak j r q hq K L⟩

/-- The complete canonical sum map has the actual transported zero component. -/
theorem original_canonical_zero :
    eqToHom (perfectOpenScalarZeroPairTarget_zero j).symm ≫
        (perfectOpenScalarCanonicalSumTransformation j r q hq).app ((V).zero, (V).zero) ≫
        eqToHom (perfectOpenScalarConePairTarget_zero j r q hq) = 𝟙 (V).zero :=
  perfectOpenScalarCanonicalSumTransformation_zero j r q hq

/-- The whole original natural-transformation square is retained before realization. -/
theorem original_whole_square :
    perfectOpenScalarSeparatedSumTransformation j r q hq ≫
        (perfectOpenScalarConeSumNormalizationIso j r q hq).hom =
      (perfectOpenScalarZeroSumNormalizationIso j).hom ≫
        perfectOpenScalarCanonicalSumTransformation j r q hq :=
  perfectOpenScalarSumNormalizationSquare j r q hq

/-- Every pair of coefficients satisfies the same whole-square component equation. -/
theorem original_square_component (K L : Perfect X) :
    (perfectOpenScalarSeparatedSumTransformation j r q hq).app (K, L) ≫
        (perfectOpenScalarConeSumNormalizationIso j r q hq).hom.app (K, L) =
      (perfectOpenScalarZeroSumNormalizationIso j).hom.app (K, L) ≫
        (perfectOpenScalarCanonicalSumTransformation j r q hq).app (K, L) :=
  NatTrans.congr_app (perfectOpenScalarSumNormalizationSquare j r q hq) (K, L)

end QuillenTest.ScalarCofiberSumNormalization
