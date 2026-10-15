/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFunctorNaturality
public import Quillen.Waldhausen.Additivity.GroupFormula

/-! # Literal supported sums of exact restriction squares

The supported two-summand operator retains exactly the original ambient
coproduct complex and chain map. The supported-category coproduct supplies
its support proof and exactness through the canonical coproduct comparison.
-/
@[expose] public section

open Quillen.Waldhausen
open Quillen.Waldhausen.ExtensionCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.OpenFunctorNaturality
open Waldhausen Waldhausen.ExtensionCategory

variable {U X V Y : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The actual full-subcategory inclusion forgetting support. -/
def supportInclusion : (perfectSupported j).FullSubcategory ⥤ Perfect X :=
  ObjectProperty.ιOfLE (show perfectSupported j ≤ locallyPerfect X from fun _ h => h.1)

instance supportInclusion_additive : (supportInclusion j).Additive := by
  unfold supportInclusion
  infer_instance

instance supportInclusion_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (supportInclusion j) := by
  let : PreservesBinaryBiproducts (supportInclusion j) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact preservesBinaryCoproducts_of_preservesBinaryBiproducts _

/-- Canonical postcomposition comparison for the original selected coproducts. -/
def coproductPostcomposeIso {C : Type v} [Category C] {D E : Type w} [Category D] [Category E]
    [HasBinaryCoproducts D] [HasBinaryCoproducts E] (H F : C ⥤ D) (J : D ⥤ E)
    [PreservesColimitsOfShape (Discrete WalkingPair) J] :
    Additivity.sumFunctor H F ⋙ J ≅ Additivity.sumFunctor (H ⋙ J) (F ⋙ J) :=
  (NatIso.ofComponents
    (fun K => asIso (coprodComparison J (H.obj K) (F.obj K)))
    (fun f => (coprodComparison_natural J (H.map f) (F.map f)).symm)).symm

namespace ExactRestrictionSquare
variable {j k} (D E : ExactRestrictionSquare j k)

/-- The original ordered ambient two-summand functor. -/
def ambientPair : Perfect X × Perfect X ⥤ Perfect Y :=
  Additivity.sumFunctor (CategoryTheory.Prod.fst _ _ ⋙ D.ambient)
    (CategoryTheory.Prod.snd _ _ ⋙ E.ambient)

/-- The original ambient sum is exact. -/
theorem ambientPair_exact : IsExact
    (productStructure (perfectWaldhausen X) (perfectWaldhausen X)).cof
    (productStructure (perfectWaldhausen X) (perfectWaldhausen X)).weq
    (perfectWaldhausen Y).cof (perfectWaldhausen Y).weq (D.ambientPair E) :=
  Additivity.sumFunctor_isExact _ _
    ((fst_exact _ _).comp D.ambient_exact) ((snd_exact _ _).comp E.ambient_exact)

/-- The supported-category coproduct of the actual supported summands. -/
def supportedSum : (perfectSupported j).FullSubcategory × (perfectSupported j).FullSubcategory ⥤
    (perfectSupported k).FullSubcategory :=
  Additivity.sumFunctor (CategoryTheory.Prod.fst _ _ ⋙ D.supported)
    (CategoryTheory.Prod.snd _ _ ⋙ E.supported)

/-- Exactness of the supported-category coproduct. -/
theorem supportedSum_exact : IsExact
    (productStructure (perfectSupportedWaldhausen j) (perfectSupportedWaldhausen j)).cof
    (productStructure (perfectSupportedWaldhausen j) (perfectSupportedWaldhausen j)).weq
    (perfectSupportedWaldhausen k).cof (perfectSupportedWaldhausen k).weq
    (D.supportedSum E) :=
  Additivity.sumFunctor_isExact _ _
    ((fst_exact _ _).comp D.supported_exact) ((snd_exact _ _).comp E.supported_exact)

/-- The canonical coproduct comparison retains the actual original ambient sum. -/
def supportedSumForgetIso : D.supportedSum E ⋙ supportInclusion k ≅
    (supportInclusion j).prod (supportInclusion j) ⋙ D.ambientPair E :=
  coproductPostcomposeIso (CategoryTheory.Prod.fst _ _ ⋙ D.supported)
    (CategoryTheory.Prod.snd _ _ ⋙ E.supported) (supportInclusion k)

/-- Restrict the literal original ambient sum, preserving its objects and maps. -/
def supportedPair : (perfectSupported j).FullSubcategory × (perfectSupported j).FullSubcategory ⥤
    (perfectSupported k).FullSubcategory :=
  (perfectSupported k).lift
    ((supportInclusion j).prod (supportInclusion j) ⋙ D.ambientPair E ⋙ (locallyPerfect Y).ι)
    (fun K => (perfectSupported k).prop_of_iso
      ((locallyPerfect Y).ι.mapIso ((D.supportedSumForgetIso E).app K))
      ((D.supportedSum E).obj K).property)

/-- The supported lift has precisely the original ambient sum complex. -/
@[simp] theorem supportedPair_obj
    (K : (perfectSupported j).FullSubcategory × (perfectSupported j).FullSubcategory) :
    ((D.supportedPair E).obj K).obj =
      ((D.ambientPair E).obj ((supportInclusion j).obj K.1,
        (supportInclusion j).obj K.2)).obj := rfl

/-- The supported lift has precisely the original ambient sum chain map. -/
@[simp] theorem supportedPair_map
    {K L : (perfectSupported j).FullSubcategory × (perfectSupported j).FullSubcategory}
    (f : K ⟶ L) :
    ((D.supportedPair E).map f).hom =
      ((D.ambientPair E).map ((supportInclusion j).map f.1,
        (supportInclusion j).map f.2)).hom := rfl

/-- The original selected coproduct is canonically compared with the supported coproduct. -/
def supportedPairIso : D.supportedSum E ≅ D.supportedPair E :=
  Functor.fullyFaithfulCancelRight (perfectSupported k).ι
    (Functor.isoWhiskerRight (D.supportedSumForgetIso E) (locallyPerfect Y).ι)

/-- The literal original two-summand lift is exact on the actual supported categories. -/
theorem supportedPair_exact : IsExact
    (productStructure (perfectSupportedWaldhausen j) (perfectSupportedWaldhausen j)).cof
    (productStructure (perfectSupportedWaldhausen j) (perfectSupportedWaldhausen j)).weq
    (perfectSupportedWaldhausen k).cof (perfectSupportedWaldhausen k).weq
    (D.supportedPair E) :=
  (D.supportedSum_exact E).of_iso (D.supportedPairIso E)

/-- The supported map uses the original product K-equivalence and literal ambient sum. -/
def supportedPairKMap (n : ℕ) :
    PerfectSupportedK j n × PerfectSupportedK j n →* PerfectSupportedK k n :=
  (KMap (D.supportedPair_exact E) n).comp
    (Product.KEquiv (perfectSupportedWaldhausen j) (perfectSupportedWaldhausen j)
      n).symm.toMonoidHom

/-- The literal supported sum induces precisely the product of its two original K-maps. -/
theorem supportedPairKMap_apply (n : ℕ) (a b : PerfectSupportedK j n) :
    D.supportedPairKMap E n (a, b) = D.supportedKMap n a * E.supportedKMap n b := by
  let z := (Product.KEquiv (perfectSupportedWaldhausen j) (perfectSupportedWaldhausen j)
    n).symm (a, b)
  have hz : (KMap (fst_exact (perfectSupportedWaldhausen j) (perfectSupportedWaldhausen j)) n z,
      KMap (snd_exact (perfectSupportedWaldhausen j) (perfectSupportedWaldhausen j)) n z) =
        (a, b) :=
    (Product.KEquiv (perfectSupportedWaldhausen j) (perfectSupportedWaldhausen j)
      n).apply_symm_apply _
  change KMap (D.supportedPair_exact E) n z = _
  rw [← KMap_eq_of_iso (D.supportedSum_exact E) (D.supportedPair_exact E)
    (D.supportedPairIso E) n]
  rw [Additivity.KMap_sum_apply _ _
    ((fst_exact _ _).comp D.supported_exact) ((snd_exact _ _).comp E.supported_exact)]
  rw [← KMap_comp_KMap (fst_exact (perfectSupportedWaldhausen j)
      (perfectSupportedWaldhausen j)) D.supported_exact,
    ← KMap_comp_KMap (snd_exact (perfectSupportedWaldhausen j)
      (perfectSupportedWaldhausen j)) E.supported_exact]
  exact congrArg₂ (fun x y => D.supportedKMap n x * E.supportedKMap n y)
    (congrArg _root_.Prod.fst hz) (congrArg _root_.Prod.snd hz)

/-- Forgetting support gives the two original ambient summands in the same order. -/
theorem supportedPairKMap_forget (n : ℕ) (a b : PerfectSupportedK j n) :
    perfectSupportedKMap k n (D.supportedPairKMap E n (a, b)) =
      KMap D.ambient_exact n (perfectSupportedKMap j n a) *
        KMap E.ambient_exact n (perfectSupportedKMap j n b) := by
  rw [D.supportedPairKMap_apply E, map_mul]
  exact congrArg₂ (· * ·)
    (DFunLike.congr_fun (D.supportedKMap_forget n) a)
    (DFunLike.congr_fun (E.supportedKMap_forget n) b)

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace V]

/-- The literal supported two-summand map commutes with the original positive boundary. -/
theorem supportedPairKMap_connecting (n : ℕ) (a b : PerfectK U (n + 1)) :
    D.supportedPairKMap E n (qcqsPerfectConnectingHom j n a, qcqsPerfectConnectingHom j n b) =
      qcqsPerfectConnectingHom k n
        (KMap D.onOpen_exact (n + 1) a * KMap E.onOpen_exact (n + 1) b) := by
  rw [D.supportedPairKMap_apply E, map_mul]
  exact congrArg₂ (· * ·)
    (DFunLike.congr_fun (D.qcqsConnectingHom n) a)
    (DFunLike.congr_fun (E.qcqsConnectingHom n) b)

end ExactRestrictionSquare
end Quillen.PerfectComplexes.OpenFunctorNaturality
