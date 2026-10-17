/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Conjugation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompNative

/-! The prescribed Laurent-seed edge on genuine polynomial inputs, with both full attachments. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedChartLaurentEdge
open CommonReferenceNerve CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Conjugation
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "la" => CategoryTheory.Functor.obj (laurentUnderFunctor R) a
local notation "lb" => CategoryTheory.Functor.obj (laurentUnderFunctor R) b
local notation "k" => CategoryTheory.Functor.map (laurentUnderFunctor R) f
local notation "e" => (𝟙 la : la ⟶ la)
local notation "A" => BassH0Merge.normalizedMap (coefficientMap P (CategoryTheory.NatTrans.app α a))
local notation "F" => polyRef P e k
local notation "G" => laurentRef P e k
local notation "J" => chart P (c := lb)
local notation "η₀" => ordinary P e k
local notation "η₁" => shifted P e k

/-- The full ordinary anchor is precomposed by the actual source chart model map. -/
abbrev ordinaryAnchor := CutOpenPrecomp.anchor A F J G η₀
/-- The second full anchor retains the original Laurent unit shift. -/
abbrev shiftedAnchor := CutOpenPrecomp.anchor A F J G η₁

/-- This sector has polynomial inputs, without identifying them with base inputs. -/
abbrev space := CutOpenCarrier.space (A ≫ F) J (A ≫ G)
  (ordinaryAnchor P f α) (shiftedAnchor P f α)

/-- The original J0 carrier changes input only by the actual coefficient chart. -/
def inputMap : C(CutOpenCarrier.space F J G η₀ η₁, space P f α) :=
  (CutOpenPrecomp.map A F J G η₀ η₁).hom

/-- Every ordinary attachment node retains its entire reference isomorphism. -/
theorem ordinary_node (N : Node F) :
    precompNode A (attachPostcompNode F J G η₀ N) =
      attachPostcompNode (A ≫ F) J (A ≫ G) (ordinaryAnchor P f α) (precompNode A N) :=
  CutOpenPrecomp.attachment_node A F J G η₀ N

/-- Every unit-shifted attachment node independently retains its entire reference. -/
theorem shifted_node (N : Node F) :
    precompNode A (attachPostcompNode F J G η₁ N) =
      attachPostcompNode (A ≫ F) J (A ≫ G) (shiftedAnchor P f α) (precompNode A N) :=
  CutOpenPrecomp.attachment_node A F J G η₁ N

/-- The scalar edge is the original reversed J0 comparison at its unchanged two clocks. -/
def edge : C(I × I, space P f α) :=
  ⟨fun z ↦ inputMap P f α (reverseComparison P e k z), by fun_prop⟩

/-- The whole initial word is the prescribed original new-seed word. -/
theorem edge_zero (s : I) :
    edge P f α (0, s) = inputMap P f α (targetWord P e k s) :=
  congrArg (inputMap P f α) ((reverseComparison P e k).toHomotopy.apply_zero s)

/-- The whole terminal word is the prescribed original old-seed word. -/
theorem edge_one (s : I) :
    edge P f α (1, s) = inputMap P f α (sourceWord P e k s) :=
  congrArg (inputMap P f α) ((reverseComparison P e k).toHomotopy.apply_one s)

/-- The input map preserves the minus tip independently of the plus tip. -/
theorem inputMap_tipMinus :
    inputMap P f α (CutOpenCarrier.tipMinus F J G η₀ η₁) =
      CutOpenCarrier.tipMinus (A ≫ F) J (A ≫ G)
        (ordinaryAnchor P f α) (shiftedAnchor P f α) :=
  CutOpenPrecomp.map_tipMinus A F J G η₀ η₁

/-- The input map preserves the other original tip. -/
theorem inputMap_tipPlus :
    inputMap P f α (CutOpenCarrier.tipPlus F J G η₀ η₁) =
      CutOpenCarrier.tipPlus (A ≫ F) J (A ≫ G)
        (ordinaryAnchor P f α) (shiftedAnchor P f α) :=
  CutOpenPrecomp.map_tipPlus A F J G η₀ η₁

/-- Every polynomial input follows the original Laurent seed track after its actual chart map. -/
theorem edge_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, (polynomialUnderFunctor R).obj a))))).space n) :
    CutOpenCarrier.nativeEval (A ≫ F) J (A ≫ G)
      (ordinaryAnchor P f α) (shiftedAnchor P f α) n (edge P f α (r, s)) x =
    Path.toContinuousMap ((boundedFlatCoefficientBassPositiveTransitionHomotopy P k).level n
      (unitInterval.symm r, (prespectrumMap A).map n x)) s := by
  have hm := CutOpenPrecomp.map_native A F J G η₀ η₁ n
    (reverseComparison P e k (r, s)) x
  have hj := reverseComparison_transition P e k n r s ((prespectrumMap A).map n x)
  have hk := congrArg (fun w : la ⟶ lb ↦
    Path.toContinuousMap ((boundedFlatCoefficientBassPositiveTransitionHomotopy P w).level n
      (unitInterval.symm r, (prespectrumMap A).map n x)) s) (Category.id_comp k)
  exact hm.trans (hj.trans hk)

/-- The supported value is exactly the full original reversed Laurent seed homotopy. -/
theorem edge_full_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, (polynomialUnderFunctor R).obj a))))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P lb).map n
      (CutOpenCarrier.nativeEval (A ≫ F) J (A ≫ G)
        (ordinaryAnchor P f α) (shiftedAnchor P f α) n (edge P f α (r, s)) x) =
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P k).symm.level n
        (r, (prespectrumMap A).map n x)) s :=
  (congrArg ((boundedFlatCoefficientBassPositiveConeInclusion P lb).map n)
    (edge_native P f α n r s x)).trans
    (boundedFlatCoefficientBassPositiveTransitionHomotopy_factor P k n
      (unitInterval.symm r) s ((prespectrumMap A).map n x))

end Quillen.PerfectComplexes.CoefficientBassSeedChartLaurentEdge
