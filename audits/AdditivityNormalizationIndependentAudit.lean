import Quillen.Waldhausen.Additivity.NormalizedMixedHomotopy
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origins := #[`Quillen.Waldhausen.Additivity.DiagramIso,
    `Quillen.Waldhausen.Additivity.NormalizeFunctor,
    `Quillen.Waldhausen.Additivity.NormalizedPushout,
    `Quillen.Waldhausen.Additivity.NormalizedMixedDiagrams,
    `Quillen.Waldhausen.Additivity.NormalizedDeformationMap,
    `Quillen.Waldhausen.Additivity.NormalizedSumMap,
    `Quillen.Waldhausen.Additivity.NormalizedZeroMaps,
    `Quillen.Waldhausen.Additivity.MixedEndpointHomotopy,
    `Quillen.Waldhausen.Additivity.NormalizedMixedHomotopy]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origins.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 77 do throwError "Expected frozen 77-declaration scope; audited {count}"
  logInfo m!"Audited all {count} normalization-core declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.MixedOrdinalCylinder
open scoped Simplicial Topology
universe u v u' v'

section IndependentUniverses
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)
example (K : C ⥤ D) (c : C) (d : D) (e : K.obj c ≅ d) :
    (normalizedFunctor K c d e).obj c = d := normalizedFunctor_obj_base K c d e
example : pushoutFunctor W a hc.app_cof ≅ normalizedPushoutFunctor V W a hF hG hc :=
  normalizedPushoutIso V W a hF hG hc
example : (normalizedPushoutFunctor V W a hF hG hc).obj (Arrow.mk (𝟙 V.zero)) = W.zero :=
  normalizedPushoutFunctor_obj_zero V W a hF hG hc
example {n p m : SimplexCategory} (α β : n ⟶ p) (h : ∀ i, α.toOrderHom i ≤ β.toOrderHom i)
    (A : Grid₂ p m ⥤ C) :
    normalizedIntervalDiagram V W a hF hG hc α β h A =
      intervalArrows α β h A ⋙ normalizedPushoutFunctor V W a hF hG hc := rfl
example {n p m : SimplexCategory} (α β : n ⟶ p) (h : ∀ i, α.toOrderHom i ≤ β.toOrderHom i)
    (A : Grid₂ p m ⥤ C) (hA : IsSimplex₂ V.cof V.weq A) :
    IsSimplex₂ W.cof W.weq (normalizedIntervalDiagram V W a hF hG hc α β h A) :=
  normalizedIntervalDiagram_isSimplex₂ V W a hF hG hc α β h hA
example {n p m : SimplexCategory} (α β : n ⟶ p) (h : ∀ i, α.toOrderHom i ≤ β.toOrderHom i)
    (x : Grid₂ n m) :
    (normalizedIntervalDiagram V W a hF hG hc α β h
      ((Functor.const (Grid₂ p m)).obj V.zero)).obj x = W.zero :=
  normalizedIntervalDiagram_zero_obj V W a hF hG hc α β h x
end IndependentUniverses

section SameUniverses
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)
example (c : C) (d : D) (e : G.obj c ≅ d) :
    normalizedFunctor G c d e = rebaseFunctor G c d e := rfl
example (c : C) (d : D) (e : G.obj c ≅ d) :
    normalizationIso G c d e = rebaseFunctorIso G c d e := rfl
example : outerZeroSection (bisimplicialSSet V) ≫ normalizedMixedMap V W a hF hG hc =
    normalizedIdentityMap V W a hF hG hc := normalizedMixedMap_zero V W a hF hG hc
example : outerOneSection (bisimplicialSSet V) ≫ normalizedMixedMap V W a hF hG hc =
    normalizedSeparatedMap V W a hF hG hc := normalizedMixedMap_one V W a hF hG hc
example (n m : SimplexCategoryᵒᵖ) (φ : Cut n.unop) :
    ((normalizedMixedMap V W a hF hG hc).app n).app m
      ⟨φ, zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (mixedOrdinal φ)) m⟩ =
        zeroSimplex₂ W.cof W.weq W.zero W.isZero n m :=
  normalizedMixedMap_zero_grid V W a hF hG hc n m φ
example : (normalizedMixedEndpointHomotopy V W a hF hG hc).h =
    TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)) ▷ Δ[1] ≫
      (outerContraction (bisimplicialSSet V)).h ≫
      TheoremA.diagonalMap (normalizedMixedMap V W a hF hG hc) := rfl
example : SSet.ι₀ ≫ (normalizedMixedEndpointHomotopy V W a hF hG hc).h =
    TheoremA.diagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) ≫
      TheoremA.diagonalMap (normalizedIdentityMap V W a hF hG hc) :=
  (normalizedMixedEndpointHomotopy V W a hF hG hc).h₀
example : SSet.ι₁ ≫ (normalizedMixedEndpointHomotopy V W a hF hG hc).h =
    TheoremA.diagonalMap (normalizedSeparatedMap V W a hF hG hc) :=
  (normalizedMixedEndpointHomotopy V W a hF hG hc).h₁
example (t : unitInterval) :
    realizationSimplicialHomotopy (normalizedMixedEndpointHomotopy V W a hF hG hc)
      (t, realizationPoint
        (show (TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)) _⦋0⦌ from
          zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (OrdinalSubdivision.δ.obj ⦋0⦌)) (op ⦋0⦌))) =
        realizationPoint (diagonalZeroVertex W) :=
  normalizedMixedRealizationHomotopy_fixed_zero V W a hF hG hc t
variable [HasBinaryCoproducts D] (hH : IsExact V.cof V.weq W.cof W.weq H)
example {n m : SimplexCategory} (A : Grid₂ (OrdinalSubdivision.δ.obj n) m ⥤ C) :
    normalizedSumGrid V W hH hF A = separatedPairGrid A ⋙ normalizedSplitEndpoint V W hH hF := rfl
example (n m : SimplexCategoryᵒᵖ) :
    ((normalizedSumMap V W hH hF).app n).app m
      (zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (OrdinalSubdivision.δ.obj n.unop)) m) =
        zeroSimplex₂ W.cof W.weq W.zero W.isZero n m := normalizedSumMap_zero V W hF hH n m
end SameUniverses
