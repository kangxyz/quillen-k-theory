import Quillen.Waldhausen.Additivity.NormalizedEndpointFamilies
import Quillen.Waldhausen.SConstruction.WeakGridHomotopy
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origin := `Quillen.Waldhausen.Additivity.NormalizedEndpointFamilies
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 17 do throwError "Expected frozen 17-declaration scope; audited {count}"
  logInfo m!"Audited all {count} normalized endpoint-family declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Additivity
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)

example (n m : SimplexCategoryᵒᵖ) (A : ((bisimplicialSSet V).obj n).obj m) :
    (((normalizedIdentityMap V W a hF hG hc).app n).app m A).1 ≅
      (((bisimplicialSSetMap V.cof V.weq hG.rebase).app n).app m A).1 :=
  normalizedIdentityEndpointIso V W a hF hG hc n m A

example (n m : SimplexCategoryᵒᵖ) (A : ((bisimplicialSSet V).obj n).obj m)
    (x : Grid₂ n.unop m.unop) :
    (normalizedIdentityEndpointFamily V W a hF hG hc n m A).app x =
      (normalizedPushoutIso V W a hF hG hc).inv.app
        ((intervalArrows (𝟙 n.unop) (𝟙 n.unop) (fun _ ↦ le_rfl) A.1).obj x) ≫
      (identityEndpointFamily V W a hF hG hc n m A).app x ≫
      (Quillen.rebaseFunctorIso G V.zero W.zero ((hG.zero V.isZero).iso W.isZero)).hom.app
        (A.1.obj x) := rfl

example :
    SSet.Homotopy (TheoremA.diagonalMap (normalizedIdentityMap V W a hF hG hc))
      (TheoremA.diagonalMap (bisimplicialSSetMap V.cof V.weq hG.rebase)) :=
  diagonalWeakGridHomotopy W _ _ (normalizedIdentityEndpointFamily V W a hF hG hc)
    (normalizedIdentityEndpointFamily_weak V W a hF hG hc) (by
      intro n n' α A x
      exact (normalizedIdentityEndpointFamily_reindex_app V W a hF hG hc α.unop α.unop A x).symm)

variable [HasBinaryCoproducts D] (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

example (n m : SimplexCategoryᵒᵖ)
    (A : ((OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m)
    (x : Grid₂ n.unop m.unop) :
    (normalizedSeparatedEndpointFamily V W a b hs n m A).app x =
      (normalizedPushoutIso V W a hs.exactF hs.exactG hs.cofibration).inv.app
        ((intervalArrows (Edgewise.left n.unop n.unop) (Edgewise.right n.unop n.unop)
          (left_le_right n.unop) A.1).obj x) ≫
      (separatedEndpointFamily V W a b hs n m A).app x ≫
      (normalizedSplitIso V W hs.exactH hs.exactF).hom.app ((separatedPairGrid A.1).obj x) := rfl

example : SSet.Homotopy
    (TheoremA.diagonalMap
      (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration))
    (TheoremA.diagonalMap (normalizedSumMap V W hs.exactH hs.exactF)) :=
  diagonalWeakGridHomotopy W _ _ (normalizedSeparatedEndpointFamily V W a b hs)
    (normalizedSeparatedEndpointFamily_weak V W a b hs) (by
      intro n n' α A x
      exact (normalizedSeparatedEndpointFamily_reindex_app V W a b hs α.unop α.unop A x).symm)
