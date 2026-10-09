import Quillen.Waldhausen.SConstruction.Rows.NerveFunctoriality
import Quillen.Waldhausen.Fibration.RelativeRows.Simplicial
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.SConstruction.Rows.NerveBridge,
    `Quillen.Waldhausen.SConstruction.Rows.NervePresentation,
    `Quillen.Waldhausen.SConstruction.Rows.NerveFunctoriality]
  let mut counts : Array Nat := #[0,0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (·+1)
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless counts == #[43,19,13] do throwError "Expected75 origins (43+19+13), got {counts}"
  logInfo m!"Audited all75 nerve-presentation origins: {counts}"
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type u} [Category.{v} C] (W : Structure C) (n k : SimplexCategory)
example : {F : Grid₂ n k ⥤ C // IsSimplex₂ W.cof W.weq F} ≃
    ComposableArrows (WeakRows W n) k.len := gridWeakChainEquiv W n k
example (F : Grid₂ n k ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)
    (t : Fin (k.len+1)) (p : Interval n) :
    ((gridToWeakChain W F hF).obj t).obj.obj.obj p = F.obj (t,p) := rfl
example (F : ComposableArrows (WeakRows W n) k.len) (t : Fin (k.len+1)) (p : Interval n) :
    (weakChainToGrid W F).obj (t,p) = (F.obj t).obj.obj.obj p := rfl
example (F : Grid₂ n k ⥤ C) (hF : IsSimplex₂ W.cof W.weq F) :
    weakChainToGrid W (gridToWeakChain W F hF) = F := weakChainToGrid_gridToWeakChain W F hF
example (F : ComposableArrows (WeakRows W n) k.len) :
    gridToWeakChain W (weakChainToGrid W F) (weakChainToGrid_isSimplex₂ W F) = F :=
  gridToWeakChain_weakChainToGrid W F
example (F : ComposableArrows (WeakRows W n) k.len) {p q : Grid₂ n k} (a : p ⟶ q) :
    (weakChainToGrid W F).map a = (F.obj p.1).obj.obj.map (homOfLE (leOfHom a).2) ≫
      (F.map (homOfLE (leOfHom a).1)).hom.hom.app q.2 := rfl
example (F : ComposableArrows (WeakRows W n) k.len) :
    IsSimplex₂ W.cof W.weq (weakChainToGrid W F) := weakChainToGrid_isSimplex₂ W F
example {n' k' : SimplexCategory} (α : n' ⟶ n) (β : k' ⟶ k)
    (F : Grid₂ n k ⥤ C) (hF : IsSimplex₂ W.cof W.weq F) :
    gridToWeakChain W (gridMap₂ α β ⋙ F) (hF.precomp W.cof W.weq α β) =
      (SimplexCategory.toCat.map β).toFunctor ⋙ gridToWeakChain W F hF ⋙ weakRowsReindex W α :=
  gridToWeakChain_reindex W α β F hF
example : bisimplicialSSet W ≅ weakRowNerve W := gridNerveIso W
example (F : Grid₂ n k ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)
    (t : Fin (k.len+1)) (p : Interval n) :
    (((((gridNerveIso W).hom.app (op n)).app (op k) ⟨F,hF⟩).obj t).obj.obj.obj p) =
      F.obj (t,p) := rfl
example (F : ComposableArrows (WeakRows W n) k.len) :
    ((((gridNerveIso W).inv.app (op n)).app (op k) F).val) = weakChainToGrid W F := rfl
example : sSet W.cof W.weq ≅ TheoremA.diagonalSSet (weakRowNerve W) := sSetWeakRowDiagonalIso W
example (F : (sSet W.cof W.weq).obj (op n)) :
    (sSetWeakRowDiagonalIso W).hom.app (op n) F =
      gridToWeakChain W F.val ((isSimplex₂_diagonal_iff W.cof W.weq F.val).2 F.property) := rfl
example : {F : Grid₂ ⦋0⦌ ⦋0⦌ ⥤ C // IsSimplex₂ W.cof W.weq F} ≃
    ComposableArrows (WeakRows W ⦋0⦌) 0 := gridWeakChainEquiv W ⦋0⦌ ⦋0⦌
example (t : Fin (k.len+1)) (p : Interval n) :
    (((((gridNerveIso W).hom.app (op n)).app (op k)
      (zeroSimplex₂ W.cof W.weq W.zero W.isZero (op n) (op k))).obj t).obj.obj.obj p) = W.zero := rfl
example (t : Fin (n.len+1)) (p : Interval n) :
    ((((sSetWeakRowDiagonalIso W).hom.app (op n)
      (zeroSimplex W.cof W.weq W.zero W.isZero (op n))).obj t).obj.obj.obj p) = W.zero := rfl
end Generic
section Functorial
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
example (n : SimplexCategory) : WeakRows V n ⥤ WeakRows W n := weakRowsPostcompose V W hF n
example {n k : SimplexCategory} (G : Grid₂ n k ⥤ C) (hG : IsSimplex₂ V.cof V.weq G) :
    gridToWeakChain W (G ⋙ F) (hG.postcomp V.cof V.weq hF) =
      gridToWeakChain V G hG ⋙ weakRowsPostcompose V W hF n := gridToWeakChain_postcompose V W hF G hG
end Functorial
section Natural
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
example : bisimplicialSSetMap V.cof V.weq hF ≫ (gridNerveIso W).hom =
    (gridNerveIso V).hom ≫ weakRowNerveMap V W hF := gridNerveIso_naturality V W hF
example : sSetMap hF ≫ (sSetWeakRowDiagonalIso W).hom =
    (sSetWeakRowDiagonalIso V).hom ≫ TheoremA.diagonalMap (weakRowNerveMap V W hF) :=
  sSetWeakRowDiagonalIso_naturality V W hF
example (n k : SimplexCategory) (G : ComposableArrows (WeakRows V n) k.len)
    (t : Fin (k.len+1)) (p : Interval n) :
    (((((weakRowNerveMap V W hF).app (op n)).app (op k) G).obj t).obj.obj.obj p) =
      F.obj ((G.obj t).obj.obj.obj p) := rfl
end Natural
section OriginalRelative
variable {C : Type u} [Category.{u} C] {V : Structure C}
  (N : Fibration.NestedWeakEquivalences V) (n : SimplexCategory)
example : (Fibration.RelativeRows.relativeSRows N).obj (op n) ≅
    TheoremA.diagonalSSet (weakRowNerve (Fibration.RelativeRows.waldhausenStructure N n)) :=
  sSetWeakRowDiagonalIso _
end OriginalRelative

section Independent
variable {C : Type u} [Category.{v} C] (W : Structure C) (n k : SimplexCategory)
example (F : ComposableArrows (WeakRows W n) k.len) {p q : Grid₂ n k} (a : p ⟶ q) :
    (((((gridNerveIso W).inv.app (op n)).app (op k) F).val).map a) =
      (F.obj p.1).obj.obj.map (homOfLE (leOfHom a).2) ≫
        (F.map (homOfLE (leOfHom a).1)).hom.hom.app q.2 := rfl
example {n' : SimplexCategoryᵒᵖ} (α : n' ⟶ op n) :
    (weakRowNerve W).map α ≫ (gridNerveIso W).inv.app (op n) =
      (gridNerveIso W).inv.app n' ≫ (bisimplicialSSet W).map α :=
  (gridNerveIso W).inv.naturality α
example {k' : SimplexCategoryᵒᵖ} (β : k' ⟶ op k) :
    ((weakRowNerve W).obj (op n)).map β ≫ ((gridNerveIso W).inv.app (op n)).app (op k) =
      ((gridNerveIso W).inv.app (op n)).app k' ≫ ((bisimplicialSSet W).obj (op n)).map β :=
  ((gridNerveIso W).inv.app (op n)).naturality β
example : weakChainToGrid W (gridToWeakChain W
    (zeroSimplex₂ W.cof W.weq W.zero W.isZero (op n) (op k)).val
    (zeroSimplex₂ W.cof W.weq W.zero W.isZero (op n) (op k)).property) =
      (zeroSimplex₂ W.cof W.weq W.zero W.isZero (op n) (op k)).val :=
  weakChainToGrid_gridToWeakChain W _ _
example (F : Grid₂ n k ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)
    {s t : Fin (k.len+1)} (f : s ⟶ t) (p : Interval n) :
    ((gridToWeakChain W F hF).map f).hom.hom.app p =
      F.map (homOfLE (show (s,p) ≤ (t,p) from ⟨leOfHom f,le_rfl⟩)) := rfl
example (F : ComposableArrows (WeakRows W ⦋0⦌) 0) :
    (((gridNerveIso W).inv.app (op ⦋0⦌)).app (op ⦋0⦌) F).val = weakChainToGrid W F := rfl
end Independent
section IndependentExactMaps
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
example (n : SimplexCategory) {X Y : WeakRows V n} (f : X ⟶ Y) (p : Interval n) :
    (((weakRowsPostcompose V W hF n).map f).hom.hom.app p) = F.map (f.hom.hom.app p) := rfl
end IndependentExactMaps
