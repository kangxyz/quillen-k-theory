import Quillen.Library
import Quillen.Waldhausen.Fibration.RelativeRows.Completion
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Lean.Util.CollectAxioms
noncomputable section
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.ZeroAugmentation,
      `Quillen.Waldhausen.SConstruction.Rows.Completion,
      `Quillen.Waldhausen.Fibration.RelativeRows.Completion]
  let mut subtotals : Array Nat := #[0, 0, 0]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    subtotals := subtotals.modify i (· + 1)
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless subtotals[i]! > 0 do throwError "Missing defining origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {subtotals[i]!}"
  unless count == 86 do throwError "Expected 86 completion origins, found {count}"
  logInfo m!"Audited {count} actual generic completion origins; only standard3."

open CategoryTheory CategoryTheory.Limits
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.RelativeRows
universe u v
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section GenericRows
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {n : SimplexCategory} (F : Fin (n.len+1) ⥤ C)
  (hF : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), W.cof (F.map f))
example : QuotientRows.cofiberCompletion W F hF =
    QuotientRows.cofibrationArrowDiagram W F hF ⋙ ExtensionCategory.cofiber W := rfl
example (i j k : Fin (n.len+1)) (hij : i ≤ j) (hjk : j ≤ k) :
    ExtensionCategory.cof W ((QuotientRows.cofibrationArrowDiagram W F hF).map
      (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl,hjk⟩))) :=
  QuotientRows.cofibrationArrowDiagram_horizontal_cof W F hF i j k hij hjk
example : QuotientRows.IsRow W (QuotientRows.cofiberCompletion W F hF) :=
  QuotientRows.cofiberCompletion_isRow W F hF
example (p : Interval n) :
    QuotientRows.completionQuotient W F hF p =
      (ExtensionCategory.quotient W).app ((QuotientRows.cofibrationArrowDiagram W F hF).obj p) := rfl
example (p : Interval n) :
    IsPushout (F.map (homOfLE p.property)) (W.isZero.from_ (F.obj p.val.1))
      (QuotientRows.completionQuotient W F hF p)
      (W.isZero.to_ ((QuotientRows.completeCofibrationFlag W F hF).obj.obj p)) :=
  QuotientRows.completionQuotient_isPushout W F hF p
example (G : Fin (n.len+1) ⥤ C)
    (hG : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), W.cof (G.map f))
    (α : F ⟶ G) (hα : ∀ i, W.weq (α.app i)) :
    QuotientRows.weq W n (QuotientRows.completeCofibrationFlagMap W hF hG α) :=
  QuotientRows.completeCofibrationFlagMap_weak W hF hG α hα
-- Generic completion also applies to the actual row Waldhausen category.
example (m : SimplexCategory) (A : Fin (n.len+1) ⥤ QuotientRows.Obj W m)
    (hA : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j),
      (QuotientRows.waldhausenStructure W m).cof (A.map f)) :
    QuotientRows.IsRow (QuotientRows.waldhausenStructure W m)
      (QuotientRows.cofiberCompletion (QuotientRows.waldhausenStructure W m) A hA) :=
  QuotientRows.cofiberCompletion_isRow (QuotientRows.waldhausenStructure W m) A hA
end GenericRows

section Relative
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {n : SimplexCategory}
  (F : ComposableArrows C n.len)
  (hF : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), V.cof (F.map f))
  (hw : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), N.coarse.weq (F.map f))
-- No extension or saturation assumption enters the genuine completion direction.
example : F ≅ (initialFiltrationFunctor N n).obj (relativeCompletion N F hF hw) :=
  relativeCompletionInitialIso N F hF hw
example : ∃ R : Obj N n, Nonempty (F ≅ (initialFiltrationFunctor N n).obj R) :=
  initialFiltration_exists_of_cof_weak N F hF hw
example (i : Fin (n.len+1)) :
    (relativeCompletionInitialIso N F hF hw).hom.app i =
      QuotientRows.completionQuotient V (zeroAugment V F) (zeroAugment_map_cof V F hF)
        (interval 0 i.succ (Fin.zero_le _)) := rfl
example (i : Fin (n.len+1)) : IsIso ((relativeCompletionUnit N F hF hw).app i) :=
  relativeCompletionUnit_app_isIso N F hF hw i
example (G : ComposableArrows C n.len)
    (hG : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), V.cof (G.map f))
    (hwG : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), N.coarse.weq (G.map f))
    (α : F ⟶ G) (hα : ∀ i, V.weq (α.app i)) :
    (waldhausenStructure N n).weq (relativeCompletionMap N hF hw hG hwG α) :=
  relativeCompletionMap_weak N hF hw hG hwG α hα
example (G : ComposableArrows C n.len)
    (hG : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), V.cof (G.map f))
    (hwG : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), N.coarse.weq (G.map f)) (α : F ⟶ G) :
    α ≫ relativeCompletionUnit N G hG hwG = relativeCompletionUnit N F hF hw ≫
      (initialFiltrationFunctor N n).map (relativeCompletionMap N hF hw hG hwG α) :=
  relativeCompletionUnit_naturality N hF hw hG hwG α
end Relative

section Bounded
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example (n : SimplexCategory) (F : ComposableArrows (boundedTerms P).FullSubcategory n.len)
    (hF : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), (boundedTermsExactStructure P).inflation (F.map f))
    (hw : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), QuasiIso (F.map f).hom) :
    ∃ R : Obj (boundedTermsNested P) n,
      Nonempty (F ≅ (initialFiltrationFunctor (boundedTermsNested P) n).obj R) :=
  initialFiltration_exists_of_cof_weak (boundedTermsNested P) F hF hw
end Bounded

section IndependentZeroAndFunctorLaws
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {n : SimplexCategory} (F : ComposableArrows C n.len)
  (hF : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), W.cof (F.map f))
example : (zeroAugment W F).obj 0 = W.zero := rfl
example (i : Fin (n.len+1)) : (zeroAugment W F).obj i.succ = F.obj i := rfl
example : successorIndex n.len ⋙ zeroAugment W F = F := successorIndex_zeroAugment W F
example (G : ComposableArrows C n.len) (α : F ⟶ G) (i : Fin (n.len+1)) :
    (zeroAugmentNatTrans W α).app i.succ = α.app i := rfl
example : QuotientRows.completeCofibrationFlagMap W hF hF (𝟙 F) =
    𝟙 (QuotientRows.completeCofibrationFlag W F hF) :=
  QuotientRows.completeCofibrationFlagMap_id W hF
example (G H : ComposableArrows C n.len)
    (hG : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), W.cof (G.map f))
    (hH : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), W.cof (H.map f))
    (α : F ⟶ G) (β : G ⟶ H) :
    QuotientRows.completeCofibrationFlagMap W hF hH (α ≫ β) =
      QuotientRows.completeCofibrationFlagMap W hF hG α ≫
        QuotientRows.completeCofibrationFlagMap W hG hH β :=
  QuotientRows.completeCofibrationFlagMap_comp W hF hG hH α β
end IndependentZeroAndFunctorLaws
section IndependentDegreeZero
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (F : ComposableArrows C 0)
  (hF : ∀ {i j : Fin 1} (f : i ⟶ j), V.cof (F.map f))
  (hw : ∀ {i j : Fin 1} (f : i ⟶ j), N.coarse.weq (F.map f))
example : F ≅ (initialFiltrationFunctor N ⦋0⦌).obj (relativeCompletion N F hF hw) :=
  relativeCompletionInitialIso N F hF hw
end IndependentDegreeZero
