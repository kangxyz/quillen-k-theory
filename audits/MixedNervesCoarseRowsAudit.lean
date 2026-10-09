import Quillen.Waldhausen.Fibration.MixedNerves.CoarseRows
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.MixedNerves.CoarseRows]
  let mut counts : Array Nat := targets.map (fun _ ↦ 0)
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[idx.toNat]!
    let some i := targets.findIdx? (· == origin) | continue
    counts := counts.modify i (· + 1)
    total := total + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "{origin}: {name} depends on unsupported {ax}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless total == 40 && counts == #[40] do
    throwError "Expected fixed40 origins, found {total}: {counts}"
  logInfo m!"TOTAL_ORIGINS {total}: {counts}"
noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (n k : SimplexCategory)
example (F : Interval n ⥤ C) : QuotientRows.IsRow V F ↔ QuotientRows.IsRow N.coarse F := isRow_coarse_iff N F
example (F : QuotientRows.Obj V n) : ((coarseRowView N n).obj F).obj = F.obj := rfl
example (F : QuotientRows.Obj N.coarse n) : ((fineRowView N n).obj F).obj = F.obj := rfl
example {F G : QuotientRows.Obj V n} (f : F ⟶ G) : ((coarseRowView N n).map f).hom = f.hom := rfl
example {F G : QuotientRows.Obj N.coarse n} (f : F ⟶ G) : ((fineRowView N n).map f).hom = f.hom := rfl
example : coarseRowView N n ⋙ fineRowView N n = 𝟭 _ := coarseRowView_fineRowView N n
example : fineRowView N n ⋙ coarseRowView N n = 𝟭 _ := fineRowView_coarseRowView N n
example : coarseWeakRows N n ≌ QuotientRows.WeakRows N.coarse n := coarseWeakRowsEquivalence N n
example : (coarseWeakRowsEquivalence N n).functor = coarseWeakRowsToStandard N n := rfl
example : (coarseWeakRowsEquivalence N n).inverse = standardToCoarseWeakRows N n := rfl
example (X : coarseWeakRows N n) : ((coarseWeakRowsToStandard N n).obj X).obj.obj = X.obj.obj := rfl
example {X Y : coarseWeakRows N n} (f : X ⟶ Y) (p : Interval n) :
    ((coarseWeakRowsToStandard N n).map f).hom.hom.app p = f.hom.hom.app p := rfl
example {m : SimplexCategory} (α : m ⟶ n) : coarseWeakRowsReindex N α =
    widePostcompose (rowReindexCompatible N α).toFunctor _ _ (rowReindexCompatible N α).coarse := rfl
example {m : SimplexCategory} (α : m ⟶ n) :
    coarseWeakRowsReindex N α ⋙ coarseWeakRowsToStandard N m =
      coarseWeakRowsToStandard N n ⋙ QuotientRows.weakRowsReindex N.coarse α :=
  coarseWeakRowsToStandard_reindex N α
example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := coarseWeakRowNerve N
example : coarseWeakRowNerve N ≅ QuotientRows.weakRowNerve N.coarse := coarseWeakRowNerveIso N
example (F : ComposableArrows (coarseWeakRows N n) k.len) (t : Fin (k.len+1)) (p : Interval n) :
    (((((coarseWeakRowNerveIso N).hom.app (op n)).app (op k) F).obj t).obj.obj.obj p) =
      (F.obj t).obj.obj.obj p := rfl
example (F : ComposableArrows (QuotientRows.WeakRows N.coarse n) k.len)
    {i j : Fin (k.len+1)} (f : i ⟶ j) (p : Interval n) :
    (((((coarseWeakRowNerveIso N).inv.app (op n)).app (op k) F).map f).hom.hom.app p) =
      (F.map f).hom.hom.app p := rfl
example : TheoremA.diagonalSSet (coarseWeakRowNerve N) ≅ sSet N.coarse.cof N.coarse.weq := coarseSSetIso N
example (F : ComposableArrows (coarseWeakRows N n) n.len) :
    ((coarseSSetIso N).hom.app (op n) F).val =
      QuotientRows.weakChainToGrid N.coarse (F ⋙ coarseWeakRowsToStandard N n) := rfl
example (F : ComposableArrows (coarseWeakRows N n) n.len) {a b : Grid n} (f : a ⟶ b) :
    ((coarseSSetIso N).hom.app (op n) F).val.map f =
      (QuotientRows.weakChainToGrid N.coarse (F ⋙ coarseWeakRowsToStandard N n)).map f := rfl
example (F : (sSet N.coarse.cof N.coarse.weq).obj (op n)) (t : Fin (n.len+1)) (p : Interval n) :
    ((((coarseSSetIso N).inv.app (op n) F).obj t).obj.obj.obj p) = F.val.obj (t,p) := rfl
example (F : ComposableArrows (coarseWeakRows N (SimplexCategory.mk 0)) 0) :
    (((coarseSSetIso N).hom.app (op (SimplexCategory.mk 0)) F).val.obj
      (0, interval 0 0 le_rfl)) = (F.obj 0).obj.obj.obj (interval 0 0 le_rfl) := rfl
end Quillen.Waldhausen.Fibration.MixedNerves
