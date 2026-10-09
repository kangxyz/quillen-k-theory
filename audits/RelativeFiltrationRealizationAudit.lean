import Quillen.Waldhausen.Fibration.RelativeRows.FiltrationRealization
import Quillen.Waldhausen.Fibration.ComplexExtension
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.FiltrationNerves,
    `Quillen.Waldhausen.Fibration.RelativeRows.FiltrationRealization]
  let mut counts : Array Nat := #[0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (·+1)
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless counts == #[16,28] do throwError "Expected44 origins, found {counts}"
  logInfo m!"Relative-filtration origin counts: {counts}"
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse) (m n : SimplexCategory)
example : QuotientRows.WeakRows (waldhausenStructure N n) m ≌
    FineWeakChains (RowWeakEquivalences.nested N m) n := innerSFiltrationEquivalence N he m n
example : (innerSFiltrationEquivalence N he m n).functor = innerSFiltration N he m n := rfl
example (F : QuotientRows.WeakRows (waldhausenStructure N n) m)
    (i : Fin (n.len+1)) (p : Interval m) :
    (((innerSFiltration N he m n).obj F).obj.obj.obj i).obj.obj p =
      (F.obj.obj.obj p).obj.obj.obj (interval 0 i.succ (Fin.zero_le _)) := rfl
example : (innerSFiltrationClassifyingHomotopyEquiv N he m n).toFun =
    (classifyingSpaceMap (innerSFiltration N he m n)).hom := rfl
example {n' : SimplexCategory} (α : n' ⟶ n) :
    QuotientRows.weakRowsPostcompose (waldhausenStructure N n) (waldhausenStructure N n')
        (reindex_exact N α) m ⋙ innerSFiltration N he m n' =
      innerSFiltration N he m n ⋙ MixedNerves.fineWeakCofReindex (RowWeakEquivalences.nested N m) α :=
  innerSFiltration_relative_reindex N he m α
example {m' : SimplexCategory} (α : m' ⟶ m) :
    QuotientRows.weakRowsReindex (waldhausenStructure N n) α ⋙ innerSFiltration N he m' n =
      innerSFiltration N he m n ⋙ MixedNerves.fineWeakCofPostcompose (MixedNerves.rowReindexCompatible N α) n :=
  innerSFiltration_inner_reindex N he n α
example : QuotientRows.weakRowNerve (waldhausenStructure N n) ⟶ innerFiltrationNerve N n :=
  innerFiltrationNerveMap N he n
example : TheoremA.diagonalSSet (relativeFiltrationDiagonals N) ≅
    TheoremA.diagonalSSet (MixedNerves.cofRowDiagonals N) := relativeFiltrationTotalIso N
example (F : (TheoremA.diagonalSSet (relativeFiltrationDiagonals N)).obj (op n)) :
    (relativeFiltrationTotalIso N).hom.app (op n) F = F := rfl
example : QuotientRows.WeakRows (waldhausenStructure N ⦋0⦌) ⦋0⦌ ≌
    FineWeakChains (RowWeakEquivalences.nested N ⦋0⦌) ⦋0⦌ := innerSFiltrationEquivalence N he ⦋0⦌ ⦋0⦌
end Generic
section Realization
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse) (n : SimplexCategory)
example : (relativeSRows N).obj (op n) ⟶ (relativeFiltrationDiagonals N).obj (op n) :=
  relativeFiltrationSSet N he n
example : (relativeFiltrationHomotopyEquiv N he n).toFun =
    (SSet.toTop.map (relativeFiltrationSSet N he n)).hom := relativeFiltrationHomotopyEquiv_toFun N he n
example : relativeSRows N ⟶ relativeFiltrationDiagonals N := relativeFiltrationMap N he
example : relativeFiltrationTotalMap N he =
    TheoremA.diagonalMap (relativeFiltrationMap N he) ≫ (relativeFiltrationTotalIso N).hom := rfl
example : ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (relativeSRows N)|
    |TheoremA.diagonalSSet (MixedNerves.cofRowDiagonals N)| := relativeFiltrationTotalHomotopyEquiv N he
example : (relativeFiltrationTotalHomotopyEquiv N he).toFun =
    (SSet.toTop.map (relativeFiltrationTotalMap N he)).hom := relativeFiltrationTotalHomotopyEquiv_toFun N he
example (i j : Fin (n.len+1)) (p : Interval n) :
    (((((relativeFiltrationSSet N he n).app (op n)
      (zeroSimplex (waldhausenStructure N n).cof (waldhausenStructure N n).weq
        (zero N n) (isZero N n) (op n))).obj i).obj.obj.obj j).obj.obj p) = V.zero := rfl
end Realization
section Complex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
open GilletWaldhausen
example : ContinuousMap.HomotopyEquiv
    |TheoremA.diagonalSSet (relativeSRows (boundedTermsNested P))|
    |TheoremA.diagonalSSet (MixedNerves.cofRowDiagonals (boundedTermsNested P))| :=
  relativeFiltrationTotalHomotopyEquiv (boundedTermsNested P) (complexSubcategory_extensionAxiom (boundedTerms P))
end Complex
