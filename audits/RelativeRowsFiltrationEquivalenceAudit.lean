import Quillen.Waldhausen.Fibration.RelativeRows.FiltrationWeakEquivalence
import Quillen.Waldhausen.Fibration.ComplexExtension
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.FiltrationEquivalence,
    `Quillen.Waldhausen.Fibration.RelativeRows.FiltrationWeakEquivalence]
  let mut counts : Array Nat := #[0, 0]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    count := count + 1
    counts := counts.modify i (· + 1)
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing module {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless count == 59 do throwError "Expected exactly 59 presentation origins, found {count}"
  logInfo m!"Audited {count} original filtration presentation origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse) (n : SimplexCategory)
example : Obj N n ≌ CofibrationWeakChain N n := filtrationEquivalence N he n
example : (filtrationEquivalence N he n).functor ⋙ (cofibrationWeakChains N n).ι =
    initialFiltrationFunctor N n := rfl
example (F : CofibrationWeakChain N n) :
    (filtrationEquivalence N he n).inverse.obj F =
      relativeCompletion N F.obj F.property.1 F.property.2 := rfl
example {F G : CofibrationWeakChain N n} (f : F ⟶ G) :
    (filtrationEquivalence N he n).inverse.map f =
      relativeCompletionMap N F.property.1 F.property.2 G.property.1 G.property.2 f.hom := rfl
example {F G : Obj N n} (f : F ⟶ G) :
    chainFineWeak N n ((filtrationEquivalence N he n).functor.map f) ↔
      (waldhausenStructure N n).weq f := filtrationPresentation_weak_iff N he f
example (F : CofibrationWeakChain N n) (i : Fin (n.len+1)) :
    ((completionFiltrationIso N he n).hom.app F).hom.app i =
      QuotientRows.completionQuotient V (zeroAugment V F.obj)
        (zeroAugment_map_cof V F.obj F.property.1) (interval 0 i.succ (Fin.zero_le _)) := rfl
example : FineWeakRows N n ≌ FineWeakChains N n := weakFiltrationEquivalence N he n
example : (weakFiltrationEquivalence N he n).functor = weakFiltrationPresentation N he n := rfl
example : (weakFiltrationEquivalence N he n).inverse = weakCompletionFunctor N n := rfl
example {F G : FineWeakRows N n} (f : F ⟶ G) (i : Fin (n.len+1)) :
    (((weakFiltrationEquivalence N he n).functor.map f).hom.hom).app i =
      f.hom.hom.hom.app (interval 0 i.succ (Fin.zero_le _)) := rfl
example : ContinuousMap.HomotopyEquiv (ClassifyingSpace (FineWeakRows N n))
    (ClassifyingSpace (FineWeakChains N n)) := weakFiltrationClassifyingHomotopyEquiv N he n
example : (weakFiltrationClassifyingHomotopyEquiv N he n).toFun =
    (classifyingSpaceMap (weakFiltrationPresentation N he n)).hom := rfl
example : (weakFiltrationClassifyingHomotopyEquiv N he n).invFun =
    (classifyingSpaceMap (weakCompletionFunctor N n)).hom := rfl
example : FineWeakRows N ⦋0⦌ ≌ FineWeakChains N ⦋0⦌ := weakFiltrationEquivalence N he ⦋0⦌
end Generic

section Bounded
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example (n : SimplexCategory) :
    Obj (boundedTermsNested P) n ≌ CofibrationWeakChain (boundedTermsNested P) n :=
  filtrationEquivalence (boundedTermsNested P) (complexSubcategory_extensionAxiom (boundedTerms P)) n
example (n : SimplexCategory) :
    FineWeakRows (boundedTermsNested P) n ≌ FineWeakChains (boundedTermsNested P) n :=
  weakFiltrationEquivalence (boundedTermsNested P) (complexSubcategory_extensionAxiom (boundedTerms P)) n
end Bounded
