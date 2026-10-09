import Quillen.Waldhausen.Fibration.RelativeRows.FiltrationWeakEquivalence
import Quillen.Waldhausen.Fibration.ComplexExtension
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.FiltrationEquivalence,
    `Quillen.Waldhausen.Fibration.RelativeRows.FiltrationWeakEquivalence]
  let mut counts : Array Nat := #[0, 0]
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some target := targets.findIdx? (· == origin) | continue
    total := total + 1
    counts := counts.modify target (· + 1)
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless total == 59 && counts == #[26, 33] do
    throwError "Expected fixed59 origins (26+33), found {total} with {counts}"
  logInfo m!"Audited all {total} original filtration presentation origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows
section Generic
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse) (n : SimplexCategory)
example (F : ComposableArrows C n.len) : cofibrationWeakChains N n F ↔
    (∀ {i j : Fin (n.len+1)} (f : i ⟶ j), V.cof (F.map f)) ∧
    (∀ {i j : Fin (n.len+1)} (f : i ⟶ j), N.coarse.weq (F.map f)) := Iff.rfl
example : filtrationPresentation N he n ⋙ (cofibrationWeakChains N n).ι =
    initialFiltrationFunctor N n := rfl
example (F : Obj N n) : ((filtrationPresentation N he n).obj F).obj = initialFiltration F.obj := rfl
example {F G : Obj N n} (f : F ⟶ G) (i : Fin (n.len+1)) :
    (((filtrationPresentation N he n).map f).hom).app i =
      f.hom.hom.app (interval 0 i.succ (Fin.zero_le _)) := rfl
example (F : CofibrationWeakChain N n) : (completionFunctor N n).obj F =
    relativeCompletion N F.obj F.property.1 F.property.2 := rfl
example {F G : CofibrationWeakChain N n} (f : F ⟶ G) : (completionFunctor N n).map f =
    relativeCompletionMap N F.property.1 F.property.2 G.property.1 G.property.2 f.hom := rfl
example (F : CofibrationWeakChain N n) (i : Fin (n.len+1)) :
    ((completionFiltrationIso N he n).hom.app F).hom.app i =
      QuotientRows.completionQuotient V (zeroAugment V F.obj) (zeroAugment_map_cof V F.obj F.property.1)
        (interval 0 i.succ (Fin.zero_le _)) := rfl
example (F : Obj N n) : (filtrationCompletionIso N he n).hom.app F =
    (initialFiltrationFullyFaithful N n).preimage
      (relativeCompletionInitialIso N ((filtrationPresentation N he n).obj F).obj
        ((filtrationPresentation N he n).obj F).property.1
        ((filtrationPresentation N he n).obj F).property.2).hom := rfl
example : Obj N n ≌ CofibrationWeakChain N n := filtrationEquivalence N he n
example : (filtrationEquivalence N he n).functor = filtrationPresentation N he n := rfl
example : (filtrationEquivalence N he n).inverse = completionFunctor N n := rfl
example {F G : Obj N n} (f : F ⟶ G) :
    chainFineWeak N n ((filtrationPresentation N he n).map f) ↔ (waldhausenStructure N n).weq f :=
  filtrationPresentation_weak_iff N he f
example {F G : CofibrationWeakChain N n} (f : F ⟶ G) (hf : ∀ i, V.weq (f.hom.app i)) :
    (waldhausenStructure N n).weq ((completionFunctor N n).map f) := completionFunctor_weak N f hf
example : FineWeakRows N n ≌ FineWeakChains N n := weakFiltrationEquivalence N he n
example : (weakFiltrationEquivalence N he n).functor = weakFiltrationPresentation N he n := rfl
example : (weakFiltrationEquivalence N he n).inverse = weakCompletionFunctor N n := rfl
example {F G : FineWeakRows N n} (f : F ⟶ G) (i : Fin (n.len+1)) :
    (((weakFiltrationPresentation N he n).map f).hom.hom).app i =
      f.hom.hom.hom.app (interval 0 i.succ (Fin.zero_le _)) := rfl
example {F G : FineWeakChains N n} (f : F ⟶ G) : ((weakCompletionFunctor N n).map f).hom =
    relativeCompletionMap N F.obj.property.1 F.obj.property.2
      G.obj.property.1 G.obj.property.2 f.hom.hom := rfl
example (F : FineWeakRows N n) :
    ((weakFiltrationCompletionIso N he n).hom.app F).hom =
      (filtrationCompletionIso N he n).hom.app F.obj := rfl
example (F : FineWeakChains N n) :
    ((weakCompletionFiltrationIso N he n).hom.app F).hom =
      (completionFiltrationIso N he n).hom.app F.obj := rfl
example : ContinuousMap.HomotopyEquiv (ClassifyingSpace (FineWeakRows N n))
    (ClassifyingSpace (FineWeakChains N n)) := weakFiltrationClassifyingHomotopyEquiv N he n
example : (weakFiltrationClassifyingHomotopyEquiv N he n).toFun =
    (classifyingSpaceMap (weakFiltrationPresentation N he n)).hom := rfl
example : (weakFiltrationClassifyingHomotopyEquiv N he n).invFun =
    (classifyingSpaceMap (weakCompletionFunctor N n)).hom := rfl
example : (weakFiltrationClassifyingHomotopyEquiv N he ⦋0⦌).toFun =
    (classifyingSpaceMap (weakFiltrationPresentation N he ⦋0⦌)).hom := rfl
end Generic
section Concrete
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example (n : SimplexCategory) : Obj (boundedTermsNested P) n ≌ CofibrationWeakChain (boundedTermsNested P) n :=
  filtrationEquivalence _ (complexSubcategory_extensionAxiom (boundedTerms P)) n
example (n : SimplexCategory) : FineWeakRows (boundedTermsNested P) n ≌ FineWeakChains (boundedTermsNested P) n :=
  weakFiltrationEquivalence _ (complexSubcategory_extensionAxiom (boundedTerms P)) n
example (n : SimplexCategory) : ContinuousMap.HomotopyEquiv
    (ClassifyingSpace (FineWeakRows (boundedTermsNested P) n))
    (ClassifyingSpace (FineWeakChains (boundedTermsNested P) n)) :=
  weakFiltrationClassifyingHomotopyEquiv _ (complexSubcategory_extensionAxiom (boundedTerms P)) n
example (X : Scheme.{u}) (n : SimplexCategory) : ContinuousMap.HomotopyEquiv
    (ClassifyingSpace (FineWeakRows (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n))
    (ClassifyingSpace (FineWeakChains (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n)) :=
  weakFiltrationClassifyingHomotopyEquiv _ (complexSubcategory_extensionAxiom _) n
end Concrete
end Quillen.Waldhausen.Fibration.RelativeRows
