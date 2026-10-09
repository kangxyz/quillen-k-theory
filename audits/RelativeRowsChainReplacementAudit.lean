import Quillen.Waldhausen.Fibration.RelativeRows.ComplexChainReplacement
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.ChainReplacement,
    `Quillen.Waldhausen.Fibration.RelativeRows.ComplexChainReplacement]
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
    unless counts[i]! > 0 do throwError "Missing defining module {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless count == 24 do throwError "Expected exactly 24 replacement origins, found {count}"
  logInfo m!"Audited {count} actual relative-chain replacement origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : FunctorialFactorization N.coarse)
  [N.coarse.weq.HasTwoOutOfThreeProperty] (n : SimplexCategory)
-- No extension axiom and no fine saturation are assumed here.
example : CoarseWeakChain N n ⥤ Obj N n := relativeReplacement N D n
example (F : CoarseWeakChain N n) :
    ((replacementChainFunctor N D n).obj F).obj =
      (FunctorialFactorization.finiteReplacement D n.len).obj F.obj := rfl
example (F : CoarseWeakChain N n) :
    (relativeReplacement N D n).obj F = (completionFunctor N n).obj
      ((replacementChainFunctor N D n).obj F) := rfl
example (F : CoarseWeakChain N n) {i j : Fin (n.len+1)} (f : i ⟶ j) :
    V.cof (((replacementChainFunctor N D n).obj F).obj.map f) :=
  ((replacementChainFunctor N D n).obj F).property.1 f
example (F : CoarseWeakChain N n) {i j : Fin (n.len+1)} (f : i ⟶ j) :
    N.coarse.weq (((replacementChainFunctor N D n).obj F).obj.map f) :=
  ((replacementChainFunctor N D n).obj F).property.2 f
example : replacementChainFunctor N D n ⋙ (cofibrationWeakChains N n).ι ≅
    relativeReplacement N D n ⋙ initialFiltrationFunctor N n := replacementInitialIso N D n
example (F : CoarseWeakChain N n) (i : Fin (n.len+1)) :
    ((relativeReplacementProjection N D n).app F).app i =
      ((replacementInitialIso N D n).inv.app F).app i ≫
        ((FunctorialFactorization.finiteProjection D n.len).app F.obj).app i := rfl
example (F : CoarseWeakChain N n) (i : Fin (n.len+1)) :
    N.coarse.weq (((relativeReplacementProjection N D n).app F).app i) :=
  relativeReplacementProjection_coarse N D n F i
example {F G : CoarseWeakChain N n} (f : F ⟶ G) :
    (relativeReplacement N D n ⋙ initialFiltrationFunctor N n).map f ≫
      (relativeReplacementProjection N D n).app G =
      (relativeReplacementProjection N D n).app F ≫ f.hom :=
  (relativeReplacementProjection N D n).naturality f
example (hD : MixedChainReplacement.PreservesFineSquares N D)
    {F G : CoarseWeakChain N n} (f : F ⟶ G) (hf : ∀ i, V.weq (f.hom.app i)) :
    (waldhausenStructure N n).weq ((relativeReplacement N D n).map f) :=
  relativeReplacement_fine N D hD f hf
example (F : CoarseWeakChain N n) :
    ((replacementChainFunctor N D n).obj F).obj.obj 0 = F.obj.obj 0 :=
  replacementChainFunctor_obj_zero N D n F
example : CoarseWeakChain N ⦋0⦌ ⥤ Obj N ⦋0⦌ := relativeReplacement N D ⦋0⦌
end Generic

section Concrete
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
example (m n : SimplexCategory) :
    CoarseWeakChain (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n ⥤
      Obj (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n :=
  complexRowRelativeReplacement P hcone hshift m n
example (m n : SimplexCategory)
    (F : CoarseWeakChain (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n)
    (i : Fin (n.len+1)) (p : Interval m) :
    QuasiIso (((((complexRowRelativeProjection P hcone hshift m n).app F).app i).hom.app p).hom) :=
  complexRowRelativeProjection_quasi P hcone hshift m n F i p
example (m n : SimplexCategory)
    {F G : CoarseWeakChain (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n}
    (f : F ⟶ G) (hf : ∀ i p, IsIso ((f.hom.app i).hom.app p)) :
    (waldhausenStructure (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n).weq
      ((complexRowRelativeReplacement P hcone hshift m n).map f) :=
  complexRowRelativeReplacement_fine P hcone hshift m n f hf
end Concrete

section Bounded
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example (m n : SimplexCategory) :
    CoarseWeakChain (RowWeakEquivalences.nested (boundedTermsNested P) m) n ⥤
      Obj (RowWeakEquivalences.nested (boundedTermsNested P) m) n :=
  complexRowRelativeReplacement (boundedTerms P) (fun hK hL f ↦ boundedTerms_mappingCone P hK hL f)
    (fun _ hK ↦ boundedTerms_shift P hK 1) m n
example (X : Scheme.{u}) (m n : SimplexCategory) :
    CoarseWeakChain (RowWeakEquivalences.nested (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) m) n ⥤
      Obj (RowWeakEquivalences.nested (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) m) n :=
  complexRowRelativeReplacement (boundedTerms (SchemeSheaf.finiteLocallyFree X))
    (fun hK hL f ↦ boundedTerms_mappingCone _ hK hL f)
    (fun _ hK ↦ boundedTerms_shift _ hK 1) m n
end Bounded
