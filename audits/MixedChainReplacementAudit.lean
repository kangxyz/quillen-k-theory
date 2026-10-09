import Quillen.Waldhausen.Fibration.ComplexChainReplacement
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
noncomputable section
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless #[`Quillen.Waldhausen.Fibration.MixedChainReplacement,
      `Quillen.Waldhausen.Fibration.ComplexChainReplacement].contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 28 do
    throwError "Expected 28 mixed-chain replacement origins, found {count}"
  logInfo m!"Audited {count} mixed-chain replacement origins; only standard3."

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open FunctorialFactorization MixedChainReplacement
section Generic
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : FunctorialFactorization N.coarse)
-- No two-out-of-three hypothesis for the fine class, and no fine projection premise.
example (hD : PreservesFineSquares N D) (n : ℕ) {F G : ComposableArrows C n}
    (α : F ⟶ G) (hα : ∀ i, V.weq (α.app i)) (i : Fin (n+1)) :
    V.weq (((finiteReplacement D n).map α).app i) := finiteReplacement_map_fine N D hD n α hα i
example (n : ℕ) (F : ComposableArrows C n) (i : Fin (n+1)) :
    N.coarse.weq (((finiteProjection D n).app F).app i) := finiteProjection_coarse N D n F i
example (n : ℕ) (F : ComposableArrows C n) {i j : Fin (n+1)} (f : i ⟶ j) :
    V.cof (((finiteReplacement D n).obj F).map f) := finiteReplacement_map_fine_cof N D n F f
example (n : ℕ) {F G : ComposableArrows C n} (α : F ⟶ G) :
    (finiteReplacement D n).map α ≫ (finiteProjection D n).app G =
      (finiteProjection D n).app F ≫ α := (finiteProjection D n).naturality α
example (F : ComposableArrows C 0) : ((finiteReplacement D 0).obj F).obj 0 = F.obj 0 :=
  finiteReplacement_initial N D 0 F
example [N.coarse.weq.HasTwoOutOfThreeProperty] (n : ℕ) (F : ComposableArrows C n)
    {i j : Fin (n+1)} (f : i ⟶ j) (hf : N.coarse.weq (F.map f)) :
    N.coarse.weq (((finiteReplacement D n).obj F).map f) := finiteReplacement_map_coarse N D n F f hf
end Generic

section Complexes
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
example (f : Arrow P.FullSubcategory) :
    ((complexSubcategoryFactorization P hcone).inclusion.app f).hom =
      SplitFactorization.inclusion f.hom.hom := rfl
example (f : Arrow P.FullSubcategory) :
    ((complexSubcategoryFactorization P hcone).projection.app f).hom =
      SplitFactorization.projection f.hom.hom := rfl
example : PreservesFineSquares (complexSubcategoryNested P) (complexSubcategoryFactorization P hcone) :=
  complexSubcategoryFactorization_fineSquares P hcone
example (n : ℕ) {F G : ComposableArrows P.FullSubcategory n} (α : F ⟶ G)
    (hα : ∀ i, IsIso (α.app i)) (i : Fin (n+1)) :
    IsIso (((finiteReplacement (complexSubcategoryFactorization P hcone) n).map α).app i) :=
  complexFiniteReplacement_map_fine P hcone n α hα i
example (n : ℕ) (F : ComposableArrows P.FullSubcategory n)
    (hF : ∀ {i j : Fin (n+1)} (f : i ⟶ j), QuasiIso (F.map f).hom)
    {i j : Fin (n+1)} (f : i ⟶ j) :
    subcategoryCofibrations P (((finiteReplacement (complexSubcategoryFactorization P hcone) n).obj F).map f) ∧
    QuasiIso ((((finiteReplacement (complexSubcategoryFactorization P hcone) n).obj F).map f).hom) :=
  complexFiniteReplacement_map_cof_quasi P hcone n F hF f
example (n : ℕ) (F : ComposableArrows P.FullSubcategory n) (i : Fin (n+1)) :
    QuasiIso ((((finiteProjection (complexSubcategoryFactorization P hcone) n).app F).app i).hom) :=
  complexFiniteProjection_quasi P hcone n F i
end Complexes

section Bounded
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
-- The original bounded-term nested model, with no kernel closure or fixed global bound.
example : boundedTermsNested P = complexSubcategoryNested (boundedTerms P) := rfl
example : PreservesFineSquares (boundedTermsNested P)
    (complexSubcategoryFactorization (boundedTerms P) (boundedTerms_mappingCone P)) :=
  complexSubcategoryFactorization_fineSquares (boundedTerms P) (boundedTerms_mappingCone P)
example (n : ℕ) (F : ComposableArrows (boundedTerms P).FullSubcategory n) (i : Fin (n+1)) :
    QuasiIso ((((finiteProjection
      (complexSubcategoryFactorization (boundedTerms P) (boundedTerms_mappingCone P)) n).app F).app i).hom) :=
  complexFiniteProjection_quasi (boundedTerms P) (boundedTerms_mappingCone P) n F i
end Bounded

open AlgebraicGeometry GilletWaldhausen
example (X : Scheme.{u}) : PreservesFineSquares (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))
    (complexSubcategoryFactorization (boundedTerms (SchemeSheaf.finiteLocallyFree X))
      (boundedTerms_mappingCone (SchemeSheaf.finiteLocallyFree X))) :=
  complexSubcategoryFactorization_fineSquares _ (boundedTerms_mappingCone _)
