import Lean.Util.CollectAxioms
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsSSetColimit

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Waldhausen.GilletWaldhausen.BoundedTermsStrata,
    `Quillen.Waldhausen.GilletWaldhausen.BoundedTermsSSet,
    `Quillen.Waldhausen.GilletWaldhausen.BoundedTermsSSetColimit]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    seen := seen.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 53 do throwError "Expected frozen count53, found {count}"
  unless seen.size == 3 do throwError "Missing defining module"
  logInfo m!"Independently audited all {count} origins of the three bounded-term coverage modules."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.GilletWaldhausen
open scoped Simplicial Topology
universe u v w
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

-- Actual finite bounds do not assume kernel closure or any closure property.
example {I : Type w} [Finite I] (F : I → (boundedTerms P).FullSubcategory) :
    ∃ N : ℕ, ∀ i, HasTermBounds (F i).obj (-(N : ℤ)) N := boundedTermsStratum_covers_finite P F
example {N M : ℕ} (h : N ≤ M) (X : (boundedTermsStratum P N).FullSubcategory) :
    ((boundedTermsStratumTransition P h).obj X).obj = X.obj := rfl

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  (W : MorphismProperty (boundedTerms P).FullSubcategory)
example (N : ℕ) {X Y : (boundedTermsStratum P N).FullSubcategory} (f : X ⟶ Y) :
    (boundedTermsStratumExactStructure P N).inflation f ↔
      (boundedTermsExactStructure P).inflation f.hom := boundedTermsStratum_inflation_iff P N f
example (N : ℕ) {X Y : (boundedTermsStratum P N).FullSubcategory} (f : X ⟶ Y) :
    boundedTermsStratumWeak P W N f ↔ W f.hom := Iff.rfl
example (N : ℕ) : boundedTermsStratumWeak P (MorphismProperty.isomorphisms _) N =
    MorphismProperty.isomorphisms _ := by
  ext X Y f
  exact ObjectProperty.isIso_hom_iff f
example (N : ℕ) (n : SimplexCategoryᵒᵖ) (F : (boundedTermsStratumSSet P W N).obj n) :
    ((boundedTermsStratumSSetInclusion P W N).app n F).val =
      F.val ⋙ (boundedTermsStratum P N).ι := rfl
example {N M : ℕ} (h : N ≤ M) :
    boundedTermsStratumSSetTransition P W h ≫ boundedTermsStratumSSetInclusion P W M =
      boundedTermsStratumSSetInclusion P W N := boundedTermsStratumSSetTransition_inclusion P W h
example : IsColimit (boundedTermsSSetCocone P W) := boundedTermsSSetCocone_isColimit P W
example (N : ℕ) : (boundedTermsSSetCocone P W).ι.app (boundedStageIndex N) =
    boundedTermsStratumSSetInclusion P W N := rfl
example {N M : ℕ} (h : N ≤ M) :
    (boundedTermsSSetDiagram P W).map (AsSmall.up.map (homOfLE h)) =
      boundedTermsStratumSSetTransition P W h := rfl

example {T : Type w} [TopologicalSpace T] [CompactSpace T] (N : ℕ)
    (f : C(T, |boundedTermsSSet P W|)) :
    ∃ M : ℕ, N ≤ M ∧ ∃ g : C(T, |boundedTermsStratumSSet P W M|),
      (SSet.toTop.map (boundedTermsStratumSSetInclusion P W M)).hom.comp g = f :=
  boundedTermsSSet_compact_factors_above P W N f
example {T : Type w} [TopologicalSpace T] [CompactSpace T] (N : ℕ)
    {a b : C(T, |boundedTermsStratumSSet P W N|)} (S : Set T) (hS : IsCompact S)
    (H : ((SSet.toTop.map (boundedTermsStratumSSetInclusion P W N)).hom.comp a).HomotopyRel
      ((SSet.toTop.map (boundedTermsStratumSSetInclusion P W N)).hom.comp b) S) :
    ∃ M : ℕ, ∃ h : N ≤ M,
      Nonempty (((SSet.toTop.map (boundedTermsStratumSSetTransition P W h)).hom.comp a).HomotopyRel
        ((SSet.toTop.map (boundedTermsStratumSSetTransition P W h)).hom.comp b) S) :=
  boundedTermsSSet_homotopyRel_factors P W N S hS H

example (N : ℕ) {X Y : (boundedTermsStratum P N).FullSubcategory} (f : X ⟶ Y) :
    boundedTermsStratumWeak P (complexSubcategory (boundedTerms P)).weq N f ↔
      QuasiIso f.hom.hom := Iff.rfl
