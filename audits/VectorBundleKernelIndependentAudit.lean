import Quillen.Scheme.VectorBundle.KernelClosure
import Quillen.Waldhausen.GilletWaldhausen.TruncationFunctor
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless #[`Quillen.Scheme.VectorBundle.AffineProjective,
      `Quillen.Scheme.VectorBundle.KernelClosure,
      `Quillen.Waldhausen.GilletWaldhausen.TruncationFunctor].contains origin do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 34 do throwError "Unexpected affine/kernel/functor origin count: {count}"
  logInfo m!"Audited all {count} affine/kernel/truncation-functor declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen
open SchemeSheaf Waldhausen.GilletWaldhausen
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
open scoped ModuleCat.Algebra

example (R : CommRingCat.{u}) (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) :=
  finitePresentation_globalSections_of_finiteLocallyFree R M
example (R : CommRingCat.{u}) (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    Module.Projective R (moduleSpecΓFunctor.obj M) :=
  projective_globalSections_of_finiteLocallyFree R M
example (X : Scheme.{u}) : (sheafExactStructure X).IsKernelClosed (finiteLocallyFree X) :=
  inferInstance
example (X : Scheme.{u}) {M N : FiniteLocallyFree X} (p : M ⟶ N) [Epi p.hom] :
    (vectorBundleExactStructure X).deflation p := vectorBundle_deflation_of_ambient_epi p
example (X : Scheme.{u}) (n : ℤ) :
    (boundedAcyclic (finiteLocallyFree X)).FullSubcategory ⥤
      (boundedAcyclicConflations (finiteLocallyFree X)).FullSubcategory :=
  acyclicTruncationConflationFunctor (finiteLocallyFree X) n
example (X : Scheme.{u}) (n : ℤ) :
    acyclicTruncationConflationFunctor (finiteLocallyFree X) n ⋙
      (boundedAcyclicConflations (finiteLocallyFree X)).ι =
      acyclicTruncationSequenceFunctor (finiteLocallyFree X) n := rfl
example (X : Scheme.{u}) (n : ℤ)
    {K L : (boundedAcyclic (finiteLocallyFree X)).FullSubcategory} (f : K ⟶ L) :
    ((acyclicTruncationSequenceFunctor (finiteLocallyFree X) n).map f).τ₂ = f := rfl
