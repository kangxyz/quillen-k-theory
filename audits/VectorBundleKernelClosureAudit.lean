import Quillen.Scheme.VectorBundle.KernelClosure
import Quillen.PerfectComplexes.Strict
import Quillen.Waldhausen.GilletWaldhausen.AcyclicTruncation
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origins := #[`Quillen.Scheme.VectorBundle.AffineProjective,
    `Quillen.Scheme.VectorBundle.KernelClosure]
  for origin in origins do
    let mut count : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {name}: {axioms}"
    let expected := if origin == `Quillen.Scheme.VectorBundle.AffineProjective then 2 else 5
    unless count == expected do throwError "Unexpected declaration count {count} from {origin}"
    logInfo m!"PASS: all {count} declarations from {origin}, including private/generated constants, have only standard Lean axioms."

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen Quillen.SchemeSheaf Quillen.PerfectComplexes
open Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts

example (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) ∧
      Module.Projective R (moduleSpecΓFunctor.obj M) :=
  ⟨finitePresentation_globalSections_of_finiteLocallyFree R M,
    projective_globalSections_of_finiteLocallyFree R M⟩

example (X : Scheme.{u}) :
    (sheafExactStructure X).IsKernelClosed (finiteLocallyFree X) := inferInstance

example {X : Scheme.{u}} {M N : FiniteLocallyFree X} (p : M ⟶ N) [Epi p.hom] :
    (vectorBundleExactStructure X).deflation p := vectorBundle_deflation_of_ambient_epi p

example {X : Scheme.{u}} {M N : X.Modules} [IsFiniteLocallyFree X M]
    [IsFiniteLocallyFree X N] (p : M ⟶ N) [Epi p] :
    IsFiniteLocallyFree X (kernel p) := finiteLocallyFree_kernel p

example {X : Scheme.{u}} (K : Complex X) (hK : strictPerfect X K)
    (hA : K.Acyclic) (n : ℤ) : IsFiniteLocallyFree X (K.cycles n) := by
  obtain ⟨a, b, hab⟩ := hK.1
  exact cycles_mem (finiteLocallyFree X) K hK.2 hA b
    (fun j hj ↦ hab j (Or.inr hj)) n

example {X : Scheme.{u}} (K : Complex X) (hK : strictPerfect X K)
    (hA : K.Acyclic) (n : ℤ) :
    strictPerfect X (K.truncLE n) ∧ (K.truncLE n).Acyclic := by
  have h := truncLE_mem K n (finiteLocallyFree X) ⟨hK.1, hK.2, hA⟩
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

example {X : Scheme.{u}} (K : Complex X) (hK : strictPerfect X K)
    (hA : K.Acyclic) (n : ℤ) :
    strictPerfect X (K.shortComplexTruncLE n).X₃ ∧ (K.shortComplexTruncLE n).X₃.Acyclic := by
  have h := truncationQuotient_mem K n (finiteLocallyFree X) ⟨hK.1, hK.2, hA⟩
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

example {X : Scheme.{u}} (K : Complex X) (hK : strictPerfect X K)
    (hA : K.Acyclic) (n : ℤ) :
    (boundedAcyclicExactStructure (finiteLocallyFree X)).conflation
      (acyclicTruncationSequence K n (finiteLocallyFree X) ⟨hK.1, hK.2, hA⟩) :=
  acyclicTruncationSequence_conflation K n (finiteLocallyFree X) ⟨hK.1, hK.2, hA⟩

#print axioms Quillen.SchemeSheaf.finiteLocallyFree_kernelClosed
#print axioms Quillen.SchemeSheaf.vectorBundle_deflation_of_ambient_epi
#check @Quillen.SchemeSheaf.finiteLocallyFree_kernel_of_shortExact
#check @Quillen.SchemeSheaf.vectorBundle_deflation_of_ambient_epi
