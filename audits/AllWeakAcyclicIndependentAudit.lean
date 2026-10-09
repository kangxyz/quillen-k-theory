import Quillen.Waldhausen.Fibration.AllWeak.AcyclicEquivalence
import Quillen.Waldhausen.Fibration.AllWeak.AcyclicInclusion
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.Waldhausen.Approximation.Properties
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.AllWeak.AcyclicEquivalence,
    `Quillen.Waldhausen.Fibration.AllWeak.AcyclicInclusion]
  let mut counts : Array Nat := #[0, 0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (· + 1)
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing defining module {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless counts == #[17, 5] do throwError "Expected22 origins, got {counts}"
  logInfo m!"Audited all all-weak acyclic origins: {counts}"

noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Equivalence
variable {C : Type u} [Category.{v} C] (W : Structure C)
example : (AllWeak.acyclicEquivalence W).functor = acyclicInclusion (AllWeak.nested W) := rfl
example : (AllWeak.acyclicEquivalence W).inverse = AllWeak.acyclicLift W := rfl
example (X : C) : ((AllWeak.acyclicLift W).obj X).obj = X := rfl
example {X Y : C} (f : X ⟶ Y) : ((AllWeak.acyclicLift W).map f).hom = f := rfl
example : AllWeak.acyclicLift W ⋙ acyclicInclusion (AllWeak.nested W) = 𝟭 C :=
  AllWeak.acyclicLift_inclusion W
example : acyclicInclusion (AllWeak.nested W) ⋙ AllWeak.acyclicLift W = 𝟭 _ :=
  AllWeak.acyclicInclusion_lift W
example : IsExact W.cof W.weq (acyclicStructure (AllWeak.nested W)).cof
    (acyclicStructure (AllWeak.nested W)).weq (AllWeak.acyclicLift W) := AllWeak.acyclicLift_exact W
example : IsExact (acyclicStructure (AllWeak.nested W)).cof
    (acyclicStructure (AllWeak.nested W)).weq W.cof W.weq
    (AllWeak.acyclicEquivalence W).functor := AllWeak.acyclicEquivalence_functor_exact W
example : (AllWeak.acyclicLift W).obj W.zero = (acyclicStructure (AllWeak.nested W)).zero := rfl
example : (AllWeak.acyclicEquivalence W).functor.obj
    (acyclicStructure (AllWeak.nested W)).zero = W.zero := rfl
example {X Y : C} (f : X ⟶ Y) :
    (acyclicStructure (AllWeak.nested W)).weq ((AllWeak.acyclicLift W).map f) ↔ W.weq f := Iff.rfl
example {X Y : C} (f : X ⟶ Y) :
    (acyclicStructure (AllWeak.nested W)).cof ((AllWeak.acyclicLift W).map f) ↔ W.cof f := Iff.rfl
end Equivalence
section Inclusion
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]
example : IsExact (AllWeak.waldhausenStructure (acyclicStructure N)).cof
    (AllWeak.waldhausenStructure (acyclicStructure N)).weq N.coarse.cof N.coarse.weq
    (acyclicInclusion N) := AllWeak.acyclicInclusion_exact N
example : sSetMap (changeWeak_exact (AllWeak.nested (acyclicStructure N))) ≫
    sSetMap (AllWeak.acyclicInclusion_exact N) = sSetMap (acyclicInclusion_coarse_exact N) :=
  AllWeak.changeWeak_acyclicInclusion_sSetMap N
example : (deloopingMap (AllWeak.acyclicInclusion_exact N)).hom.comp
    (changeWeakMap (AllWeak.nested (acyclicStructure N))) =
      (changeWeakMap N).comp (acyclicInclusionMap N) :=
  AllWeak.changeWeak_acyclicInclusion_realized N
example (X : AcyclicCategory N) :
    (acyclicInclusion N).map ((AllWeak.zeroToIdentity (acyclicStructure N)).app X) =
      eqToHom N.zero_eq.symm ≫ (zeroToAcyclicInclusion N).app X :=
  AllWeak.zeroToIdentity_acyclicInclusion_app N X
example : (acyclicInclusion N).obj (AllWeak.waldhausenStructure (acyclicStructure N)).zero =
    N.coarse.zero := AllWeak.acyclicInclusion_zero N
end Inclusion
section BoundedTerms
open GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example : AcyclicCategory (AllWeak.nested (ofExactCategory (boundedTermsExactStructure P))) ≌
    (boundedTerms P).FullSubcategory := AllWeak.acyclicEquivalence _
example : IsExact
    (AllWeak.waldhausenStructure (acyclicStructure (boundedTermsNested P))).cof
    (AllWeak.waldhausenStructure (acyclicStructure (boundedTermsNested P))).weq
    (boundedTermsNested P).coarse.cof (boundedTermsNested P).coarse.weq
    (acyclicInclusion (boundedTermsNested P)) := by
  let : (boundedTermsNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (boundedTerms P)
  exact AllWeak.acyclicInclusion_exact _
end BoundedTerms

section IndependentOriginalWitnesses
variable {C : Type u} [Category.{v} C] (W : Structure C)
example {X Y : C} (f : X ⟶ Y) :
    (AllWeak.acyclicEquivalence W).functor.map ((AllWeak.acyclicLift W).map f) = f := rfl
example {X Y : AcyclicCategory (AllWeak.nested W)} (f : X ⟶ Y) :
    ((AllWeak.acyclicEquivalence W).inverse.map ((AllWeak.acyclicEquivalence W).functor.map f)).hom =
      f.hom := rfl
example {X Y : C} (f : X ⟶ Y) :
    (acyclicStructure (AllWeak.nested W)).weq ((AllWeak.acyclicLift W).map f) = W.weq f := rfl
example {V : Structure C} (N : NestedWeakEquivalences V) (X : AcyclicCategory N) :
    (Fibration.acyclicInclusion N).map ((AllWeak.zeroToIdentity (acyclicStructure N)).app X) =
      eqToHom N.zero_eq.symm ≫ (zeroToAcyclicInclusion N).app X :=
  AllWeak.zeroToIdentity_acyclicInclusion_app N X
example {V : Structure C} (N : NestedWeakEquivalences V) :
    (Fibration.acyclicInclusion N).obj (AllWeak.waldhausenStructure (acyclicStructure N)).zero =
      N.coarse.zero := AllWeak.acyclicInclusion_zero N
end IndependentOriginalWitnesses
section IndependentActualTriangle
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]
example (x : (acyclicStructure N).Delooping) :
    deloopingMap (AllWeak.acyclicInclusion_exact N)
      (changeWeakMap (AllWeak.nested (acyclicStructure N)) x) =
        changeWeakMap N (acyclicInclusionMap N x) :=
  ContinuousMap.congr_fun (AllWeak.changeWeak_acyclicInclusion_realized N) x
end IndependentActualTriangle
