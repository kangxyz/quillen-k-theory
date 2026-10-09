import Quillen.Waldhausen.GilletWaldhausen.FibrationModelKEquivalence
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Functoriality.ExactEquivalence, `Quillen.Waldhausen.GilletWaldhausen.FibrationModels, `Quillen.Waldhausen.GilletWaldhausen.FibrationModelKEquivalence]
  let mut count : Nat := 0
  for origin in targets do
    let mut subtotal : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      subtotal := subtotal + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{origin}: {name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
    logInfo m!"ORIGIN_COUNT {origin}: {subtotal}"
  unless count == 37 do throwError "Expected 37 adapter3 origins, got {count}"
  logInfo m!"Audited all {count} fibration-model-equivalence declaration origins."
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
universe u v
section General
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (e : C ≌ D)
  (hF : IsExact V.cof V.weq W.cof W.weq e.functor)
  (hG : IsExact W.cof W.weq V.cof V.weq e.inverse)
example (n : ℕ) : (KEquivOfExactEquivalence V W e hF hG n).toMonoidHom = KMap hF n := rfl
example (n : ℕ) : (KEquivOfExactEquivalence V W e hF hG n).symm.toMonoidHom = KMap hG n := rfl
example (x : V.K 0) : KMap hG 0 (KMap hF 0 x) = x :=
  KMap_exactEquivalence_left_inv V W e hF hG 0 x
end General
section Complexes
open GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicToFiberObjects P).obj K).obj.obj = K.obj := rfl
example {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    ((boundedAcyclicToFiberObjects P).map f).hom.hom = f.hom := rfl
example : (boundedTermsNested P).coarse = complexSubcategory (boundedTerms P) := rfl
example {K L : (boundedTerms P).FullSubcategory} (f : K ⟶ L) :
    (boundedTermsNested P).coarse.weq f ↔ QuasiIso f.hom := Iff.rfl
example : boundedAcyclicToFiberObjects P ⋙ Fibration.acyclicInclusion (boundedTermsNested P) =
    boundedAcyclicTermsInclusion P := rfl
example (n : ℕ) : (boundedAcyclicFiberKEquiv P n).toMonoidHom =
    KMap (boundedAcyclicToFiberObjects_exact P) n := rfl
example (n : ℕ) : (boundedAcyclicFiberKEquiv P n).symm.toMonoidHom =
    KMap (fiberObjectsToBoundedAcyclic_exact P) n := rfl
example (n : ℕ) :
    (KMap (Fibration.acyclicInclusion_exact (boundedTermsNested P)) n).comp
      (boundedAcyclicFiberKEquiv P n).toMonoidHom =
        KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact n :=
  boundedAcyclicFiberKEquiv_inclusion P n
example (x : (ofExactCategory (boundedAcyclicExactStructure P)).K 0) :
    (boundedAcyclicFiberKEquiv P 0).symm (boundedAcyclicFiberKEquiv P 0 x) = x :=
  (boundedAcyclicFiberKEquiv P 0).symm_apply_apply x
end Complexes
