import Quillen.Waldhausen.Functoriality.ExactEquivalence
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
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
example (n : ℕ) (x : V.K n) : KMap hG n (KMap hF n x) = x :=
  KMap_exactEquivalence_left_inv V W e hF hG n x
example (n : ℕ) (x : W.K n) : KMap hF n (KMap hG n x) = x :=
  KMap_exactEquivalence_right_inv V W e hF hG n x
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
example : (boundedTermsNested P).coarse.cof = (ofExactCategory (boundedTermsExactStructure P)).cof := rfl
example : (boundedTermsNested P).coarse.zero = (ofExactCategory (boundedTermsExactStructure P)).zero := rfl
example {K L : (boundedTerms P).FullSubcategory} (f : K ⟶ L) :
    (ofExactCategory (boundedTermsExactStructure P)).weq f ↔ IsIso f := Iff.rfl
example {K L : Fibration.AcyclicCategory (boundedTermsNested P)} (f : K ⟶ L) :
    (Fibration.acyclicStructure (boundedTermsNested P)).weq f ↔ IsIso f.hom := Iff.rfl
example {K L : Fibration.AcyclicCategory (boundedTermsNested P)} (f : K ⟶ L) :
    (Fibration.acyclicStructure (boundedTermsNested P)).cof f ↔
      (boundedTermsExactStructure P).inflation f.hom := Iff.rfl
example (K : Fibration.AcyclicCategory (boundedTermsNested P)) :
    ((fiberObjectsToBoundedAcyclic P).obj K).obj = K.obj.obj := rfl
example {K L : Fibration.AcyclicCategory (boundedTermsNested P)} (f : K ⟶ L) :
    ((fiberObjectsToBoundedAcyclic P).map f).hom = f.hom.hom := rfl
example : boundedAcyclicToFiberObjects P ⋙ fiberObjectsToBoundedAcyclic P = 𝟭 _ :=
  boundedAcyclicToFiberObjects_comp_inverse P
example : fiberObjectsToBoundedAcyclic P ⋙ boundedAcyclicToFiberObjects P = 𝟭 _ :=
  fiberObjectsToBoundedAcyclic_comp_inverse P
example : IsExact (ofExactCategory (boundedAcyclicExactStructure P)).cof
    (ofExactCategory (boundedAcyclicExactStructure P)).weq
    (Fibration.acyclicStructure (boundedTermsNested P)).cof
    (Fibration.acyclicStructure (boundedTermsNested P)).weq (boundedAcyclicToFiberObjects P) :=
  boundedAcyclicToFiberObjects_exact P
example : IsExact (Fibration.acyclicStructure (boundedTermsNested P)).cof
    (Fibration.acyclicStructure (boundedTermsNested P)).weq
    (ofExactCategory (boundedAcyclicExactStructure P)).cof
    (ofExactCategory (boundedAcyclicExactStructure P)).weq (fiberObjectsToBoundedAcyclic P) :=
  fiberObjectsToBoundedAcyclic_exact P
example {A₀ B₀ C₀ D₀ : (boundedAcyclic P).FullSubcategory}
    {f : A₀ ⟶ B₀} {g : A₀ ⟶ C₀} {i : B₀ ⟶ D₀} {j : C₀ ⟶ D₀}
    (hf : (boundedAcyclicExactStructure P).inflation f) (h : IsPushout f g i j) :
    IsPushout ((boundedAcyclicToFiberObjects P).map f) ((boundedAcyclicToFiberObjects P).map g)
      ((boundedAcyclicToFiberObjects P).map i) ((boundedAcyclicToFiberObjects P).map j) :=
  (boundedAcyclicToFiberObjects_exact P).pushout hf h
example {A₀ B₀ C₀ D₀ : Fibration.AcyclicCategory (boundedTermsNested P)}
    {f : A₀ ⟶ B₀} {g : A₀ ⟶ C₀} {i : B₀ ⟶ D₀} {j : C₀ ⟶ D₀}
    (hf : (Fibration.acyclicStructure (boundedTermsNested P)).cof f) (h : IsPushout f g i j) :
    IsPushout ((fiberObjectsToBoundedAcyclic P).map f) ((fiberObjectsToBoundedAcyclic P).map g)
      ((fiberObjectsToBoundedAcyclic P).map i) ((fiberObjectsToBoundedAcyclic P).map j) :=
  (fiberObjectsToBoundedAcyclic_exact P).pushout hf h
end Complexes
