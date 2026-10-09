import Quillen.Waldhausen.QuillenComparison.ExactNaturality
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless #[`Quillen.CategoryTheory.ExactCategory.MatrixInflation,
      `Quillen.CategoryTheory.ExactCategory.FunctorPushout,
      `Quillen.Waldhausen.ExactFunctor,
      `Quillen.Waldhausen.QuillenComparison.ExactNaturality].contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 17 do throwError "Expected frozen 17-declaration scope; audited {count}"
  logInfo m!"Audited all {count} exact functor/Waldhausen declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
universe v u v' u'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

example {A T : C} (f : A ⟶ T) :
    EC.inflation (biprod.lift (𝟙 A) f) := EC.inflation_graph f
example {A B T : C} (i : A ⟶ B) (f : A ⟶ T) (hi : EC.inflation i) :
    EC.inflation (biprod.lift i f) := EC.inflation_biprod_lift i f hi
example {A B T P : C} {i : A ⟶ B} {f : A ⟶ T} {g : B ⟶ P} {j : T ⟶ P}
    (w : i ≫ g = f ≫ j) : (pushoutShortComplex w).f = biprod.lift i (-f) := rfl
example {A B T P : C} {i : A ⟶ B} {f : A ⟶ T} {g : B ⟶ P} {j : T ⟶ P}
    (w : i ≫ g = f ≫ j) : (pushoutShortComplex w).g = biprod.desc g j := rfl
example {A B T P : C} {i : A ⟶ B} {f : A ⟶ T} {g : B ⟶ P} {j : T ⟶ P}
    (h : IsPushout i f g j) :
    IsColimit (CokernelCofork.ofπ (pushoutShortComplex h.w).g (pushoutShortComplex h.w).zero) :=
  isCokernelOfBiprodPushout h
example {A B T P : C} {i : A ⟶ B} {f : A ⟶ T} {g : B ⟶ P} {j : T ⟶ P}
    (hi : EC.inflation i) (h : IsPushout i f g j) :
    IsPushout (F.toFunctor.map i) (F.toFunctor.map f)
      (F.toFunctor.map g) (F.toFunctor.map j) := F.map_isPushout hi h
example : Waldhausen.IsExact
    (Waldhausen.ofExactCategory EC).cof (Waldhausen.ofExactCategory EC).weq
    (Waldhausen.ofExactCategory ED).cof (Waldhausen.ofExactCategory ED).weq F.toFunctor :=
  F.waldhausenExact

section SameUniverses
variable {D' : Type u} [Category.{v} D'] [Preadditive D'] [HasFiniteBiproducts D']
  {ED' : ExactStructure D'} (G : ExactFunctor EC ED')
open Waldhausen.QuillenComparison
example (n : ℕ) : normalizedExactSKMap G n = Waldhausen.KMap G.waldhausenExact n :=
  normalizedExactSKMap_eq_KMap G G.waldhausenExact n
example (n : ℕ) :
    (comparisonKEquiv ED' n).toMonoidHom.comp (Waldhausen.KMap G.waldhausenExact n) =
      (G.KMap n).comp (comparisonKEquiv EC n).toMonoidHom :=
  comparisonKEquiv_exactFunctor_naturality G n
end SameUniverses

#print axioms Quillen.ExactFunctor.map_isPushout
#print axioms Quillen.Waldhausen.QuillenComparison.comparisonKEquiv_exactFunctor_naturality
#check @Quillen.ExactFunctor.waldhausenExact
#check @Quillen.Waldhausen.QuillenComparison.comparisonKEquiv_exactFunctor_naturality
