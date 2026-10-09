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
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 17 do throwError "Unexpected exact-functor origin count: {count}"
  logInfo m!"Audited all {count} exact functor/Waldhausen declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
universe v u v' u'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

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
example (n : ℕ) :
    (comparisonKEquiv ED' n).toMonoidHom.comp (Waldhausen.KMap G.waldhausenExact n) =
      (G.KMap n).comp (comparisonKEquiv EC n).toMonoidHom :=
  comparisonKEquiv_exactFunctor_naturality G n
end SameUniverses
