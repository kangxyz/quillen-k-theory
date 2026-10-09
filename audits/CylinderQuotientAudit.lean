import Quillen.Waldhausen.Cylinder.ComplexQuotient
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless #[`Quillen.Waldhausen.Cylinder.RelativeQuotient,
      `Quillen.Waldhausen.Cylinder.ComplexQuotient].contains origin do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 25 do
    throwError "Expected 25 origins, found {count}"
  logInfo m!"Audited all {count} actual relative cylinder quotient declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization
universe v u
variable {A : Type u} [Category.{v} A] [Abelian A]
  {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g)
  {P : CochainComplex A ℤ} {i : middle f.hom ⟶ P} {j : g.left ⊞ g.right ⟶ P}
  (h : IsPushout (jointInclusion f.hom) (biprod.map α.left α.right) i j)
  (k : P ⟶ middle g.hom) (hi : i ≫ k = middleFunctor.map α)
  (hj : j ≫ k = jointInclusion g.hom)

example : (relativeQuotientSequence α h k hi hj).X₃ = (cokernel α.left)⟦(1 : ℤ)⟧ := rfl
example : (relativeQuotientSequence α h k hi hj).f = k := rfl
example : (relativeQuotientSequence α h k hi hj).g =
    jointProjection g.hom ≫ (cokernel.π α.left)⟦(1 : ℤ)⟧' := rfl
example (ha : degreewiseSplitMono α.left) :
    (relativeQuotientSequence α h k hi hj).ShortExact :=
  relativeQuotientSequence_shortExact α h k hi hj ha
example : IsColimit (CokernelCofork.ofπ (relativeQuotientSequence α h k hi hj).g
    (relativeQuotientSequence α h k hi hj).zero) := relativeQuotientIsCokernel α h k hi hj
