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

example : (relativeQuotientSequence α h k hi hj).X₁ = P := rfl
example : (relativeQuotientSequence α h k hi hj).X₂ = middle g.hom := rfl
example : relativeQuotientProjection α =
    jointProjection g.hom ≫ (cokernel.π α.left)⟦(1 : ℤ)⟧' := rfl
example : k ≫ (jointProjection g.hom ≫ (cokernel.π α.left)⟦(1 : ℤ)⟧') = 0 :=
  relativeQuotient_zero α h k hi hj
example (ha : degreewiseSplitMono α.left) : degreewiseSplitMono
    (relativeQuotientSequence α h k hi hj).f :=
  relative_jointInclusion_degreewiseSplitMono α ha h k hi hj

section MinimalCategoricalScope
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {S T : ShortComplex C} (φ : S ⟶ T) [Epi S.g]
  (hT : IsColimit (CokernelCofork.ofπ T.g T.zero))
  {P Q : C} {a : S.X₂ ⟶ P} {b : T.X₁ ⟶ P}
  (k : P ⟶ T.X₂) (ha : a ≫ k = φ.τ₂) (hb : b ≫ k = T.f)
  (p : T.X₃ ⟶ Q) (hp : φ.τ₃ ≫ p = 0)
  (hc : IsColimit (CokernelCofork.ofπ p hp))
  (hk : k ≫ T.g ≫ p = 0)
example : IsColimit (CokernelCofork.ofπ (T.g ≫ p) hk) :=
  isCokernel_relative_middle φ hT k ha hb p hp hc hk
end MinimalCategoricalScope

#print axioms Quillen.Waldhausen.isCokernel_relative_middle
#print axioms Quillen.Waldhausen.SplitFactorization.relativeQuotientSequence_shortExact
#check @Quillen.Waldhausen.isCokernel_relative_middle
#check @Quillen.Waldhausen.SplitFactorization.relativeQuotientSequence_shortExact
