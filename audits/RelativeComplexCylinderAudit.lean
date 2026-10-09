import Quillen.Waldhausen.Cylinder.RelativeComplex
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == `Quillen.Waldhausen.Cylinder.RelativeComplex do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 12 do throwError "Unexpected relative cylinder origin count: {count}"
  logInfo m!"Audited all {count} relative complex-cylinder declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization
universe v u
variable {A : Type u} [Category.{v} A] [Abelian A]
  {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g)

example : jointSequence f.hom ⟶ jointSequence g.hom := jointSequenceMap α
example : (jointSequenceMap α).τ₂ = middleFunctor.map α := rfl
example : (jointSequenceMap α).τ₃ = α.left⟦(1 : ℤ)⟧' := rfl
example (ha : degreewiseSplitMono α.left) (hb : degreewiseSplitMono α.right) :
    (splitComplexes A).cof (middleFunctor.map α) :=
  middleFunctor_map_degreewiseSplitMono α ha hb
example (ha : degreewiseSplitMono α.left)
    {P : CochainComplex A ℤ} {i : middle f.hom ⟶ P} {j : g.left ⊞ g.right ⟶ P}
    (h : IsPushout (jointInclusion f.hom) (biprod.map α.left α.right) i j)
    (k : P ⟶ middle g.hom)
    (hi : i ≫ k = middleFunctor.map α) (hj : j ≫ k = jointInclusion g.hom) :
    (splitComplexes A).cof k := relative_jointInclusion_degreewiseSplitMono α ha h k hi hj
