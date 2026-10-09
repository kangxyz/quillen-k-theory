import Quillen.Waldhausen.Cylinder.ZeroEndpoint
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless #[`Quillen.Waldhausen.Cylinder.ZeroEndpoint].contains origin do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 10 do
    throwError "Expected 10 zero-source endpoint origins, found {count}"
  logInfo m!"Audited all {count} actual zero-source endpoint declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen.Waldhausen.SplitFactorization
universe v u w t
variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L : CochainComplex A ℤ} (f : K ⟶ L) (hK : IsZero K)
example : (projectionIsoOfIsZeroSource f hK).hom = projection f := rfl
example : (projectionIsoOfIsZeroSource f hK).inv = (biprod.inr : L ⟶ middle f) := rfl
example : IsIso (projection f) := (projectionIsoOfIsZeroSource f hK).isIso_hom
example {J : Type t} [Category.{w} J] (F : J ⥤ Arrow (CochainComplex A ℤ))
    (hF : ∀ j, IsZero (F.obj j).left) : F ⋙ middleFunctor ≅ F ⋙ Arrow.rightFunc :=
  zeroSourceProjectionNatIso F hF
