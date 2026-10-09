import Lean.Util.CollectAxioms
import Quillen.Waldhausen.QuillenComparison.ExactAdditivity

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Waldhausen.QuillenComparison.KCommutativity,
    `Quillen.Waldhausen.QuillenComparison.ExactAdditivity]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    seen := seen.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 3 do throwError "Expected frozen count3, found {count}"
  unless seen.size == 2 do throwError "Missing defining module"
  logInfo m!"Audited all {count} origins of the two original Quillen K-group adapters."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  (E : ExactStructure C) (E' : ExactStructure D)

example (a b : E.K 0) : a * b = b * a := E.K_mul_comm 0 a b
example (n : ℕ) : (E.KCommGroup n).toGroup = inferInstanceAs (Group (E.K n)) := rfl
example : CommGroup (E.K 0) := E.KCommGroup 0

variable (F G H : ExactFunctor E E')
  (a : F.toFunctor ⟶ G.toFunctor) (b : G.toFunctor ⟶ H.toFunctor)
  (w : a ≫ b = 0)
  (hc : ∀ X, E'.conflation (ShortComplex.mk (a.app X) (b.app X) (NatTrans.congr_app w X)))
example (n : ℕ) (x : E.K n) : G.KMap n x = F.KMap n x * H.KMap n x :=
  ExactFunctor.KMap_conflation_additivity F G H a b w hc n x
example (x : E.K 0) : G.KMap 0 x = F.KMap 0 x * H.KMap 0 x :=
  ExactFunctor.KMap_conflation_additivity F G H a b w hc 0 x
