import Quillen.Waldhausen.QuillenComparison.ReconstructionIndices
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origin := `Quillen.Waldhausen.QuillenComparison.ReconstructionIndices
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count > 0 do throwError "No declarations audited from {origin}"
  logInfo m!"PASS: all {count} declarations from {origin}, including private/generated constants, have only standard Lean axioms."

noncomputable section
universe u v
open CategoryTheory CategoryTheory.ComposableArrows
open Quillen.Waldhausen.QuillenComparison
open scoped Simplicial

example {D : Type u} [Category.{v} D] {n : ℕ} (F G : ComposableArrows D (n + 1))
    (e : Fin.castSuccFunctor (n + 1) ⋙ F ≅ Fin.castSuccFunctor (n + 1) ⋙ G)
    (a : F.obj (Fin.last (n + 1)) ≅ G.obj (Fin.last (n + 1)))
    (w : F.map' n (n + 1) ≫ a.hom = (e.app (Fin.last n)).hom ≫ G.map' n (n + 1)) :
    F ≅ G := chainIsoMkLast e a w

example (n : ℕ) (i : Fin (n + 1)) :
    (nestedIntervalMap (reconstructionMiddleOrdinal n)).obj (centralInterval ⦋n⦌ i) =
      centralInterval ⦋n + 1⦌ i.castSucc := reconstructionMiddleOrdinal_central n i

#print axioms Quillen.Waldhausen.QuillenComparison.chainIsoMkLast
#check @Quillen.Waldhausen.QuillenComparison.chainIsoMkLast
#check @Quillen.Waldhausen.QuillenComparison.reconstructionMiddle_centralFunctor
