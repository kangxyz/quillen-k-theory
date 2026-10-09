import Quillen.Waldhausen.Additivity.SubdivisionBasepoint
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! ==
        `Quillen.Waldhausen.Additivity.SubdivisionBasepoint do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 10 do
    throwError "Expected 10 based subdivision origins, found {count}"
  unless count == 10 do
    throwError "Expected 10 subdivision-basepoint origins, found {count}"
  logInfo m!"Audited all {count} based subdivision declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Quillen Quillen.Waldhausen Quillen.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v
variable {C : Type u} [Category.{v} C] (V : Structure C)

example : subdivisionZeroVertex V =
    zeroSimplex₂ V.cof V.weq V.zero V.isZero
      (op (OrdinalSubdivision.δ.obj ⦋0⦌)) (op ⦋0⦌) := rfl
example : subdivisionBasepoint V = realizationPoint (subdivisionZeroVertex V) := rfl
example : (TheoremA.diagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))).app
    (op ⦋0⦌) (subdivisionZeroVertex V) = diagonalZeroVertex V := rfl
example (n : ℕ) : (subdivisionPiEquiv V n).toMonoidHom =
    piMap n (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
      (horizontalEndpoint_basepoint V) := rfl
example (n : ℕ) : Function.Surjective
    (piMap n (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
      (horizontalEndpoint_basepoint V)) := subdivisionPiMap_surjective V n


example (n : ℕ) : Function.Injective
    (piMap n (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
      (horizontalEndpoint_basepoint V)) := (subdivisionPiEquiv V n).injective

-- Actual based precomposition cancels, without any based inverse as input.
universe w
example (n : ℕ) {G : Type w} [Monoid G]
    (f g : HomotopyGroup.Pi (n + 1) |TheoremA.diagonalSSet (bisimplicialSSet V)|
      (realizationPoint (diagonalZeroVertex V)) →* G)
    (h : f.comp (piMap n
        (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
        (horizontalEndpoint_basepoint V)) =
      g.comp (piMap n
        (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
        (horizontalEndpoint_basepoint V))) : f = g := by
  ext x
  obtain ⟨a, rfl⟩ := subdivisionPiMap_surjective V n x
  exact DFunLike.congr_fun h a
