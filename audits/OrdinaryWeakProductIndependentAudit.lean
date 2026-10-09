import Quillen.Library
import Lean.Util.CollectAxioms
import Quillen.Topology.HomotopyGroups.ProductWeakEquivalence
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := `Quillen.Topology.HomotopyGroups.ProductWeakEquivalence
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == wanted do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 9 do throwError "Expected 9 declarations, found {count}"
  logInfo m!"Audited all {count} origins of ordinary weak product closure."
noncomputable section
open Quillen
open scoped Topology
universe w u v u' v'
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  (f : C(X,X')) (g : C(Y,Y'))
  (hf : IsWeakHomotopyEquivalence f) (hg : IsWeakHomotopyEquivalence g)
example (N : Type w) (x : X) (y : Y) : Function.Bijective (homotopyProdMap N x y) :=
  homotopyProdMap_bijective N x y
example (x : X) (y : Y) : Function.Bijective (homotopyProdMap (Fin 0) x y) :=
  homotopyProdMap_bijective (Fin 0) x y
example (N : Type w) (x : X) (y : Y) (a : HomotopyGroup N (X × Y) (x,y)) :
    (homotopyProdMap N x y a).1 = homotopyGroupMap ContinuousMap.fst rfl a := rfl
example (N : Type w) (x : X) (y : Y) (a : HomotopyGroup N (X × Y) (x,y)) :
    (homotopyProdMap N x y a).2 = homotopyGroupMap ContinuousMap.snd rfl a := rfl
example (x : X) (y : Y) (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (f.prodMap g) (x := (x,y)) rfl) :=
  (hf.prodMap hg).homotopy_bijective (x,y) n
example (z : X' × Y') : ∃ a, Joined ((f.prodMap g) a) z :=
  (hf.prodMap hg).component_surjective z
example (x : X) (y : Y) (n : ℕ) :
    homotopyProdMap (Fin (n+1)) x y = (piProdMap n x y : _ → _) := rfl
example : IsWeakHomotopyEquivalence (f.prodMap (ContinuousMap.id Y)) := hf.prodMap_id Y
example : IsWeakHomotopyEquivalence ((ContinuousMap.id X).prodMap g) := hg.id_prodMap X
example [IsEmpty X] : IsEmpty (X' × Y') := by
  let : IsEmpty (X × Y) := ⟨fun z ↦ isEmptyElim z.1⟩
  exact (hf.prodMap hg).isEmpty_target
example (N : Type w) (x : X) (y : Y) (a : HomotopyGroup N (X × Y) (x,y)) :
    homotopyProdMap N (f x) (g y) (homotopyGroupMap (f.prodMap g) rfl a) =
      Prod.map (homotopyGroupMap f (x := x) rfl) (homotopyGroupMap g (x := y) rfl)
        (homotopyProdMap N x y a) := homotopyProdMap_naturality N f g x y a
