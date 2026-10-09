import Quillen.Library
import Quillen.Topology.HomotopyFiber.WeakSquareTransport
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Topology.HomotopyFiber.StrictWeakTransport,
    `Quillen.Topology.HomotopyFiber.WeakSquareTransport]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[index.toNat]! do continue
    count := count + 1
    let axioms ← collectAxioms name
    for a in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do throwError "Unsupported {a}: {name}"
    logInfo m!"ACCEPTED {env.header.moduleNames[index.toNat]!} {name}: {axioms}"
  unless count == 19 do throwError "Expected 19 weak square origins, got {count}"
  logInfo m!"Audited all {count} weak square transport origins."
noncomputable section
open Quillen
open scoped Topology unitInterval
universe u
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B]
variable (p : C(X,A)) (q : C(Y,B)) (m : C(X,Y)) (v : C(A,B))
    (sq : v.comp p = q.comp m) (hm : IsWeakHomotopyEquivalence m)
    (hv : IsWeakHomotopyEquivalence v) (a : A)
example : IsWeakHomotopyEquivalence (MappingPath.map m v sq.symm) :=
  MappingPath.map_isWeakHomotopyEquivalence m v sq.symm hm
example (z : MappingPath p) : (MappingPath.map m v sq.symm z).1.1 = m z.1.1 := rfl
example (z : MappingPath p) : (MappingPath.map m v sq.symm z).1.2 = v.comp z.1.2 := rfl
example : IsWeakHomotopyEquivalence (MappingPath.strictComparison m v sq.symm) :=
  MappingPath.strictComparison_isWeakHomotopyEquivalence m v sq.symm hm hv
example (z : MappingPath p) : (MappingPath.strictComparison m v sq.symm z).1 =
    (MappingPath.endpoint p z, MappingPath.map m v sq.symm z) := rfl
example : IsWeakHomotopyEquivalence (HomotopyFiber.map m v sq a) :=
  HomotopyFiber.map_isWeakHomotopyEquivalence m v sq hm hv a
example (z : HomotopyFiber p a) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (HomotopyFiber.map m v sq a) (x := z) rfl) :=
  (HomotopyFiber.map_isWeakHomotopyEquivalence m v sq hm hv a).homotopy_bijective z n
example (z : HomotopyFiber p a) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (HomotopyFiber.map m v sq a) (x := z) rfl) :=
  (HomotopyFiber.map_isWeakHomotopyEquivalence m v sq hm hv a).homotopy_bijective z 0
example (z : HomotopyFiber p a) :
    Function.Bijective (homotopyGroupMap (N := Fin 1) (HomotopyFiber.map m v sq a) (x := z) rfl) :=
  (HomotopyFiber.map_isWeakHomotopyEquivalence m v sq hm hv a).homotopy_bijective z 1
example (z : HomotopyFiber p a) : (HomotopyFiber.map m v sq a z).1.1 = m z.1.1 := rfl
example (z : HomotopyFiber p a) : (HomotopyFiber.map m v sq a z).1.2 = v.comp z.1.2 := rfl
example (x : X) (hx : p x = a) :
    HomotopyFiber.map m v sq a (HomotopyFiber.basepoint p a x hx) =
      HomotopyFiber.basepoint q (v a) (m x) ((ContinuousMap.congr_fun sq x).symm.trans (congrArg v hx)) :=
  HomotopyFiber.map_basepoint m v sq x a hx
example (z : HomotopyFiber q (v a)) : ∃ x : HomotopyFiber p a,
    Joined (HomotopyFiber.map m v sq a x) z :=
  (HomotopyFiber.map_isWeakHomotopyEquivalence m v sq hm hv a).component_surjective z
example [IsEmpty (HomotopyFiber p a)] : IsEmpty (HomotopyFiber q (v a)) :=
  (HomotopyFiber.map_isWeakHomotopyEquivalence m v sq hm hv a).isEmpty_target
example [IsEmpty (HomotopyFiber q (v a))] : IsEmpty (HomotopyFiber p a) :=
  ⟨fun z ↦ isEmptyElim (HomotopyFiber.map m v sq a z)⟩
example (em : ContinuousMap.HomotopyEquiv X Y) (ev : ContinuousMap.HomotopyEquiv A B)
    (hs : ev.toFun.comp p = q.comp em.toFun) :
    IsWeakHomotopyEquivalence (HomotopyFiber.map em.toFun ev.toFun hs a) :=
  HomotopyFiber.map_isWeakHomotopyEquivalence_of_equivalences em ev hs a
example (z : HomotopyFiber p a) :
    HomotopyFiber.map m v sq a z =
      (MappingPath.endpointFiberHomeomorph q (v a))
        ((HomotopyPullback.strictPullbackFiberHomeomorph (MappingPath.endpoint q) v a)
          (HomotopyFiber.strictMapOver (MappingPath.endpoint p)
            (HomotopyPullback.strictBaseProjection (MappingPath.endpoint q) v)
            (MappingPath.strictComparison m v sq.symm) rfl a
            ((MappingPath.endpointFiberHomeomorph p a).symm z))) := rfl
section Strict
variable (f : C(X,B)) (g : C(Y,B)) (w : g.comp m = f) (b : B)
example (z : {x : X // f x = b}) : (HomotopyFiber.strictMapOver f g m w b z).1 = m z.1 := rfl
example (hf : HomotopyLiftingProperty f) (hg : HomotopyLiftingProperty g) :
    IsWeakHomotopyEquivalence (HomotopyFiber.strictMapOver f g m w b) :=
  HomotopyFiber.strictMapOver_isWeakHomotopyEquivalence f g m w b hf hg hm
example (hf : HomotopyLiftingProperty f) (hg : HomotopyLiftingProperty g)
    (z : {x : X // f x = b}) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (HomotopyFiber.strictMapOver f g m w b)
      (x := z) rfl) :=
  (HomotopyFiber.strictMapOver_isWeakHomotopyEquivalence f g m w b hf hg hm).homotopy_bijective z 0
example (r : C(A,B)) (z : {z : {z : A × X // f z.2 = r z.1} //
    HomotopyPullback.strictBaseProjection f r z = a}) :
    (HomotopyPullback.strictPullbackFiberHomeomorph f r a z).1 = z.1.1.2 := rfl
example (r : C(A,B)) (z : {x : X // f x = r a}) :
    ((HomotopyPullback.strictPullbackFiberHomeomorph f r a).symm z).1.1 = (a, z.1) := rfl
end Strict
