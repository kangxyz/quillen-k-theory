import Quillen.Library
import Quillen.Topology.HomotopyFiber.BasepointHELP
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HomotopyFiber.BasepointTransport,
    `Quillen.Topology.HomotopyFiber.BasepointHELP]
  let mut count : Nat := 0
  for origin in targets do
    let mut subtotal : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      subtotal := subtotal + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{origin}: {name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
    logInfo m!"ORIGIN_COUNT {origin}: {subtotal}"
  unless count == 13 do throwError "Expected 13 path-transport origins, found {count}"
  logInfo m!"Audited all {count} path-transport origins."
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.HomotopyFiber
variable {E F B B' : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace B] [TopologicalSpace B']
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    {b c : B} (γ : Path b c)
example : (pointMapHomotopy γ).toContinuousMap = γ.toContinuousMap.comp ContinuousMap.fst := rfl
example (z : HomotopyFiber p b) : (basepointTransportEquiv p γ z).val.1 = z.val.1 := rfl
example (z : HomotopyFiber p b) : (basepointTransportEquiv p γ z).val.2 =
    ((toPath p b z).trans γ).toContinuousMap := basepointTransportEquiv_path p γ z
example : (projection p c).comp (basepointTransportEquiv p γ).toFun = projection p b := rfl
example : (basepointTransportEquiv q γ).toFun.comp (mapOver p q f sq b) =
    (mapOver p q f sq c).comp (basepointTransportEquiv p γ).toFun :=
  basepointTransportEquiv_mapOver p q f sq γ
example (q' : C(F,B')) (v : C(B,B')) (sq' : v.comp p = q'.comp f) :
    (basepointTransportEquiv q' (γ.map v.continuous)).toFun.comp (map f v sq' b) =
      (map f v sq' c).comp (basepointTransportEquiv p γ).toFun :=
  basepointTransportEquiv_map p q' f v sq' γ
example (h : CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty (mapOver p q f sq c) :=
  compactHELP_mapOver_of_path p q f sq γ h
example (hbc : Joined b c) (h : CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty (mapOver p q f sq c) :=
  compactHELP_mapOver_of_joined p q f sq hbc h
example (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q) :
    CompactHomotopyExtensionLiftingProperty (strictMapOver p q f sq b) ↔
      CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b) :=
  compactHELP_strictMapOver_iff p q f sq hp hq b
example (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hbc : Joined b c) (h : CompactHomotopyExtensionLiftingProperty (strictMapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty (strictMapOver p q f sq c) :=
  compactHELP_strictMapOver_of_joined p q f sq hp hq hbc h
example (q' : C(F,B')) (v : C(B,B')) (sq' : v.comp p = q'.comp f)
    (h : CompactHomotopyExtensionLiftingProperty (map f v sq' b)) :
    CompactHomotopyExtensionLiftingProperty (map f v sq' c) :=
  compactHELP_map_of_path p f q' v sq' γ h
example (z : HomotopyFiber p b) (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (basepointTransportEquiv p γ).toFun (x := z) rfl) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (basepointTransportEquiv p γ) rfl n
example (z : HomotopyFiber p b) : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (basepointTransportEquiv p γ).toFun (x := z) rfl) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (basepointTransportEquiv p γ) rfl 0
example [IsEmpty (HomotopyFiber p b)] : IsEmpty (HomotopyFiber p c) :=
  ⟨fun z ↦ isEmptyElim ((basepointTransportEquiv p γ).invFun z)⟩
example (hbc : Joined b c) :
    CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b) ↔
      CompactHomotopyExtensionLiftingProperty (mapOver p q f sq c) :=
  ⟨compactHELP_mapOver_of_joined p q f sq hbc,
    compactHELP_mapOver_of_joined p q f sq hbc.symm⟩
example (h : CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b))
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (α : C(A,HomotopyFiber p c)) (β : C(D,HomotopyFiber q c))
    (H : ((mapOver p q f sq c).comp α).Homotopy (β.comp i.hom)) :
    ∃ l : C(D,HomotopyFiber p c), l.comp i.hom = α ∧
      ∃ K : ((mapOver p q f sq c).comp l).Homotopy β,
        ∀ t x, K (t, i x) = H (t, x) :=
  compactHELP_mapOver_of_path p q f sq γ h A D i hi α β H
example (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hbc : Joined b c) (h : CompactHomotopyExtensionLiftingProperty (strictMapOver p q f sq b))
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (α : C(A,{e : E // p e = c})) (β : C(D,{y : F // q y = c}))
    (H : ((strictMapOver p q f sq c).comp α).Homotopy (β.comp i.hom)) :
    ∃ l : C(D,{e : E // p e = c}), l.comp i.hom = α ∧
      ∃ K : ((strictMapOver p q f sq c).comp l).Homotopy β,
        ∀ t x, K (t, i x) = H (t, x) :=
  compactHELP_strictMapOver_of_joined p q f sq hp hq hbc h A D i hi α β H
end Quillen.HomotopyFiber
