import Quillen.Topology.HomotopyLifting.Compact.OverBaseCorrection
import Quillen.Topology.HomotopyLifting.Compact.FiberwiseExtension
import Quillen.Topology.HomotopyLifting.Compact.FiberwiseBoundaryCorrection
import Quillen.Topology.HomotopyLifting.CubeDuration
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HomotopyLifting.Compact.Stationary,
    `Quillen.Topology.HomotopyLifting.Compact.ParallelLifts,
    `Quillen.Topology.HomotopyLifting.Compact.OverBaseCorrection,
    `Quillen.Topology.HomotopyLifting.Compact.FiberwiseExtension,
    `Quillen.Topology.HomotopyLifting.Compact.FiberwiseBoundaryCorrection]
  let mut counts := targets.map fun _ ↦ (0 : Nat)
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (· + 1)
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless counts == #[4,5,1,1,5] do throwError "Expected16 source origins, found {counts}"
  logInfo m!"FIXED16: {counts}"

noncomputable section
open CategoryTheory Quillen
open scoped Topology unitInterval
universe u
variable {E F B X : Type u} [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace B] [TopologicalSpace X] [CompactSpace X] [LocallyCompactSpace X]
  (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
  (hp : CompactHomotopyLiftingProperty p) (hq : CompactHomotopyLiftingProperty q)

example (hp' : HomotopyLiftingProperty p) : CompactHomotopyLiftingProperty p := hp'.compact
example (a : C(X,E)) (H : C(unitInterval × X,B)) (h₀ : ∀ x,H (0,x) = p (a x)) :
    ∃ L : C(unitInterval × X,E), (∀ x,L (0,x) = a x) ∧
      ∀ t x,p (L (t,x)) = H (t,x) := hp X a H h₀
example (a : C(X,E)) (H : C(unitInterval × X,B))
    (h₀ : ∀ x,H (0,x) = p (a x)) (duration : C(X,unitInterval))
    (hf : ∀ x,duration x = 0 → ∀ t,H (t,x) = p (a x)) :
    ∃ L : C(unitInterval × X,E), (∀ x,L (0,x) = a x) ∧
      (∀ t x,p (L (t,x)) = H (t,x)) ∧
      ∀ x,duration x = 0 → ∀ t,L (t,x) = a x := hp.lift_fixed_zero a H h₀ duration hf
example (a : C(X,E)) (b : C(X,B)) (H : (p.comp a).Homotopy b)
    (duration : C(X,unitInterval))
    (hf : ∀ x,duration x = 0 → ∀ t,H (t,x) = p (a x)) :
    ∃ c : C(X,E),p.comp c = b ∧ (∀ x,duration x = 0 → c x = a x) ∧
      ∃ K : a.Homotopy c,(∀ t x,p (K (t,x)) = H (t,x)) ∧
        ∀ x,duration x = 0 → ∀ t,K (t,x) = a x :=
  hp.correct_over_fixed_zero a b H duration hf
example (a : C(X,E)) (b : C(X,F)) (H : (f.comp a).Homotopy b)
    (duration : C(X,unitInterval))
    (hf : ∀ x,duration x = 0 → ∀ t,H (t,x) = f (a x)) :
    ∃ c : C(X,E),p.comp c = q.comp b ∧ (∀ x,duration x = 0 → c x = a x) ∧
      ∃ V : (f.comp c).Homotopy b,HomotopyOver (q.comp b) q V ∧
        ∀ x,duration x = 0 → ∀ t,V (t,x) = f (a x) :=
  compact_correct_comparison_over_fixed_zero p q f sq hp hq a b H duration hf

example {a b c : C(X,F)} (H : a.Homotopy b) (K : a.Homotopy c)
    (hs : ∀ t x,q (H (t,x)) = q (K (t,x))) (duration : C(X,unitInterval))
    (hH : ∀ x,duration x = 0 → ∀ t,H (t,x) = a x)
    (hK : ∀ x,duration x = 0 → ∀ t,K (t,x) = a x) :
    ∃ V : b.Homotopy c,HomotopyOver (q.comp b) q V ∧
      ∀ x,duration x = 0 → ∀ t,V (t,x) = a x :=
  CompactHomotopyLiftingProperty.parallel_lifts q H K hq hs duration hH hK
example {a b c : C(X,F)} (H : a.Homotopy b) (K : a.Homotopy c)
    (hs : ∀ t x,q (H (t,x)) = q (K (t,x))) (duration : C(X,unitInterval))
    (hH : ∀ x,duration x = 0 → ∀ t,H (t,x) = a x)
    (hK : ∀ x,duration x = 0 → ∀ t,K (t,x) = a x) :
    ∃ V : b.Homotopy c,HomotopyOver (q.comp b) q V ∧
      (∀ x,duration x = 0 → ∀ t,V (t,x) = a x) ∧
      ∃ S : (H.symm.trans K).toContinuousMap.Homotopy V.toContinuousMap,
        (∀ r t x,q (S (r,(t,x))) = q (H (unitInterval.symm
          (unitInterval.symm r * unitInterval.symm (backtrackTime t)),x))) ∧
        (∀ r x,S (r,(0,x)) = b x) ∧ (∀ r x,S (r,(1,x)) = c x) ∧
        ∀ x,duration x = 0 → ∀ r t,S (r,(t,x)) = a x :=
  CompactHomotopyLiftingProperty.parallel_lifts_with_coherence q H K hq hs duration hH hK

example (A D : TopCat.{u}) [CompactSpace D] [LocallyCompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (b : C(D,F)) (H : C(unitInterval × A,F)) (h₀ : ∀ a,H (0,a) = b (i a))
    (hbase : ∀ t a,q (H (t,a)) = q (b (i a))) :
    ∃ T : C(unitInterval × D,F), (∀ x,T (0,x) = b x) ∧
      (∀ t a,T (t,i a) = H (t,a)) ∧ ∀ t x,q (T (t,x)) = q (b x) :=
  hq.extend_over_fixed_base A D i hi duration hzero b H h₀ hbase
example (n : ℕ) : CompactSpace (CubicalTests.cube.{u} n) := inferInstance
example (n : ℕ) : LocallyCompactSpace (CubicalTests.cube.{u} n) := inferInstance

example {A D : TopCat.{u}} [CompactSpace D] [LocallyCompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (base : C(D,B)) {a b : C(D,F)} (K : a.Homotopy b) (hK : HomotopyOver base q K)
    (L : (a.comp i.hom).Homotopy (b.comp i.hom))
    (Q : (K.compContinuousMap i.hom).toContinuousMap.HomotopyRel L.toContinuousMap
      {z : unitInterval × A | z.1 = 0 ∨ z.1 = 1})
    (hQ : ∀ s t a,q (Q (s,(t,a))) = base (i a)) :
    ∃ K' : a.Homotopy b,HomotopyOver base q K' ∧ ∀ t a,K' (t,i a) = L (t,a) :=
  compact_correct_boundary_over_fixed_base q hq i hi duration hzero base K hK L Q hQ
example {A D : TopCat.{u}} [CompactSpace D] [LocallyCompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (base : C(D,B)) {a b : C(D,F)} (K : a.Homotopy b) (hK : HomotopyOver base q K)
    (L : (a.comp i.hom).Homotopy (b.comp i.hom))
    (hL : ∀ t a,q (L (t,a)) = base (i a))
    (hKL : ∀ t a,K (t,i a) = Path.delayReflLeft 0 (L.evalAt a) t) :
    ∃ K' : a.Homotopy b,HomotopyOver base q K' ∧ ∀ t a,K' (t,i a) = L (t,a) :=
  compact_unpad_boundary_over_fixed_base q hq i hi duration hzero base K hK L hL hKL
example (x : CubicalTests.cube.{u} 0) : CubicalTests.boundaryDuration 0 x = 1 :=
  CubicalTests.boundaryDuration_zero_dim x
example (n : ℕ) (a : C(CubicalTests.cube.{u} n,E))
    (H : C(unitInterval × CubicalTests.cube.{u} n,B))
    (h₀ : ∀ x,H (0,x) = p (a x))
    (hf : ∀ x,CubicalTests.boundaryDuration n x = 0 → ∀ t,H (t,x) = p (a x)) :
    ∃ L : C(unitInterval × CubicalTests.cube.{u} n,E), (∀ x,L (0,x) = a x) ∧
      (∀ t x,p (L (t,x)) = H (t,x)) ∧
      ∀ x,CubicalTests.boundaryDuration n x = 0 → ∀ t,L (t,x) = a x :=
  hp.lift_fixed_zero a H h₀ (CubicalTests.boundaryDuration n) hf
