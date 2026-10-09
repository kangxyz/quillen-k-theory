import Quillen.Topology.HomotopyLifting.CubeOverBase
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HomotopyLifting.VariableTime,
    `Quillen.Topology.HomotopyLifting.Stationary,
    `Quillen.Topology.HomotopyLifting.ParallelLifts,
    `Quillen.Topology.HomotopyLifting.OverBaseCorrection,
    `Quillen.Topology.HomotopyLifting.CubeDuration,
    `Quillen.Topology.HELP.ContractibleTestOverBase,
    `Quillen.Topology.HomotopyLifting.CubeOverBase]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    seen := seen.insert origin
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axs}"
  unless seen.size == 7 do throwError "Missing strict-over-base origin"
  unless count == 41 do throwError "Expected 41 strict-over-base origins, found {count}"
  logInfo m!"Audited all {count} strict-over-base origins."
noncomputable section
open CategoryTheory Quillen
open scoped Topology unitInterval
universe u v w z
example {K : Type u} {X : Type v} {Y : Type w} {Z : Type z}
    [TopologicalSpace K] [CompactSpace K] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    (H : C(K × X,Y)) (a : Z → K) (b : C(Z,X)) (z₀ : Z) (k₀ : K)
    (h : ∀ k,H (k,b z₀) = H (k₀,b z₀)) :
    ContinuousAt (fun z ↦ H (a z,b z)) z₀ := continuousAt_compact_eval_of_constant H a b z₀ k₀ h
example (d : unitInterval) : acceleratedTime 0 d = 0 := acceleratedTime_zero d
example (t d : unitInterval) (h : d ≠ 0) : acceleratedTime (t*d) d = t := acceleratedTime_mul t d h
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (H : C(unitInterval × X,Y)) (d : C(X,unitInterval))
    (h : ∀ x,d x = 0 → ∀ t,H (t,x) = H (0,x)) (t : unitInterval) (x : X) :
    acceleratedHomotopy H d h (t*d x,x) = H (t,x) := acceleratedHomotopy_mul H d h t x
example {E B X : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
    {p : C(E,B)} (hp : HomotopyLiftingProperty p) (a : C(X,E)) (H : C(unitInterval × X,B))
    (h₀ : ∀ x,H (0,x) = p (a x)) (d : C(X,unitInterval))
    (h : ∀ x,d x = 0 → ∀ t,H (t,x) = p (a x)) :
    ∃ L : C(unitInterval × X,E),(∀ x,L (0,x) = a x) ∧
      (∀ t x,p (L (t,x)) = H (t,x)) ∧ ∀ x,d x = 0 → ∀ t,L (t,x) = a x :=
  hp.lift_fixed_zero a H h₀ d h
example {E B X : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
    {p : C(E,B)} (hp : HomotopyLiftingProperty p) (a : C(X,E)) (b : C(X,B))
    (H : (p.comp a).Homotopy b) (d : C(X,unitInterval))
    (h : ∀ x,d x = 0 → ∀ t,H (t,x) = p (a x)) :
    ∃ c : C(X,E),p.comp c = b ∧ (∀ x,d x = 0 → c x = a x) ∧
      ∃ K : a.Homotopy c,(∀ t x,p (K (t,x)) = H (t,x)) ∧
        ∀ x,d x = 0 → ∀ t,K (t,x) = a x := hp.correct_over_fixed_zero a b H d h
example : backtrackTime 0 = 1 ∧ backtrackTime 1 = 1 := ⟨backtrackTime_zero,backtrackTime_one⟩
example {X E B : Type u} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace B]
    (q : C(E,B)) {a b c : C(X,E)} (H : a.Homotopy b) (K : a.Homotopy c)
    (hq : HomotopyLiftingProperty q) (hsame : ∀ t x,q (H (t,x)) = q (K (t,x)))
    (d : C(X,unitInterval)) (hH : ∀ x,d x = 0 → ∀ t,H (t,x) = a x)
    (hK : ∀ x,d x = 0 → ∀ t,K (t,x) = a x) :
    ∃ V : b.Homotopy c,HomotopyOver (q.comp b) q V ∧
      (∀ x,d x = 0 → ∀ t,V (t,x) = a x) ∧
      ∃ S : (H.symm.trans K).toContinuousMap.Homotopy V.toContinuousMap,
        (∀ r t x,q (S (r,(t,x))) = q (H (unitInterval.symm
          (unitInterval.symm r * unitInterval.symm (backtrackTime t)),x))) ∧
        (∀ r x,S (r,(0,x)) = b x) ∧ (∀ r x,S (r,(1,x)) = c x) ∧
        ∀ x,d x = 0 → ∀ r t,S (r,(t,x)) = a x :=
  HomotopyLiftingProperty.parallel_lifts_with_coherence q H K hq hsame d hH hK
example (n : ℕ) (x : CubicalTests.cube.{u} n) :
    CubicalTests.boundaryDuration n x = 0 ↔ x.down ∈ Cube.boundary (Fin n) :=
  CubicalTests.boundaryDuration_eq_zero_iff n x
example (x : CubicalTests.cube.{u} 0) : CubicalTests.boundaryDuration 0 x = 1 :=
  CubicalTests.boundaryDuration_zero_dim x
example (n : ℕ) (x : CubicalTests.boundary.{u} n) : CubicalTests.boundaryDuration n x.val = 0 :=
  CubicalTests.boundaryDuration_boundary n x
example {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
    (n : ℕ) (a : C(CubicalTests.boundary.{u} n,E)) (b : C(CubicalTests.cube.{u} n,F))
    (w : f.comp a = b.comp (CubicalTests.boundaryInclusion n).hom) :
    ∃ c : C(CubicalTests.cube.{u} n,E),c.comp (CubicalTests.boundaryInclusion n).hom = a ∧
      p.comp c = q.comp b ∧ ∃ V : (f.comp c).Homotopy b,HomotopyOver (q.comp b) q V ∧
        ∀ t x,V (t,(x : CubicalTests.boundary.{u} n).val) = f (a x) :=
  strictHELP_over_cube_of_fiberHELP p q f sq hp hq hf n a b w

example {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
    (a : C(CubicalTests.boundary.{u} 0,E)) (b : C(CubicalTests.cube.{u} 0,F))
    (w : f.comp a = b.comp (CubicalTests.boundaryInclusion 0).hom) :
    ∃ c : C(CubicalTests.cube.{u} 0,E),c.comp (CubicalTests.boundaryInclusion 0).hom = a ∧
      p.comp c = q.comp b ∧ ∃ V : (f.comp c).Homotopy b,HomotopyOver (q.comp b) q V ∧
        ∀ t x,V (t,(x : CubicalTests.boundary.{u} 0).val) = f (a x) :=
  strictHELP_over_cube_of_fiberHELP p q f sq hp hq hf 0 a b w
