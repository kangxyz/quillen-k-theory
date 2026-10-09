import Quillen.Topology.HELP.ContractibleTestFullOverBase
import Quillen.Topology.HomotopyLifting.CubeOverBase
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HomotopyLifting.FiberwiseExtension,
    `Quillen.Topology.HomotopyLifting.FiberwiseBoundaryCorrection,
    `Quillen.Topology.HELP.ContractibleTestFullOverBase]
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
  unless seen.size == 3 do throwError "Missing full-over-base origin"
  unless count == 7 do throwError "Expected 7 full-over-base origins, found {count}"
  logInfo m!"Audited all {count} full-over-base origins."
noncomputable section
open CategoryTheory Quillen
open scoped Topology unitInterval
universe u

section
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
example
    {q : C(E,B)} (hq : HomotopyLiftingProperty q)
    (A D : TopCat.{u}) (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (b : C(D,E)) (H : C(unitInterval × A,E))
    (h₀ : ∀ a,H (0,a) = b (i a))
    (hbase : ∀ t a,q (H (t,a)) = q (b (i a))) :
    ∃ T : C(unitInterval × D,E),
      (∀ x,T (0,x) = b x) ∧ (∀ t a,T (t,i a) = H (t,a)) ∧
      ∀ t x,q (T (t,x)) = q (b x) :=
  HomotopyLiftingProperty.extend_over_fixed_base hq A D i hi duration hzero b H h₀ hbase

end

section
variable {A D : TopCat.{u}} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
example
    (q : C(E,B)) (hq : HomotopyLiftingProperty q)
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (base : C(D,B)) {f g : C(D,E)} (K : f.Homotopy g)
    (hK : HomotopyOver base q K)
    (L : (f.comp i.hom).Homotopy (g.comp i.hom))
    (Q : (K.compContinuousMap i.hom).toContinuousMap.HomotopyRel L.toContinuousMap
      {z : unitInterval × A | z.1 = 0 ∨ z.1 = 1})
    (hQ : ∀ s t a,q (Q (s,(t,a))) = base (i a)) :
    ∃ K' : f.Homotopy g,HomotopyOver base q K' ∧ ∀ t a,K' (t,i a) = L (t,a) :=
  correct_boundary_over_fixed_base q hq i hi duration hzero base K hK L Q hQ

example
    (q : C(E,B)) (hq : HomotopyLiftingProperty q)
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (base : C(D,B)) {f g : C(D,E)} (K : f.Homotopy g) (hK : HomotopyOver base q K)
    (L : (f.comp i.hom).Homotopy (g.comp i.hom))
    (hL : ∀ t a,q (L (t,a)) = base (i a))
    (hKL : ∀ t a,K (t,i a) = Path.delayReflLeft 0 (L.evalAt a) t) :
    ∃ K' : f.Homotopy g,HomotopyOver base q K' ∧ ∀ t a,K' (t,i a) = L (t,a) :=
  unpad_boundary_over_fixed_base q hq i hi duration hzero base K hK L hL hKL

end

section
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
example
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B,CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b))
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (a : C(A,E)) (b : C(D,F)) (H : (f.comp a).Homotopy (b.comp i.hom))
    (hH : ∀ t x,q (H (t,x)) = q (b (i x))) :
    ∃ c : C(D,E),c.comp i.hom = a ∧ p.comp c = q.comp b ∧
      ∃ V : (f.comp c).Homotopy b,
        HomotopyOver (q.comp b) q V ∧ ∀ t x,V (t,i x) = H (t,x) :=
  fullHELP_over_contracted_test p q f sq hp hq hf A D i hi d₀ HD duration hzero a b H hH

end

section
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
example (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
    (n : ℕ) (a : C(CubicalTests.boundary.{u} n,E)) (b : C(CubicalTests.cube.{u} n,F))
    (H : (f.comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion n).hom))
    (hH : ∀ t x,q (H (t,x)) = q (b x.val)) :
    ∃ c : C(CubicalTests.cube.{u} n,E),
      (∀ x,c x.val = a x) ∧ (∀ x,p (c x) = q (b x)) ∧
      ∃ V : (f.comp c).Homotopy b,
        (∀ t x,q (V (t,x)) = q (b x)) ∧ (∀ t x,V (t,x.val) = H (t,x)) := by
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  have hz : ∀ x,CubicalTests.boundaryDuration n x = 0 ↔
      x ∈ Set.range (CubicalTests.boundaryInclusion.{u} n) := by
    intro x
    rw [CubicalTests.boundaryDuration_eq_zero_iff]
    exact ⟨fun hx ↦ ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ ↦ hy ▸ y.property⟩
  obtain ⟨c,hc,hb,V,hV,hA⟩ := fullHELP_over_contracted_test p q f sq hp hq hf _ _
    (CubicalTests.boundaryInclusion n) (CubicalTests.boundaryInclusion_hep n)
    (CubicalTests.zero n) (CubicalTests.contraction n) (CubicalTests.boundaryDuration n) hz a b H hH
  exact ⟨c,ContinuousMap.congr_fun hc,ContinuousMap.congr_fun hb,V,hV,hA⟩
end
