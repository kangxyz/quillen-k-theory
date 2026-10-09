import Quillen.Library
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

-- The literal mapping-path space stores the entire given boundary track.
example {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (a : C(A,E)) (b : C(D,F)) (H : (f.comp a).Homotopy (b.comp i.hom))
    (hH : ∀ t x,q (H (t,x)) = q (b (i x))) :
    ∃ L : C(D,MappingPath f),
      (MappingPath.endpoint f).comp L = b ∧
      ((MappingPath.source f).comp L).comp i.hom = a ∧
      (∀ x,p (L x).val.1 = q (b x)) ∧
      (∀ t x,q ((L x).val.2 t) = q (b x)) ∧
      ∀ t x,(L (i x)).val.2 t = H (t,x) := by
  obtain ⟨c,hc,hbase,V,hV,hboundary⟩ :=
    fullHELP_over_contracted_test p q f sq hp hq hf A D i hi d₀ HD duration hzero a b H hH
  let L : C(D,MappingPath f) := {
    toFun x := ⟨(c x,⟨fun t ↦ V (t,x),by fun_prop⟩),V.map_zero_left x⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk c.continuous
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact V.continuous.comp continuous_swap }
  refine ⟨L,?_,hc,ContinuousMap.congr_fun hbase,hV,hboundary⟩
  ext x
  exact V.map_one_left x

-- No positive-dimensional assumption: this specializes for every n, including zero.
example {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
    (n : ℕ) (a : C(CubicalTests.boundary.{u} n,E)) (b : C(CubicalTests.cube.{u} n,F))
    (H : (f.comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion n).hom))
    (hH : ∀ t x,q (H (t,x)) = q (b x.val)) :
    ∃ c : C(CubicalTests.cube.{u} n,E),c.comp (CubicalTests.boundaryInclusion n).hom = a ∧
      p.comp c = q.comp b ∧ ∃ V : (f.comp c).Homotopy b,
        (∀ t x,q (V (t,x)) = q (b x)) ∧ ∀ t x,V (t,x.val) = H (t,x) := by
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  apply fullHELP_over_contracted_test p q f sq hp hq hf _ _
    (CubicalTests.boundaryInclusion n) (CubicalTests.boundaryInclusion_hep n)
    (CubicalTests.zero n) (CubicalTests.contraction n) (CubicalTests.boundaryDuration n) _ a b H hH
  intro x
  rw [CubicalTests.boundaryDuration_eq_zero_iff]
  constructor
  · exact fun hx ↦ ⟨⟨x,hx⟩,rfl⟩
  · rintro ⟨y,rfl⟩
    exact y.property

-- Zero-dimensional boundary is genuinely empty, so no boundary-verticality premise is needed.
example {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
    (a : C(CubicalTests.boundary.{u} 0,E)) (b : C(CubicalTests.cube.{u} 0,F))
    (H : (f.comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion 0).hom)) :
    ∃ c : C(CubicalTests.cube.{u} 0,E),c.comp (CubicalTests.boundaryInclusion 0).hom = a ∧
      p.comp c = q.comp b ∧ ∃ V : (f.comp c).Homotopy b,
        (∀ t x,q (V (t,x)) = q (b x)) ∧ ∀ t x,V (t,x.val) = H (t,x) := by
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} 0).space :=
    (CubicalTests.boundaryPresentation 0).compact
  let : CompactSpace (CubicalTests.boundary.{u} 0) :=
    (CubicalTests.boundaryPresentationHomeomorph 0).compactSpace
  apply fullHELP_over_contracted_test p q f sq hp hq hf _ _
    (CubicalTests.boundaryInclusion 0) (CubicalTests.boundaryInclusion_hep 0)
    (CubicalTests.zero 0) (CubicalTests.contraction 0) (CubicalTests.boundaryDuration 0) _ a b H (by
      intro t x
      have hx := CubicalTests.boundaryDuration_boundary 0 x
      rw [CubicalTests.boundaryDuration_zero_dim] at hx
      exact False.elim (one_ne_zero hx))
  intro x
  rw [CubicalTests.boundaryDuration_eq_zero_iff]
  constructor
  · exact fun hx ↦ ⟨⟨x,hx⟩,rfl⟩
  · rintro ⟨y,rfl⟩
    exact y.property

example {A D : TopCat.{u}} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (q : C(E,B)) (hq : HomotopyLiftingProperty q)
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (base : C(D,B)) {f g : C(D,E)} (K : f.Homotopy g)
    (hK : HomotopyOver base q K)
    (L : (f.comp i.hom).Homotopy (g.comp i.hom))
    (Q : (K.compContinuousMap i.hom).toContinuousMap.HomotopyRel L.toContinuousMap
      {z : unitInterval × A | z.1 = 0 ∨ z.1 = 1})
    (hQ : ∀ s t a,q (Q (s,(t,a))) = base (i a)) :
    ∃ K' : f.Homotopy g,(∀ x,K' (0,x) = f x) ∧ (∀ x,K' (1,x) = g x) ∧
      (∀ t x,q (K' (t,x)) = base x) ∧ ∀ t a,K' (t,i a) = L (t,a) := by
  obtain ⟨K',hbase,hboundary⟩ :=
    correct_boundary_over_fixed_base q hq i hi duration hzero base K hK L Q hQ
  exact ⟨K',K'.map_zero_left,K'.map_one_left,hbase,hboundary⟩

example {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b,CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (a : C(A,E)) (b : C(D,F)) (H : (f.comp a).Homotopy (b.comp i.hom))
    (hH : ∀ t x,q (H (t,x)) = q (b (i x))) :
    ∃ c : C(D,E),(∀ x,c (i x) = a x) ∧ (∀ x,p (c x) = q (b x)) ∧
      ∃ V : (f.comp c).Homotopy b,
        (∀ x,V (0,x) = f (c x)) ∧ (∀ x,V (1,x) = b x) ∧
        (∀ t x,q (V (t,x)) = q (b x)) ∧ ∀ t x,V (t,i x) = H (t,x) := by
  obtain ⟨c,hc,hbase,V,hV,hboundary⟩ :=
    fullHELP_over_contracted_test p q f sq hp hq hf A D i hi d₀ HD duration hzero a b H hH
  exact ⟨c,ContinuousMap.congr_fun hc,ContinuousMap.congr_fun hbase,V,
    V.map_zero_left,V.map_one_left,hV,hboundary⟩
