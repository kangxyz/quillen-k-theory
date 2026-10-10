/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.PathSubdivision.GlobalComparison

/-!
# Path subdivision regression tests

Check genuine free path pools, tails at moving parameters, whole-slab covers,
and complete original boundary fixing through finite subdivision.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
open Quillen Quillen.PathSubdivision Quillen.CubicalTests Quillen.CubicalSubdivision
universe u
section MovingTails
variable {A D E X B : Type u} [TopologicalSpace A] [TopologicalSpace D]
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace B]
  (p : C(E, B)) (f : C(X, B)) (H : C(unitInterval × D, B)) (k : C(D, X))
  (hEnd : ∀ d, H (1, d) = f (k d))

-- The input parameter may vary through the whole homotopy; the output uses its CURRENT value.
example (s : unitInterval) (Q : C(unitInterval × A, HomotopyPullback p (slice H s)))
    (r : unitInterval) (x : A) :
    (appendToPullback p f H k hEnd s (Q (r, x))).val.1 = k (Q (r, x)).val.1 := rfl

-- The remaining tail likewise uses the current parameter at EVERY homotopy time.
example (s : unitInterval) (Q : C(unitInterval × A, HomotopyPullback p (slice H s)))
    (r : unitInterval) (x : A) :
    (appendToPullback p f H k hEnd s (Q (r, x))).val.2.2 =
      ((⟨(Q (r, x)).val.2.2, (Q (r, x)).property.1, (Q (r, x)).property.2⟩ :
          Path (p (Q (r, x)).val.2.1) (H (s, (Q (r, x)).val.1))).trans
        (familyPath H s 1 (Q (r, x)).val.1)).toContinuousMap := rfl

-- Removing a subdivision needs no monotone ordering of its three time endpoints.
example (r : unitInterval) :
    timeJoinHomotopy 1 0 1 (r, 0) = 1 ∧ timeJoinHomotopy 1 0 1 (r, 1) = 1 :=
  ⟨timeJoinHomotopy_source 1 0 1 r, timeJoinHomotopy_target 1 0 1 r⟩

-- Mesh m=0 is one complete closed time interval, not an empty iteration.
example (r : unitInterval) : intervalCell 0 ⟨0, by omega⟩ r = r := by
  apply Subtype.ext
  simp [intervalCell]

-- Direct step consumer: the whole original outer-boundary point remains fixed.
example (n : ℕ) (a : C(boundary.{u} n, D)) (e : C(boundary.{u} n, E))
    (he : ∀ z, p (e z) = H (1, a z)) (hfixed : ∀ t z, H (t, a z) = H (1, a z))
    (m : ℕ) (i : Fin (m + 1)) (U V : Set B)
    (hc : ∀ d, slabMap H m i d ∈ pathSet U ∨ slabMap H m i d ∈ pathSet V)
    (hw : IsWeakHomotopyEquivalence (twoPoolComparison p (slabMap H m i) U V hc))
    (c : C(cube.{u} n, Stage p H (intervalCell m i 0)))
    (h₀ : c.comp (boundaryInclusion n).hom =
      boundaryStage p H n a e he hfixed (intervalCell m i 0)) :
    ∃ c' : C(cube.{u} n, Stage p H (intervalCell m i 1)),
      c'.comp (boundaryInclusion n).hom = boundaryStage p H n a e he hfixed (intervalCell m i 1) ∧
      ∃ K : ((stageToPullback p f H k hEnd (intervalCell m i 1)).comp c').Homotopy
        ((stageToPullback p f H k hEnd (intervalCell m i 0)).comp c),
        (∀ r z, (K (r, z.val)).val.1 = k (a z)) ∧
        (∀ r z, (K (r, z.val)).val.2.1 = e z) ∧
        (∀ r z t, (K (r, z.val)).val.2.2 t = H (1, a z)) := by
  obtain ⟨c', hc', ⟨K⟩⟩ :=
    exists_finite_slab_step p H n a e he hfixed f k hEnd m i U V hc hw c h₀
  have hK (r : unitInterval) (z : boundary.{u} n) :
      K (r, z.val) = stageToPullback p f H k hEnd (intervalCell m i 1)
        (boundaryStage p H n a e he hfixed (intervalCell m i 1) z) := by
    exact (K.prop r z.val ⟨z, rfl⟩).trans
      (congrArg (stageToPullback p f H k hEnd (intervalCell m i 1))
        (ContinuousMap.congr_fun hc' z))
  refine ⟨c', hc', K.toHomotopy, ?_, ?_, ?_⟩
  · intro r z
    exact congrArg (fun q : HomotopyPullback p f ↦ q.val.1) (hK r z)
  · intro r z
    exact congrArg (fun q : HomotopyPullback p f ↦ q.val.2.1) (hK r z)
  · intro r z t
    exact (congrArg (fun q : HomotopyPullback p f ↦ q.val.2.2 t) (hK r z)).trans
      (hfixed _ z)

-- Both the empty outer boundary n=0 and the one-slab mesh m=0 are actually admissible.
example (a : C(boundary.{u} 0, D)) (e : C(boundary.{u} 0, E))
    (he : ∀ z, p (e z) = H (1, a z)) (hfixed : ∀ t z, H (t, a z) = H (1, a z))
    (U V : Set B)
    (hc : ∀ (i : Fin 1) d, slabMap H 0 i d ∈ pathSet U ∨ slabMap H 0 i d ∈ pathSet V)
    (hw : ∀ i : Fin 1, IsWeakHomotopyEquivalence (twoPoolComparison p (slabMap H 0 i) U V (hc i)))
    (c₀ : C(cube.{u} 0, Stage p H 0))
    (h₀ : c₀.comp (boundaryInclusion 0).hom = boundaryStage p H 0 a e he hfixed 0) :
    ∃ c₁ : C(cube.{u} 0, Stage p H 1),
      c₁.comp (boundaryInclusion 0).hom = boundaryStage p H 0 a e he hfixed 1 ∧
      Nonempty (((stageToPullback p f H k hEnd 1).comp c₁).HomotopyRel
        ((stageToPullback p f H k hEnd 0).comp c₀) (Set.range (boundaryInclusion 0))) :=
  exists_finite_time_lift p H 0 a e he hfixed f k hEnd 0 U V hc hw c₀ h₀

variable (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
  (hp : TwoChartPoolComparison p U V)

-- Full HELP retains an arbitrary originally prescribed boundary homotopy, not just constant paths.
example (n : ℕ) (a : C(boundary.{u} n, {z : X × E // p z.2 = f z.1}))
    (b : C(cube.{u} n, HomotopyPullback p f))
    (J : ((HomotopyPullback.strictPullbackInclusion p f).comp a).Homotopy
      (b.comp (boundaryInclusion n).hom)) :
    ∃ c : C(cube.{u} n, {z : X × E // p z.2 = f z.1}),
      c.comp (boundaryInclusion n).hom = a ∧
      ∃ K : ((HomotopyPullback.strictPullbackInclusion p f).comp c).Homotopy b,
        ∀ t z, K (t, z.val) = J (t, z) :=
  (strictPullbackInclusion_finiteCubeStrictHELP_of_pools p f U V hU hV hc hp).full n a b J

example (z : HomotopyPullback p f) :
    ∃ y : {y : X × E // p y.2 = f y.1},
      Joined (HomotopyPullback.strictPullbackInclusion p f y) z :=
  (strictPullbackInclusion_isWeakHomotopyEquivalence_of_pools p f U V hU hV hc
    hp).component_surjective z

example (z : {z : X × E // p z.2 = f z.1}) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (HomotopyPullback.strictPullbackInclusion p f) (x := z) rfl) :=
  (strictPullbackInclusion_isWeakHomotopyEquivalence_of_pools p f U V hU hV hc
    hp).homotopy_bijective z n

example (z : {z : X × E // p z.2 = f z.1}) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (HomotopyPullback.strictPullbackInclusion p f) (x := z) rfl) :=
  (strictPullbackInclusion_isWeakHomotopyEquivalence_of_pools p f U V hU hV hc
    hp).homotopy_bijective z 0

example [IsEmpty {z : X × E // p z.2 = f z.1}] : IsEmpty (HomotopyPullback p f) :=
  (strictPullbackInclusion_isWeakHomotopyEquivalence_of_pools p f U V hU hV hc hp).isEmpty_target

-- Local compact HLP is a sufficient route to the result; no global HLP is smuggled in.
example (hpU : CompactHomotopyLiftingProperty (restriction p U))
    (hpV : CompactHomotopyLiftingProperty (restriction p V))
    (hpUV : CompactHomotopyLiftingProperty (restriction p (U ∩ V))) :
    UniversalStrictPullbackComparison p :=
  universalStrictPullbackComparison_of_two_open p U V hU hV hc
    hpU.universalStrictPullbackComparison hpV.universalStrictPullbackComparison
    hpUV.universalStrictPullbackComparison

end MovingTails

section Pools
variable {D E B : Type u} [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (γ : C(D, C(unitInterval, B))) (U V : Set B)

example (d : D) (e : E) (η : C(unitInterval, B))
    (h0 : η 0 = p e) (h1 : η 1 = γ d 1)
    (hγ : ∀ t, γ d t ∈ U) (hη : ∀ t, η t ∈ U) :
    ∃ z : TwoPool p γ U V,
      z.val.val.1 = d ∧ z.val.val.2.1 = e ∧ z.val.val.2.2 = η :=
  ⟨⟨⟨(d, e, η), h0, h1⟩, Or.inl ⟨hγ, hη⟩⟩, rfl, rfl, rfl⟩

example (hc : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V)
    (z : TwoPool p γ U V) (hz : ∃ t, z.val.val.2.2 t ≠ z.val.val.2.2 1) :
    ∀ y : StrictPool p γ, twoPoolComparison p γ U V hc y ≠ z := by
  intro y heq
  obtain ⟨t, ht⟩ := hz
  apply ht
  rw [← heq]
  rfl

example (z : HomotopyPullback p (PathSubdivision.endpoint γ)) (t : unitInterval)
    (h : z.val.2.2 t ∉ U) : z ∉ chartSet p γ U := fun hz ↦ h (hz.2 t)

example (z : HomotopyPullback p (PathSubdivision.endpoint γ)) (t : unitInterval)
    (h : γ z.val.1 t ∉ U) : z ∉ chartSet p γ U := fun hz ↦ h (hz.1 t)

example (z : chartSet p γ U) :
    ((chartTargetHomeomorph p γ U).symm (chartTargetHomeomorph p γ U z)).val.val.2.2 =
      z.val.val.2.2 :=
  congrArg (fun z : chartSet p γ U ↦ z.val.val.2.2)
    ((chartTargetHomeomorph p γ U).symm_apply_apply z)

example (hc : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V)
    (z : {z : D × E // p z.2 = γ z.1 0}) (t : unitInterval) :
    ((twoPoolForget p γ U V).comp (twoPoolEntrance p γ U V hc) z).val.2.2 t =
      γ z.val.1 t := rfl

example : IsEmpty (ChartParameter γ ∅) := ⟨fun d ↦ d.property 0⟩
end Pools

section Slabs
variable {D B : Type u} [TopologicalSpace D] [TopologicalSpace B]

-- Whole-slab loci are open without compactness of the parameter space or its chart locus.
example (H : C(unitInterval × D, B)) (U : Set B) (hU : IsOpen U)
    (m : ℕ) (i : Fin (m + 1)) :
    IsOpen {d : D | ∀ t, H (intervalCell m i t, d) ∈ U} :=
  slabSet_isOpen H hU m i

-- A single time mesh gives genuine open covers even for a zero-dimensional cube family.
example (H : C(unitInterval × Quillen.CubicalSubdivision.Cube 0, B))
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hc : ∀ t d, H (t, d) ∈ U ∪ V) :
    ∃ m : ℕ, ∀ i : Fin (m + 1),
      IsOpen (slabSet H U m i) ∧ IsOpen (slabSet H V m i) ∧
      slabSet H U m i ∪ slabSet H V m i = Set.univ := by
  obtain ⟨m, hm⟩ := exists_uniform_two_slab_cover 0 H U V hU hV hc
  exact ⟨m, fun i ↦ ⟨slabSet_isOpen H hU m i, slabSet_isOpen H hV m i, hm i⟩⟩
end Slabs
