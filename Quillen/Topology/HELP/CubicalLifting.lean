/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HELP.CubeBoundary
public import Quillen.Topology.HELP.StrictCompact
public import Quillen.Topology.HomotopyGroups.WeakEquivalenceProperty

/-! # Original finite homotopy sets from compact contracted-test lifting

Actual cubical loop representatives are lifted with their complete boundaries.
Their homotopies use the actual compact pushout cylinder boundary. Dimension
zero and component surjectivity are proved, including empty-source cases.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
namespace Quillen
open TheoremA CubicalTests

/-- Strict HELP restricted to actual compact HEP pairs with displayed contracted
 target. This does not posit any homotopy-group or weak-equivalence conclusion. -/
def ContractedStrictHELP {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    (f : C(E, F)) : Prop :=
  ∀ (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D] (i : A ⟶ D),
    homotopyExtensionProperty i → ∀ (d : D)
    (_HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d))
    (a : C(A,E)) (b : C(D,F)), f.comp a = b.comp i.hom →
      ∃ c : C(D,E), c.comp i.hom = a ∧ Nonempty ((f.comp c).HomotopyRel b (Set.range i))

variable {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
  {f : C(E, F)}

/-- Ordinary full compact HELP supplies the restricted genuine lifting tests. -/
theorem CompactHomotopyExtensionLiftingProperty.contractedStrict
    (hf : CompactHomotopyExtensionLiftingProperty f) : ContractedStrictHELP f := by
  intro A D _ _ i hi _ _ a b w
  exact hf.strict A D i hi a b w

/-- The empty-boundary point test supplies actual component surjectivity,
without presuming that the source is nonempty. -/
theorem ContractedStrictHELP.component_surjective (hf : ContractedStrictHELP f) (y : F) :
    ∃ x : E, Joined (f x) y := by
  let A := TopCat.of PEmpty.{u+1}
  let i : A ⟶ cube.{u} 0 := TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩
  have hi : homotopyExtensionProperty i := by
    apply homotopyExtensionProperty_of_continuous
    intro Z b H _
    exact ⟨b.comp ContinuousMap.snd, fun _ ↦ rfl, fun _ a ↦ isEmptyElim a⟩
  let a : C(A,E) := ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let b := ContinuousMap.const (cube.{u} 0) y
  have w : f.comp a = b.comp i.hom := by ext z; exact isEmptyElim z
  obtain ⟨c, _, ⟨K⟩⟩ := hf A (cube 0) i hi (zero 0) (contraction 0) a b w
  exact ⟨c (zero 0), ⟨K.toHomotopy.evalAt (zero 0)⟩⟩

/-- Surjectivity on the actual original cubical homotopy-set maps in every
finite degree, with the original boundary and basepoint values retained. -/
theorem ContractedStrictHELP.homotopy_surjective (hf : ContractedStrictHELP f)
    (x : E) (n : ℕ) :
    Function.Surjective (homotopyGroupMap (N := Fin n) f (x := x) rfl) := by
  intro a
  induction a using Quotient.inductionOn with | h p =>
    let P := boundaryPresentation.{u} n
    let : CompactSpace P.space := P.compact
    let down : C(cube.{u} n, Fin n → unitInterval) := ⟨ULift.down, continuous_uliftDown⟩
    let up : C((Fin n → unitInterval), cube.{u} n) := ⟨ULift.up, continuous_uliftUp⟩
    let a := ContinuousMap.const P.space x
    let b := p.val.comp down
    have w : f.comp a = b.comp P.map.hom := by
      ext z
      exact (GenLoop.boundary p (P.map z).down (P.lands z)).symm
    obtain ⟨c, hc, ⟨K⟩⟩ := hf P.space (cube n) P.map P.hep (zero n) (contraction n) a b w
    let q : GenLoop (Fin n) E x := ⟨c.comp up, by
      intro z hz
      obtain ⟨a, ha⟩ := P.covers ⟨z⟩ hz
      change c ⟨z⟩ = x
      rw [← ha]
      exact ContinuousMap.congr_fun hc a⟩
    refine ⟨Quotient.mk' q, Quotient.sound ⟨{
      toHomotopy := {
        toFun z := K (z.1, ULift.up z.2)
        continuous_toFun := K.continuous.comp
          (continuous_fst.prodMk (continuous_uliftUp.comp continuous_snd))
        map_zero_left z := K.toHomotopy.map_zero_left (ULift.up z)
        map_one_left z := K.toHomotopy.map_one_left (ULift.up z) }
      prop' := ?_ }⟩⟩
    intro t z hz
    exact K.prop t (ULift.up z) (P.covers (ULift.up z) hz)

/-- Injectivity uses the actual pushout of the side cylinder and both endpoint
cubes. Its lift is the required original relative homotopy of loop representatives. -/
theorem ContractedStrictHELP.homotopy_injective (hf : ContractedStrictHELP f)
    (x : E) (n : ℕ) :
    Function.Injective (homotopyGroupMap (N := Fin n) f (x := x) rfl) := by
  intro a b hab
  induction a using Quotient.inductionOn with | h p =>
    induction b using Quotient.inductionOn with | h q =>
      obtain ⟨H⟩ := Quotient.exact hab
      let P := boundaryPresentation.{u} n
      let : CompactSpace P.space := P.compact
      let S : TopCat.of (P.space × unitInterval) ⟶ TopCat.of E :=
        TopCat.ofHom (ContinuousMap.const _ x)
      let caps : TopCat.of (cube.{u} n ⊕ cube.{u} n) ⟶ TopCat.of E :=
        TopCat.ofHom ⟨Sum.elim (fun z ↦ p z.down) (fun z ↦ q z.down),
          (p.val.continuous.comp continuous_uliftDown).sumElim
            (q.val.continuous.comp continuous_uliftDown)⟩
      have w : cylinderBoundaryEnds P.space ≫ S = cylinderBoundarySumMap P.map ≫ caps := by
        ext z
        rcases z with a | a
        · exact (GenLoop.boundary p (P.map a).down (P.lands a)).symm
        · exact (GenLoop.boundary q (P.map a).down (P.lands a)).symm
      let d : CylinderBoundary P.map ⟶ TopCat.of E := pushout.desc S caps w
      have hS : cylinderBoundarySide P.map ≫ d = S := pushout.inl_desc _ _ _
      have hcaps : cylinderBoundaryCaps P.map ≫ d = caps := pushout.inr_desc _ _ _
      let k : TopCat.of (cube.{u} n × unitInterval) ⟶ TopCat.of F :=
        TopCat.ofHom ⟨fun z ↦ H (z.2, z.1.down),
          H.continuous.comp (continuous_snd.prodMk (continuous_uliftDown.comp continuous_fst))⟩
      have hw : d ≫ TopCat.ofHom f = cylinderBoundaryMap P.map ≫ k := by
        apply (cylinderBoundary_isPushout P.map).hom_ext
        · rw [← Category.assoc, hS, ← Category.assoc, cylinderBoundarySide_map]
          ext ⟨a,t⟩
          exact ((H.eq_fst t (P.lands a)).trans
            (congrArg f (GenLoop.boundary p (P.map a).down (P.lands a)))).symm
        · rw [← Category.assoc, hcaps, ← Category.assoc, cylinderBoundaryCaps_map]
          ext z
          rcases z with z | z
          · exact (H.apply_zero z.down).symm
          · exact (H.apply_one z.down).symm
      let HD : (ContinuousMap.id (cube.{u} n × unitInterval)).Homotopy
          (ContinuousMap.const _ (zero n, (0 : unitInterval))) := {
        toFun z := (contraction n (z.1,z.2.1), unitInterval.symm z.1 * z.2.2)
        continuous_toFun := by fun_prop
        map_zero_left z := Prod.ext ((contraction n).map_zero_left z.1) (by simp)
        map_one_left z := Prod.ext ((contraction n).map_one_left z.1) (by simp) }
      obtain ⟨c, hc, _⟩ := hf (CylinderBoundary P.map) (TopCat.of (cube n × unitInterval))
        (cylinderBoundaryMap P.map) (homotopyExtensionProperty_cylinderBoundaryMap P.map P.hep)
        (zero n, 0) HD d.hom k.hom (congrArg TopCat.Hom.hom hw)
      have hside (a : P.space) (t : unitInterval) : c (P.map a, t) = x := by
        have he := ContinuousMap.congr_fun hc (cylinderBoundarySide P.map (a,t))
        have hs := ConcreteCategory.congr_hom (cylinderBoundarySide_map P.map) (a,t)
        have hd := ConcreteCategory.congr_hom hS (a,t)
        exact (congrArg c hs).symm.trans (he.trans hd)
      have hzero (z : cube.{u} n) : c (z,0) = p z.down := by
        have he := ContinuousMap.congr_fun hc (cylinderBoundaryCaps P.map (Sum.inl z))
        have hs := ConcreteCategory.congr_hom (cylinderBoundaryCaps_map P.map) (Sum.inl z)
        have hd := ConcreteCategory.congr_hom hcaps (Sum.inl z)
        exact (congrArg c hs).symm.trans (he.trans hd)
      have hone (z : cube.{u} n) : c (z,1) = q z.down := by
        have he := ContinuousMap.congr_fun hc (cylinderBoundaryCaps P.map (Sum.inr z))
        have hs := ConcreteCategory.congr_hom (cylinderBoundaryCaps_map P.map) (Sum.inr z)
        have hd := ConcreteCategory.congr_hom hcaps (Sum.inr z)
        exact (congrArg c hs).symm.trans (he.trans hd)
      apply Quotient.sound
      refine ⟨{
        toHomotopy := {
          toFun z := c (ULift.up z.2, z.1)
          continuous_toFun := c.continuous.comp
            ((continuous_uliftUp.comp continuous_snd).prodMk continuous_fst)
          map_zero_left z := hzero (ULift.up z)
          map_one_left z := hone (ULift.up z) }
        prop' := ?_ }⟩
      intro t z hz
      obtain ⟨a, ha⟩ := P.covers (ULift.up z) hz
      change c (ULift.up z,t) = p z
      rw [← ha]
      exact (hside a t).trans (GenLoop.boundary p z hz).symm

/-- Empty-aware weakness is a conclusion about the original continuous map,
including its actual zero-dimensional homotopy-set map. -/
theorem ContractedStrictHELP.isWeakHomotopyEquivalence (hf : ContractedStrictHELP f) :
    IsWeakHomotopyEquivalence f :=
  ⟨hf.component_surjective, fun x n ↦ ⟨hf.homotopy_injective x n, hf.homotopy_surjective x n⟩⟩

/-- In particular, full compact HELP gives complete original-map weakness. -/
theorem CompactHomotopyExtensionLiftingProperty.isWeakHomotopyEquivalence
    (hf : CompactHomotopyExtensionLiftingProperty f) : IsWeakHomotopyEquivalence f :=
  hf.contractedStrict.isWeakHomotopyEquivalence

end Quillen
