import Quillen.Topology.FilteredRealization.BasedGroups
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsBasedStrata
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsKCoverage
import Quillen.Waldhausen.GilletWaldhausen.BoundedAcyclicBasedStrata
import Quillen.Waldhausen.GilletWaldhausen.BoundedAcyclicKCoverage
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.FilteredRealization.BasedGroups, `Quillen.Waldhausen.GilletWaldhausen.BoundedTermsBasedStrata, `Quillen.Waldhausen.GilletWaldhausen.BoundedTermsKCoverage, `Quillen.Waldhausen.GilletWaldhausen.BoundedAcyclicBasedStrata, `Quillen.Waldhausen.GilletWaldhausen.BoundedAcyclicKCoverage]
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
  unless count == 70 do throwError "Expected 70 narrow coverage5 origins, got {count}"
  logInfo m!"Audited all {count} based-coverage declaration origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits Topology Quillen Quillen.Waldhausen
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
section Generic
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
  (x : ∀ j, |F.obj j|) (z : |c.pt|)
  (hx : ∀ {j k} (f : j ⟶ k), SSet.toTop.map (F.map f) (x j) = x k)
  (hz : ∀ j, SSet.toTop.map (c.ι.app j) (x j) = z)
example (n : ℕ) (a : HomotopyGroup.Pi n |c.pt| z) :
    ∃ j, ∃ b : HomotopyGroup.Pi n |F.obj j| (x j),
      homotopyGroupMap (SSet.toTop.map (c.ι.app j)).hom (hz j) b = a :=
  FilteredRealization.homotopyGroupMap_jointlySurjective F c hc x z hx hz n a
example (a : HomotopyGroup.Pi 0 |c.pt| z) :
    ∃ j, ∃ b : HomotopyGroup.Pi 0 |F.obj j| (x j),
      homotopyGroupMap (SSet.toTop.map (c.ι.app j)).hom (hz j) b = a :=
  FilteredRealization.homotopyGroupMap_jointlySurjective F c hc x z hx hz 0 a
example (j : J) (n : ℕ) (a b : HomotopyGroup.Pi n |F.obj j| (x j))
    (h : homotopyGroupMap (SSet.toTop.map (c.ι.app j)).hom (hz j) a = homotopyGroupMap (SSet.toTop.map (c.ι.app j)).hom (hz j) b) :
    ∃ k, ∃ f : j ⟶ k, homotopyGroupMap (SSet.toTop.map (F.map f)).hom (hx f) a = homotopyGroupMap (SSet.toTop.map (F.map f)).hom (hx f) b :=
  FilteredRealization.homotopyGroupMap_eq_eventually F c hc x z hx hz j n a b h
example (j : J) (n : ℕ) (a : HomotopyGroup.Pi (n+1) |F.obj j| (x j))
    (h : piMap n (SSet.toTop.map (c.ι.app j)).hom (hz j) a = 1) :
    ∃ k, ∃ f : j ⟶ k, piMap n (SSet.toTop.map (F.map f)).hom (hx f) a = 1 :=
  FilteredRealization.piMap_eq_one_eventually F c hc x z hx hz j n a h
end Generic
open Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example (N : ℕ) : (boundedTermsBasedStructure P N).zero.obj = (ofExactCategory (boundedTermsExactStructure P)).zero := rfl
example (N : ℕ) : (boundedTermsBasedStructure P N).weq = boundedTermsStratumWeak P (MorphismProperty.isomorphisms _) N := rfl
example (N : ℕ) : (boundedTermsBasedStructure P N).cof = (ofExactCategory (boundedTermsStratumExactStructure P N)).cof := rfl
example (N : ℕ) : (boundedTermsStratum P N).ι.obj (boundedTermsBasedStructure P N).zero = (ofExactCategory (boundedTermsExactStructure P)).zero := rfl
example {N M : ℕ} (h : N ≤ M) : (boundedTermsStratumTransition P h).obj (boundedTermsBasedStructure P N).zero = (boundedTermsBasedStructure P M).zero := rfl
example (N : ℕ) : IsExact (boundedTermsBasedStructure P N).cof (boundedTermsBasedStructure P N).weq (ofExactCategory (boundedTermsExactStructure P)).cof (ofExactCategory (boundedTermsExactStructure P)).weq (boundedTermsStratum P N).ι := boundedTermsBasedInclusionExact P N
example {N M : ℕ} (h : N ≤ M) : IsExact (boundedTermsBasedStructure P N).cof (boundedTermsBasedStructure P N).weq (boundedTermsBasedStructure P M).cof (boundedTermsBasedStructure P M).weq (boundedTermsStratumTransition P h) := boundedTermsBasedTransitionExact P h
example (N k : ℕ) (x : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k) :
    KMap (boundedTermsBasedToOriginalExact P N) k (KMap (boundedTermsOriginalToBasedExact P N) k x) = x := boundedTermsOriginalBased_KMap_inv P N k x
example (N k : ℕ) (x : (boundedTermsBasedStructure P N).K k) :
    KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k (KMap (boundedTermsBasedToOriginalExact P N) k x) = KMap (boundedTermsBasedInclusionExact P N) k x := boundedTermsBasedInclusion_KMap P N k x
example (k : ℕ) (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    ∃ N : ℕ, ∃ y : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k,
      KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y = x := boundedTerms_KMap_jointlySurjective P k x
example (N k : ℕ) (x y : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k)
    (he : KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x = KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y) :
    ∃ M : ℕ, ∃ h : N ≤ M, KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k x = KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k y := boundedTerms_KMap_eq_eventually P N k x y he
example (N k : ℕ) (x : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k)
    (he : KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x = 1) :
    ∃ M : ℕ, ∃ h : N ≤ M, KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k x = 1 := boundedTerms_KMap_eq_one_eventually P N k x he
example (N : ℕ) : (boundedAcyclicBasedStructure P N).zero.obj = (ofExactCategory (boundedAcyclicExactStructure P)).zero := rfl
example (N : ℕ) : (boundedAcyclicBasedStructure P N).weq = boundedStratumWeak P (MorphismProperty.isomorphisms _) N := rfl
example (N : ℕ) : (boundedAcyclicBasedStructure P N).cof = (ofExactCategory (boundedStratumExactStructure P N)).cof := rfl
example (N : ℕ) : (boundedStratum P N).ι.obj (boundedAcyclicBasedStructure P N).zero = (ofExactCategory (boundedAcyclicExactStructure P)).zero := rfl
example {N M : ℕ} (h : N ≤ M) : (boundedStratumTransition P h).obj (boundedAcyclicBasedStructure P N).zero = (boundedAcyclicBasedStructure P M).zero := rfl
example (N : ℕ) : IsExact (boundedAcyclicBasedStructure P N).cof (boundedAcyclicBasedStructure P N).weq (ofExactCategory (boundedAcyclicExactStructure P)).cof (ofExactCategory (boundedAcyclicExactStructure P)).weq (boundedStratum P N).ι := boundedAcyclicBasedInclusionExact P N
example {N M : ℕ} (h : N ≤ M) : IsExact (boundedAcyclicBasedStructure P N).cof (boundedAcyclicBasedStructure P N).weq (boundedAcyclicBasedStructure P M).cof (boundedAcyclicBasedStructure P M).weq (boundedStratumTransition P h) := boundedAcyclicBasedTransitionExact P h
example (N k : ℕ) (x : (ofExactCategory (boundedStratumExactStructure P N)).K k) :
    KMap (boundedAcyclicBasedToOriginalExact P N) k (KMap (boundedAcyclicOriginalToBasedExact P N) k x) = x := boundedAcyclicOriginalBased_KMap_inv P N k x
example (N k : ℕ) (x : (boundedAcyclicBasedStructure P N).K k) :
    KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k (KMap (boundedAcyclicBasedToOriginalExact P N) k x) = KMap (boundedAcyclicBasedInclusionExact P N) k x := boundedAcyclicBasedInclusion_KMap P N k x
example (k : ℕ) (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k) :
    ∃ N : ℕ, ∃ y : (ofExactCategory (boundedStratumExactStructure P N)).K k,
      KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y = x := boundedAcyclic_KMap_jointlySurjective P k x
example (N k : ℕ) (x y : (ofExactCategory (boundedStratumExactStructure P N)).K k)
    (he : KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x = KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y) :
    ∃ M : ℕ, ∃ h : N ≤ M, KMap (boundedStratumTransitionExact P h).waldhausenExact k x = KMap (boundedStratumTransitionExact P h).waldhausenExact k y := boundedAcyclic_KMap_eq_eventually P N k x y he
example (N k : ℕ) (x : (ofExactCategory (boundedStratumExactStructure P N)).K k)
    (he : KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x = 1) :
    ∃ M : ℕ, ∃ h : N ≤ M, KMap (boundedStratumTransitionExact P h).waldhausenExact k x = 1 := boundedAcyclic_KMap_eq_one_eventually P N k x he
example (N : ℕ) : SSet.toTop.map (boundedTermsStratumSSetInclusion P (MorphismProperty.isomorphisms _) N) (boundedTermsBasedStructure P N).kBasepoint = (ofExactCategory (boundedTermsExactStructure P)).kBasepoint := boundedTermsBasedInclusion_basepoint P N
example {N M : ℕ} (h : N ≤ M) : SSet.toTop.map (boundedTermsStratumSSetTransition P (MorphismProperty.isomorphisms _) h) (boundedTermsBasedStructure P N).kBasepoint = (boundedTermsBasedStructure P M).kBasepoint := boundedTermsBasedTransition_basepoint P h
example (N : ℕ) (x : (ofExactCategory (boundedTermsStratumExactStructure P N)).K 0)
    (he : KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact 0 x = 1) :
    ∃ M : ℕ, ∃ h : N ≤ M, KMap (boundedTermsStratumTransitionExact P h).waldhausenExact 0 x = 1 := boundedTerms_KMap_eq_one_eventually P N 0 x he
example (N : ℕ) : SSet.toTop.map (boundedStratumSSetInclusion P (MorphismProperty.isomorphisms _) N) (boundedAcyclicBasedStructure P N).kBasepoint = (ofExactCategory (boundedAcyclicExactStructure P)).kBasepoint := boundedAcyclicBasedInclusion_basepoint P N
example {N M : ℕ} (h : N ≤ M) : SSet.toTop.map (boundedStratumSSetTransition P (MorphismProperty.isomorphisms _) h) (boundedAcyclicBasedStructure P N).kBasepoint = (boundedAcyclicBasedStructure P M).kBasepoint := boundedAcyclicBasedTransition_basepoint P h
example (N : ℕ) (x : (ofExactCategory (boundedStratumExactStructure P N)).K 0)
    (he : KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact 0 x = 1) :
    ∃ M : ℕ, ∃ h : N ≤ M, KMap (boundedStratumTransitionExact P h).waldhausenExact 0 x = 1 := boundedAcyclic_KMap_eq_one_eventually P N 0 x he
