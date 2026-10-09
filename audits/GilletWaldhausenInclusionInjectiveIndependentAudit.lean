import Quillen.Waldhausen.GilletWaldhausen.FiniteCycleInclusion
import Quillen.Waldhausen.GilletWaldhausen.AcyclicInclusionInjective
import Quillen.Topology.FilteredRealization.BasedGroups
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsBasedStrata
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsKCoverage
import Quillen.Waldhausen.GilletWaldhausen.BoundedAcyclicBasedStrata
import Quillen.Waldhausen.GilletWaldhausen.BoundedAcyclicKCoverage
import Quillen.Scheme.VectorBundle.KernelClosure
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.GilletWaldhausen.FiniteCycleInclusion, `Quillen.Waldhausen.GilletWaldhausen.AcyclicInclusionInjective]
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
  unless count == 12 do throwError "Expected 12 inclusion2 origins, got {count}"
  logInfo m!"Audited all {count} inclusion-injectivity declaration origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.GilletWaldhausen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
section OriginalSquares
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example (X : (boundedAcyclic P).FullSubcategory) : ((boundedAcyclicTermsInclusion P).obj X).obj = X.obj := rfl
example {X Y : (boundedAcyclic P).FullSubcategory} (f : X ⟶ Y) : ((boundedAcyclicTermsInclusion P).map f).hom = f.hom := rfl
example (a b : ℤ) (X : (fixedAcyclicBounds P a b).FullSubcategory) : ((finiteAcyclicTermsInclusion P a b).obj X).obj.obj = X.obj.obj := rfl
example (a b : ℤ) {X Y : (fixedAcyclicBounds P a b).FullSubcategory} (f : X ⟶ Y) : ((finiteAcyclicTermsInclusion P a b).map f).hom.hom = f.hom.hom := rfl
-- The original squares themselves do not require kernel closure.
example (a b : ℤ) (k : ℕ) (x : (ofExactCategory (fixedAcyclicExactStructure P a b)).K k) :
    KMap (fixedTermsInclusionExactFunctor P a b).waldhausenExact k
      (KMap (finiteAcyclicTermsExactInclusion P a b).waldhausenExact k x) =
    KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k
      (KMap (fixedAcyclicInclusionExactFunctor P a b).waldhausenExact k x) :=
  finiteAcyclicTermsInclusion_KMap_square P a b k x
example {N M : ℕ} (h : N ≤ M) (k : ℕ) (x : (ofExactCategory (boundedStratumExactStructure P N)).K k) :
    KMap (finiteAcyclicTermsExactInclusion P (-(M : ℤ)) M).waldhausenExact k
      (KMap (boundedStratumTransitionExact P h).waldhausenExact k x) =
    KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k
      (KMap (finiteAcyclicTermsExactInclusion P (-(N : ℤ)) N).waldhausenExact k x) :=
  finiteAcyclicTermsInclusion_KMap_transition P h k x
variable [(abelianExactStructure A).IsKernelClosed P]
example (a : ℤ) (m k : ℕ) (x : (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k)
    (hx : KMap (finiteAcyclicTermsExactInclusion P a (a + (m : ℤ))).waldhausenExact k x = 1) : x = 1 :=
  finiteCycleInclusion_KMap_eq_one P a m k x hx
example (a b : ℤ) (k : ℕ) : Function.Injective (KMap (finiteAcyclicTermsExactInclusion P a b).waldhausenExact k) :=
  finiteAcyclicTermsInclusion_KMap_injective P a b k
example (a : ℤ) (k : ℕ) : Function.Injective (KMap (finiteAcyclicTermsExactInclusion P a (a-1)).waldhausenExact k) :=
  finiteAcyclicTermsInclusion_KMap_injective P a (a-1) k
example (k : ℕ) (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k)
    (hx : KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k x = 1) : x = 1 :=
  boundedAcyclicTermsInclusion_KMap_eq_one P k x hx
example (k : ℕ) : Function.Injective (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k) :=
  boundedAcyclicTermsInclusion_KMap_injective P k
example : Function.Injective (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact 0) :=
  boundedAcyclicTermsInclusion_KMap_injective P 0
example (k : ℕ) {x y : (ofExactCategory (boundedAcyclicExactStructure P)).K k}
    (h : KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k x = KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k y) : x = y :=
  boundedAcyclicTermsInclusion_KMap_injective P k h
example {X Y : (boundedAcyclic P).FullSubcategory} (f : X ⟶ Y) :
    (ofExactCategory (boundedAcyclicExactStructure P)).weq f ↔ IsIso f := Iff.rfl
end OriginalSquares
-- Arbitrary schemes use the proved actual finite-locally-free kernel closure.
example (X : AlgebraicGeometry.Scheme.{u}) (k : ℕ) :
    Function.Injective (KMap (boundedAcyclicTermsExactInclusion (SchemeSheaf.finiteLocallyFree X)).waldhausenExact k) :=
  boundedAcyclicTermsInclusion_KMap_injective.{u,u+1} (SchemeSheaf.finiteLocallyFree X) k
example (X : AlgebraicGeometry.Scheme.{u}) :
    Function.Injective (KMap (boundedAcyclicTermsExactInclusion (SchemeSheaf.finiteLocallyFree X)).waldhausenExact 0) :=
  boundedAcyclicTermsInclusion_KMap_injective.{u,u+1} (SchemeSheaf.finiteLocallyFree X) 0
