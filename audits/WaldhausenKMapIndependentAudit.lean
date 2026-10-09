import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Functoriality.KMap
import Quillen.Waldhausen.GilletWaldhausen.FixedBounds

open Lean in
run_cmd do
  let env ← getEnv
  let wanted := `Quillen.Waldhausen.Functoriality.KMap
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == wanted do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 22 do throwError "Expected 22 K-map origins, found {count}"
  logInfo m!"Audited all {count} K-map functoriality origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
universe u v
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {V : Structure C} {W : Structure D} {U : Structure E}
  {F G : C ⥤ D} {J : D ⥤ E}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hJ : IsExact W.cof W.weq U.cof U.weq J)

example (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X)) (n : ℕ) : KMap hF n = KMap hG n :=
  KMap_eq_of_weakNatTrans hF hG η hη n
example (n : ℕ) : KMap (hF.comp hJ) n = (KMap hJ n).comp (KMap hF n) := KMap_comp hF hJ n
example : KMap (IsExact.id V.cof V.weq) 0 = MonoidHom.id (V.K 0) := KMap_id V 0
example (n : ℕ) : KMap (zeroFunctor_isExact V W) n = 1 := KMap_zeroFunctor V W n
example (h0 : F.obj V.zero = W.zero) (n : ℕ) :
    KMap hF n = piMap n (deloopingMap hF).hom (deloopingMap_basepoint_of_zeroEq hF h0) :=
  KMap_eq_piMap_of_zeroEq hF h0 n

namespace ActualFixedBounds
open GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  [(abelianExactStructure A).IsExtensionClosed P]

example (a b n : ℤ) (hn : b ≤ n) (k : ℕ) :
    KMap (fixedAcyclicTruncLEExactFunctor P a b n).waldhausenExact k =
      KMap (fixedAcyclicInclusionExactFunctor P a b).waldhausenExact k :=
  KMap_eq_of_iso _ _ (fixedBoundsTruncLEIdentityIso P a b n hn) k

example (a b n : ℤ) (hn : n < a) (k : ℕ) :
    KMap (fixedAcyclicTruncLEExactFunctor P a b n).waldhausenExact k = 1 := by
  let V := ofExactCategory (fixedAcyclicExactStructure P a b)
  let W := ofExactCategory (boundedAcyclicExactStructure P)
  exact (KMap_eq_of_iso (fixedAcyclicTruncLEExactFunctor P a b n).waldhausenExact
    (zeroFunctor_isExact V W) (fixedBoundsTruncLEZeroIso P a b n hn) k).trans
      (KMap_zeroFunctor V W k)

end ActualFixedBounds
