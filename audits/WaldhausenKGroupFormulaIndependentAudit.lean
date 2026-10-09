import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Additivity.GroupFormula
import Quillen.Waldhausen.GilletWaldhausen.TruncationCofibrationSequence

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Waldhausen.Product.Functoriality,
    `Quillen.Waldhausen.Additivity.GroupMultiplication,
    `Quillen.Waldhausen.Additivity.GroupFormula]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    seen := seen.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 32 do throwError "Expected frozen count32, found {count}"
  unless seen.size == 3 do throwError "Missing defining module"
  logInfo m!"Audited all {count} origins of the three literal K-group formula modules."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen Quillen.Waldhausen.Additivity
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D] (V : Structure C) (W : Structure D)

example (a b : W.K 0) : a * b = b * a := K_mul_comm W 0 a b
example (n : ℕ) : (KCommGroup W n).toGroup = inferInstanceAs (Group (W.K n)) := rfl
example : CommGroup (W.K 0) := KCommGroup W 0

variable [HasBinaryCoproducts D] {F G H : C ⥤ D}
example (hH : IsExact V.cof V.weq W.cof W.weq H)
    (hF : IsExact V.cof V.weq W.cof W.weq F) (x : V.K 0) :
    KMap (sumFunctor_isExact V W hH hF) 0 x = KMap hH 0 x * KMap hF 0 x :=
  KMap_sum_apply V W hH hF 0 x
example (a : F ⟶ G) (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)
    (n : ℕ) (x : V.K n) : KMap hs.exactG n x = KMap hs.exactF n x * KMap hs.exactH n x :=
  KMap_additivity_mul V W a b hs n x
example (a : F ⟶ G) (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)
    (x : V.K 0) : KMap hs.exactG 0 x = KMap hs.exactF 0 x * KMap hs.exactH 0 x :=
  KMap_additivity_mul V W a b hs 0 x

namespace ActualTruncation
open Quillen Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  [(abelianExactStructure A).IsExtensionClosed P]

example (n : ℤ) (k : ℕ) (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k) :
    let V := ofExactCategory (boundedAcyclicExactStructure P)
    letI := hasBinaryCoproducts V
    let hs := boundedAcyclicTruncation_isCofibrationSequence P n
    KMap hs.exactG k x = KMap hs.exactF k x * KMap hs.exactH k x := by
  let V := ofExactCategory (boundedAcyclicExactStructure P)
  let := hasBinaryCoproducts V
  exact KMap_additivity_mul V V (boundedAcyclicTruncationInclusion P n)
    (boundedAcyclicTruncationProjection P n) (boundedAcyclicTruncation_isCofibrationSequence P n) k x

end ActualTruncation
