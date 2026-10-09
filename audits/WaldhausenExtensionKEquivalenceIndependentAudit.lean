import Lean.Util.CollectAxioms
import Quillen.Waldhausen.ExtensionCategory.KEquivalence

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Waldhausen.Functoriality.KEquivalence,
    `Quillen.Waldhausen.ExtensionCategory.KEquivalence]
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
  unless count == 15 do throwError "Expected 15 canonical K-equivalence origins, found {count}"
  unless seen.size == 2 do throwError "Missing defining module"
  logInfo m!"Audited all {count} origins of the two canonical K-equivalence modules."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.ExtensionCategory
open scoped Topology
universe u v

section Generic
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (e : ContinuousMap.HomotopyEquiv V.Delooping W.Delooping)
  (he : e.toFun = (deloopingMap hF).hom)
example (n : ℕ) : (KEquivOfRealization hF e he n).toMonoidHom = KMap hF n := rfl
example (n : ℕ) : Function.Bijective (KMap hF n) :=
  KMap_bijective_of_realizationHomotopyEquiv hF e he n
end Generic

section ActualExtension
variable {C : Type u} [Category.{u} C] (W : Structure C)
example (n : ℕ) : (waldhausenStructure W).K n ≃* (productStructure W W).K n := KEquiv W n
example (n : ℕ) : (KEquiv W n).toMonoidHom = KMap (sourceCofiber_exact W) n := rfl
example (n : ℕ) : (KEquiv W n).symm.toMonoidHom = splitKMap W n := KEquiv_symm_toMonoidHom W n
example : (KEquiv W 0).toMonoidHom = KMap (sourceCofiber_exact W) 0 := rfl
end ActualExtension
