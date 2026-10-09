import Lean.Util.CollectAxioms
import Quillen.Waldhausen.ExtensionCategory.ProductKEquivalence

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Waldhausen.Product.SSet,
    `Quillen.Waldhausen.Product.KEquivalence,
    `Quillen.Waldhausen.ExtensionCategory.ProductKEquivalence]
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
  unless count == 40 do throwError "Expected frozen count40, found {count}"
  unless seen.size == 3 do throwError "Missing defining module"
  logInfo m!"Audited all {count} origins of the three actual product K-equivalence modules."

noncomputable section
open CategoryTheory MonoidalCategory Quillen Quillen.Waldhausen Quillen.Waldhausen.ExtensionCategory
open scoped Simplicial Topology
universe u v

section Product
variable {C D : Type u} [Category.{v} C] [Category.{v} D] (V : Structure C) (W : Structure D)
example : sSet (productStructure V W).cof (productStructure V W).weq ≅
    sSet V.cof V.weq ⊗ sSet W.cof W.weq := Product.sSetIso V W
example : Product.deloopingComparison V W (productStructure V W).kBasepoint =
    (V.kBasepoint, W.kBasepoint) := Product.deloopingComparison_basepoint V W
example (n : ℕ) : (productStructure V W).K n ≃* V.K n × W.K n := Product.KEquiv V W n
example (n : ℕ) : (Product.KEquiv V W n).toMonoidHom =
    (KMap (fst_exact V W) n).prod (KMap (snd_exact V W) n) := rfl
example : (Product.KEquiv V W 0).toMonoidHom =
    (KMap (fst_exact V W) 0).prod (KMap (snd_exact V W) 0) := rfl
end Product

section Extension
variable {C : Type u} [Category.{u} C] (W : Structure C)
example (n : ℕ) : (waldhausenStructure W).K n ≃* W.K n × W.K n := productKEquiv W n
example (n : ℕ) : (productKEquiv W n).toMonoidHom =
    (KMap (source_exact W) n).prod (KMap (cofiber_exact W) n) := productKEquiv_toMonoidHom W n
example : (productKEquiv W 0).toMonoidHom =
    (KMap (source_exact W) 0).prod (KMap (cofiber_exact W) 0) := productKEquiv_toMonoidHom W 0
end Extension
