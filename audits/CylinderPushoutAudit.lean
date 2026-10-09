import Quillen.Waldhausen.Cylinder.Pushout
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.CategoryTheory.Limits.BiproductPushout,
    `Quillen.Waldhausen.Cylinder.Pushout]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless wanted.contains env.header.moduleNames[index.toNat]! do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 16 do throwError "Expected 16 cylinder-pushout origins, found {count}"
  logInfo m!"Audited all {count} cylinder pushout origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open Quillen Quillen.Waldhausen.SplitFactorization
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

example {K L M N : CochainComplex A ℤ} {f : K ⟶ L} {g : K ⟶ M} {i : L ⟶ N} {j : M ⟶ N}
    (h : IsPushout f g i j) : IsPushout (identityConeFunctor.map f) (identityConeFunctor.map g)
      (identityConeFunctor.map i) (identityConeFunctor.map j) := identityConeFunctor_map_isPushout h

-- No component monomorphism, cofibration or weak-equivalence input is required.
example {K L M N : Arrow (CochainComplex A ℤ)} {f : K ⟶ L} {g : K ⟶ M}
    {i : L ⟶ N} {j : M ⟶ N}
    (hL : IsPushout f.left g.left i.left j.left)
    (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout (middleFunctor.map f) (middleFunctor.map g)
      (middleFunctor.map i) (middleFunctor.map j) := middleFunctor_map_isPushout hL hR

example (K : CochainComplex A ℤ) (n : ℤ) :
    (identityConeTermIso K n).hom =
      biprod.lift ((mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl)
        ((mappingCone.snd (𝟙 K)).v n n (add_zero n)) := rfl

example {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (identityConeTermIso K n).hom ≫ biprod.map (f.f (n + 1)) (f.f n) =
      (identityConeFunctor.map f).f n ≫ (identityConeTermIso L n).hom :=
  identityConeTermIso_naturality f n
