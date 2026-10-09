import Quillen.Waldhausen.Fibration.ComplexExtension
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Algebra.Homology.QuasiIsoExtension,
    `Quillen.Waldhausen.Fibration.ComplexExtension]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless wanted.contains env.header.moduleNames[index.toNat]! do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {env.header.moduleNames[index.toNat]!}: {name}: {← collectAxioms name}"
  unless count == 9 do throwError "Expected 9 concrete extension origins, found {count}"
  logInfo m!"Audited all {count} concrete quasi-isomorphism extension origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

example {S T : ShortComplex (CochainComplex A ℤ)} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := quasiIso_middle_of_shortExact φ hS hT h₁ h₃

example : ExtensionAxiom (complexes A) := complexes_extensionAxiom
example (X : ExtensionCategory.Obj (complexes A)) :
    Acyclic (complexes A) ((ExtensionCategory.cofiber (complexes A)).obj X) ↔
      (complexes A).weq X.obj.hom := cofiber_acyclic_iff _ complexes_extensionAxiom X

attribute [local instance] Abelian.hasFiniteBiproducts
variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

-- No extension-axiom, cone closure, shift closure or kernel closure is supplied.
example : ExtensionAxiom (complexSubcategory P) := complexSubcategory_extensionAxiom P
example (X : ExtensionCategory.Obj (complexSubcategory P)) :
    Acyclic (complexSubcategory P) ((ExtensionCategory.cofiber (complexSubcategory P)).obj X) ↔
      (complexSubcategory P).weq X.obj.hom :=
  cofiber_acyclic_iff _ (complexSubcategory_extensionAxiom P) X

-- The displayed quotient object and projection themselves form a categorical cokernel.
example {C : Type u} [Category.{v} C] [Abelian C] {X Y Q Z : C}
    {i : X ⟶ Y} {z : X ⟶ Z} {q : Y ⟶ Q} {t : Z ⟶ Q}
    (h : IsPushout i z q t) (hZ : IsZero Z) :
    IsColimit (CokernelCofork.ofπ q (cofiber_comp_zero h hZ)) :=
  cofiberIsCokernel h hZ
example {C : Type u} [Category.{v} C] [Abelian C] {X Y Q Z : C}
    {i : X ⟶ Y} {z : X ⟶ Z} {q : Y ⟶ Q} {t : Z ⟶ Q}
    (h : IsPushout i z q t) (hZ : IsZero Z) [Mono i] :
    (ShortComplex.mk i q (cofiber_comp_zero h hZ)).ShortExact :=
  cofiber_shortExact h hZ
