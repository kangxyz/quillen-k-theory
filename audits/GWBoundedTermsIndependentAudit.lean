import Quillen.Waldhausen.Cylinder.AmbientRelative
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsAcyclic
import Quillen.PerfectComplexes.Strict
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origins := #[`Quillen.Waldhausen.GilletWaldhausen.BoundedTerms,
    `Quillen.Waldhausen.GilletWaldhausen.BoundedTermsAcyclic]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origins.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 27 do throwError "Expected frozen 27-origin scope; got {count}"
  logInfo m!"Audited all {count} bounded-terms declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.GilletWaldhausen
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts
universe u v
section BoundedTerms
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

-- Shifts do not require any closure assumptions on the term predicate.
example {K : CochainComplex A ℤ} (hK : boundedTerms P K) (s : ℤ) :
    boundedTerms P (K⟦s⟧) := boundedTerms_shift P hK s
example {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    ((boundedAcyclicTermsInclusion P).map f).hom = f.hom := rfl

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

-- Neither kernel closure nor projectivity is an input to this ambient category.
example : ExactStructure (boundedTerms P).FullSubcategory := boundedTermsExactStructure P
example {K L : CochainComplex A ℤ} (hK : boundedTerms P K) (hL : boundedTerms P L)
    (f : K ⟶ L) : boundedTerms P (CochainComplex.mappingCone f) :=
  boundedTerms_mappingCone P hK hL f
example : ExactFunctor (boundedAcyclicExactStructure P) (boundedTermsExactStructure P) :=
  boundedAcyclicTermsExactInclusion P
example {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    (boundedTermsExactStructure P).inflation ((boundedAcyclicTermsInclusion P).map f) ↔
      (boundedAcyclicExactStructure P).inflation f :=
  boundedAcyclicTermsInclusion_inflation_iff P f
example : IsExact
    (complexSubcategory (boundedAcyclic P)).cof (complexSubcategory (boundedAcyclic P)).weq
    (complexSubcategory (boundedTerms P)).cof (complexSubcategory (boundedTerms P)).weq
    (boundedAcyclicTermsInclusion P) := boundedAcyclicTermsInclusion_quasiExact P
example {Z K : (boundedTerms P).FullSubcategory} (hZ : IsZero Z) (f : Z ⟶ K) :
    (complexSubcategory (boundedTerms P)).weq f ↔ K.obj.Acyclic :=
  boundedTerms_weq_from_zero_iff P hZ f
example (K : (boundedTerms P).FullSubcategory) :
    (complexSubcategory (boundedTerms P)).weq
      ((complexSubcategory (boundedTerms P)).isZero.to_ K) ↔ boundedAcyclic P K.obj :=
  boundedTerms_weaklyAcyclic_iff P K
-- The proved generic cone/shift closure supplies the actual inherited cylinder endpoints.
example (f : Arrow (boundedTerms P).FullSubcategory) :
    (complexSubcategory (boundedTerms P)).cof
      (SplitFactorization.subcategoryJointInclusion (boundedTerms P)
        (boundedTerms_mappingCone P) f) :=
  (SplitFactorization.subcategoryJointInclusion_cof (boundedTerms P)
    (boundedTerms_mappingCone P) (fun _ hK ↦ boundedTerms_shift P hK 1) f).1
end BoundedTerms

-- On an arbitrary scheme, the generic ambient objects are exactly the
-- already accepted actual strict-perfect complexes, by definition.
example (X : AlgebraicGeometry.Scheme.{u}) :
    boundedTerms (SchemeSheaf.finiteLocallyFree X) = PerfectComplexes.strictPerfect X := rfl

section AdditionalMinimalClosure
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)
  [(abelianExactStructure A).IsExtensionClosed P]
example {S : ShortComplex (CochainComplex A ℤ)} (hS : S.ShortExact)
    (h₁ : boundedTerms P S.X₁) (h₃ : boundedTerms P S.X₃) : boundedTerms P S.X₂ :=
  boundedTerms_of_shortExact P hS h₁ h₃
variable [P.IsClosedUnderIsomorphisms]
example {K L : CochainComplex A ℤ} (hK : boundedTerms P K) (hL : boundedTerms P L)
    (f : K ⟶ L) : boundedTerms P (CochainComplex.mappingCone f) :=
  boundedTerms_mappingCone P hK hL f
end AdditionalMinimalClosure

section AdditionalActualInclusion
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)
example (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicTermsInclusion P).obj K).obj = K.obj := rfl
example : boundedAcyclicTermsInclusion P ⋙ (boundedTerms P).ι = (boundedAcyclic P).ι := rfl
variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    (complexSubcategory (boundedTerms P)).cof ((boundedAcyclicTermsInclusion P).map f) ↔
      (complexSubcategory (boundedAcyclic P)).cof f :=
  boundedAcyclicTermsInclusion_inflation_iff P f
example {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    (complexSubcategory (boundedTerms P)).weq ((boundedAcyclicTermsInclusion P).map f) ↔
      (complexSubcategory (boundedAcyclic P)).weq f := Iff.rfl
end AdditionalActualInclusion
