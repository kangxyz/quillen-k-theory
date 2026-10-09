import Quillen.Waldhausen.Cylinder.AmbientRelative
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == `Quillen.Waldhausen.Cylinder.AmbientRelative do
      continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 4 do
    throwError "Expected 4 ambient relative-cylinder origins, found {count}"
  logInfo m!"Audited all {count} ambient relative-cylinder declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g)
  {R : CochainComplex A ℤ} {i : middle f.hom ⟶ R} {j : g.left ⊞ g.right ⟶ R}
  (h : IsPushout (jointInclusion f.hom) (biprod.map α.left α.right) i j)
  (k : R ⟶ middle g.hom) (hi : i ≫ k = middleFunctor.map α)
  (hj : j ≫ k = jointInclusion g.hom)

-- In particular, neither splitting nor a monic target map is assumed.
example [Mono α.left] : Mono k := relative_jointInclusion_mono α h k hi hj
example [Mono α.left] : (relativeQuotientSequence α h k hi hj).ShortExact :=
  relativeQuotientSequence_shortExact_of_mono α h k hi hj

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
  {f' g' : Arrow P.FullSubcategory} (β : f' ⟶ g') {T : P.FullSubcategory}
  (i' : (subcategoryMiddleFunctor P hcone).obj f' ⟶ T)
  (j' : subcategoryJointSource P g' ⟶ T)
  (h' : IsPushout (jointInclusion f'.hom.hom) (biprod.map β.left.hom β.right.hom) i'.hom j'.hom)
  (k' : T ⟶ (subcategoryMiddleFunctor P hcone).obj g')
  (hi' : i' ≫ k' = (subcategoryMiddleFunctor P hcone).map β)
  (hj' : j' ≫ k' = subcategoryJointInclusion P hcone g')

-- The conclusion retains the original ordinary inherited cofibration class.
example (hβ : (complexSubcategory P).cof β.left) : (complexSubcategory P).cof k' :=
  subcategoryRelativeJoint_ambient_cof P hcone hshift β i' j' h' k' hi' hj' hβ
