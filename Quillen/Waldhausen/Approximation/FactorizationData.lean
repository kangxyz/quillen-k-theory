import Quillen.Waldhausen.Approximation.Properties
import Quillen.Waldhausen.Approximation.FunctorialFactorization

/-!
# Constructed functorial cofibration factorizations

This packages genuine functorial factorizations, not an approximation
conclusion. The structure is instantiated from the proved identity-cone
construction for cone-closed complex subcategories. It will be used to
replace finite filtrations coherently on objects and natural transformations.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u

namespace Quillen.Waldhausen

/-- A coherent cofibration/weak-equivalence factorization of every morphism. -/
structure FunctorialFactorization {C : Type u} [Category.{v} C] (W : Structure C) where
  middle : Arrow C ⥤ C
  inclusion : Arrow.leftFunc ⟶ middle
  projection : middle ⟶ Arrow.rightFunc
  factorization (f : Arrow C) : inclusion.app f ≫ projection.app f = f.hom
  cofibration (f : Arrow C) : W.cof (inclusion.app f)
  weak (f : Arrow C) : W.weq (projection.app f)

attribute [reassoc (attr := simp)] FunctorialFactorization.factorization

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The actual functorial factorization on all complexes with split cofibrations. -/
def splitComplexesFunctorialFactorization : FunctorialFactorization (splitComplexes A) where
  middle := SplitFactorization.middleFunctor
  inclusion := SplitFactorization.inclusionNat
  projection := SplitFactorization.projectionNat
  factorization f := SplitFactorization.inclusion_projection f.hom
  cofibration f := SplitFactorization.inclusion_degreewiseSplitMono f.hom
  weak f := SplitFactorization.projection_quasiIso f.hom

attribute [local instance] Abelian.hasFiniteBiproducts

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

/-- The explicit middle-object functor, restricted to the actual full subcategory. -/
def subcategoryMiddleFunctor : Arrow P.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P.ι.mapArrow ⋙ SplitFactorization.middleFunctor)
    (fun f ↦ SplitFactorization.middle_property P hcone f.left.property f.right.property f.hom.hom)

/-- The actual functorial factorization stays in the cone-closed full subcategory. -/
def splitSubcategoryFunctorialFactorization : FunctorialFactorization (splitComplexSubcategory P) where
  middle := subcategoryMiddleFunctor P hcone
  inclusion := {
    app f := P.homMk (SplitFactorization.inclusion f.hom.hom)
    naturality _ _ α := ObjectProperty.hom_ext _
      (SplitFactorization.inclusion_naturality (P.ι.mapArrow.map α)).symm }
  projection := {
    app f := P.homMk (SplitFactorization.projection f.hom.hom)
    naturality _ _ α := ObjectProperty.hom_ext _
      (SplitFactorization.projection_naturality (P.ι.mapArrow.map α)) }
  factorization f := ObjectProperty.hom_ext _ (SplitFactorization.inclusion_projection f.hom.hom)
  cofibration f := by
    apply (splitSubcategoryCofibrations_iff P _).2
    exact ⟨mappingCone (-f.hom.hom), hcone f.left.property f.right.property (-f.hom.hom),
      SplitFactorization.quotientMap f.hom.hom,
      SplitFactorization.inclusion_quotientMap f.hom.hom,
      fun n ↦ ⟨SplitFactorization.quotientSequenceSplitting f.hom.hom n⟩⟩
  weak f := SplitFactorization.projection_quasiIso f.hom.hom

end Quillen.Waldhausen
