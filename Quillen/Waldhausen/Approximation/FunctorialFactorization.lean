import Quillen.Waldhausen.SplitComplexes.FactorizationQuotient

/-!
# Functoriality of the actual complex factorization

The contractible identity-cone construction is functorial, as is the
factorization object on the arrow category. Its inclusion, target section,
and projection are natural. The projection is always a quasi-isomorphism,
and a square with quasi-isomorphic target map induces a quasi-isomorphism
of factorization objects. This is not yet the complete cylinder-functor
contract: joint-endpoint/relative cofibrations and zero normalization are
separate obligations.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

universe v u

namespace Quillen.Waldhausen.SplitFactorization

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Functorial identity cones. -/
def identityConeFunctor : CochainComplex A ℤ ⥤ CochainComplex A ℤ where
  obj K := mappingCone (𝟙 K)
  map f := mappingCone.map _ _ f f (by simp)
  map_id K := mappingCone.map_id _
  map_comp f g := by
    ext n
    simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map]

/-- The actual factorization object depends functorially on the input arrow. -/
def middleFunctor : Arrow (CochainComplex A ℤ) ⥤ CochainComplex A ℤ where
  obj f := middle f.hom
  map α := biprod.map (identityConeFunctor.map α.left) α.right
  map_id f := by
    apply biprod.hom_ext
    · simp
      exact Category.comp_id _
    · simp
  map_comp α β := by
    apply biprod.hom_ext <;> simp

/-- Naturality of the first factor, for actual commutative squares. -/
theorem inclusion_naturality {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g) :
    inclusion f.hom ≫ middleFunctor.map α = α.left ≫ inclusion g.hom := by
  apply biprod.hom_ext
  · ext n
    simp [inclusion, middleFunctor, identityConeFunctor, mappingCone.map]
  · simpa [inclusion, middleFunctor] using α.w

/-- Naturality of the target section. -/
theorem section_naturality {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g) :
    (biprod.inr : f.right ⟶ middle f.hom) ≫ middleFunctor.map α =
      α.right ≫ (biprod.inr : g.right ⟶ middle g.hom) := by
  simp [middleFunctor]

/-- Naturality of the second factor. -/
theorem projection_naturality {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g) :
    middleFunctor.map α ≫ projection g.hom = projection f.hom ≫ α.right := by
  simp [middleFunctor, projection]

/-- The first factor as a natural transformation on the arrow category. -/
def inclusionNat : Arrow.leftFunc ⟶ middleFunctor (A := A) where
  app f := inclusion f.hom
  naturality _ _ α := (inclusion_naturality α).symm

/-- The target section as a natural transformation on the arrow category. -/
def sectionNat : Arrow.rightFunc ⟶ middleFunctor (A := A) where
  app _ := biprod.inr
  naturality _ _ α := (section_naturality α).symm

/-- The second factor as a natural transformation on the arrow category. -/
def projectionNat : middleFunctor (A := A) ⟶ Arrow.rightFunc where
  app f := projection f.hom
  naturality _ _ α := projection_naturality α

/-- The functorial factorization satisfies its cylinder-axiom projection
condition, separately from the other cylinder-functor conditions. -/
theorem projectionNat_quasiIso (f : Arrow (CochainComplex A ℤ)) :
    QuasiIso (projectionNat.app f) := projection_quasiIso f.hom

/-- A quasi-isomorphism on the targets of a commutative square suffices for
a quasi-isomorphism on the factorization objects. -/
theorem middleFunctor_map_quasiIso {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g)
    [QuasiIso α.right] : QuasiIso (middleFunctor.map α) := by
  have h : QuasiIso (middleFunctor.map α ≫ projection g.hom) := by
    rw [projection_naturality]
    infer_instance
  exact (quasiIso_iff_comp_right _ (projection g.hom)).1 h

end Quillen.Waldhausen.SplitFactorization
