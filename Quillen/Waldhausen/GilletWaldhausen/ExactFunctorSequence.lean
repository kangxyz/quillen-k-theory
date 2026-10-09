import Quillen.Waldhausen.Additivity.CofibrationSequence
import Quillen.Waldhausen.ExactFunctor
import Quillen.Waldhausen.QuillenComparison.PullbackQuotients

/-!
# Actual conflation sequences of exact functors are cofibration sequences

The relative-cofibration axiom is derived from exactness of the quotient
functor. The genuine relative pushout fits in a conflation with the same
kernel as the target; its comparison is the pullback of an admissible
inclusion along an admissible epimorphism. No additivity conclusion occurs
among the hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
universe v u v' u'

namespace Quillen.Waldhausen.GilletWaldhausen

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The actual relative pushout comparison of two conflations is admissible
whenever the map on their actual quotients is admissible. -/
theorem relativePushout_inflation (E : ExactStructure C)
    {S T : ShortComplex C} (φ : S ⟶ T) (hS : E.conflation S)
    (hT : E.conflation T) (hφ : E.inflation φ.τ₃)
    [HasPushout S.f φ.τ₁] :
    E.inflation (pushout.desc φ.τ₂ T.f φ.comm₁₂.symm) := by
  let q := pushout.desc (f := S.f) (g := φ.τ₁) φ.τ₂ T.f φ.comm₁₂.symm
  let U := ExactStructure.pushoutConflation T.X₁ φ.τ₁ (S := S)
  have hU : E.conflation U := E.pushoutConflation_mem hS φ.τ₁
  have hiq : U.f ≫ q = T.f := by simp [U, q, ExactStructure.pushoutConflation]
  have hpq : U.g ≫ φ.τ₃ = q ≫ T.g := by
    apply pushout.hom_ext
    · simp only [U, ExactStructure.pushoutConflation, q, pushout.inl_desc_assoc]
      exact φ.comm₂₃.symm
    · simp [U, ExactStructure.pushoutConflation, q, T.zero]
  have sq := E.isPullback_of_conflations_same_kernel hU hT q φ.τ₃ hiq hpq
  obtain ⟨Q, p, w, hQ⟩ := hφ
  exact E.inflation_of_conflation
    (QuillenComparison.pullback_conflation_same_quotient E sq w hQ
      (E.deflation_of_conflation hT))

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
variable (E : ExactStructure C) (E' : ExactStructure D)
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H) (w : a ≫ b = 0)
variable (hc : ∀ X, E'.conflation
  (ShortComplex.mk (a.app X) (b.app X) (NatTrans.congr_app w X)))

/-- The pointwise actual conflations, without modifying their arrows. -/
def exactFunctorSequenceAt (X : C) : ShortComplex D :=
  ShortComplex.mk (a.app X) (b.app X) (NatTrans.congr_app w X)

/-- The actual map of pointwise conflations induced by a source morphism. -/
def exactFunctorSequenceMap {X Y : C} (f : X ⟶ Y) :
    exactFunctorSequenceAt a b w X ⟶ exactFunctorSequenceAt a b w Y where
  τ₁ := F.map f
  τ₂ := G.map f
  τ₃ := H.map f
  comm₁₂ := a.naturality f
  comm₂₃ := b.naturality f

include hc in
/-- Quotient exactness forces the genuine relative-cofibration condition. -/
theorem exactFunctorSequence_cofibration
    (hH : ∀ {X Y : C} (f : X ⟶ Y), E.inflation f → E'.inflation (H.map f)) :
    Additivity.IsCofibrationTransformation (ofExactCategory E') a (ofExactCategory E) where
  app_cof X := E'.inflation_of_conflation (hc X)
  relative_cof {X Y} f hf := by
    let : HasPushout (exactFunctorSequenceAt a b w X).f
        (exactFunctorSequenceMap a b w f).τ₁ := Additivity.hasPushout (ofExactCategory E') a
      (fun X ↦ E'.inflation_of_conflation (hc X)) f
    exact relativePushout_inflation E' (exactFunctorSequenceMap a b w f)
      (hc X) (hc Y) (hH f hf)

include w hc in
/-- A pointwise conflation sequence of genuine exact functors satisfies
all structural hypotheses of Waldhausen additivity. -/
theorem exactFunctorSequence_isCofibrationSequence
    (EF : ExactFunctor E E') (EG : ExactFunctor E E') (EH : ExactFunctor E E')
    (hF : EF.toFunctor = F) (hG : EG.toFunctor = G) (hH : EH.toFunctor = H) :
    Additivity.IsCofibrationSequence (ofExactCategory E) (ofExactCategory E') a b where
  exactF := hF ▸ EF.waldhausenExact
  exactG := hG ▸ EG.waldhausenExact
  exactH := hH ▸ EH.waldhausenExact
  cofibration := exactFunctorSequence_cofibration E E' a b w hc (by
    intro X Y f hf
    rw [← hH]
    exact EH.map_inflation f hf)
  cofiber X := QuillenComparison.isPushoutOfZeroCokernel _ (E'.cokernel _ (hc X))
    (ofExactCategory E').isZero _ _

end Quillen.Waldhausen.GilletWaldhausen
