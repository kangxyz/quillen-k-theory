import Quillen.Scheme.Coherent.ClosedImmersion.GeneralReflection

/-!
# The actual closed essential image is the ideal-annihilated subcategory

Annihilation is tested on genuine affine quotient presentations of the
base-changed closed immersion. The equivalence with the actual direct-image
essential image follows from the canonical adjunction-unit base-change square.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme.ClosedImmersion.General
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- Annihilation by the actual closed defining ideal on all affine charts.
The ideals here occur in genuine quotient presentations of the actual
base-changed closed immersion, rather than being chosen unrelated ideals. -/
def annihilatedByClosedIdeal : ObjectProperty (Coherent X) := fun M ↦
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (a : Spec R ⟶ X) [IsOpenImmersion a]
    (I : Ideal R) (e : pullback i a ≅ Spec (Ideal.closedRing R I)),
    pullback.snd i a = e.hom ≫ Ideal.closedMap R I →
      Ideal.coherentKilledBy R I ((coherentRestriction a).obj M)

/-- The proved global closed essential image is precisely genuine
annihilation by the defining ideal in every affine quotient chart. -/
theorem coherentKilled_iff_annihilatedByClosedIdeal (M : Coherent X) :
    coherentKilled i M ↔ annihilatedByClosedIdeal i M := by
  constructor
  · rintro ⟨N, ⟨d⟩⟩ R _ a _ I e hi
    apply (coherentPushforward_essImage_iff R (pullback.snd i a) I e hi _).mp
    exact ⟨(coherentRestriction (pullback.fst i a)).obj N,
      ⟨((coherentOpenBaseChange i a).app N).symm ≪≫ (coherentRestriction a).mapIso d⟩⟩
  · intro hM
    apply (coherentKilled_iff_unit_isIso i M).mpr
    have hk : IsZero (kernel ((coherentAdjunction i).unit.app M)) := by
      apply coherent_isZero_of_affineRestrictions
      intro R _ a _
      obtain ⟨I, e, hi⟩ :=
        (IsClosedImmersion.Spec_iff (f := pullback.snd i a)).mp inferInstance
      have hlocal : coherentKilled (pullback.snd i a) ((coherentRestriction a).obj M) :=
        (coherentPushforward_essImage_iff R (pullback.snd i a) I e hi _).mpr
          (hM R a I e hi)
      have : IsIso ((coherentAdjunction (pullback.snd i a)).unit.app
          ((coherentRestriction a).obj M)) :=
        (coherentKilled_iff_unit_isIso (pullback.snd i a) _).mp hlocal
      exact (isZero_kernel_of_mono _).of_iso (kernelUnitOpenBaseChange i a M)
    have : Mono ((coherentAdjunction i).unit.app M) := Preadditive.mono_of_isZero_kernel _ hk
    exact isIso_of_mono_of_epi _

/-- Equality of the actual closed-image and geometric annihilator properties. -/
theorem coherentKilled_eq_annihilatedByClosedIdeal :
    coherentKilled i = annihilatedByClosedIdeal i := by
  funext M
  exact propext (coherentKilled_iff_annihilatedByClosedIdeal i M)

instance annihilatedByClosedIdeal_isoClosed :
    (annihilatedByClosedIdeal i).IsClosedUnderIsomorphisms := by
  rw [← coherentKilled_eq_annihilatedByClosedIdeal]
  infer_instance

/-- Actual closed pushforward is an equivalence onto precisely the coherent
sheaves annihilated by its defining ideal, independently characterized on
genuine affine quotient charts. -/
def coherentAnnihilatorEquivalence :
    Coherent Z ≌ (annihilatedByClosedIdeal i).FullSubcategory :=
  (coherentPushforward i).toEssImage.asEquivalence |>.trans
    ((CategoryTheory.Equivalence.refl : Coherent X ≌ Coherent X).congrFullSubcategory
      (P := coherentKilled i) (Q := annihilatedByClosedIdeal i)
      (coherentKilled_eq_annihilatedByClosedIdeal i).symm)

/-- The equivalence onto ideal-annihilated objects retains actual i_*. -/
theorem coherentAnnihilatorEquivalence_comp_inclusion :
    (coherentAnnihilatorEquivalence i).functor ⋙ (annihilatedByClosedIdeal i).ι =
      coherentPushforward i := rfl

end Quillen.CoherentScheme.ClosedImmersion.General
