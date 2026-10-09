import Quillen.Localization.Serre.AuxiliaryArrowLift
import Quillen.Localization.Serre.AuxiliaryDiagram

/-! # Faithfulness and eventual equality of auxiliary object lifts -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.Q
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{u} C] [Abelian C]

/-- Ordinary monomorphisms retain their underlying map in the Q-construction. -/
theorem inflationArrow_injective {X Y : C} (f g : X ⟶ Y) [Mono f] [Mono g]
    (h : inflationArrow f = inflationArrow g) : f = g := by
  obtain ⟨e, hl, hr⟩ := (mkHom_eq_iff_apexIso _ _ _ _).1 h
  change e.hom ≫ 𝟙 X = 𝟙 X at hl
  change e.hom ≫ g = f at hr
  have he : e.hom = 𝟙 X := by simpa using hl
  simpa [he] using hr.symm

end Quillen.Q
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
variable (P : ObjectProperty C) [P.IsSerreClass]

instance auxiliaryForgetQ_faithful (N : C) : (auxiliaryForgetQ P N).Faithful := by
  dsimp [auxiliaryForgetQ]
  infer_instance

/-- Each comparison leg is faithful before taking the filtered colimit. -/
instance auxiliaryToIsoStructuredWithBase_faithful {N : C} {V : Quotient P}
    (φ : P.isoModSerre.Q.obj N ≅ V) : (auxiliaryToIsoStructuredWithBase P φ).Faithful where
  map_injective := by
    intro X Y f g h
    apply (auxiliaryForgetQ P N).map_injective
    exact congrArg (fun k => k.hom.right) h

/-- Equal comparison objects on the same ambient source have equal
localized ordinary structure maps. -/
lemma auxiliaryOverMk_map_eq_of_comparison_eq {N S : C} {V : Quotient P}
    (φ : P.isoModSerre.Q.obj N ≅ V) (f g : S ⟶ N)
    (hf : P.isoModSerre f) (hg : P.isoModSerre g)
    (h : (auxiliaryToIsoStructuredWithBase P φ).obj (auxiliaryOverMk P f hf) =
      (auxiliaryToIsoStructuredWithBase P φ).obj (auxiliaryOverMk P g hg)) :
    P.isoModSerre.Q.map f = P.isoModSerre.Q.map g := by
  let a := auxiliaryQuotientObjIsoWithBase P φ (auxiliaryOverMk P f hf)
  let b := auxiliaryQuotientObjIsoWithBase P φ (auxiliaryOverMk P g hg)
  have hinv : a.inv = b.inv := by
    have hh := StructuredArrow.w (eqToHom h).hom
    simp only [ObjectProperty.eqToHom_hom, StructuredArrow.eqToHom_right, eqToHom_refl] at hh
    erw [(quotientMapQ P).map_id, Category.comp_id] at hh
    exact hh
  have hhom := (Iso.inv_eq_inv a b).1 hinv
  have : IsIso (P.isoModSerre.Q.map f) := Localization.inverts _ _ _ hf
  have : IsIso (P.isoModSerre.Q.map g) := Localization.inverts _ _ _ hg
  change Q.inflationArrow (P.isoModSerre.Q.map f ≫ φ.hom) =
    Q.inflationArrow (P.isoModSerre.Q.map g ≫ φ.hom) at hhom
  exact (cancel_mono φ.hom).1 (Q.inflationArrow_injective _ _ hhom)

/-- Objects identified by one comparison leg become literally equal after
one Serre-isomorphic postcomposition. The denominator is supplied by the
proved calculus of fractions. -/
theorem auxiliary_eventual_obj_eq {N : C} {V : Quotient P}
    (φ : P.isoModSerre.Q.obj N ≅ V) (X Y : AuxiliaryKernel P N)
    (h : (auxiliaryToIsoStructuredWithBase P φ).obj X =
      (auxiliaryToIsoStructuredWithBase P φ).obj Y) :
    ∃ (M : C) (s : N ⟶ M) (hs : P.isoModSerre s),
      (auxiliaryPostcompose P s hs).obj X = (auxiliaryPostcompose P s hs).obj Y := by
  rcases X with ⟨⟨⟨X⟩⟩, hX⟩
  rcases Y with ⟨⟨⟨Y⟩⟩, hY⟩
  obtain ⟨S, f, rfl⟩ := Over.mk_surjective X
  obtain ⟨T, g, rfl⟩ := Over.mk_surjective Y
  have hST : S = T := congrArg (fun A => A.obj.right.obj.of) h
  subst T
  have heq := auxiliaryOverMk_map_eq_of_comparison_eq P φ f g hX hY h
  obtain ⟨M, s, hs, hfg⟩ := (MorphismProperty.map_eq_iff_postcomp
    P.isoModSerre.Q P.isoModSerre f g).1 heq
  refine ⟨M, s, hs, ?_⟩
  apply ObjectProperty.FullSubcategory.ext
  change Q.of _ _ (Over.mk (f ≫ s)) = Q.of _ _ (Over.mk (g ≫ s))
  rw [hfg]

/-- A denominator refinement is itself a morphism of ordinary quotient
lifts, so the previous equality holds at a genuine later diagram stage. -/
theorem quotientAuxiliaryLift_eventual_obj_eq {V : Quotient P}
    (A : QuotientAuxiliaryLift P V) (X Y : AuxiliaryKernel P A.obj.left)
    (h : (auxiliaryToIsoStructuredWithBase P (asIso A.obj.hom)).obj X =
      (auxiliaryToIsoStructuredWithBase P (asIso A.obj.hom)).obj Y) :
    ∃ (B : QuotientAuxiliaryLift P V) (s : A ⟶ B),
      (auxiliaryPostcompose P s.hom.left
        (auxiliaryLift_hom_isoModSerre P.isoModSerre.Q V P s)).obj X =
      (auxiliaryPostcompose P s.hom.left
        (auxiliaryLift_hom_isoModSerre P.isoModSerre.Q V P s)).obj Y := by
  obtain ⟨M, s, hs, heq⟩ := auxiliary_eventual_obj_eq P (asIso A.obj.hom) X Y h
  have : IsIso (P.isoModSerre.Q.map s) := Localization.inverts _ _ _ hs
  let e : P.isoModSerre.Q.obj M ≅ V := (asIso (P.isoModSerre.Q.map s)).symm ≪≫ asIso A.obj.hom
  let B : QuotientAuxiliaryLift P V := auxiliaryLiftMk P.isoModSerre.Q V e
  let t : A ⟶ B := ObjectProperty.homMk (CostructuredArrow.homMk s (by simp [B, e, auxiliaryLiftMk]))
  exact ⟨B, t, heq⟩

end Quillen.SerreLocalization
