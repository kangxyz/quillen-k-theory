import Quillen.Scheme.Coherent.Localization.Quotient

/-!
# Graph fractions from coherent subobject extension

This file is a conditional proof-reduction helper. It does not assert the
geometric subobject-extension hypothesis. Given that hypothesis, the actual
graph of an open morphism extends inside a coherent biproduct, and its two
projections give a genuine supported-Serre fraction. The existing faithful
quotient functor is then full.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Extension of coherent subobjects gives the genuine fraction required
for quotient fullness. The geometric extension hypothesis remains explicit. -/
theorem coherent_fraction_of_subobject_extension
    (hSub : ∀ (H : Coherent X) (A : Coherent U)
      (i : A ⟶ (coherentRestriction j).obj H), Mono i →
      ∃ (H' : Coherent X) (s : H' ⟶ H), Mono s ∧
        ∃ (e : (coherentRestriction j).obj H' ≅ A),
          (coherentRestriction j).map s = e.hom ≫ i)
    {M N : Coherent X}
    (φ : (coherentRestriction j).obj M ⟶ (coherentRestriction j).obj N) :
    ∃ (M' : Coherent X) (s : M' ⟶ M) (g : M' ⟶ N),
      (coherentSupportedAway j).isoModSerre s ∧
        (coherentRestriction j).map s ≫ φ = (coherentRestriction j).map g := by
  let F := coherentRestriction j
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  let i : F.obj M ⟶ F.obj (M ⊞ N) := biprod.lift (𝟙 _) φ ≫ (F.mapBiprod M N).inv
  have hi : Mono i := by
    change Mono (biprod.lift (𝟙 _) φ ≫ (F.mapBiprod M N).inv)
    infer_instance
  have hi₁ : i ≫ F.map biprod.fst = 𝟙 _ := by
    dsimp [i]
    simp [← F.map_comp]
  have hi₂ : i ≫ F.map biprod.snd = φ := by
    dsimp [i]
    simp [← F.map_comp]
    exact Category.comp_id φ
  obtain ⟨H', t, _, e, ht⟩ := hSub (M ⊞ N) (F.obj M) i hi
  let s : H' ⟶ M := t ≫ biprod.fst
  let g : H' ⟶ N := t ≫ biprod.snd
  have hs : F.map s = e.hom := by
    dsimp [s]
    rw [F.map_comp, ht, Category.assoc, hi₁, Category.comp_id]
  have hg : F.map g = e.hom ≫ φ := by
    dsimp [g]
    rw [F.map_comp, ht, Category.assoc, hi₂]
  refine ⟨H', s, g, ?_, ?_⟩
  · rw [coherentSupportedAway_isoModSerre_iff]
    change IsIso (F.map s)
    rw [hs]
    infer_instance
  · change F.map s ≫ φ = F.map g
    rw [hs, hg]

/-- The graph-extension hypothesis proves fullness of the actual quotient
functor; faithfulness was already proved without this hypothesis. -/
theorem quotientCoherentRestriction_full_of_subobject_extension
    (hSub : ∀ (H : Coherent X) (A : Coherent U)
      (i : A ⟶ (coherentRestriction j).obj H), Mono i →
      ∃ (H' : Coherent X) (s : H' ⟶ H), Mono s ∧
        ∃ (e : (coherentRestriction j).obj H' ≅ A),
          (coherentRestriction j).map s = e.hom ≫ i) :
    (quotientCoherentRestriction j).Full := by
  let Q := (coherentSupportedAway j).isoModSerre.Q
  have : Q.EssSurj := Localization.essSurj Q (coherentSupportedAway j).isoModSerre
  apply Functor.full_of_comp_essSurj (quotientCoherentRestriction j) Q
  intro M N φ
  change (coherentRestriction j).obj M ⟶ (coherentRestriction j).obj N at φ
  obtain ⟨M', s, g, hs, hsg⟩ := coherent_fraction_of_subobject_extension j hSub φ
  have : IsIso (Q.map s) := Localization.inverts Q (coherentSupportedAway j).isoModSerre s hs
  have : IsIso ((coherentRestriction j).map s) :=
    (coherentSupportedAway_isoModSerre_iff j s).mp hs
  refine ⟨inv (Q.map s) ≫ Q.map g, ?_⟩
  apply (cancel_epi ((coherentRestriction j).map s)).mp
  rw [Functor.map_comp, Functor.map_inv]
  simp only [Q, quotientCoherentRestriction_map_Q, IsIso.hom_inv_id_assoc]
  exact hsg.symm

end Quillen.CoherentScheme
