/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.Bass.TwoChart

/-!
# Right exactness of the two-chart Bass cokernel

The original two-chart contraction preserves pointwise right exact sequences. The proof lifts
actual Laurent representatives and then lifts the two chart relations. Exactness at a given object
requires exactness at its Laurent object and surjectivity at its polynomial object; preservation of
surjectivity requires only the Laurent component. The resulting cokernel universal property uses
the original induced maps. No left exactness, negative boundary, or spectral comparison is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Quillen.Bass.TwoChart

variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)
  {F G H : D ⥤ AddCommGrpCat.{v}}

/-- Surjectivity of the Laurent component gives surjectivity on the actual Bass quotient. -/
lemma contractionMap_surjective (α : F ⟶ G) (R : D)
    (hα : Function.Surjective (α.app (L.obj R))) :
    Function.Surjective ((contractionMap p m α).app R) := by
  intro x
  obtain ⟨y, rfl⟩ := contractionπ_surjective p m G R x
  obtain ⟨z, rfl⟩ := hα y
  refine ⟨(contractionπ p m F).app R z, ?_⟩
  exact congrArg (fun f ↦ f z) (contractionMap_π p m α R)

/-- The induced maps retain the original zero composite at the Laurent object. -/
lemma contractionMap_comp_eq_zero (α : F ⟶ G) (β : G ⟶ H) (R : D)
    (h : α.app (L.obj R) ≫ β.app (L.obj R) = 0) :
    (contractionMap p m α).app R ≫ (contractionMap p m β).app R = 0 := by
  apply contraction_hom_ext p m F R
  rw [← Category.assoc, contractionMap_π, Category.assoc, contractionMap_π,
    ← Category.assoc, h, zero_comp, comp_zero]

/-- The actual contracted sequence, with the induced original natural-transformation maps. -/
def contractionShortComplex (α : F ⟶ G) (β : G ⟶ H) (R : D)
    (h : α.app (L.obj R) ≫ β.app (L.obj R) = 0) : ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk ((contractionMap p m α).app R) ((contractionMap p m β).app R)
    (contractionMap_comp_eq_zero p m α β R h)

/-- Lift a vanishing Laurent representative, correcting it by both original polynomial charts. -/
lemma contractionShortComplex_exact (α : F ⟶ G) (β : G ⟶ H) (R : D)
    (h : α.app (L.obj R) ≫ β.app (L.obj R) = 0)
    (he : (ShortComplex.mk (α.app (L.obj R)) (β.app (L.obj R)) h).Exact)
    (hp : Function.Surjective (β.app (P.obj R))) :
    (contractionShortComplex p m α β R h).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := contractionπ_surjective p m G R x
  change G.obj (L.obj R) at y
  have hy : (contractionπ p m H).app R (β.app (L.obj R) y) = 0 := by
    have hn := congrArg (fun f ↦ f y) (contractionMap_π p m β R)
    exact hn.symm.trans hx
  obtain ⟨a, b, hab⟩ := (contractionπ_eq_zero_iff p m H R _).mp hy
  obtain ⟨a', ha⟩ := hp a
  obtain ⟨b', hb⟩ := hp b
  have hn (q : P ⟶ L) (z : G.obj (P.obj R)) :
      β.app (L.obj R) (G.map (q.app R) z) = H.map (q.app R) (β.app (P.obj R) z) :=
    congrArg (fun f ↦ f z) (β.naturality (q.app R))
  have hz : β.app (L.obj R) (y - (G.map (p.app R) a' - G.map (m.app R) b')) = 0 := by
    simp only [map_sub, hn, ha, hb, hab, sub_self]
  obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).mp he _ hz
  refine ⟨(contractionπ p m F).app R z, ?_⟩
  change (contractionMap p m α).app R ((contractionπ p m F).app R z) = _
  rw [show (contractionMap p m α).app R ((contractionπ p m F).app R z) =
      (contractionπ p m G).app R (α.app (L.obj R) z) from
    congrArg (fun f ↦ f z) (contractionMap_π p m α R)]
  change α.app (L.obj R) z = _ at hz
  rw [hz, map_sub, map_sub]
  have hp' := congrArg (fun f ↦ f a') (plus_contractionπ p m G R)
  have hm' := congrArg (fun f ↦ f b') (minus_contractionπ p m G R)
  change (contractionπ p m G).app R (G.map (p.app R) a') = 0 at hp'
  change (contractionπ p m G).app R (G.map (m.app R) b') = 0 at hm'
  rw [hp', hm', sub_zero, sub_zero]

/-- A pointwise cokernel sequence remains a cokernel sequence under actual Bass contraction. -/
def contractionCokernel (α : F ⟶ G) (β : G ⟶ H) (R : D)
    (h : α.app (L.obj R) ≫ β.app (L.obj R) = 0)
    (he : (ShortComplex.mk (α.app (L.obj R)) (β.app (L.obj R)) h).Exact)
    (hp : Function.Surjective (β.app (P.obj R)))
    (hl : Function.Surjective (β.app (L.obj R))) :
    IsColimit (CokernelCofork.ofπ ((contractionMap p m β).app R)
      (contractionMap_comp_eq_zero p m α β R h)) := by
  have : Epi ((contractionShortComplex p m α β R h).g) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (contractionMap_surjective p m β R hl)
  exact (contractionShortComplex_exact p m α β R h he hp).gIsCokernel

/-- Pointwise cokernel data descend through both chart quotients, using the original maps. -/
def contractionCokernelOfPointwise (α : F ⟶ G) (β : G ⟶ H)
    (h : α ≫ β = 0)
    (hc : ∀ R, IsColimit (CokernelCofork.ofπ (β.app R)
      (show α.app R ≫ β.app R = 0 from congrArg (fun γ ↦ γ.app R) h))) (R : D) :
    IsColimit (CokernelCofork.ofπ ((contractionMap p m β).app R)
      (contractionMap_comp_eq_zero p m α β R
        (congrArg (fun γ ↦ γ.app (L.obj R)) h))) := by
  apply contractionCokernel p m α β R (congrArg (fun γ ↦ γ.app (L.obj R)) h)
  · exact ShortComplex.exact_of_g_is_cokernel _ (hc (L.obj R))
  · exact (AddCommGrpCat.epi_iff_surjective _).mp (epi_of_isColimit_cofork (hc (P.obj R)))
  · exact (AddCommGrpCat.epi_iff_surjective _).mp (epi_of_isColimit_cofork (hc (L.obj R)))

/-- The canonical comparison from the cokernel of the induced map to the contracted endpoint. -/
def contractionCokernelIso (α : F ⟶ G) (β : G ⟶ H) (R : D)
    (h : α.app (L.obj R) ≫ β.app (L.obj R) = 0)
    (he : (ShortComplex.mk (α.app (L.obj R)) (β.app (L.obj R)) h).Exact)
    (hp : Function.Surjective (β.app (P.obj R)))
    (hl : Function.Surjective (β.app (L.obj R))) :
    cokernel ((contractionMap p m α).app R) ≅ (contraction p m H).obj R where
  hom := cokernel.desc _ ((contractionMap p m β).app R)
    (contractionMap_comp_eq_zero p m α β R h)
  inv := (contractionCokernel p m α β R h he hp hl).desc
    (CokernelCofork.ofπ (cokernel.π _) (cokernel.condition _))
  hom_inv_id := by
    apply (cancel_epi (cokernel.π ((contractionMap p m α).app R))).mp
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    exact Cofork.IsColimit.π_desc (contractionCokernel p m α β R h he hp hl)
  inv_hom_id := by
    apply Cofork.IsColimit.hom_ext (contractionCokernel p m α β R h he hp hl)
    rw [← Category.assoc, Cofork.IsColimit.π_desc]
    exact (cokernel.π_desc
      ((contractionMap p m α).app R) ((contractionMap p m β).app R)
      (contractionMap_comp_eq_zero p m α β R h)).trans (Category.comp_id _).symm

/-- The canonical cokernel comparison has the original induced Bass map as its forward square. -/
@[reassoc (attr := simp)]
lemma contractionCokernelIso_π (α : F ⟶ G) (β : G ⟶ H) (R : D)
    (h : α.app (L.obj R) ≫ β.app (L.obj R) = 0)
    (he : (ShortComplex.mk (α.app (L.obj R)) (β.app (L.obj R)) h).Exact)
    (hp : Function.Surjective (β.app (P.obj R)))
    (hl : Function.Surjective (β.app (L.obj R))) :
    cokernel.π ((contractionMap p m α).app R) ≫
      (contractionCokernelIso p m α β R h he hp hl).hom = (contractionMap p m β).app R :=
  cokernel.π_desc _ _ _

/-- In particular the comparison square retains every original Laurent representative. -/
@[reassoc]
lemma contractionCokernelIso_laurent (α : F ⟶ G) (β : G ⟶ H) (R : D)
    (h : α.app (L.obj R) ≫ β.app (L.obj R) = 0)
    (he : (ShortComplex.mk (α.app (L.obj R)) (β.app (L.obj R)) h).Exact)
    (hp : Function.Surjective (β.app (P.obj R)))
    (hl : Function.Surjective (β.app (L.obj R))) :
    (contractionπ p m G).app R ≫ cokernel.π ((contractionMap p m α).app R) ≫
      (contractionCokernelIso p m α β R h he hp hl).hom =
      β.app (L.obj R) ≫ (contractionπ p m H).app R := by
  rw [contractionCokernelIso_π, contractionMap_π]

end Quillen.Bass.TwoChart
