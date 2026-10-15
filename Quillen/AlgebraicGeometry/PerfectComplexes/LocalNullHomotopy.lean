/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalHomotopyStep
public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalRestriction

/-!
# Local nullhomotopies from bounded vector-bundle complexes

The finite descending induction shrinks the open at each step. Its output
is an actual open immersion through the chosen point and an actual chain
homotopy after restriction. Finite local freeness is used only for the
finitely many corrections; global projectivity is never assumed.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex.HomComplex
open scoped ZeroObject

universe u

namespace Quillen.PerfectComplexes

/-- Exact geometric restriction preserves acyclic complexes. -/
theorem acyclic_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K : Complex X} (hK : K.Acyclic) : ((restrict j).obj K).Acyclic := by
  intro n
  change ((K.sc n).map (Scheme.Modules.restrictFunctor j)).Exact
  exact (show (K.sc n).Exact from hK n).map (Scheme.Modules.restrictFunctor j)

/-- A natural isomorphism of functors transports actual nullhomotopies. -/
def nullHomotopyOfNatIso {X Y : Scheme.{u}} {F G : Complex X ⥤ Complex Y}
    (e : F ≅ G) {K L : Complex X} {f : K ⟶ L}
    (h : Homotopy (F.map f) 0) : Homotopy (G.map f) 0 := by
  have he : G.map f = (e.inv.app K ≫ F.map f) ≫ e.hom.app L := by
    rw [Category.assoc, e.hom.naturality]
    simp
  exact (Homotopy.ofEq he).trans
    (((h.compLeft (e.inv.app K)).compRight (e.hom.app L)).trans
      (Homotopy.ofEq (by simp)))

/-- Once the approximation is correct down to the lower bound of the
source, it is an actual chain homotopy to zero. -/
def nullHomotopyOfAbove {X : Scheme.{u}} {K L : Complex X} (f : K ⟶ L)
    (α : Cochain K L (-1)) (a : ℤ)
    (hα : HomotopyAbove f α (a - 1)) (hb : ∀ p : ℤ, p < a → IsZero (K.X p)) :
    Homotopy f 0 := by
  refine (Cochain.equivHomotopy f 0).symm ⟨α, ?_⟩
  rw [Cochain.ofHom_zero, add_zero]
  apply Cochain.ext₀
  intro p
  rw [δ_v (-1) 0 (by simp) α p p (by simp) (p - 1) (p + 1) rfl rfl]
  simp only [Cochain.ofHom_v, Int.negOnePow_zero, one_smul]
  by_cases hp : a ≤ p
  · exact hα p (by omega)
  · exact (hb p (by omega)).eq_of_src _ _

/-- Finite descending correction of an approximate nullhomotopy. The output
keeps the composite open immersion, so successive shrinkings need not be
identified by equality of their underlying schemes. -/
theorem exists_local_nullHomotopy_from_approx (N : ℕ)
    {X : Scheme.{u}} {K L : Complex X} (a : ℤ) (f : K ⟶ L) (α : Cochain K L (-1))
    (hα : HomotopyAbove f α (a + N - 1))
    (hb : ∀ p : ℤ, p < a → IsZero (K.X p))
    (hv : ∀ p : ℤ, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X (K.X p))
    (hL : L.Acyclic) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      Nonempty (Homotopy ((@restrict Y X j hj).map f) 0) := by
  induction N generalizing X K L with
  | zero =>
      have ha : HomotopyAbove f α (a - 1) := by simpa using hα
      let h := nullHomotopyOfAbove f α a ha hb
      refine ⟨X, 𝟙 X, inferInstance, x, by simp, ?_⟩
      exact ⟨((Scheme.Modules.restrictFunctor (𝟙 X)).mapHomotopy h).trans
        (Homotopy.ofEq (by simp))⟩
  | succ N ih =>
      have ha : HomotopyAbove f α (a + N) := by
        convert hα using 1
        omega
      let : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X (K.X (a + N)) := hv _
      obtain ⟨O, hxO, β, hβ⟩ := exists_local_homotopy_step f α (a + N) ha (hL _) x
      have hb' (p : ℤ) (hp : p < a) : IsZero (((restrict O.ι).obj K).X p) :=
        (Scheme.Modules.restrictFunctor O.ι).map_isZero (hb p hp)
      have hv' (p : ℤ) : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree O.toScheme (((restrict
        O.ι).obj K).X p) :=
        @AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_restrict O.toScheme X O.ι inferInstance
          (K.X p) (hv p)
      obtain ⟨Y, j, hj, y, hy, ⟨h⟩⟩ := ih ((restrict O.ι).map f) β hβ hb' hv'
        (acyclic_restrict O.ι hL) ⟨x, hxO⟩
      let := hj
      refine ⟨Y, j ≫ O.ι, inferInstance, y, ?_, ?_⟩
      · change O.ι (j y) = x
        rw [hy]
        rfl
      · exact ⟨nullHomotopyOfNatIso (restrictCompIso j O.ι) h⟩

/-- A map from a strict perfect complex to an acyclic complex becomes
nullhomotopic near any chosen point. This is a genuine local lifting theorem,
not a global K-projective instance for vector bundles. -/
theorem exists_local_nullHomotopy {X : Scheme.{u}} {K L : Complex X}
    (hK : strictPerfect X K) (f : K ⟶ L) (hL : L.Acyclic) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      Nonempty (Homotopy ((@restrict Y X j hj).map f) 0) := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hK
  let N : ℕ := (b - a + 1).toNat
  have hα : HomotopyAbove f 0 (a + N - 1) := by
    intro p hp
    exact (hb p (Or.inr (by dsimp [N] at hp; omega))).eq_of_src _ _
  exact exists_local_nullHomotopy_from_approx N a f 0 hα
    (fun p hp ↦ hb p (Or.inl hp)) hv hL x

end Quillen.PerfectComplexes
