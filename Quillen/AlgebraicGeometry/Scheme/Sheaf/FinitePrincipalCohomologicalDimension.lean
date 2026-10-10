/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.Sites.MayerVietorisSections
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite principal-cover bounds for actual section complexes

For a termwise flasque complex and an arbitrary finite family `s` of
principal opens, a uniform upper bound `b` on sections over every principal
contained in a chosen open gives the bound `b + s.card - 1` on the union.
The proof uses the original Mayer--Vietoris short exact sequence, induction
on the number of opens, and the literal identity `D(fg) = D(f) ∩ D(g)`.
The empty family is allowed: its actual section complex is zero.

For a compact open this produces an upper bound from a genuine finite
principal subcover. These are structural theorems with explicit bounds on
principal section complexes. Applying affine acyclicity to establish those
bounds for an injective resolution with quasicoherent homology is a separate
geometric step. The family need not cover the whole spectrum, and no domain,
noetherianity, or nontrivial-ring assumption is imposed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

namespace Quillen.SheafCohomology

variable {X : TopCat.{u}} {A : Type v} [Category.{u} A] [Abelian A]
  [HasSheafify (Opens.grothendieckTopology X) A]

lemma isZero_sectionsComplex_bot (K : CochainComplex (TopCat.Sheaf A X) ℤ) :
    IsZero (sectionsComplex K ⊥) := by
  rw [IsZero.iff_id_eq_zero]
  ext n
  exact (K.X n).isTerminalOfEmpty.hom_ext _ _

lemma sectionsComplex_isLE_bot (K : CochainComplex (TopCat.Sheaf A X) ℤ) (n : ℤ) :
    CochainComplex.IsLE (sectionsComplex K ⊥) n := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact (homologyFunctor A (.up ℤ) i).map_isZero (isZero_sectionsComplex_bot K)

variable (R : CommRingCat.{u})
local instance : DecidableEq R := Classical.decEq _

/-- The actual union of a finite family of principal opens. The family need
not cover the ambient spectrum. -/
def principalUnion (s : Finset R) : Opens (PrimeSpectrum R) :=
  ⨆ r ∈ s, PrimeSpectrum.basicOpen r

@[simp]
lemma principalUnion_empty : principalUnion R ∅ = ⊥ := by simp [principalUnion]

@[simp]
lemma principalUnion_insert (r : R) (s : Finset R) :
    principalUnion R (insert r s) = PrimeSpectrum.basicOpen r ⊔ principalUnion R s := by
  classical
  apply le_antisymm
  · refine iSup₂_le fun q hq => ?_
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact le_sup_left
    · have h : PrimeSpectrum.basicOpen q ≤ principalUnion R s :=
        le_iSup_of_le q (le_iSup_of_le hq le_rfl)
      exact h.trans le_sup_right
  · refine sup_le (le_iSup_of_le r (le_iSup_of_le (Finset.mem_insert_self r s) le_rfl)) ?_
    exact iSup₂_le fun q hq => le_iSup_of_le q
      (le_iSup_of_le (Finset.mem_insert_of_mem hq) le_rfl)

lemma basicOpen_le_principalUnion {s : Finset R} {r : R} (hr : r ∈ s) :
    PrimeSpectrum.basicOpen r ≤ principalUnion R s :=
  le_iSup_of_le r (le_iSup_of_le hr le_rfl)

lemma principalUnion_mono {s t : Finset R} (h : s ⊆ t) :
    principalUnion R s ≤ principalUnion R t := by
  exact iSup₂_le fun r hr => basicOpen_le_principalUnion R (h hr)

lemma principalUnion_mul (s : Finset R) (r : R) :
    principalUnion R (s.image (fun t => t * r)) =
      principalUnion R s ⊓ PrimeSpectrum.basicOpen r := by
  classical
  apply le_antisymm
  · refine iSup₂_le fun q hq => ?_
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    rw [PrimeSpectrum.basicOpen_mul]
    exact inf_le_inf (basicOpen_le_principalUnion R ht) le_rfl
  · rw [principalUnion, iSup_inf_eq]
    refine iSup_le fun t => ?_
    rw [iSup_inf_eq]
    refine iSup_le fun ht => ?_
    rw [← PrimeSpectrum.basicOpen_mul]
    exact basicOpen_le_principalUnion R (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

variable [HasSheafify (Opens.grothendieckTopology (TopCat.of (PrimeSpectrum R))) A]
variable (K : CochainComplex (TopCat.Sheaf A (TopCat.of (PrimeSpectrum R))) ℤ)
  [∀ i, TopCat.Presheaf.IsFlasque (K.X i).obj]

/-- For a finite principal family, each extra open costs at most one
cohomological degree. The empty family is included. -/
lemma sectionsComplex_isLE_principalUnion (W : Opens (PrimeSpectrum R)) (b : ℤ)
    (hlocal : ∀ r : R, PrimeSpectrum.basicOpen r ≤ W →
      CochainComplex.IsLE (sectionsComplex K (PrimeSpectrum.basicOpen r)) b)
    (s : Finset R) (hs : principalUnion R s ≤ W) :
    CochainComplex.IsLE (sectionsComplex K (principalUnion R s)) (b + (s.card : ℤ) - 1) := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hzero : s = ∅
    · subst s
      simpa using sectionsComplex_isLE_bot K (b + (n : ℤ) - 1)
    obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
    let t := s.erase r
    have hrs : insert r t = s := Finset.insert_erase hr
    have hcard : t.card + 1 = s.card := Finset.card_erase_add_one hr
    have ht : principalUnion R t ≤ W :=
      (principalUnion_mono R (Finset.erase_subset r s)).trans hs
    have hi : principalUnion R (t.image (fun q => q * r)) ≤ W := by
      rw [principalUnion_mul]
      exact inf_le_left.trans ht
    have hct : t.card < n := by omega
    have hci : (t.image (fun q => q * r)).card < n :=
      lt_of_le_of_lt (Finset.card_image_le) hct
    have htbound := ih t.card hct t ht rfl
    have hibound := ih _ hci (t.image (fun q => q * r)) hi rfl
    have hrbound := hlocal r ((basicOpen_le_principalUnion R hr).trans hs)
    have : CochainComplex.IsLE (sectionsComplex K (PrimeSpectrum.basicOpen r))
        (b + (t.card : ℤ)) :=
      CochainComplex.isLE_of_le _ b _ (by omega)
    have : CochainComplex.IsLE (sectionsComplex K (principalUnion R t))
        (b + (t.card : ℤ)) :=
      CochainComplex.isLE_of_le _ (b + (t.card : ℤ) - 1) _ (by omega)
    have : CochainComplex.IsLE (sectionsComplex K
        (PrimeSpectrum.basicOpen r ⊓ principalUnion R t)) (b + (t.card : ℤ) - 1) := by
      rw [inf_comm, ← principalUnion_mul]
      exact CochainComplex.isLE_of_le _
        (b + ((t.image (fun q => q * r)).card : ℤ) - 1) _ (by
          have := Finset.card_image_le (s := t) (f := fun q => q * r)
          omega)
    have hout := sectionsComplex_isLE_sup K (PrimeSpectrum.basicOpen r)
      (principalUnion R t) (b + (t.card : ℤ))
    rw [← principalUnion_insert, hrs] at hout
    convert hout using 1; omega

/-- A compact open has a finite cohomological bound, obtained from an actual
finite principal cover and uniform bounds on all contained principal opens. -/
lemma exists_sectionsComplex_isLE_of_isCompact (W : Opens (PrimeSpectrum R))
    (hW : IsCompact (W : Set (PrimeSpectrum R))) (b : ℤ)
    (hlocal : ∀ r : R, PrimeSpectrum.basicOpen r ≤ W →
      CochainComplex.IsLE (sectionsComplex K (PrimeSpectrum.basicOpen r)) b) :
    ∃ n : ℤ, CochainComplex.IsLE (sectionsComplex K W) n := by
  classical
  obtain ⟨ι, _, r, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact W hW
  let := Fintype.ofFinite ι
  let s : Finset R := Finset.univ.image r
  have hs : principalUnion R s = W := by
    rw [hr]
    apply le_antisymm
    · refine iSup₂_le fun q hq => ?_
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact le_iSup (fun i => PrimeSpectrum.basicOpen (r i)) i
    · exact iSup_le fun i => basicOpen_le_principalUnion R
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  refine ⟨b + (s.card : ℤ) - 1, ?_⟩
  rw [← hs]
  exact sectionsComplex_isLE_principalUnion R K W b hlocal s hs.le

end Quillen.SheafCohomology
