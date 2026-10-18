/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.ULift

/-!
# Integral bar cocycles, central extensions, and coefficient comparison

Intended upstream module: `Aglib.RepresentationTheory.Homological.GroupHomology.IntegralBar`.
The original Mathlib bar complex uses a commutative coefficient ring and a group.
Chosen cocycles and extension perfectness retain their perfect-group hypotheses;
integral comparisons use `ULift ℤ`, and central lifts retain surjectivity and central kernel.
Current consumer: `Quillen.Algebra.Group.StableSteinbergSchur`.
-/
@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Finsupp
namespace groupHomology.IntegralBar
variable (k G : Type u) [CommRing k] [Group G] [Group.IsPerfect G]

/-- The existing trivial coefficient representation, with no replacement bar complex. -/
abbrev coefficients := Rep.trivial k G k

/-- Perfectness makes the original first group homology with these trivial coefficients zero. -/
theorem hOne_subsingleton : Subsingleton (groupHomology.H1 (coefficients k G)) := by
  let : Group.IsPerfect (Abelianization G) := by
    change Group.IsPerfect (G ⧸ commutator G)
    infer_instance
  let : Subsingleton (Abelianization G) := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact (groupHomology.H1AddEquivOfIsTrivial (coefficients k G)).injective.subsingleton

/-- Every original one-chain has an actual bar two-chain filler. -/
theorem dTwo_surjective : Function.Surjective (groupHomology.d₂₁ (coefficients k G)) := by
  intro c
  let z : groupHomology.cycles₁ (coefficients k G) :=
    (groupHomology.cycles₁IsoOfIsTrivial (coefficients k G)).inv c
  let := hOne_subsingleton k G
  exact (groupHomology.H1π_eq_zero_iff z).mp (Subsingleton.elim _ _)

omit [Group.IsPerfect G] in
/-- The actual native bar two-differential on a unit generator with trivial coefficients. -/
theorem dTwo_single (g h : G) :
    groupHomology.d₂₁ (coefficients k G) (single (g, h) 1) =
      single h 1 - single (g * h) 1 + single g 1 := by
  exact (groupHomology.d₂₁_single (A := coefficients k G) (g, h) 1).trans rfl

omit [Group.IsPerfect G] in
/-- The actual native bar three-differential on its original unit generator. -/
theorem dThree_single (g h j : G) :
    groupHomology.d₃₂ (coefficients k G) (single (g, h, j) 1) =
      single (h, j) 1 - single (g * h, j) 1 + single (g, h * j) 1 - single (g, h) 1 := by
  exact (groupHomology.d₃₂_single (A := coefficients k G) (g, h, j) 1).trans rfl

/-- Choose genuine bar fillers, with the identity normalized by the original degenerate bar. -/
def filler (g : G) : G × G →₀ k := by
  classical
  exact if g = 1 then single (1, 1) 1 else (dTwo_surjective k G (single g 1)).choose

/-- The identity filler is fixed rather than left as an arbitrary choice. -/
@[simp] theorem filler_one : filler k G 1 = single (1, 1) 1 := by simp [filler]

/-- Each chosen filler has the stated ORIGINAL bar differential. -/
@[simp] theorem filler_boundary (g : G) :
    groupHomology.d₂₁ (coefficients k G) (filler k G g) = single g 1 := by
  classical
  by_cases hg : g = 1
  · subst g
    rw [filler_one, dTwo_single]
    simp
  · simp only [filler, ite_eq_right hg]
    exact (dTwo_surjective k G (single g 1)).choose_spec

/-- The failure of the chosen fillers to be multiplicative is an actual original bar two-cycle. -/
def fillerCycle (g h : G) : groupHomology.cycles₂ (coefficients k G) :=
  ⟨filler k G g + filler k G h - filler k G (g * h) - single (g, h) 1, by
    change groupHomology.d₂₁ (coefficients k G) _ = 0
    simp only [map_sub, map_add]
    erw [filler_boundary, filler_boundary, filler_boundary, dTwo_single]
    abel⟩

/-- The cocycle value lies in the existing original H-two. No new quotient law is assumed. -/
def barCocycle (g h : G) : groupHomology.H2 (coefficients k G) :=
  groupHomology.H2π (coefficients k G) (fillerCycle k G g h)

/-- The identity-first value vanishes by an actual degenerate three-bar boundary. -/
@[simp] theorem barCocycle_one_left (g : G) : barCocycle k G 1 g = 0 := by
  apply (groupHomology.H2π_eq_zero_iff _).mpr
  refine ⟨-single (1, 1, g) 1, ?_⟩
  change groupHomology.d₃₂ (coefficients k G) (-single (1, 1, g) 1) = _
  rw [map_neg]
  erw [dThree_single]
  simp only [one_mul, fillerCycle, filler_one]
  abel

/-- The identity-last value vanishes by the other actual degenerate three-bar boundary. -/
@[simp] theorem barCocycle_one_right (g : G) : barCocycle k G g 1 = 0 := by
  apply (groupHomology.H2π_eq_zero_iff _).mpr
  refine ⟨single (g, 1, 1) 1, ?_⟩
  change groupHomology.d₃₂ (coefficients k G) (single (g, 1, 1) 1) = _
  erw [dThree_single]
  simp only [mul_one, fillerCycle, filler_one]
  abel

/-- The associativity identity is the boundary of the ORIGINAL bar three-simplex. -/
theorem barCocycle_identity (g h j : G) :
    barCocycle k G g h + barCocycle k G (g * h) j =
      barCocycle k G h j + barCocycle k G g (h * j) := by
  change groupHomology.H2π (coefficients k G) (fillerCycle k G g h) +
      groupHomology.H2π (coefficients k G) (fillerCycle k G (g * h) j) = _
  rw [← map_add]
  change groupHomology.H2π (coefficients k G) _ =
    groupHomology.H2π (coefficients k G) (fillerCycle k G h j) +
      groupHomology.H2π (coefficients k G) (fillerCycle k G g (h * j))
  rw [← map_add, groupHomology.H2π_eq_iff]
  refine ⟨single (g, h, j) 1, ?_⟩
  change groupHomology.d₃₂ (coefficients k G) (single (g, h, j) 1) = _
  erw [dThree_single]
  simp only [Submodule.coe_add, fillerCycle, mul_assoc]
  abel

end groupHomology.IntegralBar

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
namespace groupHomology.IntegralBar
variable (k G : Type u) [CommRing k] [Group G] [Group.IsPerfect G]

/-- The concrete group carrier uses the EXISTING group H-two and the original group. -/
@[ext] structure BarExtension where
  /-- The original native bar H-two coordinate. -/
  homology : groupHomology.H2 (coefficients k G)
  /-- The original quotient-group coordinate. -/
  base : G

/-- The normalized bar cocycle gives the actual multiplication, identity, and inverse. -/
instance : Group (BarExtension k G) where
  mul a b := ⟨a.homology + b.homology + barCocycle k G a.base b.base, a.base * b.base⟩
  one := ⟨0, 1⟩
  inv a := ⟨-a.homology - barCocycle k G a.base⁻¹ a.base, a.base⁻¹⟩
  mul_assoc a b c := by
    apply BarExtension.ext
    · change a.homology + b.homology + barCocycle k G a.base b.base + c.homology +
        barCocycle k G (a.base * b.base) c.base =
      a.homology + (b.homology + c.homology + barCocycle k G b.base c.base) +
        barCocycle k G a.base (b.base * c.base)
      have h := barCocycle_identity k G a.base b.base c.base
      calc
        _ = a.homology + b.homology + c.homology +
            (barCocycle k G a.base b.base + barCocycle k G (a.base * b.base) c.base) := by abel
        _ = a.homology + b.homology + c.homology +
            (barCocycle k G b.base c.base + barCocycle k G a.base (b.base * c.base)) :=
          congrArg (fun z => a.homology + b.homology + c.homology + z) h
        _ = _ := by abel
    · exact mul_assoc _ _ _
  one_mul a := by
    apply BarExtension.ext
    · change 0 + a.homology + barCocycle k G 1 a.base = a.homology
      simp
    · exact one_mul _
  mul_one a := by
    apply BarExtension.ext
    · change a.homology + 0 + barCocycle k G a.base 1 = a.homology
      simp
    · exact mul_one _
  inv_mul_cancel a := by
    apply BarExtension.ext
    · change -a.homology - barCocycle k G a.base⁻¹ a.base + a.homology +
        barCocycle k G a.base⁻¹ a.base = 0
      abel
    · exact inv_mul_cancel _

/-- Projection retains the original group. -/
def barProjection : BarExtension k G →* G where
  toFun a := a.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection is genuinely surjective with the literal zero-homology section. -/
theorem barProjection_surjective : Function.Surjective (barProjection k G) :=
  fun g => ⟨⟨0, g⟩, rfl⟩

/-- The original H-two is precisely the actual projection kernel. -/
def barKernelEquiv : Multiplicative (groupHomology.H2 (coefficients k G)) ≃*
    (barProjection k G).ker where
  toFun a := ⟨⟨a.toAdd, 1⟩, rfl⟩
  invFun a := Multiplicative.ofAdd a.val.homology
  left_inv _ := rfl
  right_inv a := by
    apply Subtype.ext
    apply BarExtension.ext
    · rfl
    · exact a.property.symm
  map_mul' a b := by
    apply Subtype.ext
    apply BarExtension.ext
    · change a.toAdd + b.toAdd = a.toAdd + b.toAdd + barCocycle k G 1 1
      simp
    · exact (one_mul _).symm

/-- The actual kernel is central, by the two proved unit normalizations. -/
theorem barProjection_ker_le_center :
    (barProjection k G).ker ≤ Subgroup.center (BarExtension k G) := by
  intro a ha
  apply Subgroup.mem_center_iff.mpr
  intro b
  apply BarExtension.ext
  · change b.homology + a.homology + barCocycle k G b.base a.base =
      a.homology + b.homology + barCocycle k G a.base b.base
    have ha' : a.base = 1 := ha
    rw [ha', barCocycle_one_left, barCocycle_one_right]
    abel
  · change b.base * a.base = a.base * b.base
    have ha' : a.base = 1 := ha
    rw [ha', mul_one, one_mul]

end groupHomology.IntegralBar

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits
namespace groupHomology.IntegralBar
variable (G : Type u) [Group G]

/-- The genuine scalar restriction from the lifted integer ring to the original integers. -/
abbrev integerRestriction := ModuleCat.restrictScalars.{u} (Int.castRingHom (ULift.{u} ℤ))

/-- The original native bar short complex, regarded in actual integral modules.
The coefficient elements remain the original ULift integers used by singular chains. -/
def integerBarShortComplex : ShortComplex (ModuleCat.{u} ℤ) :=
  (groupHomology.shortComplexH2 (coefficients (ULift.{u} ℤ) G)).map integerRestriction

/-- The actual integral-module H-two of that displayed bar short complex. -/
abbrev integerBarH2 := (integerBarShortComplex G).homology

/-- Exact scalar restriction preserves the ORIGINAL native H-two, through its original
cycle quotient data rather than a chosen abstract group isomorphism. -/
def integerBarH2Iso : integerBarH2 G ≅
    integerRestriction.obj (groupHomology.H2 (coefficients (ULift.{u} ℤ) G)) :=
  (((groupHomology.shortComplexH2 (coefficients (ULift.{u} ℤ) G)).moduleCatLeftHomologyData).map
    integerRestriction).homologyIso ≪≫
      integerRestriction.mapIso (groupHomology.H2Iso (coefficients (ULift.{u} ℤ) G)).symm

/-- The underlying comparison is a genuine additive group equivalence. -/
def integerBarH2AddEquiv : integerBarH2 G ≃+
    groupHomology.H2 (coefficients (ULift.{u} ℤ) G) :=
  (integerBarH2Iso G).toLinearEquiv.toAddEquiv

/-- An original native two-cycle is the same actual chain in the integral-module complex. -/
def integerBarCycle (c : groupHomology.cycles₂ (coefficients (ULift.{u} ℤ) G)) :
    (integerBarShortComplex G).cycles :=
  (integerBarShortComplex G).cyclesMk c.val c.property

/-- Its actual integral homology class, with no change of the original bar representative. -/
def integerBarCycleClass (c : groupHomology.cycles₂ (coefficients (ULift.{u} ℤ) G)) :
    integerBarH2 G := (integerBarShortComplex G).homologyπ (integerBarCycle G c)

/-- The lifted-integer comparison retains the original native H-two projection on every cycle. -/
theorem integerBarH2Iso_cycleClass
    (c : groupHomology.cycles₂ (coefficients (ULift.{u} ℤ) G)) :
    (integerBarH2Iso G).hom (integerBarCycleClass G c) =
      groupHomology.H2π (coefficients (ULift.{u} ℤ) G) c := by
  let S := groupHomology.shortComplexH2 (coefficients (ULift.{u} ℤ) G)
  let h := S.moduleCatLeftHomologyData
  let hZ := h.map integerRestriction
  have hc : hZ.cyclesIso.hom (integerBarCycle G c) = c := by
    apply ((ModuleCat.mono_iff_injective hZ.i).mp inferInstance)
    have he := ConcreteCategory.congr_hom hZ.cyclesIso_hom_comp_i (integerBarCycle G c)
    exact he.trans ((integerBarShortComplex G).i_cyclesMk c.val c.property)
  have hπ := ConcreteCategory.congr_hom hZ.homologyπ_comp_homologyIso_hom (integerBarCycle G c)
  change hZ.homologyIso.hom (integerBarCycleClass G c) = hZ.π (hZ.cyclesIso.hom
    (integerBarCycle G c)) at hπ
  rw [hc] at hπ
  change integerRestriction.map (groupHomology.H2Iso (coefficients (ULift.{u} ℤ) G)).inv
    (hZ.homologyIso.hom (integerBarCycleClass G c)) = _
  rw [hπ]
  change (h.π ≫ (groupHomology.H2Iso (coefficients (ULift.{u} ℤ) G)).inv) c = _
  rw [groupHomology.π_comp_H2Iso_inv]
  rfl

/-- The actual two-differential has exactly the usual integral bar signs. -/
theorem integerBar_dTwo_single (g h : G) :
    (integerBarShortComplex G).g (Finsupp.single (g, h) (1 : ULift.{u} ℤ)) =
      Finsupp.single h 1 - Finsupp.single (g * h) 1 + Finsupp.single g 1 :=
  dTwo_single (ULift.{u} ℤ) G g h

/-- The actual three-differential has exactly the usual integral bar signs. -/
theorem integerBar_dThree_single (g h j : G) :
    (integerBarShortComplex G).f (Finsupp.single (g, h, j) (1 : ULift.{u} ℤ)) =
      Finsupp.single (h, j) 1 - Finsupp.single (g * h, j) 1 +
        Finsupp.single (g, h * j) 1 - Finsupp.single (g, h) 1 :=
  dThree_single (ULift.{u} ℤ) G g h j

end groupHomology.IntegralBar

end
