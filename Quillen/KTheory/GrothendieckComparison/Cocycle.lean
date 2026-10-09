import Quillen.KTheory.GrothendieckComparison.Edges
import Mathlib.CategoryTheory.SingleObj

/-!
# The Grothendieck cocycle on the Q-category

An admissible span `X ← M → Y` is assigned `[M] - [X]`. Isomorphism invariance
and the exact pullback relation prove that this is a genuine group-valued
functor, rather than an assumed presentation map.
-/

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Any chosen kernel of an admissible quotient belongs to its conflation. -/
lemma conflation_of_deflation_of_isKernel {S : ShortComplex C}
    (hg : E.deflation S.g) (hf : IsLimit (KernelFork.ofι S.f S.zero)) :
    E.conflation S := by
  obtain ⟨K, i, hi, hT⟩ := hg
  let hTf := E.kernel (ShortComplex.mk i S.g hi) hT
  let e := hTf.conePointUniqueUpToIso hf
  let eS : ShortComplex.mk i S.g hi ≅ S :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by
      simpa using hTf.conePointUniqueUpToIso_hom_comp hf WalkingParallelPair.zero) (by simp)
  exact E.iso_closed eS hT

/-- Pulling back an admissible quotient gives a conflation with the same
kernel object, using the genuine pullback universal property. -/
lemma conflation_pullback_same_kernel {S : ShortComplex C} (hS : E.conflation S)
    {A P : C} {a : P ⟶ A} {b : P ⟶ S.X₂} {i : A ⟶ S.X₃}
    (sq : IsPullback a b i S.g) :
    E.conflation (ShortComplex.mk (sq.lift 0 S.f (by simp [S.zero])) a (by simp)) := by
  let k := sq.lift 0 S.f (by simp [S.zero])
  have hk : k ≫ a = 0 := by simp [k]
  have ha : E.deflation a := E.deflation.of_isPullback sq.flip (E.deflation_of_conflation hS)
  apply E.conflation_of_deflation_of_isKernel ha
  refine KernelFork.IsLimit.ofι k hk
    (fun {W} g hg => (E.kernel S hS).lift
      (KernelFork.ofι (g ≫ b) (by rw [Category.assoc, ← sq.w, ← Category.assoc, hg]; simp)))
    ?_ ?_
  · intro W g hg
    apply sq.hom_ext
    · simp [Category.assoc, k, hg]
    · simpa [k] using (E.kernel S hS).fac
        (KernelFork.ofι (g ≫ b)
          (by rw [Category.assoc, ← sq.w, ← Category.assoc, hg]; simp))
        WalkingParallelPair.zero
  · intro W g hg m hm
    apply Fork.IsLimit.hom_ext (E.kernel S hS)
    have hmk : m ≫ k ≫ b = g ≫ b := by rw [← Category.assoc, hm]
    simpa [k] using hmk.trans
      ((E.kernel S hS).fac
        (KernelFork.ofι (g ≫ b)
          (by rw [Category.assoc, ← sq.w, ← Category.assoc, hg]; simp))
          WalkingParallelPair.zero).symm

/-- The Grothendieck classes in a pullback along an admissible quotient satisfy
the expected additive square relation. -/
lemma grothendieckClass_pullback {A B T P : C} {a : P ⟶ A} {b : P ⟶ B}
    {i : A ⟶ T} {p : B ⟶ T} (sq : IsPullback a b i p) (hp : E.deflation p) :
    E.grothendieckClass P + E.grothendieckClass T =
      E.grothendieckClass A + E.grothendieckClass B := by
  obtain ⟨K, k, hk, hS⟩ := hp
  have h₁ := E.grothendieckClass_additive hS
  have h₂ := E.grothendieckClass_additive (E.conflation_pullback_same_kernel hS sq)
  change E.grothendieckClass B = E.grothendieckClass K + E.grothendieckClass T at h₁
  change E.grothendieckClass P = E.grothendieckClass K + E.grothendieckClass A at h₂
  rw [h₁, h₂]
  abel

/-- The additive Grothendieck weight of a representative Q-span. -/
def qSpanGrothendieckWeight {X Y : C} (s : Span E.deflation E.inflation X Y) :
    E.GrothendieckGroup := E.grothendieckClass s.apex - E.grothendieckClass X

lemma qSpanGrothendieckWeight_iso {X Y : C}
    {s t : Span E.deflation E.inflation X Y} (e : s ≅ t) :
    E.qSpanGrothendieckWeight s = E.qSpanGrothendieckWeight t := by
  let e' : s.apex ≅ t.apex :=
    { hom := e.hom.hom, inv := e.inv.hom
      hom_inv_id := congrArg Span.Hom.hom e.hom_inv_id
      inv_hom_id := congrArg Span.Hom.hom e.inv_hom_id }
  simp only [qSpanGrothendieckWeight, E.grothendieckClass_iso e']

/-- The pullback definition of span composition makes the weights additive. -/
lemma qSpanGrothendieckWeight_comp {X Y Z : C}
    (s : Span E.deflation E.inflation X Y) (t : Span E.deflation E.inflation Y Z) :
    E.qSpanGrothendieckWeight (Span.comp s t) =
      E.qSpanGrothendieckWeight s + E.qSpanGrothendieckWeight t := by
  have h := E.grothendieckClass_pullback (IsPullback.of_hasPullback s.r t.l) t.wl
  dsimp only [qSpanGrothendieckWeight, Span.comp_apex]
  rw [eq_sub_iff_add_eq.mpr h]
  abel

/-- The Grothendieck weight descends through the actual apex-isomorphism quotient. -/
def qGrothendieckWeight {X Y : E.QCategory} (f : X ⟶ Y) : E.GrothendieckGroup :=
  Quotient.lift (fun s : Span E.deflation E.inflation X.obj.of Y.obj.of => E.qSpanGrothendieckWeight s)
    (fun s t (h : Nonempty (s ≅ t)) => E.qSpanGrothendieckWeight_iso h.some) f

@[simp] lemma qGrothendieckWeight_mkHom {X Y : C}
    (s : Span E.deflation E.inflation X Y) :
    E.qGrothendieckWeight (Q.mkHom E.deflation E.inflation s) =
      E.qSpanGrothendieckWeight s := rfl

@[simp] lemma qGrothendieckWeight_id (X : E.QCategory) :
    E.qGrothendieckWeight (𝟙 X) = 0 := sub_self _

lemma qGrothendieckWeight_comp {X Y Z : E.QCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    E.qGrothendieckWeight (f ≫ g) = E.qGrothendieckWeight f + E.qGrothendieckWeight g := by
  refine Quotient.inductionOn₂ f g (fun s t => ?_)
  exact E.qSpanGrothendieckWeight_comp s t

/-- The canonical Grothendieck cocycle as an actual functor on Q. -/
def qGrothendieckFunctor : E.QCategory ⥤ SingleObj (Multiplicative E.GrothendieckGroup) where
  obj _ := SingleObj.star _
  map f := Multiplicative.ofAdd (E.qGrothendieckWeight f)
  map_id X := by change Multiplicative.ofAdd _ = 1; simp
  map_comp f g := by
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [E.qGrothendieckWeight_comp, add_comm]
    rfl

/-- The zero-apex path has weight zero. -/
@[simp] lemma qGrothendieckWeight_fromZero (X : E.QCategory) :
    E.qGrothendieckWeight (E.fromZero X) = 0 := by
  change E.grothendieckClass (0 : C) - E.grothendieckClass (0 : C) = 0
  simp

/-- The whole-apex path has the canonical Grothendieck class as its weight. -/
@[simp] lemma qGrothendieckWeight_fromZeroTotal (X : E.QCategory) :
    E.qGrothendieckWeight (E.fromZeroTotal X) = E.grothendieckClass X.obj.of := by
  change E.grothendieckClass X.obj.of - E.grothendieckClass (0 : C) = _
  simp

/-- The Q-cocycle recovers each canonical object generator exactly. -/
@[simp] lemma qObjectClass_qGrothendieckFunctor (X : C) :
    E.qObjectClass E.qGrothendieckFunctor X =
      SingleObj.toEnd (Multiplicative E.GrothendieckGroup)
        (Multiplicative.ofAdd (E.grothendieckClass X)) := by
  simp only [qObjectClass, qGrothendieckFunctor, qGrothendieckWeight_fromZeroTotal,
    qGrothendieckWeight_fromZero, SingleObj.inv_as_inv, SingleObj.comp_as_mul]
  change (1 : Multiplicative E.GrothendieckGroup)⁻¹ *
      Multiplicative.ofAdd (E.grothendieckClass X) = Multiplicative.ofAdd (E.grothendieckClass X)
  simp

end Quillen.ExactStructure
