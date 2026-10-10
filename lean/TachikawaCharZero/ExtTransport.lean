import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! Isomorphism transport of genuine Yoneda self-Ext, with units and products.
This does not introduce a coordinate model or any extra axiom. -/
namespace TachikawaCharZero.ExtTransport
noncomputable section
open CategoryTheory CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C] [HasExt C]
  {M N : C}

def conjugate (e : M ≅ N) {n : ℕ} (x : Ext M M n) : Ext N N n :=
  (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ e.hom) (add_zero n)) (zero_add n)

theorem conjugate_zero (e : M ≅ N) (n : ℕ) :
    conjugate e (0 : Ext M M n) = 0 := by simp [conjugate]

theorem conjugate_mk₀ (e : M ≅ N) (f : M ⟶ M) :
    conjugate e (Ext.mk₀ f) = Ext.mk₀ (e.inv ≫ f ≫ e.hom) := by
  simp [conjugate]

theorem conjugate_unit (e : M ≅ N) :
    conjugate e (Ext.mk₀ (𝟙 M)) = Ext.mk₀ (𝟙 N) := by
  simp [conjugate_mk₀]

theorem conjugate_symm (e : M ≅ N) {n : ℕ} (x : Ext M M n) :
    conjugate e.symm (conjugate e x) = x := by
  simp [conjugate, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀_assoc]

theorem conjugate_injective (e : M ≅ N) (n : ℕ) :
    Function.Injective (conjugate e (n := n)) := by
  intro x y h
  rw [← conjugate_symm e x, ← conjugate_symm e y, h]

theorem conjugate_comp (e : M ≅ N) {a b c : ℕ}
    (x : Ext M M a) (y : Ext M M b) (h : a+b=c) :
    conjugate e (x.comp y h) = (conjugate e x).comp (conjugate e y) h := by
  unfold conjugate
  symm
  rw [Ext.comp_assoc (a₂₃ := c) _ _ _ (zero_add a) h (by omega),
    Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp,
    ← Ext.comp_assoc_of_third_deg_zero]

section Linear
variable (R : Type*) [Ring R] [CategoryTheory.Linear R C]

def conjugateLinearMap (e : M ≅ N) (n : ℕ) : Ext M M n →ₗ[R] Ext N N n where
  toFun := conjugate e
  map_add' x y := by simp [conjugate, Ext.add_comp, Ext.comp_add]
  map_smul' r x := by simp [conjugate, Ext.smul_comp, Ext.comp_smul]

def conjugateLinearEquiv (e : M ≅ N) (n : ℕ) : Ext M M n ≃ₗ[R] Ext N N n where
  __ := conjugateLinearMap R e n
  invFun := conjugate e.symm
  left_inv := conjugate_symm e
  right_inv := conjugate_symm e.symm

end Linear

section ExactFunctor
variable {D : Type*} [Category* D] [Abelian D] [HasExt D]
  (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
  [CategoryTheory.Limits.PreservesFiniteColimits F]

theorem map_conjugate (e : M ≅ N) {n : ℕ} (x : Ext M M n) :
    (conjugate e x).mapExactFunctor F = conjugate (F.mapIso e) (x.mapExactFunctor F) := by
  simp only [conjugate, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rfl

theorem conjugate_map_natIso {G : C ⥤ D} [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (e : F ≅ G) {X : C} {n : ℕ} (x : Ext X X n) :
    conjugate (e.app X) (x.mapExactFunctor F) = x.mapExactFunctor G := by
  unfold conjugate
  change (Ext.mk₀ (e.inv.app X)).comp
    ((x.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app X)) (add_zero n)) (zero_add n) = _
  rw [Ext.mapExactFunctor_comp_mk₀_natTransApp x e.hom]
  simp only [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_app, Ext.mk₀_id_comp]

theorem map_zero_of_natIso {G : C ⥤ D} [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (e : F ≅ G) {X Y : C} {n : ℕ} (x : Ext X Y n)
    (hx : x.mapExactFunctor F = 0) : x.mapExactFunctor G = 0 := by
  have h := (Ext.mapExactFunctor_comp_mk₀_natTransApp x e.hom).symm
  rw [hx, Ext.zero_comp] at h
  have hi := congrArg (fun z => (Ext.mk₀ (e.inv.app X)).comp z (zero_add n)) h
  simpa only [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_app, Ext.mk₀_id_comp,
    Ext.comp_zero] using hi

end ExactFunctor
end
end TachikawaCharZero.ExtTransport
