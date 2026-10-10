import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! Compare indexed Ext products without expanding the underlying modules. -/
namespace TachikawaCharZero.ExtIndex
open CategoryTheory CategoryTheory.Abelian
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
  {X Y Z : C} {a b b' c d : ℕ}

theorem comp_right_index (x : Ext X Y a) (f : (n : ℕ) → Ext Y Z (d*n))
    (hb : b=b') (h : a+d*b=c) (h' : a+d*b'=c) :
    x.comp (f b) h = x.comp (f b') h' := by
  subst b'
  rfl

end TachikawaCharZero.ExtIndex
