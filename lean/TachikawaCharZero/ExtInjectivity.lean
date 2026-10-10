import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! Injectivity criteria from the contravariant long exact sequence.
These use ordinary Ext and do not choose projective resolutions. -/
namespace TachikawaCharZero.ExtInjectivity
noncomputable section
open CategoryTheory CategoryTheory.Abelian
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
  {L : ShortComplex C} (hL : L.ShortExact) (Y : C)

theorem connecting (n c : ℕ) (hc : 1+n=c) [Subsingleton (Ext L.X₂ Y n)] :
    Function.Injective (hL.extClass.precomp Y hc) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hL Y x hc hx
  rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
  exact hy.symm

include hL in
theorem pullback (n : ℕ) (hzero : ∀ i, Subsingleton (Ext L.X₁ Y i)) :
    Function.Injective ((Ext.mk₀ L.g).precomp Y (zero_add n)) := by
  cases n with
  | zero =>
    let := hL.epi_g
    exact Ext.precomp_mk₀_injective_of_epi Y L.g
  | succ n =>
    rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hL Y x hx (n₀ := n) (by omega)
    let := hzero n
    rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
    exact hy.symm

end
end TachikawaCharZero.ExtInjectivity
