import TachikawaCharZero.CornerTensorModel

/-! Ordinary Ext from the actual degree-five corner-total cokernel to X
vanishes in all natural-number degrees. The tail resolution has no maps
to X: every positive total summand contains a Te corner, and Te has no
maps to the character at f. This is an auxiliary mixed-Ext statement,
not the final self-Ext vanishing theorem. -/
namespace TachikawaCharZero.CornerTensorExt
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
open ScalingSocle SocleBimodule InducedTensorComparison CornerTensorModel

theorem jTerm_finite (n : ℕ) : Module.Finite Induced.T (Induced.complex.X n) := by
  cases n with
  | zero =>
    change Module.Finite Induced.T Induced.TF
    exact Module.Finite.of_restrictScalars_finite ℚ Induced.T Induced.TF
  | succ n =>
    change Module.Finite Induced.T Induced.TE
    exact Module.Finite.of_restrictScalars_finite ℚ Induced.T Induced.TE

theorem jTerm_projective (n : ℕ) : Module.Projective Induced.T (Induced.complex.X n) := by
  cases n with
  | zero => exact Induced.tfProjective
  | succ n => exact Induced.teProjective

local instance (n : ℕ) : Module.Finite Induced.T (Induced.complex.X n) := jTerm_finite n
local instance (n : ℕ) : Module.Projective Induced.T (Induced.complex.X n) := jTerm_projective n
local instance (n : ℕ) : FiniteDimensional ℚ (Induced.complex.X n) :=
  Module.Finite.trans Induced.T (Induced.complex.X n)

theorem jHom_zero (n : ℕ) (hn : n≠0) (f : Induced.complex.X n ⟶ Induced.X) : f=0 := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    apply ModuleCat.hom_ext
    exact Induced.homTE_zero f.hom

theorem summandHom_subsingleton (i j : ℕ) (h : i≠0 ∨ j≠0) :
    Subsingleton ((((OuterTensor.bifunctor ℚ T T).obj
      (Induced.complex.X i)).obj (Induced.complex.X j)) ⟶ X) := by
  rcases h with hi | hj
  · let : Subsingleton (Induced.complex.X i ⟶ Induced.X) :=
      ⟨fun f g => (jHom_zero i hi f).trans (jHom_zero i hi g).symm⟩
    exact (OuterTensor.homEquiv (k := ℚ) (Induced.complex.X i) Induced.X
      (Induced.complex.X j) Induced.X).symm.injective.subsingleton
  · let : Subsingleton (Induced.complex.X j ⟶ Induced.X) :=
      ⟨fun f g => (jHom_zero j hj f).trans (jHom_zero j hj g).symm⟩
    exact (OuterTensor.homEquiv (k := ℚ) (Induced.complex.X i) Induced.X
      (Induced.complex.X j) Induced.X).symm.injective.subsingleton

theorem totalHom_zero (n : ℕ) (hn : n≠0) (f : cornerTensorChain.X n ⟶ X) : f=0 := by
  apply mapBifunctor.hom_ext
  intro i j h
  rw [comp_zero]
  have hij : i+j=n := h
  exact (summandHom_subsingleton i j (by omega)).elim _ _

theorem cokerFive_X_ext_zero (n : ℕ) : Subsingleton (Ext cokerFive.obj X n) := by
  let P := projectiveResolution
  have hz (α : Ext cokerFive.obj X n) : α=0 := by
    obtain ⟨f,hf,rfl⟩ := P.extMk_surjective α (n+1) rfl
    have hmap : f=0 := totalHom_zero (n+5) (by omega) f
    subst f
    exact P.extMk_zero _ _
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

end
end TachikawaCharZero.CornerTensorExt
