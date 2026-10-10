import TachikawaCharZero.FCStatement
import TachikawaCharZero.TriangularSelfHom
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Module.Rat

/-! The actual rational counterexample satisfies both Ext premises in
the general Artin-algebra Auslander--Reiten statement. Finite generation
is over Gamma, not merely over the rational numbers. Self-injectivity of
the actual trivial extension supplies the additional regular-module Ext
vanishing without a new projective-resolution computation. -/
namespace TachikawaCharZero.ArtinWitness
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open CategoryTheory OAI.Tachikawa TriangularWitness
open scoped ModuleCat.Algebra
local instance finiteLambda : Module.Finite ℚ Lambda := Lambda_finite
local instance finiteGammaQ : Module.Finite ℚ Gamma := Gamma_finite
local instance finiteMQ : Module.Finite ℚ M := M_finite

theorem Gamma_artinian : IsArtinianRing Gamma := by
  let : IsScalarTower ℚ Gamma Gamma := IsScalarTower.rat (R := Gamma) (M := Gamma)
  exact IsArtinianRing.of_finite ℚ Gamma

theorem M_finite_Gamma : Module.Finite Gamma M :=
  Module.Finite.of_restrictScalars_finite ℚ Gamma M

local instance finiteMGamma : Module.Finite Gamma M := M_finite_Gamma

theorem Gamma_injective : Module.Injective Gamma Gamma := by
  infer_instance

theorem Gamma_injective_object : Injective (ModuleCat.of Gamma Gamma) := by
  let := Gamma_injective
  exact Module.injective_object_of_injective_module Gamma Gamma

theorem regular_ext_vanishing (n : ℕ) (hn : 0 < n) :
    Subsingleton (Abelian.Ext (ModuleCat.of Gamma M) (ModuleCat.of Gamma Gamma) n) := by
  let := Gamma_injective_object
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact Abelian.Ext.subsingleton_of_injective _ _ i

theorem self_ext_vanishing (n : ℕ) (hn : 0 < n) :
    Subsingleton (Abelian.Ext (ModuleCat.of Gamma M) (ModuleCat.of Gamma M) n) :=
  FinalTransfer.self_ext_vanishing cone cone_totallyAcyclic cone_finite cone_projective
    TriangularSelfHom.selfHom_vanishing n hn

/-- Both actual positive Ext families vanish, while M is nonprojective. -/
theorem counterexample :
    Module.Finite Gamma M ∧
    (∀ n : ℕ, 0 < n →
      Subsingleton (Abelian.Ext (ModuleCat.of Gamma M) (ModuleCat.of Gamma Gamma) n)) ∧
    (∀ n : ℕ, 0 < n →
      Subsingleton (Abelian.Ext (ModuleCat.of Gamma M) (ModuleCat.of Gamma M) n)) ∧
    ¬ Module.Projective Gamma M :=
  ⟨M_finite_Gamma, regular_ext_vanishing, self_ext_vanishing,
    TriangularNonprojective.M_nonprojective⟩

/-- Refute the fixed FC pointwise signature at the rational witnesses. -/
theorem not_artinCase : ¬ FCStatement.artinCase Gamma M ℚ := by
  intro h
  exact TriangularNonprojective.M_nonprojective
    (h regular_ext_vanishing self_ext_vanishing)

/-- Refute the general Artin-algebra conjecture at universe zero. -/
theorem not_artinAuslanderReiten : ¬ FCStatement.ArtinAuslanderReiten := by
  intro h
  exact not_artinCase (h Gamma M ℚ)

end
end TachikawaCharZero.ArtinWitness
