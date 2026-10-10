import OAI.RingTheory.Tachikawa.Symmetry

/-! The exact final target. The final transfer API proves this from explicit
complete-resolution hypotheses; no unconditional witness is proved yet. -/
namespace TachikawaCharZero

/-- A characteristic-zero counterexample over the rational numbers. -/
def Target : Prop :=
  ∃ (A : Type) (rA : Ring A),
    letI := rA
    ∃ (aA : Algebra ℚ A),
      letI := aA
      Module.Finite ℚ A ∧ OAI.Tachikawa.SymmetricOver ℚ A ∧
      ∃ (M : Type) (gM : AddCommGroup M),
        letI := gM
        ∃ (mA : Module A M) (mk : Module ℚ M),
          letI := mA
          letI := mk
          IsScalarTower ℚ A M ∧ Module.Finite ℚ M ∧
          ¬ Module.Projective A M ∧
          ∀ n : ℕ, 0 < n →
            Subsingleton (CategoryTheory.Abelian.Ext
              (ModuleCat.of A M) (ModuleCat.of A M) n)

end TachikawaCharZero
