import TachikawaCharZero.Statement
import OAI.RingTheory.Tachikawa.NakayamaTransfer

/-! The final rational trivial-extension construction and its acceptance
theorem. Input is an actual finite totally acyclic complete resolution
with the required all-integer Hom vanishing. Constructing that input from
the rational triangular cone remains necessary before asserting Target.
The exactness-to-transfer step follows the characteristic-independent
argument in OpenAI Math Counterexample.lean, fixed at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). -/
namespace TachikawaCharZero.FinalTransfer
noncomputable section
open CategoryTheory OAI.Tachikawa
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R] [Algebra ℚ R]

abbrev Gamma (R : Type) [Ring R] [Algebra ℚ R] := TrivialExtension ℚ R
abbrev M (P : ChainComplex (ModuleCat.{0} R) ℤ) := TrivialInduction.Obj ℚ R (CokerAt P 0)

omit [Algebra ℚ R] in
theorem coker_finite (P : ChainComplex (ModuleCat.{0} R) ℤ)
    (fin : ∀ j, Module.Finite R (P.X j)) : Module.Finite R (CokerAt P 0) := by
  let := fin 0
  exact Module.Finite.of_surjective (CokerAt.π P 0) (CokerAt.π_surjective P 0)

theorem Gamma_symmetric (R : Type) [Ring R] [Algebra ℚ R] [FiniteDimensional ℚ R] :
    SymmetricOver ℚ (Gamma R) := TrivialExtension.symmetricOver

theorem M_finite [FiniteDimensional ℚ R] (P : ChainComplex (ModuleCat.{0} R) ℤ)
    (fin : ∀ j, Module.Finite R (P.X j)) : Module.Finite ℚ (M P) := by
  let := coker_finite P fin
  let : Module.Finite ℚ (CokerAt P 0) := Module.Finite.trans R _
  infer_instance

theorem M_nonprojective (P : ChainComplex (ModuleCat.{0} R) ℤ)
    (fin : ∀ j, Module.Finite R (P.X j))
    (hn : ¬ Module.Projective R (CokerAt P 0)) : ¬ Module.Projective (Gamma R) (M P) := by
  intro hp
  let := hp
  let := coker_finite P fin
  exact hn (TrivialInduction.projective_of_inducedProjective (k := ℚ) (R := R) (M := CokerAt P 0))

theorem exact_of_zero (P : ChainComplex (ModuleCat.{0} R) ℤ) (N : ModuleCat.{0} R) (a : ℤ)
    (hz : Subsingleton (VectorSplit.H (completeHom (k := ℚ) P N) a)) :
    Function.Exact (homPrecomp (k := ℚ) (Z := N) (P.d a (a-1)).hom)
      (homPrecomp (k := ℚ) (P.d (a+1) a).hom) := by
  intro f
  constructor
  · intro hf
    let z : VectorSplit.Z (completeHom (k := ℚ) P N) a :=
      ⟨ModuleCat.ofHom f,(completeHom_memZ P N a _).mpr (ModuleCat.hom_ext hf)⟩
    have hq : VectorSplit.quotient _ a z=0 := hz.elim _ _
    obtain ⟨g,hg⟩ := (VectorSplit.quotient_zero_iff_predecessor a z).mp hq
    exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩
  · rintro ⟨g,rfl⟩
    change (g.comp (P.d a (a-1)).hom).comp (P.d (a+1) a).hom=0
    rw [LinearMap.comp_assoc]
    have hd : (P.d a (a-1)).hom.comp (P.d (a+1) a).hom=0 :=
      ModuleCat.hom_ext_iff.mp (P.d_comp_d (a+1) a (a-1))
    rw [hd,LinearMap.comp_zero]

theorem self_ext_vanishing [FiniteDimensional ℚ R]
    (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
    (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j))
    (van : ∀ a : ℤ, 0<a ∨ a≤ -2 →
      Subsingleton (VectorSplit.H (completeHom (k := ℚ) P (ModuleCat.of R (CokerAt P 0))) a))
    (n : ℕ) (hn : 0<n) :
    Subsingleton (Abelian.Ext (ModuleCat.of (Gamma R) (M P))
      (ModuleCat.of (Gamma R) (M P)) n) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  apply TrivialInduction.transfer (k := ℚ) P hP fin proj
  · intro m
    have hx := exact_of_zero P (ModuleCat.of R (CokerAt P 0)) ((m+1:ℕ):ℤ)
      (van _ (Or.inl (by omega)))
    have h1 : ((m+1:ℕ):ℤ)-1=(m:ℤ) := by omega
    have h2 : ((m+1:ℕ):ℤ)+1=((m+2:ℕ):ℤ) := by omega
    rw [h1,h2] at hx
    exact hx
  · intro m
    have hx := exact_of_zero P (ModuleCat.of R (CokerAt P 0)) (-((m+1:ℕ):ℤ)-1)
      (van _ (Or.inr (by omega)))
    have h1 : (-((m+1:ℕ):ℤ)-1)-1 = -((m+2:ℕ):ℤ)-1 := by omega
    have h2 : (-((m+1:ℕ):ℤ)-1)+1 = -(m:ℤ)-1 := by omega
    rw [h1,h2] at hx
    exact hx

theorem target_of_complete_resolution [FiniteDimensional ℚ R]
    (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
    (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j))
    (hn : ¬ Module.Projective R (CokerAt P 0))
    (van : ∀ a : ℤ, 0<a ∨ a≤ -2 →
      Subsingleton (VectorSplit.H (completeHom (k := ℚ) P (ModuleCat.of R (CokerAt P 0))) a)) :
    Target := by
  refine ⟨Gamma R, inferInstance, inferInstance, inferInstance, Gamma_symmetric R,
    M P, (inferInstance : AddCommGroup (M P)),
    (inferInstance : Module (Gamma R) (M P)), (inferInstance : Module ℚ (M P)),
    (inferInstance : IsScalarTower ℚ (Gamma R) (M P)),
    M_finite (R := R) P fin, M_nonprojective (R := R) P fin hn, ?_⟩
  exact self_ext_vanishing P hP fin proj van

end
end TachikawaCharZero.FinalTransfer
