import OAI.RingTheory.Tachikawa.StableShift

/-! Characteristic-independent excerpts from OpenAI Math Delta.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  {L M N Q : ModuleCat.{0} R} [Module.Finite R Q] [Module.Projective R Q]
  (i₁ : M ⟶ L) (i₂ : N ⟶ L) (i₃ : Q ⟶ L)
  (p₁ : L ⟶ M) (p₂ : L ⟶ N) (p₃ : L ⟶ Q)
  (h11 : i₁ ≫ p₁ = 𝟙 _) (h12 : i₁ ≫ p₂ = 0)
  (h21 : i₂ ≫ p₁ = 0) (h22 : i₂ ≫ p₂ = 𝟙 _)
  (hs : p₁ ≫ i₁ + p₂ ≫ i₂ + p₃ ≫ i₃ = 𝟙 _)

include hP h11 h12 h21 h22 hs in
lemma completeHpair_bijective (a : ℤ) : Function.Bijective
    ((completeHmap (k := k) P p₁ a).prod (completeHmap P p₂ a)) := by
  have pair_id : ((completeHmap (k := k) P i₁ a).comp (completeHmap P p₁ a) +
      (completeHmap P i₂ a).comp (completeHmap P p₂ a)) = LinearMap.id := by
    have hh := congrArg (fun f => completeHmap (k := k) P f a) hs
    simp only [completeHmap_add,completeHmap_comp,completeHmap_id] at hh
    have hz : (completeHmap (k := k) P i₃ a).comp (completeHmap P p₃ a) = 0 := by
      apply LinearMap.ext
      intro x
      let := completeHom_projective_zero (k := k) P hP Q a
      change completeHmap P i₃ a (completeHmap P p₃ a x) = 0
      rw [Subsingleton.elim (completeHmap P p₃ a x) 0,map_zero]
    rwa [hz,add_zero] at hh
  constructor
  · intro x y h
    have hf := congrArg (fun z => completeHmap P i₁ a z.1 + completeHmap P i₂ a z.2) h
    change (completeHmap P i₁ a).comp (completeHmap P p₁ a) x +
        (completeHmap P i₂ a).comp (completeHmap P p₂ a) x =
      (completeHmap P i₁ a).comp (completeHmap P p₁ a) y +
        (completeHmap P i₂ a).comp (completeHmap P p₂ a) y at hf
    simp only [← LinearMap.add_apply,pair_id,LinearMap.id_apply] at hf
    exact hf
  · rintro ⟨x,y⟩
    refine ⟨completeHmap P i₁ a x + completeHmap P i₂ a y,?_⟩
    apply Prod.ext
    · change completeHmap P p₁ a (_+_) = x
      rw [map_add,← LinearMap.comp_apply,← LinearMap.comp_apply,
        ← completeHmap_comp,← completeHmap_comp,h11,h21,completeHmap_id,completeHmap_zero]
      exact add_zero _
    · change completeHmap P p₂ a (_+_) = y
      rw [map_add,← LinearMap.comp_apply,← LinearMap.comp_apply,
        ← completeHmap_comp,← completeHmap_comp,h12,h22,completeHmap_id,completeHmap_zero]
      exact zero_add _
end Tachikawa
namespace Tachikawa.VectorSplit
open CategoryTheory
variable {k : Type*} [Field k] {K L M : CochainComplex (ModuleCat k) ℤ}
  (i : K ⟶ L) (p : L ⟶ M)
  (hi : ∀ a, Function.Injective (i.f a))
  (he : ∀ a, Function.Exact (i.f a) (p.f a))
  (hp : ∀ a, Function.Surjective (p.f a))

include hi he hp in
lemma Hmap_exact (a : ℤ) : Function.Exact (Hmap i a) (Hmap p a) := by
  intro x
  constructor
  · intro hx
    obtain ⟨z,rfl⟩ := quotient_surjective a x
    obtain ⟨y,hy⟩ := (quotient_zero_iff_predecessor a _).mp hx
    obtain ⟨v,hv⟩ := hp (a-1) y
    have hz' : p.f a (z.val - L.d (a-1) a v) = 0 := by
      rw [map_sub,← comm_apply p,hv,hy]
      exact sub_self _
    obtain ⟨u,hu⟩ := (he a _).mp hz'
    have huz : u ∈ Z K a := by
      rw [memZ_iff]
      apply hi (a+1)
      rw [map_zero,← comm_apply i,hu,map_sub]
      rw [(memZ_iff a z.val).mp z.property]
      have hd := congrArg (fun f => f v) (L.d_comp_d (a-1) a (a+1))
      change L.d a (a+1) (L.d (a-1) a v) = 0 at hd
      rw [hd,sub_self]
    refine ⟨quotient K a ⟨u,huz⟩,?_⟩
    rw [Hmap_quotient]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (quotient_zero_iff_predecessor a _).mpr
    use -v
    change L.d (a-1) a (-v) = i.f a u - z.val
    rw [map_neg,hu]
    abel
  · rintro ⟨y,rfl⟩
    obtain ⟨z,rfl⟩ := quotient_surjective a y
    rw [Hmap_quotient,Hmap_quotient]
    have hz : cycleMap p a (cycleMap i a z) = 0 := by
      apply Subtype.ext
      exact (he a _).mpr ⟨z.val,rfl⟩
    rw [hz,map_zero]
end Tachikawa.VectorSplit

namespace Tachikawa
variable {k A B C V : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V]

lemma exact_line_surjective (i : A →ₗ[k] B) (p : B →ₗ[k] C)
    (hi : Function.Injective i) (hp : Function.Surjective p) (he : Function.Exact i p)
    (eB : B ≃ₗ[k] k × k) (eC : C ≃ₗ[k] k) (eV : V ≃ₗ[k] k)
    (v : V →ₗ[k] A) (hv : Function.Injective v) : Function.Surjective v := by
  let : FiniteDimensional k B := eB.symm.finiteDimensional
  let : FiniteDimensional k C := eC.symm.finiteDimensional
  let : FiniteDimensional k V := eV.symm.finiteDimensional
  let : FiniteDimensional k A := Module.Finite.of_injective i hi
  have hB : Module.finrank k B = 2 := by simpa using eB.finrank_eq
  have hC : Module.finrank k C = 1 := by simpa using eC.finrank_eq
  have hV : Module.finrank k V = 1 := by simpa using eV.finrank_eq
  have hr : Module.finrank k p.range = 1 := by rw [LinearMap.range_eq_top.mpr hp]; simpa using hC
  have ha : Module.finrank k A = 1 := by
    have h := p.finrank_range_add_finrank_ker
    rw [he.linearMap_ker_eq,LinearMap.finrank_range_of_inj hi,hr,hB] at h
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hV.trans ha.symm)).mp hv
end Tachikawa
end
end OAI
