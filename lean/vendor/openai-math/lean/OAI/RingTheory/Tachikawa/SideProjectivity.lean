import OAI.RingTheory.Tachikawa.InductionLeftComparison

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory
universe u v
variable {R : Type u} [Ring R]
variable {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

def linearShortComplex (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    (ModuleCat.hom_ext h.linearMap_comp_eq_zero)

lemma linearShortExact (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (linearShortComplex f g h).ShortExact := by
  have hm : Mono (linearShortComplex f g h).f := (ModuleCat.mono_iff_injective _).mpr hf
  have he : Epi (linearShortComplex f g h).g := (ModuleCat.epi_iff_surjective _).mpr hg
  exact ⟨(ShortComplex.moduleCat_exact_iff _).mpr (fun x => (h x).mp)⟩

end Tachikawa

namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra

lemma projective_kernel_of_surjective {R M P N : Type} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module.Projective R P] [Module.Projective R N]
    (i : M →ₗ[R] P) (q : P →ₗ[R] N)
    (hi : Function.Injective i) (hq : Function.Surjective q) (he : Function.Exact i q) :
    Module.Projective R M := by
  let h := linearShortExact i q he hi hq
  have : CategoryTheory.Projective (linearShortComplex i q he).X₃ :=
    show CategoryTheory.Projective (ModuleCat.of R N) from inferInstance
  have : Module.Projective R (linearShortComplex i q he).X₂ :=
    show Module.Projective R P from inferInstance
  let s := h.splittingOfProjective
  exact Module.Projective.of_split i s.r.hom (ModuleCat.hom_ext_iff.mp s.f_r)

end Tachikawa

namespace Tachikawa
open CategoryTheory
variable {R M P N : Type} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
  [AddCommGroup N] [Module R N]

lemma projective_cokernel_of_injective [Module.Injective R M] [Module.Projective R P]
    (i : M →ₗ[R] P) (q : P →ₗ[R] N)
    (hi : Function.Injective i) (hq : Function.Surjective q) (he : Function.Exact i q) :
    Module.Projective R N := by
  let h := linearShortExact i q he hi hq
  have : CategoryTheory.Injective (linearShortComplex i q he).X₁ :=
    show CategoryTheory.Injective (ModuleCat.of R M) from Module.injective_object_of_injective_module R M
  have : Module.Projective R (linearShortComplex i q he).X₂ :=
    show Module.Projective R P from inferInstance
  let s := h.splittingOfInjective
  exact Module.Projective.of_split s.s.hom q (ModuleCat.hom_ext_iff.mp s.s_g)

end Tachikawa

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R))
  (u : SymmetrizingForm (k := k) (R := S))
  (M : FiniteModule k (Alg k R S))

abbrev envelopingForm : SymmetrizingForm (k := k) (R := Alg k R S) := t.tensor u.op

lemma cosyzygy_left_projective [Module.Projective R (Obj M.obj)] :
    Module.Projective R (Obj (M.cosyzygy (envelopingForm t u)).obj) := by
  let : Module.Finite R (Obj M.obj) := Module.Finite.of_restrictScalars_finite k R _
  let : Module.Injective R R := t.injective
  let : Module.Injective R (Obj M.obj) := injective_of_finite_projective
  let τ := envelopingForm t u
  let J := ModuleCat.of (Alg k R S) (Fin (Module.finrank k M) → Alg k R S)
  let : Module.Projective R (Obj J) := freeLeftProjective _
  let i : M.obj ⟶ J := ModuleCat.ofHom (M.embed τ)
  let q : J ⟶ (M.cosyzygy τ).obj := ModuleCat.ofHom (LinearMap.range (M.embed τ)).mkQ
  apply projective_cokernel_of_injective (leftMap i) (leftMap q)
  · exact M.embed_injective τ
  · change Function.Surjective (Submodule.mkQ (LinearMap.range (M.embed τ)))
    exact Submodule.mkQ_surjective _
  · change Function.Exact (M.embed τ) (Submodule.mkQ (LinearMap.range (M.embed τ)))
    intro x
    exact Submodule.Quotient.mk_eq_zero _

lemma cosyzygy_right_projective [Module.Projective Sᵐᵒᵖ (Obj M.obj)] :
    Module.Projective Sᵐᵒᵖ (Obj (M.cosyzygy (envelopingForm t u)).obj) := by
  let : Module.Finite Sᵐᵒᵖ (Obj M.obj) := Module.Finite.of_restrictScalars_finite k Sᵐᵒᵖ _
  let : Module.Injective Sᵐᵒᵖ Sᵐᵒᵖ := u.op.injective
  let : Module.Injective Sᵐᵒᵖ (Obj M.obj) := injective_of_finite_projective
  let τ := envelopingForm t u
  let J := ModuleCat.of (Alg k R S) (Fin (Module.finrank k M) → Alg k R S)
  let : Module.Projective Sᵐᵒᵖ (Obj J) := freeRightProjective _
  let i : M.obj ⟶ J := ModuleCat.ofHom (M.embed τ)
  let q : J ⟶ (M.cosyzygy τ).obj := ModuleCat.ofHom (LinearMap.range (M.embed τ)).mkQ
  apply projective_cokernel_of_injective (rightMap i) (rightMap q)
  · exact M.embed_injective τ
  · change Function.Surjective (Submodule.mkQ (LinearMap.range (M.embed τ)))
    exact Submodule.mkQ_surjective _
  · change Function.Exact (M.embed τ) (Submodule.mkQ (LinearMap.range (M.embed τ)))
    intro x
    exact Submodule.Quotient.mk_eq_zero _

theorem negative_side_projective (n : ℕ)
    [Module.Projective R (Obj M.obj)] [Module.Projective Sᵐᵒᵖ (Obj M.obj)] :
    Module.Projective R (Obj (M.negative (envelopingForm t u) n).obj) ∧
      Module.Projective Sᵐᵒᵖ (Obj (M.negative (envelopingForm t u) n).obj) := by
  induction n with
  | zero => change Module.Projective R (Obj M.obj) ∧ Module.Projective Sᵐᵒᵖ (Obj M.obj)
            exact ⟨inferInstance,inferInstance⟩
  | succ n ih =>
    let := ih.1
    let := ih.2
    exact ⟨cosyzygy_left_projective t u _,cosyzygy_right_projective t u _⟩

end Tachikawa.Enveloping

end
end OAI
