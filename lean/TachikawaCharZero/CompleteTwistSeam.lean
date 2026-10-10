import OAI.RingTheory.Tachikawa.TwistHom

/-! The degree-zero and degree-minus-one seams of an actual complete-resolution twist.
On a pointwise fixed module, every cycle into the degree-zero injective
term factors through the embedding. The lift therefore fixes those cycles;
symmetric free-Hom duality transfers the form multiplier to degree -1.
No characteristic or dimension-one hypothesis is used. -/
namespace TachikawaCharZero.CompleteTwistSeam
noncomputable section
open CategoryTheory OAI.Tachikawa OAI.Tachikawa.SymmetrizingForm
open scoped ModuleCat.Algebra

variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k:=k) (R:=R)) (σ : R ≃ₐ[k] R)
  (e : (twistFunctor σ).obj M.obj ≅ M.obj) (he : ∀ x, e.hom x=x)

include he in
theorem zero (x : VectorSplit.H (completeHom (k:=k) (M.complete t) M.obj) 0) :
    VectorSplit.Hmap (M.completeTwistHom t σ e) 0 x=x := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective _ x
  let f : (M.complete t).X 0 ⟶ M.obj := z.val
  rw [VectorSplit.Hmap_quotient]
  congr 1
  apply Subtype.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change e.hom (f ((M.positiveTwistLift σ e).hom.f 0 y)) = f y
  refine (he _).trans ?_
  have hp := congrArg (fun f => f y)
    (M.positiveTwistLift σ e).hom_f_zero_comp_π_f_zero
  change M.cover.map ((M.positiveTwistLift σ e).hom.f 0 y) =
    e.inv (M.cover.map y) at hp
  have hp' := hp.trans (twistIso_inv_apply σ e he (M.cover.map y))
  have hπ : CokerAt.π (M.complete t) 0 ((M.positiveTwistLift σ e).hom.f 0 y) =
      CokerAt.π (M.complete t) 0 y := M.augmentation_injective t hp'
  have hz := ModuleCat.hom_ext_iff.mp
    ((completeHom_memZ (M.complete t) M.obj 0 f).mp z.property)
  exact congrArg (CokerAt.descend (M.complete t) 0 f.hom hz) hπ

include he in
theorem lift_fixes_cycles
    (l : InjectiveResolution.Hom (M.coresolution t)
      (mappedCoresolution (twistFunctor σ) (M.coresolution t)) e.inv)
    (g : M.obj →ₗ[R] M.negTerm t 0)
    (hg : (M.negDifferential t 0).comp g=0) (x : M.obj) :
    l.hom.f 0 (g x)=g x := by
  have hz : M.negDifferential t 0 (g x)=0 := LinearMap.congr_fun hg x
  obtain ⟨y,hy⟩ := (M.embed_exact t (g x)).mp hz
  rw [← hy]
  have hl := l.ι_f_zero_comp_hom_f_zero
  rw [mappedCoresolution_ι_zero,M.coresolution_ι] at hl
  have h := congrArg (fun f => f y) hl
  change l.hom.f 0 (M.embed t y) = M.embed t (e.inv y) at h
  rw [twistIso_inv_apply σ e he] at h
  exact h

include he in
theorem negative_zero_diff_boundary
    (l : InjectiveResolution.Hom (M.coresolution t)
      (mappedCoresolution (twistFunctor σ) (M.coresolution t)) e.inv)
    (c : k) (hc : ∀ r, t.linear (σ r)=c*t.linear r)
    (f : M.negTerm t 0 →ₗ[R] M.obj) :
    ∃ a : M.negTerm t 1 →ₗ[R] M.obj,
      a.comp (M.negDifferential t 0) =
        (show M.negTerm t 0 →ₗ[R] M.obj from
          (l.hom.f 0 ≫ (twistFunctor σ).map (ModuleCat.ofHom f) ≫ e.hom).hom) - c • f := by
  apply (t.free_boundary_iff_pair_cycles (M.negDifferential t 0) _).mpr
  intro g hg
  rw [map_sub,map_smul]
  exact sub_eq_zero.mpr (t.freeHomDual_semilinear_adjoint σ _ M.obj c hc (l.hom.f 0) e.hom he
    g g (fun x => (lift_fixes_cycles M t σ e he l g hg x).symm) f)

include he in
theorem negative_one (c : k) (hc : ∀ r, t.linear (σ r)=c*t.linear r)
    (x : VectorSplit.H (completeHom (k:=k) (M.complete t) M.obj) (-1)) :
    VectorSplit.Hmap (M.completeTwistHom t σ e) (-1) x=c • x := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective _ x
  rw [VectorSplit.Hmap_quotient,← map_smul]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (VectorSplit.quotient_zero_iff_predecessor _ _).mpr
  obtain ⟨a,ha⟩ := negative_zero_diff_boundary M t σ e he
    (M.negativeTwistLift t σ e) c hc z.val.hom
  refine ⟨ModuleCat.ofHom a,?_⟩
  change (M.complete t).d (-2+1) (-2) ≫ ModuleCat.ofHom a = _
  rw [M.complete_d]
  apply ModuleCat.hom_ext
  exact ha

end
end TachikawaCharZero.CompleteTwistSeam
