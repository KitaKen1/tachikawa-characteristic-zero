import OAI.RingTheory.Tachikawa.StableEquivalence
import OAI.RingTheory.Tachikawa.StableSyzygy
import OAI.RingTheory.Tachikawa.NakayamaTransfer

/-! Characteristic-independent excerpts from OpenAI Math HomProfile.lean,
fixed commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Source line ranges are recorded in vendor/openai-math/manifest.json.
Excerpt declarations are unchanged; imports and outer wrappers differ. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [Module.Injective R R]
variable {M N P Q M' N' : ModuleCat.{0} R}
variable [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]

omit [Module.Injective R R] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] in
lemma exact_square_difference_inverse
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M')
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N')
    (f : M →ₗ[R] N) (h : P →ₗ[R] Q) (g : M' →ₗ[R] N')
    (f' : N →ₗ[R] M) (h' : Q →ₗ[R] P) (g' : N' →ₗ[R] M')
    (hu : h.comp i = j.comp f) (hl : delta.comp h = g.comp pi)
    (hu' : h'.comp j = i.comp f') (hl' : pi.comp h' = g'.comp delta) :
    (h'.comp h - LinearMap.id).comp i = i.comp (f'.comp f - LinearMap.id) ∧
    pi.comp (h'.comp h - LinearMap.id) = (g'.comp g - LinearMap.id).comp pi := by
  constructor
  · simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
      LinearMap.comp_id, LinearMap.comp_assoc]
    rw [hu, ← LinearMap.comp_assoc, hu', LinearMap.comp_assoc]
  · simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
      LinearMap.comp_id]
    rw [← LinearMap.comp_assoc, hl', LinearMap.comp_assoc, hl, ← LinearMap.comp_assoc]

def StableEquiv.ofExactSquares
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (e : StableEquiv (k := k) M N)
    (h : P →ₗ[R] Q) (g : M' →ₗ[R] N')
    (h' : Q →ₗ[R] P) (g' : N' →ₗ[R] M')
    (hu : h.comp i = j.comp e.hom) (hl : delta.comp h = g.comp pi)
    (hu' : h'.comp j = i.comp e.inv) (hl' : pi.comp h' = g'.comp delta) :
    StableEquiv (k := k) M' N' where
  hom := g
  inv := g'
  inv_hom := by
    obtain ⟨a,b⟩ := exact_square_difference_inverse i pi j delta e.hom h g e.inv h' g'
      hu hl hu' hl'
    exact (exact_square_factors_iff i pi hi hex hpi i pi hi hex hpi
      _ _ _ a b).mp e.inv_hom
  hom_inv := by
    obtain ⟨a,b⟩ := exact_square_difference_inverse j delta i pi e.inv h' g' e.hom h g
      hu' hl' hu hl
    exact (exact_square_factors_iff j delta hj hex' hdelta j delta hj hex' hdelta
      _ _ _ a b).mp e.hom_inv

def StableEquiv.down
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (e : StableEquiv (k := k) M N) : StableEquiv (k := k) M' N' := by
  have H := exists_exact_square_down i pi hi hex hpi j delta hex' e.hom
  have H' := exists_exact_square_down j delta hj hex' hdelta i pi hex e.inv
  exact e.ofExactSquares i pi hi hex hpi j delta hj hex' hdelta
    H.choose H.choose_spec.choose H'.choose H'.choose_spec.choose
    H.choose_spec.choose_spec.1 H.choose_spec.choose_spec.2
    H'.choose_spec.choose_spec.1 H'.choose_spec.choose_spec.2

omit [Module.Injective R R] [Module.Finite R P] [Module.Finite R Q]
  [Module.Projective R Q] in

theorem exists_exact_square_up
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hex : Function.Exact i pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (g : M' →ₗ[R] N') :
    ∃ (h : P →ₗ[R] Q) (f : M →ₗ[R] N),
      h.comp i = j.comp f ∧ delta.comp h = g.comp pi := by
  obtain ⟨h,hh⟩ := Module.projective_lifting_property delta (g.comp pi) hdelta
  have hr (x : M) : (h.comp i) x ∈ LinearMap.range j := by
    apply (hex' _).mp
    have he := LinearMap.congr_fun hh (i x)
    change delta (h (i x)) = g (pi (i x)) at he
    change delta (h (i x)) = 0
    rw [he, (hex _).mpr ⟨x,rfl⟩, map_zero]
  let f := CokerAt.factorThrough j hj (h.comp i) hr
  exact ⟨h,f,(CokerAt.factorThrough_spec j hj (h.comp i) hr).symm,hh⟩

def StableEquiv.up
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (e : StableEquiv (k := k) M' N') : StableEquiv (k := k) M N := by
  have H := exists_exact_square_up i pi hex j delta hj hex' hdelta e.hom
  have H' := exists_exact_square_up j delta hex' i pi hi hex hpi e.inv
  let h := H.choose
  let f := H.choose_spec.choose
  let h' := H'.choose
  let f' := H'.choose_spec.choose
  have hu : h.comp i = j.comp f := H.choose_spec.choose_spec.1
  have hl : delta.comp h = e.hom.comp pi := H.choose_spec.choose_spec.2
  have hu' : h'.comp j = i.comp f' := H'.choose_spec.choose_spec.1
  have hl' : pi.comp h' = e.inv.comp delta := H'.choose_spec.choose_spec.2
  refine ⟨f,f',?_,?_⟩
  · obtain ⟨a,b⟩ := exact_square_difference_inverse i pi j delta f h e.hom f' h' e.inv
      hu hl hu' hl'
    exact (exact_square_factors_iff i pi hi hex hpi i pi hi hex hpi
      _ _ _ a b).mpr e.inv_hom
  · obtain ⟨a,b⟩ := exact_square_difference_inverse j delta i pi f' h' e.inv f h e.hom
      hu' hl' hu hl
    exact (exact_square_factors_iff j delta hj hex' hdelta j delta hj hex' hdelta
      _ _ _ a b).mpr e.hom_inv
end Tachikawa


namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : ComplexExact P)
  (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j))

def cosyCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) :
    StableEquiv (k := k) (M.cosyzygy t).obj (ModuleCat.of R (CokerAt P (j-1))) := by
  let : Module.Injective R R := t.injective
  let := fin (j-1)
  let := proj (j-1)
  exact StableEquiv.down (P := ModuleCat.of R (Fin (Module.finrank k M) → R))
    (Q := P.X (j-1)) (M.embed t) (M.cosyzygyProjection t) (M.embed_injective t)
    (M.cosyzygyProjection_exact t) (M.cosyzygyProjection_surjective t)
    (CokerAt.δ P j (j-1)) (CokerAt.π P (j-1))
    (CokerAt.δ_injective P hP j (j-1) (by omega))
    (CokerAt.δ_π_exact P j (j-1) (by omega)) (CokerAt.π_surjective P (j-1)) e

def syzyCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) :
    StableEquiv (k := k) M.syzygy.obj (ModuleCat.of R (CokerAt P (j+1))) := by
  let : Module.Injective R R := t.injective
  let := fin j
  let := proj j
  exact StableEquiv.up (P := ModuleCat.of R (Fin M.cover.rank → R))
    (Q := P.X j) M.syzygyInclusion M.cover.map M.syzygyInclusion_injective
    M.syzygyInclusion_exact M.cover.surjective
    (CokerAt.δ P (j+1) j) (CokerAt.π P j)
    (CokerAt.δ_injective P hP (j+1) j rfl)
    (CokerAt.δ_π_exact P (j+1) j rfl) (CokerAt.π_surjective P j) e

def negativeCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) (n : ℕ) :
    StableEquiv (k := k) (M.negative t n).obj (ModuleCat.of R (CokerAt P (j-(n:ℤ)))) := by
  induction n with
  | zero =>
    change StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P (j-0)))
    rw [sub_zero]
    exact e
  | succ n ih =>
    change StableEquiv (k := k) ((M.negative t n).cosyzygy t).obj _
    rw [show j-((n+1:ℕ):ℤ) = (j-(n:ℤ))-1 by omega]
    exact cosyCokerStableEquiv t P hP fin proj _ _ ih

def positiveCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) (n : ℕ) :
    StableEquiv (k := k) (M.positive n).obj (ModuleCat.of R (CokerAt P (j+(n:ℤ)))) := by
  induction n with
  | zero =>
    change StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P (j+0)))
    rw [add_zero]
    exact e
  | succ n ih =>
    change StableEquiv (k := k) (M.positive n).syzygy.obj _
    rw [show j+((n+1:ℕ):ℤ) = (j+(n:ℤ))+1 by omega]
    exact syzyCokerStableEquiv t P hP fin proj _ _ ih

end Tachikawa



namespace Tachikawa
variable {k R M N N' : Type} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
  [Module R M] [Module R N] [Module R N']
  [Module k N] [Module k N'] [IsScalarTower k R N] [IsScalarTower k R N']

def stablePostEquiv (e : N ≃ₗ[R] N') :
    StableHom (k := k) (R := R) (M := M) (N := N) ≃ₗ[k]
      StableHom (k := k) (R := R) (M := M) (N := N') :=
  { stablePostcompose e.toLinearMap with
    invFun := stablePostcompose e.symm.toLinearMap
    left_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      change stableClass (k := k) (e.symm.toLinearMap.comp (e.toLinearMap.comp f)) = stableClass (k := k) f
      congr 1
      ext z
      exact e.symm_apply_apply (f z)
    right_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      change stableClass (k := k) (e.toLinearMap.comp (e.symm.toLinearMap.comp f)) = stableClass (k := k) f
      congr 1
      ext z
      exact e.apply_symm_apply (f z) }
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : ComplexExact P)
  (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j))

def finiteCoker (j : ℤ) : FiniteModule k R where
  obj := ModuleCat.of R (CokerAt P j)
  finite := by
    let := fin j
    exact inferInstanceAs (Module.Finite R (P.X j ⧸ LinearMap.range (P.d (j+1) j).hom))

def completeCokerDuality (j : ℤ) (N : ModuleCat.{0} R) :
    StableMap (k := k) N (ModuleCat.of R (CokerAt P (j+1))) ≃ₗ[k]
      Module.Dual k (StableMap (k := k) (ModuleCat.of R (CokerAt P j)) N) := by
  let M := finiteCoker (k := k) P fin j
  let e := syzyCokerStableEquiv t P hP fin proj M j (StableEquiv.refl _)
  let e₀ := stablePostEquiv (k := k) (R := R) (M := N)
    (N := M.syzygy.obj) (N' := LinearMap.ker M.cover.map) (LinearEquiv.refl R _)
  exact (e.post N).symm.trans (e₀.trans
    (t.stableDualEquiv M.cover.map M.cover.surjective (M.embed t) (M.embed_injective t)
      M.syzygy.cover.map M.syzygy.cover.surjective))

end Tachikawa


namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ) (hP : ComplexExact P)

def cokerKernelEquiv (i : ℤ) : CokerAt P (i+1) ≃ₗ[R] LinearMap.ker (CokerAt.π P i) := by
  let f := (CokerAt.δ P (i+1) i).codRestrict (LinearMap.ker (CokerAt.π P i))
    (fun x => (CokerAt.δ_π_exact P (i+1) i rfl _).mpr ⟨x,rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact CokerAt.δ_injective P hP (i+1) i rfl (congrArg Subtype.val h)
  · intro y
    obtain ⟨x,hx⟩ := (CokerAt.δ_π_exact P (i+1) i rfl y).mp y.property
    exact ⟨x,Subtype.ext hx⟩

variable (Q : ChainComplex (ModuleCat R) ℤ) (hQ : ComplexExact Q)
  (fP : ∀ i, Module.Finite R (P.X i)) (pP : ∀ i, Module.Projective R (P.X i))
  (fQ : ∀ i, Module.Finite R (Q.X i)) (pQ : ∀ i, Module.Projective R (Q.X i))
  [Module.Injective R R]

def cokerStableHomSucc (i j : ℤ) :
    StableMap (k := k) (ModuleCat.of R (CokerAt P i)) (ModuleCat.of R (CokerAt Q j)) ≃ₗ[k]
    StableMap (k := k) (ModuleCat.of R (CokerAt P (i+1))) (ModuleCat.of R (CokerAt Q (j+1))) := by
  let := fP i
  let := pP i
  let := fQ j
  let := pQ j
  let e := StableShift.equiv (k := k) (CokerAt.π P i) (CokerAt.π Q j)
    (CokerAt.π_surjective Q j) (CokerAt.π_surjective P i)
  let eP := StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of R (CokerAt P (i+1)))
    (N := ModuleCat.of R (LinearMap.ker (CokerAt.π P i))) (cokerKernelEquiv P hP i)
  let eQ := StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of R (CokerAt Q (j+1)))
    (N := ModuleCat.of R (LinearMap.ker (CokerAt.π Q j))) (cokerKernelEquiv Q hQ j)
  exact e.trans ((eP.pre _).symm.trans (eQ.post _).symm)

def cokerStableHomNat (i j : ℤ) (n : ℕ) :
    StableMap (k := k) (ModuleCat.of R (CokerAt P i)) (ModuleCat.of R (CokerAt Q j)) ≃ₗ[k]
    StableMap (k := k) (ModuleCat.of R (CokerAt P (i+(n:ℤ)))) (ModuleCat.of R (CokerAt Q (j+(n:ℤ)))) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero,add_zero,add_zero]
  | succ n ih =>
    have e := cokerStableHomSucc P hP Q hQ fP pP fQ pQ (i+(n:ℤ)) (j+(n:ℤ)) (k := k)
    rw [show i+((n+1:ℕ):ℤ) = i+(n:ℤ)+1 by omega,
      show j+((n+1:ℕ):ℤ) = j+(n:ℤ)+1 by omega]
    exact ih.trans e

def cokerStableHomTranslate (i j a : ℤ) :
    StableMap (k := k) (ModuleCat.of R (CokerAt P i)) (ModuleCat.of R (CokerAt Q j)) ≃ₗ[k]
    StableMap (k := k) (ModuleCat.of R (CokerAt P (i+a))) (ModuleCat.of R (CokerAt Q (j+a))) := by
  cases a with
  | ofNat n => exact cokerStableHomNat P hP Q hQ fP pP fQ pQ i j n
  | negSucc n =>
    have e := (cokerStableHomNat P hP Q hQ fP pP fQ pQ
      (i+Int.negSucc n) (j+Int.negSucc n) (n+1) (k := k)).symm
    rw [show i+Int.negSucc n+((n+1:ℕ):ℤ)=i by omega,
      show j+Int.negSucc n+((n+1:ℕ):ℤ)=j by omega] at e
    exact e

end Tachikawa


namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (C : ChainComplex (ModuleCat R) ℤ) (hC : TotallyAcyclic C)
  (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j))
  (N : ModuleCat R)

namespace CompleteStableExt
abbrev Q := completeResolutionTail C hC.1 proj

def cycles (n : ℕ) :
    (CokerAt C (n : ℤ) →ₗ[R] N) →ₗ[k]
      VectorSplit.Z (resolutionHom k R (Q C hC proj).complex N) n where
  toFun f := ⟨ModuleCat.ofHom (f.comp (CokerAt.π C (n : ℤ))), by
    erw [resolutionHom_memZ,completeResolutionTail_d]
    apply ModuleCat.hom_ext
    change (f.comp (CokerAt.π C (n : ℤ))).comp
      (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom = 0
    rw [LinearMap.comp_assoc, Nat.cast_add, Nat.cast_one, CokerAt.π_d,
      LinearMap.comp_zero]⟩
  map_add' f g := by rfl
  map_smul' c f := by rfl

def toExt (n : ℕ) : (CokerAt C (n : ℤ) →ₗ[R] N) →ₗ[k]
    Ext (ModuleCat.of R (CokerAt C 0)) N n :=
  (resolutionCyclesToExt N (Q C hC proj) n).comp (cycles C hC proj N n)

lemma toExt_surjective (n : ℕ) : Function.Surjective (toExt C hC proj N n (k := k)) := by
  intro x
  obtain ⟨f,hf,rfl⟩ := (Q C hC proj).extMk_surjective x (n+1) rfl
  rw [completeResolutionTail_d] at hf
  have hf' : f.hom.comp (C.d ((n : ℤ)+1) (n : ℤ)).hom = 0 := by
    have h := congrArg ModuleCat.Hom.hom hf
    change f.hom.comp (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom = 0 at h
    rw [show ((n+1 : ℕ) : ℤ) = (n : ℤ)+1 by omega] at h
    exact h
  use CokerAt.descend C (n : ℤ) f.hom hf'
  rfl

include fin in
lemma toExt_kernel (n : ℕ) :
    LinearMap.ker (toExt C hC proj N (n+1) (k := k)) =
      projectiveFactors (k := k) (M := CokerAt C ((n+1 : ℕ) : ℤ)) (N := N) := by
  ext f
  have hz : (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))).comp
      (C.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom = 0 := by
    rw [LinearMap.comp_assoc,CokerAt.π_d,LinearMap.comp_zero]
  have hdesc : CokerAt.descend C ((n+1 : ℕ) : ℤ)
      (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))) hz = f := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective C ((n+1 : ℕ) : ℤ) x
    rfl
  have hf : (Q C hC proj).complex.d (n+2) (n+1) ≫
      ModuleCat.ofHom (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))) = 0 := by
    rw [completeResolutionTail_d]
    apply ModuleCat.hom_ext
    change (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))).comp
      (C.d (((n+1)+1 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0
    rw [show (((n+1)+1 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ)+1 by omega]
    exact hz
  change (Q C hC proj).extMk (ModuleCat.ofHom (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))))
    (n+2) rfl hf = 0 ↔ _
  have hab := hC.factors_iff_boundary (k := k) fin proj ((n+1 : ℕ) : ℤ)
    (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))) hz
  rw [hdesc, show ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) by omega] at hab
  erw [(Q C hC proj).extMk_eq_zero_iff _ _ _ _ n rfl, hab]
  constructor
  · rintro ⟨g,hg⟩
    rw [completeResolutionTail_d] at hg
    exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩
  · rintro ⟨g,hg⟩
    refine ⟨ModuleCat.ofHom g,?_⟩
    rw [completeResolutionTail_d]
    exact ModuleCat.hom_ext hg

def equiv (n : ℕ) :
    StableHom (k := k) (R := R) (M := CokerAt C ((n+1 : ℕ) : ℤ)) (N := N) ≃ₗ[k]
      Ext (ModuleCat.of R (CokerAt C 0)) N (n+1) := by
  change ((CokerAt C ((n+1 : ℕ) : ℤ) →ₗ[R] N) ⧸ projectiveFactors (k := k)) ≃ₗ[k] _
  rw [← toExt_kernel C hC fin proj N n]
  exact (toExt C hC proj N (n+1)).quotKerEquivOfSurjective
    (toExt_surjective C hC proj N (n+1))

end CompleteStableExt
end Tachikawa

end
end OAI
