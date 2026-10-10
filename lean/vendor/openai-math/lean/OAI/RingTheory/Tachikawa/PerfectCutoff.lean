import OAI.RingTheory.Tachikawa.StableShift
import OAI.RingTheory.Tachikawa.ComplexReflection

/-! Characteristic-independent excerpt from OpenAI Math Perfect.lean;
fixed commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Exact source range is recorded in vendor/openai-math/manifest.json.
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

lemma goodComponent_up_at
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l)
    (hq : Function.Exact (Q.d l j) (Q.d j i))
    [Module.Projective R (P.X j)]
    (a : P.X i →ₗ[R] Q.X j) (ha : GoodComponent f i j a) :
    ∃ b : P.X j →ₗ[R] Q.X l,
      (f.f j).hom = a.comp (P.d j i).hom + (Q.d l j).hom.comp b ∧
      GoodComponent f j l b := by
  let r := (f.f j).hom - a.comp (P.d j i).hom
  have hr (x : P.X j) : r x ∈ LinearMap.range (Q.d l j).hom := by
    have he := hq
    have hi : i = j-1 := by omega
    have hl : l = j+1 := by omega
    subst i
    subst l
    apply (he _).mp
    have hc := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm j (j-1))) x
    change Q.d j (j-1) (f.f j x) = f.f (j-1) (P.d j (j-1) x) at hc
    have hh := LinearMap.congr_fun ha x
    change f.f (j-1) (P.d j (j-1) x) - Q.d j (j-1) (a (P.d j (j-1) x)) = 0 at hh
    change Q.d j (j-1) (f.f j x - a (P.d j (j-1) x)) = 0
    rw [map_sub, hc]
    exact hh
  obtain ⟨b, hb⟩ := Module.projective_lifting_property
    (Q.d l j).hom.rangeRestrict (r.codRestrict _ hr) (by rintro ⟨x, y, rfl⟩; exact ⟨y, rfl⟩)
  have hb' : (Q.d l j).hom.comp b = r := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hb x)
  refine ⟨b, ?_, ?_⟩
  · rw [hb']
    dsimp only [r]
    abel
  · unfold GoodComponent
    rw [hb']
    dsimp only [r]
    rw [sub_sub_cancel, LinearMap.comp_assoc]
    have hd : (P.d j i).hom.comp (P.d l j).hom = 0 :=
      ModuleCat.hom_ext_iff.mp (P.d_comp_d _ _ _)
    rw [hd, LinearMap.comp_zero]

section Initial
variable {k : Type} [Field k] [Algebra k R] [Module.Injective R R]

lemma tail_initial_component (n : ℤ)
    (hp : Function.Exact (P.d (n+1) n) (P.d n (n-1)))
    (hf : CokerAt.map f n ∈ projectiveFactors (k := k)) :
    ∃ a : P.X (n-1) →ₗ[R] Q.X n, GoodComponent f (n-1) n a := by
  obtain ⟨J, hJf, hJp, u, v, hvu⟩ := hf
  let := hJf
  let := hJp
  let : Module.Injective R J := injective_of_finite_projective
  obtain ⟨u', hu⟩ := Module.Injective.extension_property R J
    (CokerAt P n) (P.X (n-1)) (CokerAt.ι P n) (CokerAt.ι_injective P n hp) u
  obtain ⟨v', hv⟩ := Module.projective_lifting_property (CokerAt.π Q n) v
    (CokerAt.π_surjective Q n)
  refine ⟨v'.comp u', ?_⟩
  unfold GoodComponent
  apply LinearMap.ext
  intro x
  have h : CokerAt.π Q n (f.f n x - v' (u' (P.d n (n-1) x))) = 0 := by
    have hu' := LinearMap.congr_fun hu (CokerAt.π P n x)
    change u' (P.d n (n-1) x) = u (CokerAt.π P n x) at hu'
    rw [map_sub, hu']
    have hv' := LinearMap.congr_fun hv (u (CokerAt.π P n x))
    dsimp only [LinearMap.comp_apply] at hv'
    have hvu' := LinearMap.congr_fun hvu (CokerAt.π P n x)
    change v (u (CokerAt.π P n x)) = CokerAt.π Q n (f.f n x) at hvu'
    rw [hv', hvu', sub_self]
  have hz := congrArg (CokerAt.ι Q n) h
  rw [map_zero, CokerAt.ι_π] at hz
  change Q.d n (n-1) (f.f n x - v' (u' (P.d n (n-1) x))) = 0 at hz
  have hc := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm n (n-1))) x
  change Q.d n (n-1) (f.f n x) = f.f (n-1) (P.d n (n-1) x) at hc
  change f.f (n-1) (P.d n (n-1) x) - Q.d n (n-1) (v' (u' (P.d n (n-1) x))) = 0
  rw [map_sub, hc] at hz
  exact hz
end Initial

lemma exact_tail_at (n : ℤ)
    (hq : ∀ j, n ≤ j → Function.Exact (Q.d (j+1) j) (Q.d j (j-1)))
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l) (hj : n ≤ j) :
    Function.Exact (Q.d l j) (Q.d j i) := by
  have hi : i=j-1 := by omega
  have hl : l=j+1 := by omega
  subst i
  subst l
  exact hq j hj

namespace TailNull
variable (n : ℤ)

def State (j : ℤ) :=
  {a : P.X j →ₗ[R] Q.X (j+1) // n-1 ≤ j → GoodComponent f j (j+1) a}

variable (hq : ∀ j, n ≤ j → Function.Exact (Q.d (j+1) j) (Q.d j (j-1)))
variable (pproj : ∀ j, Module.Projective R (P.X j))

def up (j : ℤ) (hj : n-1 ≤ j) (a : State f n j) : State f n (j+1) := by
  let := pproj (j+1)
  have he : Function.Exact (Q.d (j+1+1) (j+1)) (Q.d (j+1) j) := by
    exact exact_tail_at n hq j (j+1) (j+1+1) rfl rfl (by omega)
  let hh := goodComponent_up_at f j (j+1) (j+1+1) rfl rfl he a.val (a.property hj)
  exact ⟨hh.choose, fun _ => hh.choose_spec.2⟩

def stateMap {i : ℤ} (a : State f n i) (j : ℤ) (h : i+1=j) : P.X i →ₗ[R] Q.X j := by
  subst j
  exact a.val

def Step (i j : ℤ) (h : i+1=j) (a : State f n i) (b : State f n j) : Prop :=
  (f.f j).hom = (stateMap f n a j h).comp (P.d j i).hom + (Q.d (j+1) j).hom.comp b.val

lemma up_step (j : ℤ) (hj : n-1 ≤ j) (a : State f n j) :
    Step f n j (j+1) rfl a (up f n hq pproj j hj a) := by
  let := pproj (j+1)
  have he : Function.Exact (Q.d (j+1+1) (j+1)) (Q.d (j+1) j) := by
    exact exact_tail_at n hq j (j+1) (j+1+1) rfl rfl (by omega)
  exact (goodComponent_up_at f j (j+1) (j+1+1) rfl rfl he a.val (a.property hj)).choose_spec.1

variable (a₀ : State f n (n-1))

def component (j : ℤ) : State f n j :=
  j.inductionOn' (n-1) a₀ (fun j hj => up f n hq pproj j hj)
    (fun j hj _ => ⟨0, fun h => by omega⟩)

lemma component_up (j : ℤ) (hj : n-1 ≤ j) :
    component f n hq pproj a₀ (j+1) = up f n hq pproj j hj (component f n hq pproj a₀ j) :=
  Int.inductionOn'_add_one hj

lemma hasStep (i j : ℤ) (h : i+1=j) (hj : n ≤ j) :
    Step f n i j h (component f n hq pproj a₀ i) (component f n hq pproj a₀ j) := by
  subst j
  have hi : n-1 ≤ i := by omega
  rw [component_up f n hq pproj a₀ i hi]
  exact up_step f n hq pproj i hi _

def hom (i j : ℤ) : P.X i ⟶ Q.X j :=
  if h : i+1=j then ModuleCat.ofHom (stateMap f n (component f n hq pproj a₀ i) j h) else 0

lemma hom_zero (i j : ℤ) (h : ¬ (ComplexShape.down ℤ).Rel j i) :
    hom f n hq pproj a₀ i j = 0 := dite_eq_right h

lemma nullHomotopicMap_f (j : ℤ) (hj : n ≤ j) :
    (Homotopy.nullHomotopicMap (hom f n hq pproj a₀)).f j = f.f j := by
  rw [Homotopy.nullHomotopicMap_f
    (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)
    (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega)]
  simp only [hom, dite_eq_left (show j-1+1=j by omega)]
  apply ModuleCat.hom_ext
  exact (hasStep f n hq pproj a₀ (j-1) j (by omega) hj).symm

end TailNull

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace Cutoff
variable (Q : ChainComplex (ModuleCat.{0} R) ℤ) (n : ℤ)

def term (j : ℤ) : Submodule R (Q.X j) := if j ≤ n then ⊤ else ⊥

lemma d_mem (i j : ℤ) (x : term Q n i) : Q.d i j x.val ∈ term Q n j := by
  classical
  by_cases hj : j ≤ n
  · simp only [term, ite_eq_left hj, Submodule.mem_top]
  · by_cases hi : i ≤ n
    · have hrel : ¬ (ComplexShape.down ℤ).Rel i j := by
        change ¬ j+1=i
        omega
      rw [Q.shape i j hrel]
      exact (term Q n j).zero_mem
    · have hx : x.val = 0 := by simpa only [term, ite_eq_right hi, Submodule.mem_bot] using x.property
      rw [hx, map_zero]
      exact (term Q n j).zero_mem

def differential (i j : ℤ) : term Q n i →ₗ[R] term Q n j :=
  ((Q.d i j).hom.comp (term Q n i).subtype).codRestrict _ (d_mem Q n i j)

@[simp] lemma differential_val (i j : ℤ) (x : term Q n i) :
    (differential Q n i j x).val = Q.d i j x.val := rfl

def complex : ChainComplex (ModuleCat.{0} R) ℤ where
  X j := ModuleCat.of R (term Q n j)
  d i j := ModuleCat.ofHom (differential Q n i j)
  shape i j h := by
    apply ModuleCat.hom_ext
    ext x
    change Q.d i j x.val = 0
    rw [Q.shape i j h]
    rfl
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    ext x
    change Q.d j l (Q.d i j x.val) = 0
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (Q.d_comp_d i j l)) x.val

def inclusion : complex Q n ⟶ Q where
  f j := ModuleCat.ofHom (term Q n j).subtype
  comm' _ _ _ := rfl

variable {Q} {P : ChainComplex (ModuleCat.{0} R) ℤ}

def lift (f : P ⟶ Q) (h : ∀ j, n < j → f.f j = 0) : P ⟶ complex Q n where
  f j := ModuleCat.ofHom <| (f.f j).hom.codRestrict (term Q n j) (by
    intro x
    by_cases hj : j ≤ n
    · simp only [term, ite_eq_left hj, Submodule.mem_top]
    · change f.f j x ∈ term Q n j
      rw [h j (by omega)]
      exact (term Q n j).zero_mem)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    change Q.d i j (f.f i x) = f.f j (P.d i j x)
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm i j)) x

lemma lift_inclusion (f : P ⟶ Q) (h : ∀ j, n < j → f.f j = 0) :
    lift n f h ≫ inclusion Q n = f := by
  ext j x
  rfl

lemma term_subsingleton (j : ℤ) (h : n < j) : Subsingleton (term Q n j) := by
  simpa only [term, ite_eq_right (show ¬ j ≤ n by omega)] using
    (inferInstance : Subsingleton (⊥ : Submodule R (Q.X j)))

lemma term_projective (j : ℤ) [Module.Projective R (Q.X j)] :
    Module.Projective R (term Q n j) := by
  classical
  by_cases h : j ≤ n
  · have he : term Q n j = ⊤ := ite_eq_left h
    exact Module.Projective.of_equiv ((LinearEquiv.ofEq _ _ he).trans
      (Submodule.topEquiv : (⊤ : Submodule R (Q.X j)) ≃ₗ[R] Q.X j)).symm
  · have := term_subsingleton (Q := Q) n j (by omega)
    infer_instance

lemma term_finite (j : ℤ) [Module.Finite R (Q.X j)] : Module.Finite R (term Q n j) := by
  classical
  by_cases h : j ≤ n
  · have he : term Q n j = ⊤ := ite_eq_left h
    exact Module.Finite.equiv ((LinearEquiv.ofEq _ _ he).trans
      (Submodule.topEquiv : (⊤ : Submodule R (Q.X j)) ≃ₗ[R] Q.X j)).symm
  · have := term_subsingleton (Q := Q) n j (by omega)
    infer_instance

lemma term_subsingleton_below (l : ℤ) (hQ : ∀ j, j < l → Subsingleton (Q.X j))
    (j : ℤ) (hj : j < l) : Subsingleton (term Q n j) := by
  let := hQ j hj
  infer_instance

end Cutoff
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable [Module.Injective R R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

theorem perfect_factorization (f : P ⟶ Q) (n l : ℤ)
    (hp : Function.Exact (P.d (n+1) n) (P.d n (n-1)))
    (hq : ∀ j, n ≤ j → Function.Exact (Q.d (j+1) j) (Q.d j (j-1)))
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qproj : ∀ j, Module.Projective R (Q.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j))
    (qbound : ∀ j, j < l → Subsingleton (Q.X j))
    (hf : CokerAt.map f n ∈ projectiveFactors (k := k)) :
    ∃ (K : ChainComplex (ModuleCat.{0} R) ℤ) (a : P ⟶ K) (b : K ⟶ Q),
      Nonempty (Homotopy f (a ≫ b)) ∧
      (∀ j, Module.Projective R (K.X j)) ∧
      (∀ j, Module.Finite R (K.X j)) ∧
      (∀ j, j < l ∨ n ≤ j → Subsingleton (K.X j)) := by
  obtain ⟨a₀, ha₀⟩ := tail_initial_component f n hp hf
  let astart : TailNull.State f n (n-1) := by
    unfold TailNull.State
    have hi : n-1+1=n := by omega
    rw [hi]
    exact ⟨a₀, fun _ => ha₀⟩
  let h := TailNull.hom f n hq pproj astart
  let z := Homotopy.nullHomotopicMap h
  let f' := f-z
  have hf' (j : ℤ) (hj : n-1 < j) : f'.f j = 0 := by
    change f.f j - z.f j = 0
    rw [TailNull.nullHomotopicMap_f f n hq pproj astart j (by omega)]
    exact sub_self _
  let a := Cutoff.lift (n-1) f' hf'
  refine ⟨Cutoff.complex Q (n-1), a, Cutoff.inclusion Q (n-1), ?_, ?_, ?_, ?_⟩
  · have he : a ≫ Cutoff.inclusion Q (n-1) = f' := Cutoff.lift_inclusion (n-1) f' hf'
    rw [he]
    apply Nonempty.intro
    refine Homotopy.equivSubZero.symm ?_
    have hz : f-f'=z := by dsimp only [f']; abel
    rw [hz]
    exact Homotopy.nullHomotopy h (TailNull.hom_zero f n hq pproj astart)
  · intro j
    let := qproj j
    exact Cutoff.term_projective (Q := Q) (n-1) j
  · intro j
    let := qfin j
    exact Cutoff.term_finite (Q := Q) (n-1) j
  · intro j hj
    rcases hj with hj | hj
    · exact Cutoff.term_subsingleton_below (n-1) l qbound j hj
    · exact Cutoff.term_subsingleton (n-1) j (by omega)

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [Module.Injective R R]
variable {P Q : CochainComplex (ModuleCat.{0} R) ℤ}

theorem cochain_perfect_factorization (f : P ⟶ Q) (n l : ℤ)
    (hp : Function.Exact ((reflectCochain P).d (n+1) n) ((reflectCochain P).d n (n-1)))
    (hq : ∀ j, n ≤ j → Function.Exact ((reflectCochain Q).d (j+1) j)
      ((reflectCochain Q).d j (j-1)))
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qproj : ∀ j, Module.Projective R (Q.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j))
    (qbound : ∀ j, -l < j → Subsingleton (Q.X j))
    (hf : CokerAt.map (reflectCochainMap f) n ∈ projectiveFactors (k := k)) :
    ∃ (L : CochainComplex (ModuleCat.{0} R) ℤ)
      (a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
      (b : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj Q),
      a ≫ b = DerivedCategory.Q.map f ∧
      (∀ j, Module.Projective R (L.X j)) ∧
      (∀ j, Module.Finite R (L.X j)) ∧
      (∀ j, j < -n+1 ∨ -l < j → IsZero (L.X j)) := by
  obtain ⟨L,a,b,⟨H⟩,hproj,hfin,hbound⟩ := perfect_factorization
    (reflectCochainMap f) n l hp hq (fun j => pproj (-j))
      (fun j => qproj (-j)) (fun j => qfin (-j))
      (fun j hj => qbound (-j) (by omega)) hf
  let a' := (reflectCochainIso P).inv ≫ reflectChainMap a
  let b' := reflectChainMap b ≫ (reflectCochainIso Q).hom
  refine ⟨reflectChain L, DerivedCategory.Q.map a', DerivedCategory.Q.map b', ?_,
    (fun j => hproj (-j)), (fun j => hfin (-j)), ?_⟩
  · have he : (reflectCochainIso P).inv ≫ reflectChainMap (reflectCochainMap f) ≫
      (reflectCochainIso Q).hom = f := by
      rw [reflectCochainIso_natural, Iso.inv_hom_id_assoc]
    have H' := ((reflectChainHomotopy H).compLeft (reflectCochainIso P).inv).compRight
      (reflectCochainIso Q).hom
    have hH := DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{0} R) H'
    rw [Category.assoc,he] at hH
    rw [← Functor.map_comp]
    exact hH.symm.trans (congrArg DerivedCategory.Q.map (by rfl))
  · intro j hj
    exact ModuleCat.isZero_iff_subsingleton.mpr (hbound (-j) (by omega))

end Tachikawa

end
end OAI
