import TachikawaCharZero.InducedHomology
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! Ordinary Ext over the rational symmetric starting algebra.
Four concrete short exact sequences give a three-degree period. Using cycles
instead of the truncated quotient avoids an additional quotient comparison.
The generic short-exact and Ext-equivalence arguments are adapted from
OpenAI Math's Tachikawa/Period.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
The characteristic-zero complex and its defect are the checked local ones. -/
namespace TachikawaCharZero.Induced
universe v
noncomputable section
open CategoryTheory CategoryTheory.Abelian Resolution
open scoped ModuleCat.Algebra

abbrev X := ModuleCat.of T S
abbrev U := LinearMap.range tiMap
abbrev B₁ := LinearMap.range (teDiff 1)
abbrev B₂ := LinearMap.range (teDiff (-2))
abbrev UObj := ModuleCat.of T U
abbrev B₁Obj := ModuleCat.of T B₁
abbrev B₂Obj := ModuleCat.of T B₂
abbrev CyclesObj := ModuleCat.of T Cycles

abbrev linearShort {M N P : Type v} [AddCommGroup M] [Module T M]
    [AddCommGroup N] [Module T N] [AddCommGroup P] [Module T P]
    (f : M →ₗ[T] N) (g : N →ₗ[T] P) (h : Function.Exact f g) :
    ShortComplex (ModuleCat T) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    (ModuleCat.hom_ext h.linearMap_comp_eq_zero)

theorem linearShort_exact {M N P : Type v} [AddCommGroup M] [Module T M]
    [AddCommGroup N] [Module T N] [AddCommGroup P] [Module T P]
    (f : M →ₗ[T] N) (g : N →ₗ[T] P) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (linearShort f g h).ShortExact := by
  have : Mono (linearShort f g h).f := (ModuleCat.mono_iff_injective _).mpr hf
  have : Epi (linearShort f g h).g := (ModuleCat.epi_iff_surjective _).mpr hg
  exact ⟨(ShortComplex.moduleCat_exact_iff _).mpr (fun x => (h x).mp)⟩

theorem rangeRestrict_surjective {M N : Type*} [AddCommGroup M] [Module T M]
    [AddCommGroup N] [Module T N] (f : M →ₗ[T] N) :
    Function.Surjective f.rangeRestrict := by
  rintro ⟨y,x,hx⟩
  exact ⟨x,Subtype.ext hx⟩

theorem initial_exact : Function.Exact U.subtype aug := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (aug_exact x).mp hx
    exact ⟨⟨x,y,hy⟩,rfl⟩
  · rintro ⟨⟨x,y,hy⟩,rfl⟩
    change aug x=0
    rw [← hy]
    exact aug_exact.apply_apply_eq_zero y

abbrev initialShort := linearShort U.subtype aug initial_exact
theorem initial_shortExact : initialShort.ShortExact :=
  linearShort_exact _ _ _ Subtype.val_injective aug_surjective

theorem middle_exact : Function.Exact B₁.subtype tiMap.rangeRestrict := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (tiMap_exact x).mp (congrArg Subtype.val hx)
    exact ⟨⟨x,y,hy⟩,rfl⟩
  · rintro ⟨⟨x,y,hy⟩,rfl⟩
    apply Subtype.ext
    change tiMap x=0
    rw [← hy]
    exact tiMap_exact.apply_apply_eq_zero y

abbrev middleShort := linearShort B₁.subtype tiMap.rangeRestrict middle_exact
theorem middle_shortExact : middleShort.ShortExact :=
  linearShort_exact _ _ _ Subtype.val_injective (rangeRestrict_surjective _)

abbrev upperShort := linearShort Cycles.subtype (teDiff 1).rangeRestrict (fun x => by
  constructor
  · intro hx
    exact ⟨⟨x,congrArg Subtype.val hx⟩,rfl⟩
  · rintro ⟨y,rfl⟩
    exact Subtype.ext y.property)
theorem upper_shortExact : upperShort.ShortExact :=
  linearShort_exact _ _ _ Subtype.val_injective (rangeRestrict_surjective _)

def lowerInclusion : B₂ →ₗ[T] Cycles where
  toFun b := ⟨b.val,by
    obtain ⟨a,ha⟩ := b.property
    rw [← ha]
    simpa using teDiff_sq 1 a⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem lower_exact : Function.Exact lowerInclusion twoAug := by
  intro x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := (twoAug_exact x).mp hx
    exact ⟨⟨x.val,a,congrArg Subtype.val ha⟩,Subtype.ext rfl⟩
  · rintro ⟨⟨x,a,ha⟩,rfl⟩
    have he : lowerInclusion ⟨x,a,ha⟩=boundary a := Subtype.ext ha.symm
    rw [he]
    exact twoAug_exact.apply_apply_eq_zero a

abbrev lowerShort := linearShort lowerInclusion twoAug lower_exact
theorem lower_shortExact : lowerShort.ShortExact :=
  linearShort_exact _ _ _ (fun _ _ h => Subtype.ext (congrArg (fun z : Cycles => z.val) h))
    twoAug_surjective

def boundaryResolution : ProjectiveResolution B₂Obj :=
  resolutionOfExact _ (fun _ => ModuleCat.of T TE)
    (fun n => ModuleCat.ofHom (teDiff ((-2:ℚ)^(n+2))))
    (ModuleCat.ofHom (teDiff (-2)).rangeRestrict)
    (fun n => teDiff_exact_all_degrees (n+1))
    (fun x => by
      constructor
      · intro hx
        exact (teDiff_exact_all_degrees 0 x).mp (congrArg Subtype.val hx)
      · rintro ⟨y,rfl⟩
        exact Subtype.ext ((teDiff_exact_all_degrees 0).apply_apply_eq_zero y))
    (rangeRestrict_surjective _) (fun _ => by infer_instance)

theorem boundary_ext_zero (n : ℕ) : Subsingleton (Ext B₂Obj X n) := by
  cases n with
  | zero =>
    have : Subsingleton (B₂Obj ⟶ X) := by
      apply subsingleton_of_forall_eq 0
      intro f
      have hh : ModuleCat.ofHom (teDiff (-2)).rangeRestrict ≫ f=0 :=
        ModuleCat.hom_ext (homTE_zero _)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x,y,hy⟩
      subst x
      exact congrArg (fun g : ModuleCat.of T TE ⟶ X => g y) hh
    exact Ext.addEquiv₀.injective.subsingleton
  | succ n =>
    let P := boundaryResolution
    apply subsingleton_of_forall_eq 0
    intro α
    obtain ⟨f,hf,rfl⟩ := P.extMk_surjective α (n+2) rfl
    have hz : f=0 := ModuleCat.hom_ext (homTE_zero f.hom)
    subst f
    exact P.extMk_zero _ _

def shiftEquiv {L : ShortComplex (ModuleCat T)} (hL : L.ShortExact) (n : ℕ)
    [Subsingleton (Ext L.X₂ X n)] [Subsingleton (Ext L.X₂ X (n+1))] :
    Ext L.X₁ X n ≃ₗ[ℚ] Ext L.X₃ X (n+1) :=
  LinearEquiv.ofBijective (hL.extClass.precompOfLinear ℚ X (by omega)) (by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hL X x (by omega) hx
      rw [Subsingleton.elim y 0,Ext.comp_zero] at hy
      exact hy.symm
    · intro x
      exact Ext.contravariant_sequence_exact₃ hL X x (Subsingleton.elim _ _) (by omega))

def quotientEquiv (n : ℕ) : Ext X X n ≃ₗ[ℚ] Ext CyclesObj X n :=
  LinearEquiv.ofBijective ((Ext.mk₀ lowerShort.g).precompOfLinear ℚ X (zero_add n)) (by
    constructor
    · cases n with
      | zero =>
        let : Epi lowerShort.g := lower_shortExact.epi_g
        exact Ext.precomp_mk₀_injective_of_epi X lowerShort.g
      | succ n =>
        apply LinearMap.ker_eq_bot.mp
        apply LinearMap.ker_eq_bot'.mpr
        intro x hx
        obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ lower_shortExact X x hx
          (n₀ := n) (by omega)
        let := boundary_ext_zero n
        rw [Subsingleton.elim y 0,Ext.comp_zero] at hy
        exact hy.symm
    · intro x
      let := boundary_ext_zero n
      exact Ext.contravariant_sequence_exact₂ lower_shortExact X x (Subsingleton.elim _ _))

theorem te_ext_zero (n : ℕ) : Subsingleton (Ext (ModuleCat.of T TE) X n) := by
  cases n with
  | zero =>
    have : Subsingleton (ModuleCat.of T TE ⟶ X) :=
      ⟨fun f g => ModuleCat.hom_ext ((homTE_zero f.hom).trans (homTE_zero g.hom).symm)⟩
    exact Ext.addEquiv₀.injective.subsingleton
  | succ n => exact Ext.subsingleton_of_projective _ _ n

def upperShift (n : ℕ) : Ext CyclesObj X n ≃ₗ[ℚ] Ext B₁Obj X (n+1) := by
  let := te_ext_zero n
  let := te_ext_zero (n+1)
  exact shiftEquiv upper_shortExact n

def middleShift (n : ℕ) : Ext B₁Obj X n ≃ₗ[ℚ] Ext UObj X (n+1) := by
  let := te_ext_zero n
  let := te_ext_zero (n+1)
  exact shiftEquiv middle_shortExact n

def initialShift (n : ℕ) : Ext UObj X (n+1) ≃ₗ[ℚ] Ext X X (n+2) := by
  let : Subsingleton (Ext initialShort.X₂ X (n+1)) := Ext.subsingleton_of_projective _ _ n
  let : Subsingleton (Ext initialShort.X₂ X (n+2)) := Ext.subsingleton_of_projective _ _ (n+1)
  exact shiftEquiv initial_shortExact (n+1)

def period (n : ℕ) : Ext X X n ≃ₗ[ℚ] Ext X X (n+3) :=
  (((quotientEquiv n).trans (upperShift n)).trans (middleShift (n+1))).trans (initialShift (n+1))

def tau : Ext X X 3 := period 0 (Ext.mk₀ (𝟙 X))

theorem tau_ne_zero : tau≠0 := by
  intro h
  have he : Ext.mk₀ (𝟙 X)=0 := (period 0).injective (h.trans (map_zero (period 0)).symm)
  have hi : (𝟙 X)=0 := by
    have hh := congrArg Ext.homEquiv₀ he
    simpa using hh
  have hh : (1:ℚ)=0 := congrArg (fun f : X ⟶ X => (show ℚ from f (show S from (1:ℚ)))) hi
  exact one_ne_zero hh

theorem S_not_projective : ¬ Module.Projective T S := by
  intro h
  let := h
  let : Subsingleton (Ext X X 3) := Ext.subsingleton_of_projective _ _ 2
  exact tau_ne_zero (Subsingleton.elim _ _)

theorem range_hom_zero {M : Type*} [AddCommGroup M] [Module T M]
    (d : TE →ₗ[T] M) (f : d.range →ₗ[T] S) : f=0 := by
  have hh := homTE_zero (f.comp d.rangeRestrict)
  apply LinearMap.ext
  rintro ⟨x,y,hy⟩
  change f ⟨x,_⟩=0
  subst x
  exact LinearMap.congr_fun hh y

theorem U_ext_zero : Subsingleton (Ext UObj X 0) := by
  have : Subsingleton (UObj ⟶ X) :=
    ⟨fun f g => ModuleCat.hom_ext ((range_hom_zero tiMap f.hom).trans
      (range_hom_zero tiMap g.hom).symm)⟩
  exact Ext.addEquiv₀.injective.subsingleton

theorem B₁_ext_zero : Subsingleton (Ext B₁Obj X 0) := by
  have : Subsingleton (B₁Obj ⟶ X) :=
    ⟨fun f g => ModuleCat.hom_ext ((range_hom_zero (teDiff 1) f.hom).trans
      (range_hom_zero (teDiff 1) g.hom).symm)⟩
  exact Ext.addEquiv₀.injective.subsingleton

theorem self_ext_one_zero : Subsingleton (Ext X X 1) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let : Subsingleton (Ext initialShort.X₂ X 1) := Ext.subsingleton_of_projective _ _ 0
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ initial_shortExact X x
    (Subsingleton.elim _ _) (n₀ := 0) (by omega)
  let := U_ext_zero
  rw [Subsingleton.elim y 0,Ext.comp_zero] at hy
  exact hy.symm

theorem self_ext_two_zero : Subsingleton (Ext X X 2) := by
  let := B₁_ext_zero
  let : Subsingleton (Ext UObj X 1) := (middleShift 0).symm.injective.subsingleton
  exact (initialShift 0).symm.injective.subsingleton

end
end TachikawaCharZero.Induced
