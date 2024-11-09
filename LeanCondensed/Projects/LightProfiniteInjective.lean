/-
Authors: Lenny Taelman
-/

import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.LightProfinite.AsLimit


-- import LeanCondensed.Mathlib.Condensed.Light.Limits

/-!

# Project: show that non-empty light profinite spaces are injective in all profinite spaces

This is used in particular in the proof the the null sequence module is projective
in light condensed abelian groups.

-/

noncomputable section


universe u


open Set

-- For every closed ⊆ open in a profinite, there is an intermediate clopen

lemma clopen_of_closed_subset_open  (X : Profinite.{u}) (Z U : Set X)
    (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z ⊆ U) :
    ∃ C : Set X, IsClopen C ∧ Z ⊆ C ∧ C ⊆ U := by
  -- every z ∈ Z has clopen neighborhood V z ⊆ U
  choose V hV using fun (z : Z) ↦ compact_exists_isClopen_in_isOpen hU (hZU z.property)
  -- the V z cover Z
  have V_cover : Z ⊆ iUnion V := fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- there is a finite subcover
  choose I hI using IsCompact.elim_finite_subcover (IsClosed.isCompact hZ)
    V (fun z ↦ (hV z).1.2) V_cover
  -- the union C of this finite subcover does the job
  let C := ⋃ (i ∈ I), V i
  have C_clopen : IsClopen C := Finite.isClopen_biUnion (Finset.finite_toSet I)
    (fun i _ ↦ (hV i).1)
  have C_subset_U : C ⊆ U := by simp_all only [iUnion_subset_iff, C, implies_true]
  exact ⟨C, C_clopen, hI, C_subset_U⟩


open Fin


/-
  Let X be profinite, D i ⊆ X a finite family of clopens, and Z i ⊆ D i closed.
  Assume that all the Z i are disjoint. Then there exist clopens Z i ⊆ C i ⊆ D i
  with the C i disjoint, and such that ∪ C i = ∪ D i
-/

lemma clopen_partition_of_disjoint_closeds_in_clopens
    (X : Profinite.{u}) (n : ℕ) (Z : Fin n → Set X) (D : Fin n → Set X)
    (Z_closed : ∀ i, IsClosed (Z i)) (D_clopen : ∀ i, IsClopen (D i))
    (Z_subset_D : ∀ i, Z i ⊆ D i) (Z_disj : ∀ i j, i < j → Disjoint (Z i) (Z j) ) :
    ∃ C : Fin n → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, Z i ⊆ C i) ∧ (∀ i, C i ⊆ D i) ∧
    (⋃ i, D i) ⊆ (⋃ i, C i)  ∧ (∀ i j, i < j → Disjoint (C i) (C j)) := by
  induction n
  case zero =>
    -- single Z given, can take C 0 = D
    use fun _ ↦ univ -- empty range, can use junk
    exact ⟨elim0, fun i ↦ elim0 i, fun i ↦ elim0 i, by
      simp only [iUnion_of_empty]; trivial, fun i j ↦ elim0 i⟩
  case succ n ih =>
    -- let Z' be the restriction of Z along succ : Fin n → Fin (n+1)
    let Z' : Fin n → Set X := fun i ↦ Z (succ i)
    have Z'_closed (i : Fin n) : IsClosed (Z' i) := Z_closed (succ i)
    have Z'_disj (i j : Fin n) (hij : i < j) : Disjoint (Z' i) (Z' j)  :=
      Z_disj (succ i) (succ j) (succ_lt_succ_iff.mpr hij)
    -- find Z 0 ⊆ V ⊆ D 0 \ ⋃ Z' using clopen_sandwich
    let U : Set X  := D 0 \ iUnion Z'
    have U_open : IsOpen U := IsOpen.sdiff (D_clopen 0).2
      (isClosed_iUnion_of_finite Z'_closed)
    have Z0_subset_U : Z 0 ⊆ U := subset_diff.mpr ⟨Z_subset_D 0,
      disjoint_iUnion_right.mpr (fun i ↦ Z_disj 0 (succ i) (succ_pos ↑↑i))⟩
    obtain ⟨V, V_clopen, Z0_subset_V, V_subset_U⟩ :=
      clopen_of_closed_subset_open X (Z 0) U (Z_closed 0) U_open Z0_subset_U
    have V_subset_D0 : V ⊆ D 0 := subset_trans V_subset_U diff_subset
    -- choose Z' i ⊆ C' i ⊆ D' i = D i.succ \ V using induction hypothesis
    let D' : Fin n → Set X := fun i ↦ D (succ i) \ V
    have D'_clopen (i : Fin n): IsClopen (D' i) := IsClopen.diff (D_clopen i.succ) V_clopen
    have Z'_subset_D' (i : Fin n) : Z' i ⊆ D' i := by
      apply subset_diff.mpr
      constructor
      · exact Z_subset_D (succ i)
      · apply Disjoint.mono_right V_subset_U
        exact Disjoint.mono_left (subset_iUnion_of_subset i fun ⦃_⦄ h ↦ h) disjoint_sdiff_right
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_D', C'_cover_D', C'_disj⟩ :=
      ih Z' D' Z'_closed D'_clopen Z'_subset_D' Z'_disj
    have C'_subset_D (i : Fin n): C' i ⊆ D (succ i) := subset_trans (C'_subset_D' i) diff_subset
    -- now choose C0 = D 0 \ ⋃ C' i
    let C0 : Set X := D 0 \ iUnion (fun i ↦ C' i)
    have C0_subset_D0 : C0 ⊆ D 0 := diff_subset
    have C0_clopen : IsClopen C0 := IsClopen.diff (D_clopen 0) (isClopen_iUnion_of_finite C'_clopen)
    have Z0_subset_C0 : Z 0 ⊆ C0 := by
      unfold C0
      apply subset_diff.mpr
      constructor
      · exact Z_subset_D 0
      · apply Disjoint.mono_left Z0_subset_V
        exact disjoint_iUnion_right.mpr fun i ↦ Disjoint.mono_right (C'_subset_D' i) disjoint_sdiff_right
    -- patch together to define C := cases C0 C', and verify the needed properties
    let C : Fin (n+1) → Set X := cases C0 C'
    have C_clopen : ∀ i, IsClopen (C i) := cases C0_clopen C'_clopen
    have Z_subset_C : ∀ i, Z i ⊆ C i := cases Z0_subset_C0 Z'_subset_C'
    have C_subset_D : ∀ i, C i ⊆ D i := cases C0_subset_D0 C'_subset_D
    have C_cover_D : (⋃ i, D i) ⊆ (⋃ i, C i) := by -- messy, but I don't see easy simplification
      intro x hx
      simp
      by_cases hx0 : x ∈ C0
      · exact ⟨0, hx0⟩
      · by_cases hxD : x ∈ D 0
        · have hxC' : x ∈ iUnion C' := by
            rw [mem_diff] at hx0
            push_neg at hx0
            exact hx0 hxD
          obtain ⟨i, hi⟩ := mem_iUnion.mp hxC'
          exact ⟨i.succ, hi⟩
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          have hi' : i ≠ 0 := by
            intro h
            rw [h] at hi
            tauto
          let j := i.pred hi'
          have hij : i = j.succ := (pred_eq_iff_eq_succ hi').mp rfl
          rw [hij] at hi
          have hxD' : x ∈ ⋃ i, D' i := by
            apply mem_iUnion.mpr ⟨j, _⟩
            apply mem_diff_of_mem hi
            exact fun h ↦ hxD (V_subset_D0 h)
          apply C'_cover_D' at hxD'
          obtain ⟨k, hk⟩ := mem_iUnion.mp hxD'
          exact ⟨k.succ, hk⟩
    have C_disj (i j : Fin (n+1)) (hij : i < j) : Disjoint (C i) (C j) := by
      by_cases hi : i = 0
      · rw [hi]; rw [hi] at hij
        rw [(pred_eq_iff_eq_succ (pos_iff_ne_zero.mp hij)).mp rfl] -- j = succ _
        apply Disjoint.mono_right (subset_iUnion (fun i ↦ C' i) (j.pred (ne_zero_of_lt hij)))
        exact disjoint_sdiff_left
      · have hj : j ≠ 0 := ne_zero_of_lt hij
        rw [(pred_eq_iff_eq_succ hi).mp rfl, (pred_eq_iff_eq_succ hj).mp rfl]
        exact C'_disj (i.pred hi) (j.pred hj) (pred_lt_pred_iff.mpr hij)
    exact ⟨C, C_clopen, Z_subset_C, C_subset_D, C_cover_D, C_disj⟩


/-
  this is the key statement for the inductive proof of injectivity. Given
  a commutative square
      X >-f->  Y
      |g       |g'
      v        v
      S -f'->> T
  where Y is profinite, S is finite, f is injective and f' is surjective,
  there exists a diagonal map k : Y → S making diagram commute.
-/


lemma key_lifting_lemma (X Y S T : Profinite.{u}) [Finite S]
  (f : X → Y) (hf : Continuous f) (f_inj : Function.Injective f)
  (f' : S → T) (f'_surj : Function.Surjective f')
  (g : X → S) (hg : Continuous g) (g' : Y → T) (hg' : Continuous g')
  (h_comm : g' ∘ f = f' ∘ g) :
  ∃ k : Y → S, (Continuous k) ∧ (f' ∘ k = g') ∧ (k ∘ f = g)  := by

  -- help the instance inference a bit: T is finite
  letI : Finite T := Finite.of_surjective f' f'_surj
  -- pick bijection between Fin n and S
  obtain ⟨n, φ, ψ, h1, h2⟩ := Finite.exists_equiv_fin S
  -- define Z i to be the image of the fiber of g at i
  let Z : Fin n → Set Y := fun i ↦ f '' (g⁻¹' {ψ i})
  have Z_closed (i) : IsClosed (Z i) :=
    (ClosedEmbedding.closed_iff_image_closed (Continuous.closedEmbedding hf f_inj)).mp
    (IsClosed.preimage hg isClosed_singleton)
  have Z_disj (i j) (hij : i < j) : Disjoint (Z i) (Z j) := by
    apply (disjoint_image_iff f_inj).mpr
    apply Disjoint.preimage g
    apply disjoint_singleton.mpr
    exact Function.Injective.ne (Function.LeftInverse.injective h2) (Fin.ne_of_lt hij)
  -- define D i to be the fiber of g' at f' i
  let D : Fin n → Set Y := fun i ↦ g' ⁻¹' ( {f' (ψ i)})
  have D_clopen i : IsClopen (D i) := IsClopen.preimage (isClopen_discrete {f' (ψ i)}) hg'
  have Z_subset_D i : Z i ⊆ D i := by
    intro z hz
    rw [mem_preimage]
    simp
    obtain ⟨x, hx1, hx2⟩ := (mem_image _ _ _).mp hz
    rw [←hx2]
    have h_comm' : g' (f x) = f' (g x) := congr_fun h_comm x
    convert rfl
    exact (eq_of_mem_singleton hx1).symm
  have D_cover_univ : univ ⊆ (⋃ i, D i) := by
    intro y _
    simp only [mem_iUnion]
    obtain ⟨s, hs⟩ := f'_surj (g' y)
    use φ s
    rw [mem_preimage, h1]
    exact hs.symm
  -- obtain clopens Z i ⊆ C i ⊆ D i with C i disjoint, covering Y
  obtain ⟨C, C_clopen, Z_subset_C, C_subset_D, C_cover_D, C_disj⟩ :=
    clopen_partition_of_disjoint_closeds_in_clopens Y n Z D Z_closed D_clopen Z_subset_D Z_disj
  have C_cover_univ : ⋃ i, C i = univ :=  univ_subset_iff.mp
    (subset_trans D_cover_univ C_cover_D)
  -- define k to be the unique map sending C i to ψ i
  have h_glue (i j : Fin n) (x : Y) (hxi : x ∈ C i) (hxj : x ∈ C j) :  ψ i = ψ j := by
    by_cases hij : i = j
    · exact congrArg ψ hij
    · by_cases hij' : i < j
      · exfalso
        exact Set.disjoint_iff.mp (C_disj i j hij') (mem_inter hxi hxj)
      · have hji' : j < i := lt_of_le_of_ne (not_lt.mp hij') (hij ∘ Eq.symm)
        exfalso
        exact Set.disjoint_iff.mp (C_disj j i hji') (mem_inter hxj hxi)
  let k := liftCover C (λ i _ ↦ ψ i) h_glue C_cover_univ
  -- now verify that k has the desired properties
  have h_f'k_g' : f' ∘ k = g' := by
    ext y
    simp
    -- y is contained in C i for some i
    have hy : y ∈ ⋃ i, C i := by
      rw [C_cover_univ]
      exact mem_univ y
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have hki : k y = ψ i := liftCover_of_mem hi
    rw [hki]
    exact symm (C_subset_D i hi)
  have h_kf_g : k ∘ f = g := by
    ext x
    simp
    let i := φ (g x)
    have hfC : f x ∈ Z i := by
      rw [mem_image]
      exact ⟨x, symm (h1 (g x)), rfl⟩
    have hC : f x ∈ C i := Z_subset_C i hfC
    have hki : k (f x) = ψ i := liftCover_of_mem hC
    rw [hki]
    exact (h1 (g x))
  have C_eq_fiber (i) : C i = k⁻¹' {ψ i} := by
    ext y
    constructor
    · exact liftCover_of_mem
    · rw [preimage_liftCover]
      simp
      intro j hji hj
      rw [Function.LeftInverse.injective h2 hji] at hj
      exact hj
  have h_cont : Continuous k := by
    have h_loc_cst : IsLocallyConstant k := by
      apply IsLocallyConstant.iff_isOpen_fiber.mpr
      intro s
      have hsi : s = ψ (φ s) := by rw [h1]
      rw [hsi, ← C_eq_fiber]
      exact (C_clopen (φ s)).2
    exact { isOpen_preimage := fun s _ ↦ h_loc_cst s }
  exact ⟨k, h_cont, h_f'k_g', h_kf_g⟩




open CategoryTheory
open CompHausLike
open ConcreteCategory

-- categorically stated version of key_lifiting_lemma

lemma key_lifting_lemma' (X Y S T : Profinite.{u}) [Finite S]
  (f : X ⟶ Y) [Mono f] (f' : S ⟶ T) [Epi f']
  (g : X ⟶ S) (g' : Y ⟶ T) (h_comm : f ≫ g' = g ≫ f') :
  ∃ k : Y ⟶ S, (k ≫ f' = g') ∧ (f ≫ k = g)  := by
  have h_comm' : (f ≫ g').toFun = (g ≫ f').toFun := congrArg _ h_comm
  obtain ⟨k_fun, k_cont, h2, h3⟩ := key_lifting_lemma X Y S T
    f.toFun f.continuous ((mono_iff_injective f).mp inferInstance)
    f'.toFun ((Profinite.epi_iff_surjective f').mp inferInstance)
    g.toFun g.continuous g'.toFun g'.continuous h_comm'
  exact ⟨⟨k_fun, k_cont⟩, ConcreteCategory.hom_ext_iff.mpr (congrFun h2),
    ConcreteCategory.hom_ext_iff.mpr (congrFun h3)⟩


-- warming up exercise: nonempty finite discrete spaces are injective in profinite spaces

lemma injective_of_finite (S : Profinite.{u}) [Nonempty S] [Finite S]:
  Injective (S) := by
  constructor
  intro X Y g f f_mono
  -- let f' : S ⟶ pt and g' : Y ⟶ pt be the unique maps
  let f' := Limits.terminalIsTerminal.from S
  let g' := Limits.terminalIsTerminal.from Y
  have f'_epi : Epi f' := by
    -- maybe try to show surjectivity instead?
    rw [Profinite.epi_iff_surjective f']
    intro t
    -- choose any a in S
    let a : S  := Nonempty.some inferInstance
    use a
    unfold f'
    unfold Limits.terminalIsTerminal

    sorry
  obtain ⟨k, _, h2⟩ := key_lifting_lemma' X Y S _ f f' g g' (Limits.terminal.hom_ext _ _)
  exact ⟨k, h2⟩






open Opposite Nat





/-
  Induction step:

      X        --f-->  Y
      |g' (n+1)        |k n
      v                v
      S' (n+1) --p n-> S' n

  find k n+1 : Y ⟶ S' (n+1) making both diagrams commute. That is:
   - h_up n+1 : k (n+1) ≫ p n = k n   **** recursive, requires k n
   - h_down n+1 : f ≫ k (n+1) = g' (n+1)
  Construction of k (n+1) through lifting lemma requires as input:
   - h_comm n : g' (n+1) ≫ p n = f ≫ k n, which can be obtained from h_down n

  NOT SO BAD: h_up not used in the construction! Can be proved *after* the definition
  So constuct pairs: ⟨ k n, h_down n ⟩, and then prove h_up n+1

  use hypothesis: ∃ k : Y ⟶ S' n, f ≫ k = g' n → ∃ k' : Y ⟶ S' (n+1), f ≫ k' = g' (n+1)
  h (n : ℕ) (k : Y ⟶ S' n) (h_down : f ≫ k = g' n) : ∃ k' : Y ⟶ S' (n+1), f ≫ k' = g' (n+1) :=

-/



theorem injective_of_light (S : LightProfinite.{u}) [Nonempty S]:
  Injective (lightToProfinite.obj S) := by
  -- Injective S := by
  constructor
  intro X Y g f h

  -- write S = lim S' n, with epic transition maps p n : S' (n+1) ⟶ S' n
  let S' (n : ℕ) := lightToProfinite.obj (S.component n)
  haveI (n : ℕ) : Finite (S' n) := by unfold S'; dsimp; exact inferInstance
  haveI : Nonempty (S' 0) := Nonempty.map (S.proj 0).toFun inferInstance
  let p (n : ℕ) : S' (n+1) ⟶ S' n := S.transitionMap n
  haveI (n : ℕ) : Epi (p n) := (Profinite.epi_iff_surjective (p n)).mpr (S.surjective_transitionMap n)
  let g' (n : ℕ) : X ⟶ S' n := g ≫ (S.proj n)

  -- base step of the induction
  obtain ⟨k0, h_down0⟩ :=  (injective_of_finite (S' 0)).factors (g' 0) f
  have h_comm0 : f ≫ k0 = (g' 1) ≫ p 0 := by
    rw [h_down0]
    unfold g'
    exact congrArg _ (S.proj_comp_transitionMap 0).symm

  -- key part of induction step:
  have h_step (n : ℕ) (k : Y ⟶ S' n) (h_down : f ≫ k = g' n) :
    ∃ k' : Y ⟶ S' (n+1), k' ≫ p n = k ∧ f ≫ k' = g' (n+1) := by
    have h_comm : f ≫ k = g' (n+1) ≫ p n := by
      rw [h_down]
      unfold g'
      exact congrArg _ (S.proj_comp_transitionMap n).symm
    exact key_lifting_lemma' X Y (S' (n+1)) (S' n) f (p n) (g' (n+1)) k h_comm

  let next (n : ℕ) : { k : Y ⟶ S' n // f ≫ k = g' n } → { k : Y ⟶ S' (n+1) // f ≫ k = g' (n+1) } :=
    fun k ↦ ⟨Classical.choose (h_step n k.val k.property), (Classical.choose_spec (h_step n k.val k.property)).2⟩

  let rec k_lift : (n : Nat) → { k : Y ⟶ S' n // f ≫ k = g' n } := fun
  | 0 => ⟨k0, h_down0⟩
  | Nat.succ n => ⟨Classical.choose (h_step n (k_lift n).val (k_lift n).property),
      (Classical.choose_spec (h_step n (k_lift n).val (k_lift n).property)).2⟩

  let rec k_lift' : (n : Nat) → { k : Y ⟶ S' n // f ≫ k = g' n } := fun
  | 0 => ⟨k0, h_down0⟩
  | Nat.succ n => next n (k_lift' n)

  have h_up (n : ℕ) : (k_lift' (n+1)).val ≫ p n = (k_lift' n).val := by
    induction' n with n ih
    · dsimp
      -- unfold k_lift' -- TODO understand why this does not unfold!
      sorry
    · sorry

  let rec test : Nat → Nat
  | 0 => 0
  | n+1 => test n + 1

  have h_test (n : Nat) : test n = n := by
    induction' n with n ih
    · unfold test
      dsimp

      sorry
    · sorry

  let rec fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)



  sorry

  -- define k : Y ⟶ S as the limit of the k_lift n




  -- ok, we should be good to set up an induction loop now!
  -- first think of good naming scheme -- on paper;

  sorry



def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | .succ (.succ n) => fib n + fib (.succ n)

example : fib 5 = 5 := by
  unfold fib
  unfold fib
  unfold fib
  unfold fib
  unfold fib
  exact rfl

  sorry


-- TODO: understand why this works with "def", but not with "let rec"!

def test : Nat → Nat
  | 0 => 0
  | n+1 => test n + 1

example (n : ℕ) : test n = n := by
  induction' n with n ih
  · unfold test
    rfl
  · unfold test
    linarith
