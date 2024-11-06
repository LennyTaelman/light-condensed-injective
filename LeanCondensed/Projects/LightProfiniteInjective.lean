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
variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

open Set

-- For every closed ⊆ open in a profinite, there is an intermediate clopen

lemma clopen_of_closed_subset_open (Z U : Set X) (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z ⊆ U) :
    ∃ C : Set X, IsClopen C ∧ Z ⊆ C ∧ C ⊆ U := by
  -- every z ∈ Z has clopen neighborhood V z ⊆ U
  choose V hV using fun (z : Z) ↦ compact_exists_isClopen_in_isOpen hU (hZU z.property)
  -- the V z cover Z
  have V_cover : Z ⊆ iUnion V := fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- the V z are open and closed
  have V_open : ∀ z : Subtype Z, IsOpen (V z) := fun z ↦ (hV z).1.2
  have V_clopen : ∀ z : Subtype Z, IsClopen (V z) := fun z ↦ (hV z).1
  -- there is a finite subcover, let C be its union; this does the job
  have Z_compact := IsClosed.isCompact hZ
  choose I hI using IsCompact.elim_finite_subcover Z_compact V V_open V_cover
  let C := ⋃ (i ∈ I), V i
  have C_clopen : IsClopen C := Finite.isClopen_biUnion (Finset.finite_toSet I)
    (fun i _ ↦ V_clopen i)
  have C_subset_U : C ⊆ U := by simp_all only [iUnion_subset_iff, C, implies_true]
  exact ⟨C, C_clopen, hI, C_subset_U⟩


open Fin


/-
  Let X be profinite, D i ⊆ X a finite family of clopens, and Z i ⊆ D i closed.
  Assume that all the Z i are disjoint. Then there exist clopens Z i ⊆ C i ⊆ D i
  with the C i disjoint, and such that ∪ C i = ∪ D i
-/

lemma clopen_partition_of_disjoint_closeds_in_clopens (n : ℕ)
    (Z : Fin n → Set X) (D : Fin n → Set X)
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
      X -f->  Y
      |g      |g'
      v       v
      S -f'-> T
  where Y is profinite, S is finite, f is injective and f' is surjective,
  there exists a diagonal map k : Y --> S making diagram commute.
-/


lemma key_lifting_lemma (X Y S T : Profinite.{u}) [Finite S]
  (f : X → Y) (hf : Continuous f) (f_inj : Function.Injective f)
  (f' : S → T) (f'_surj : Function.Surjective f')
  (g : X → S) (hg : Continuous g) (g' : Y → T) (hg' : Continuous g')
  (h_comm : g' ∘ f = f' ∘ g) :
  ∃ k : Y → S, (Continuous k) ∧ (f' ∘ k = g') ∧ (k ∘ f = g)  := by

  -- help the instance inference a bit: T is finite
  have _ : Finite T := Finite.of_surjective f' f'_surj
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
    intro y hy
    simp
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

-- warming up: injectivity of finite discrete spaces in Profinite spaces
-- won't need this, but should be good exercise

lemma injective_of_finite (S : Profinite.{u}) [S_ne : Nonempty S] [Finite S]:
  Injective (S) := by
  constructor
  intro X Y g f h
  have f_inj : Function.Injective f.toFun := (mono_iff_injective f).mp h
  -- let T be the singleton space
  let T : (Profinite : Type (u + 1)) := Profinite.of (ULift (Fin 1))
  -- let f' be the unique map from S to T
  let f' : S → T := fun _ => (0 : ULift (Fin 1))
  have f'_surj : Function.Surjective f' := by
    intro t
    use Classical.choice S_ne
    simp only [CompHausLike.coe_of, T, f']
    ext : 2
    simp only [ULift.zero_down, isValue, val_eq_zero]
  -- let g' be the unique map from Y to T
  let g' : Y → T := fun _ => (0 : ULift (Fin 1))
  have g'_cont : Continuous g' := continuous_const
  have h_commutes : g' ∘ f.toFun = f' ∘ g.toFun := rfl
  -- now apply the key lifting lemma
  obtain ⟨k, h1, _, h3⟩ := key_lifting_lemma X Y S T f.toFun f.continuous f_inj f' f'_surj
    g.toFun g.continuous g' g'_cont h_commutes
  exact ⟨⟨k, h1⟩, ConcreteCategory.forget_faithful.map_injective h3⟩




open Opposite Nat

/-
  The projection maps in the diagram of a light profinite space
  are surjective. Not sure if this is true with the current definition.
  Sounds very likely.

  this actually is in mathlib!
-/
def π (n : ℕ) : (op n.succ) ⟶ (op n) := op (homOfLE (le_succ n))

lemma transition_surjective (S : LightProfinite.{u}) (i j : ℕ) (hij : i ≤ j) :
    Function.Surjective (S.toLightDiagram.diagram.map (op (homOfLE hij))) := by
  unfold LightProfinite.toLightDiagram
  dsimp

  sorry


-- this is the target theorem!
-- warning: S.component 0 will not be a one point space, even when S is Nonempty



theorem injective_of_light (S : LightProfinite.{u}) [Nonempty S]:
  -- Injective (lightToProfinite.obj S) := by
  Injective S := by
  constructor
  intro X Y g f h
  have f_inj : Function.Injective f.toFun := (mono_iff_injective f).mp h
  -- write S as sequential limit of finite discrete spaces
  -- play a bit with applying the key lifting lemma
  let (n: ℕ) := 5
  #check S.component n
  #check (S.proj n : S ⟶ S.component n)

  have gn : X ⟶ S.component n := g ≫ (S.proj n)
  have gn_cont : Continuous gn.toFun := gn.continuous_toFun
  have gnsucc : X ⟶ S.component (n+1) := g ≫ (S.proj n.succ)
  have gnsucc_cont : Continuous gnsucc.toFun := gnsucc.continuous_toFun

  -- let's do the first step by hand
  let T := S.component 0
  let T_ne : Nonempty T := Nonempty.map (S.proj 0).toFun inferInstance
  have g0 : X ⟶ T := g ≫ (S.proj 0)
  have g0_cont : Continuous g0.toFun := g0.continuous_toFun
  let T' : (Profinite : Type (u + 1)) := Profinite.of (ULift (Fin 1))
  have g0' : Y.toTop → T' := fun _ => (0 : ULift (Fin 1))
  have g0'_cont : Continuous g0' := continuous_const









  let S_diagr := S.toLightDiagram
  -- build Y → S n inductively
  -- first interpret Y as constant diagram
  let Y' : ℕᵒᵖ ⥤ Profinite := (Functor.const _).obj Y
  -- now build the maps Y → S n inductively

  sorry
