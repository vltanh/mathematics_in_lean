import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

-- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace

example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  Continuous.comp hf (Continuous.add (continuous_pow 2) continuous_id)

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl

example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr

example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (Eventually.of_forall hus)

example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s :=
  by
  rw [Metric.mem_closure_iff]
  rw [Metric.tendsto_atTop] at hu
  intro ε hεpos
  rcases (hu ε hεpos) with ⟨N, h⟩
  use u N, hs N
  rw [dist_comm]
  exact h N (le_refl N)

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff

example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_isMaxOn hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ

#check IsCompact.isClosed

example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff

example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f :=
  by
  rw [Metric.uniformContinuous_iff]
  intro ε hεpos
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  let K := { p : X × X | ε ≤ φ p }
  have hφ : Continuous φ := hf.fst'.dist hf.snd'
  have hK : IsCompact K := (isClosed_le continuous_const hφ).isCompact
  rcases eq_empty_or_nonempty K with (hKemp | hKnemp)
  · use 1
    constructor
    · exact zero_lt_one
    · intro a b _
      contrapose! hKemp
      use (a, b)
      rw [mem_setOf]
      exact hKemp
  · rcases hK.exists_isMinOn hKnemp continuous_dist.continuousOn with ⟨x, hxK, hxinf⟩
    use dist x.1 x.2
    constructor
    · apply dist_pos.mpr
      intro h
      have : ε ≤ 0 := by
        calc
          ε ≤ φ x := hxK
          _ = dist (f x.1) (f x.2) := by dsimp [φ]
          _ = dist (f x.1) (f x.1) := by rw [← h]
          _ = 0 := by apply dist_eq_zero.mpr; rfl
      linarith
    · intro a b h
      contrapose! h
      rw [isMinOn_iff] at hxinf
      exact hxinf (a, b) h


example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

open BigOperators

open Finset

theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    have : Tendsto (fun n : ℕ ↦ (1 / 2 ^ n : ℝ)) atTop (𝓝 0) := by
      simp_rw [← one_div_pow]
      apply tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
    rw [Metric.tendsto_atTop] at this
    rcases this (ε / 2) (half_pos ε_pos) with ⟨N, hN⟩
    have := hN N (le_refl N)
    use N
    rw [Real.dist_0_eq_abs] at this
    have h : 0 ≤ 1 / (2 : ℝ) ^ N := by
      rw [← one_div_pow]
      apply pow_nonneg
      simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
    rw [abs_of_nonneg h] at this
    linarith only [this]
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by
      rw [dist_comm]
      rw [add_zero N]
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) :=
      dist_le_range_sum_dist (fun i => u (N + i)) k
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) :=
      sum_le_sum fun i _ => hu (N + i)
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by
      simp_rw [← one_div_pow, pow_add, mul_sum]
    _ ≤ 1 / 2 ^ N * 2 := by
      apply mul_le_mul
      · apply le_refl
      · exact sum_geometric_two_le k
      · apply sum_nonneg
        intro _ _
        apply pow_nonneg
        simp
      · rw [← one_div_pow]
        apply pow_nonneg
        simp
    _ < ε := hN


open Metric

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n := fun n => pow_pos (by simp) n
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by
    intro n x δ hδpos
    have hdn := hd n
    rw [dense_iff] at hdn
    rcases hdn x (δ / 2) (half_pos hδpos) with ⟨y, hyb, hyfn⟩
    have hon := ho n
    rw [Metric.isOpen_iff] at hon
    rcases hon y hyfn with ⟨ε, hεpos, hbyεfn⟩
    let ε' := min (min (δ / 2) (B (n + 1))) (ε / 2)
    have hε'B : ε' ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hε'ε : ε' < ε := by
      have : ε' ≤ (ε / 2) := min_le_right _ _
      apply lt_of_le_of_lt this
      linarith [hεpos]
    use y, ε'
    constructor
    · exact lt_min (lt_min (half_pos hδpos) (Bpos (n + 1))) (half_pos hεpos)
    · constructor
      · exact le_trans (min_le_left _ _) (min_le_right _ _)
      · intro z hz
        constructor
        · rw [mem_closedBall] at *
          rw [mem_ball] at hyb
          calc
            dist z x ≤ dist z y + dist y x := dist_triangle z y x
            _ ≤ δ / 2 + δ / 2 := add_le_add (le_trans hz hε'B) (le_of_lt hyb)
            _ = δ := by ring
        · apply hbyεfn
          rw [mem_closedBall] at hz
          rw [mem_ball]
          exact lt_of_le_of_lt hz hε'ε
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x`
    belonging to all `f n`. For this, we construct inductively a sequence
    `F n = (c n, r n)` such that the closed ball `closedBall (c n) (r n)` is included
    in the previous ball and in `f n`, and such that `r n` is small enough to ensure
    that `c n` is a Cauchy sequence. Then `c n` converges to a limit which belongs
    to all the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction' n with n hn
    · dsimp [r, F]
      exact lt_min εpos (Bpos 0)
    · exact Hpos n (c n) (r n) hn
  have rB : ∀ n, r n ≤ B n := by
    intro n
    induction' n with n hn
    · dsimp [r, F, B]
      exact min_le_right _ _
    · exact HB n (c n) (r n) (rpos n)
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    intro n
    exact Hball n (c n) (r n) (rpos n)
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by
    intro n
    have := (rpos (n + 1) |> le_of_lt |> mem_closedBall_self |> incl n).left
    rw [mem_closedBall'] at this
    exact le_trans this (rB n)
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    intro n
    apply Nat.le_induction
    · exact subset_refl _
    · intro m _ hss
      exact (incl m).trans (Set.inter_subset_left.trans hss)
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by
    intro n
    apply isClosed_ball.mem_of_tendsto ylim
    apply (eventually_ge_atTop n).mono
    intro m hnm
    exact rpos m |> le_of_lt |> mem_closedBall_self |> I n m hnm
  constructor
  · rw [mem_iInter]
    intro n
    exact ((n + 1) |> yball |> incl n).right
  · rw [mem_closedBall]
    have := yball 0
    rw [mem_closedBall] at this
    dsimp [c, r, F] at this
    exact le_trans this (min_le_left _ _)
