import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Filter
open Topology Filter

-- 10.2. Metric spaces

-- Let X be a metric space.
-- Let a, b, c be points in X.
variable {X : Type*} [MetricSpace X] (a b c : X)

-- A metric space is a set of points equipped with a metric.
-- The metric is way to measure the distance between two points.

-- `dist` is a function X² → ℝ.
-- Input: two points a and b in X
-- Output: the distance in ℝ between a and b
#check (dist a b : ℝ)

-- A metric is a distance function satisfies the following properties:
-- 1. Non-negativity: the distance between two points is always non-negative.
--      dist(a, b) ≥ 0, ∀ a, b ∈ X
#check (dist_nonneg : 0 ≤ dist a b)
-- 2. The distance between two points is zero iff the points are the same.
--     dist(a, b) = 0 ↔ a = b, ∀ a, b ∈ X
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
-- 3. Symmetry: the distance between two points is the same in both directions.
--     dist(a, b) = dist(b, a), ∀ a, b ∈ X
#check (dist_comm a b : dist a b = dist b a)
-- 4. The triangle inequality: the distance between two points is always ≤ to the sum of
--                             the distances between the points and a third point.
--     dist(a, c) ≤ dist(a, b) + dist(b, c), ∀ a, b, c ∈ X
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

-- Example:
-- 1. Real numbers ℝ is a metric space with
--      dist(a, b) = |a - b| where |.| is the absolute value function.
-- 2. Euclidean space ℝⁿ is a metric space with
--      dist(a, b) = √(∑ᵢ (aᵢ - bᵢ)²) where a, b ∈ ℝⁿ

-- `EMetricSpace`: extended metric space
--   allows the distance to be infinite
#check EMetricSpace
-- `PseudoMetricSpace`: pseudo metric space
--   allows the distance between two distinct points to be zero
#check PseudoMetricSpace
-- `PseudoEMetricSpace`: pseudo extended metric space
--   (combining `EMetricSpace` and `PseudoMetricSpace`)
--   allows the distance between two points to be infinite
--   and the distance between two distinct points to be zero
#check PseudoEMetricSpace

-- 10.2.1. convergence and continuity in metric spaces

-- Metric spaces allow defining
--   convergence of sequences
--   continuity of functions between metric spaces
-- using the distance function.

-- Classic epsilon-N definition of convergence:
-- A sequence {uₙ} in a metric space converges to a point a iff
-- for every ε > 0, there exists an N such that
-- for all n ≥ N, dist(uₙ, a) < ε.
example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

-- Classic epsilon-delta definition of continuity:
-- A function f between two metric spaces is continuous iff
-- for all x in X, for all ε > 0, there exists a δ > 0 such that
-- for all x' in X, if dist(x', x) < δ, then dist(f(x'), f(x)) < ε.
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

-- The function that measures the distance between two points is continuous.
-- If X and Y are metric spaces, the Cartesian product X × Y is a metric space.
-- So, X² is a metric space.
-- ℝ is a metric space.
-- The distance function goes between two metric spaces, so we can talk about continuity.
-- The distance function is continuous.
example {X : Type*} [MetricSpace X] : Continuous fun p : X × X ↦ dist p.1 p.2 :=
  by continuity

-- Moreover, the function that measures the distance between
-- the images of points under a continuous function is also continuous.
-- i.e., if f is a continuous function from X to Y
-- then the function p ↦ dist (f p.1) (f p.2) is also continuous.

-- Proof with the `continuity` tactic
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

-- Proof with a proof term
-- `continuous_fst` and `continuous_snd`: projections are continuous
example {X : Type*} [MetricSpace X] : Continuous (Prod.fst : X × X → X) := continuous_fst
example {X : Type*} [MetricSpace X] : Continuous (Prod.snd : X × X → X) := continuous_snd
-- `Continuous.comp`: composition of continuous functions is continuous
example {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
        {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := hg.comp hf
-- `Continuous.prod_mk`: pairing of continuous functions is continuous
--   If f, g are continuous then (f × g)(x) := (f(x), g(x)) is continuous.
example {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
        {f : X → Y} {g : X → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x : X ↦ (f x, g x)) := Continuous.prod_mk hf hg
-- `λ p ↦ dist (f p.1) (f p.2)` = dist ∘ ((f ∘ `Prod.fst`) × (f ∘ `Prod.snd`))
-- `apply Continuous.comp` will not recognize the definitionally equality
-- However, a full proof term works
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))

-- Proof with `Continuous.dist`:
--   If f, g are continuous functions, then x ↦ dist(f(x), g(x)) is continuous.
--   `Continuous f → Continuous g → Continuous (fun x ↦ dist (f x) (g x))`
-- Tactic mode:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd
-- Term mode:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)

-- Proof with `Continuous.prodMap`:
-- `Continuous.prodMap`: If f, g are continuous functions,
--                       then (f × g)(p₁, p₂) := (f(p₁), g(p₂)) is continuous.
example {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
        {f : X → Y} {g : X → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun p : X × X ↦ (f p.1, g p.2) := hf.prodMap hg
-- `λ p ↦ dist (f p.1) (f p.2)` = dist ∘ (f × f)
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := continuous_dist.comp (hf.prodMap hf)

-- Proof with `Continuous.fst'` and `Continuous.snd'`:
-- `Continuous.fst'`: image of projection to the first coordinate is continuous
--   If f is continuous, then (f ∘ `Prod.fst`) is continuous.
-- Similarly, `Continuous.snd'`: If f is continuous, then (f ∘ `Prod.snd`) is continuous.
-- Problem: obfuscates the proof
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'

-- If f is continuous, then f(x² + x) is continuous.
-- `continuous_pow`: x ↦ xⁿ, denoted ⬝ⁿ,  is continuous for all n ∈ ℕ
#check continuous_pow
-- `continuous_id`: x ↦ x, denoted id, is continuous
#check continuous_id
-- `λ x ↦ f (x ^ 2 + x)` = f ∘ (⬝² + id)
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  hf.comp ((continuous_pow 2).add continuous_id)

-- A function f is continuous at a point a iff for every ε > 0,
-- there exists a δ > 0 s.t. for all x, if dist(x, a) < δ, then dist(f(x), f(a)) < ε.
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

-- A function is continuous iff it is continuous at every point.
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ a, ContinuousAt f a := continuous_iff_continuousAt

-- 10.2.2. Balls, open sets and closed sets

-- Let r be a real number.
variable (r : ℝ)

-- `Metric.ball a r`: the open ball centered at a with radius r
--   set of all points whose distance from a is strictly less than r
-- Example: an open ball in ℝ is an open interval (a - r, a + r)
-- Example: an open ball in ℝ² is a disk without its boundary circle
example : Metric.ball a r = { b | dist b a < r } :=
  rfl

-- `Metric.closedBall a r`: the closed ball centered at a with radius r
--   set of all points whose distance from a is less than or equal to r
-- Example: a closed ball in ℝ is a closed interval [a - r, a + r]
-- Example: a closed ball in ℝ² is a disk with its boundary circle
example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl

-- There is no sign restriction on the radius r.
-- If r is negative, any open or closed ball is empty.
-- If r is zero, any open ball is empty, and the closed ball is a singleton.

-- If r is positive, the center a is in the open ball.
example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

-- If r is non-negative, the center a is in the closed ball.
example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr

-- A set is open iff for every point in the set,
-- there exists an open ball centered at the point
-- that is entirely contained in the set.
-- Intuition: an open set doesn't include its boundary.
-- Intuition: every point has a wiggle room to move around without leaving the set.
-- Formally, a set s is open iff ∀ x ∈ s, ∃ ε > 0, B(x, ε) ⊆ s.
example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

-- Example: an open ball is an open set
example (a : X) (r : ℝ) : IsOpen (Metric.ball a r) :=
  -- Simple Lean proof:
  -- Metric.isOpen_ball
  -- Long proof:
  by
  rw [Metric.isOpen_iff]
  -- Consider x ∈ B(a, r).
  -- Show: there exists ε > 0 s.t. B(x, ε) ⊆ B(a, r).
  intro x hx
  -- Let ε = r - dist(x, a).
  use r - dist x a
  constructor
  · -- Show ε > 0.
    -- As x ∈ B(a, r), dist(x, a) < r. Thus, ε = r - dist(x, a) > 0.
    exact sub_pos.mpr hx
  · -- Let y ∈ B(x, ε).
    -- Show y ∈ B(a, r).
    intro y hy
    -- As y ∈ B(x, ε), dist(y, x) < ε = r - dist(x, a).
    -- Show dist(y, a) < r.
    rw [Metric.mem_ball] at *
    -- dist(y, a) ≤ dist(y, x) + dist(x, a) (∵ triangle inequality)
    --            < r - dist(x, a) + dist(x, a) (∵ dist(y, x) < r - dist(x, a))
    --            = r
    calc
      dist y a ≤ dist y x + dist x a := dist_triangle y x a
      _ < r - dist x a + dist x a := add_lt_add_right hy (dist x a)
      _ = r := sub_add_cancel r (dist x a)

-- A set is closed iff its complement is open.
-- Intuition: a closed set includes its boundary.
-- Intuition: a closed set contains all its limit points.
example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

-- Example: a closed ball is a closed set
example (a : X) (r : ℝ) : IsClosed (Metric.closedBall a r) := Metric.isClosed_ball

-- A closed set is closed under limits.

-- `mem_of_tendsto`: general version
--   if a function is *eventually* in a closed set
--   and converges to a point along a non-trivial filter,
--   then the limit point is in the closed set.

-- If a sequence is in a closed set and converges to a limit point,
-- then the limit point is also in the closed set.
-- Given
--   a set s
--   a point a
--   a sequence (uₙ)
-- If
--   s is closed
--   (uₙ) converges to a
--   ∀ n ∈ ℕ, uₙ ∈ s
-- Then
--   a ∈ s
example {s : Set X} {a : X} {u : ℕ → X}
  (hs : IsClosed s) (hu : Tendsto u atTop (𝓝 a)) (hus : ∀ n, u n ∈ s)
  : a ∈ s :=
  -- `mem_of_tendsto` only needs eventually uₙ ∈ s, not all uₙ ∈ s
  hs.mem_of_tendsto hu (Eventually.of_forall hus)

-- The closure of a set is the smallest closed set that contains the set.
-- Intuition: the closure "fills in the gaps" in a set.
-- Notation: cl(s)

-- Interior point: ∃ ε > 0, B(a, ε) ⊆ s.
-- Limit point: ∀ ε > 0, B(a, ε) ∩ s ≠ ∅.
-- Boundary point: ∀ ε > 0, B(a, ε) ∩ s ≠ ∅ ∧ B(a, ε) ∩ sᶜ ≠ ∅.

-- A point a is in the closure of a set s iff
-- for every ε > 0, there exists a point b in s s.t. a ∈ B(b, ε)
-- (or, equivalently, ∀ ε > 0, B(a, ε) ∩ s ≠ ∅)
-- `mem_closure_iff`: a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, dist(a, b) < ε
-- Intuition: we can always find a point in s arbitrarily close to a.
-- Intuition: a is a limit point of s, so a is either in s or on the boundary of s.
example {a : X} {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff

-- A point is in the closure of a set if
-- there is a sequence in the set that converges to the point.
-- Given
--  a point a
--  a sequence (uₙ)
--  a set s
-- If
--  (uₙ) converges to a
--  ∀ n ∈ ℕ, uₙ ∈ s
-- Then
--  a is in the closure of s
example {u : ℕ → X} {s : Set X} (hu : Tendsto u atTop (𝓝 a)) (hs : ∀ n, u n ∈ s) :
    a ∈ closure s :=
  by
  -- By definition of the closure of s,
  -- show ∀ ε > 0, ∃ b ∈ s, dist(a, b) < ε.
  rw [Metric.mem_closure_iff]
  -- Let ε > 0. Show ∃ b ∈ s, dist(a, b) < ε.
  intro ε hεpos
  -- Since (uₙ) converges to a and ε > 0,
  -- ∃ N ∈ ℕ, ∀ n ≥ N, dist(uₙ, a) < ε.
  rw [Metric.tendsto_atTop] at hu
  -- Fix such N ∈ ℕ. Then ∀ n ≥ N, dist(uₙ, a) < ε.
  rcases (hu ε hεpos) with ⟨N, h⟩
  -- Let b = u_N.
  -- Show b ∈ s and dist(a, b) < ε.
  use u N
  constructor
  · -- Show b ∈ s.
    -- Since uₙ ∈ s ∀ n ∈ ℕ, b = u_N ∈ s.
    exact hs N
  · -- Show dist(a, b) < ε.
    -- Or, equivalently, show dist(u_N, a) < ε.
    rw [dist_comm]
    -- Since ∀ n ≥ N, dist(uₙ, a) < ε, dist(u_N, a) < ε.
    exact h N (le_refl N)

-- Open balls form a basis for the neighborhood filter.
#check Metric.nhds_basis_ball
-- All neighborhoods of a point contain an open ball centered at the point.
-- More formally, a set s is in the neighborhood filter of a point x iff
-- there is a positive radius ε s.t. the open ball centered at x with radius ε
-- is entirely contained in s.
-- i.e., s ∈ 𝓝 x ↔ ∃ ε > 0, B(x, ε) ⊆ s
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

-- Closed balls also form a basis for the neighborhood filter.
#check Metric.nhds_basis_closedBall
-- A set s is in the neighborhood filter of a point x iff
-- there is a positive radius ε s.t. the closed ball centered at x with radius ε
-- is entirely contained in s.
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff

-- A function f is continuous at a point x iff
-- for every neighborhood V of f(x), there exists a neighborhood U of x
-- s.t. f(U) ⊆ V.
-- `mem_map_iff_exists_image`: U ∈ f(F) ↔ ∃ V ∈ F, f(V) ⊆ U
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} {x : X} :
  ContinuousAt f x ↔ (∀ V ∈ 𝓝 (f x), ∃ U ∈ 𝓝 x, f '' U ⊆ V) := ⟨
    fun h _ hV => mem_map_iff_exists_image.mp (h hV),
    fun h' V hV => mem_map_iff_exists_image.mpr (h' V hV),
  ⟩

-- A function f is continuous at a point x iff
-- for every ε > 0, there exists a δ > 0 s.t.
-- f(B(x, δ)) ⊆ B(f(x), ε).
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} {x : X} :
  ContinuousAt f x ↔ ∀ ε > 0, ∃ δ > 0, f '' Metric.ball x δ ⊆ Metric.ball (f x) ε :=
  by
  constructor
  · -- Suppose f is continuous at x.
    -- Consider ε > 0.
    -- Show ∃ δ > 0, f(B(x, δ)) ⊆ B(f(x), ε).
    intro h ε hεpos
    -- By definition of continuity at x,
    -- we have f tends to f(x) as input tends to x.
    -- This means that for all neighborhood V of f(x),
    -- f⁻¹(V) is a neighborhood of x.
    rw [ContinuousAt, tendsto_def] at h
    -- Since B(f(x), ε) is a neighborhood of f(x),
    -- f⁻¹(B(f(x), ε)) is a neighborhood of x.
    have := h (Metric.ball (f x) ε) (Metric.ball_mem_nhds (f x) hεpos)
    -- By definition of a neighborhood of x,
    -- ∃ δ > 0, B(x, δ) ⊆ f⁻¹(B(f(x), ε)).
    rw [Metric.mem_nhds_iff] at this
    -- Fix such δ > 0. Then, B(x, δ) ⊆ f⁻¹(B(f(x), ε)).
    -- Show f(B(x, δ)) ⊆ B(f(x), ε).
    rcases this with ⟨δ, hδpos, h⟩
    use δ, hδpos
    -- Since image and preimage are a Galois connection,
    -- f(B(x, δ)) ⊆ B(f(x), ε).
    exact image_subset_iff.mpr h
  · -- Suppose ∀ ε > 0, ∃ δ > 0, f(B(x, δ)) ⊆ B(f(x), ε).
    -- Show f is continuous at x.
    intro h
    -- Consider a neighborhood V of f(x).
    -- Show V ∈ f(𝓝(x)).
    intro V hV
    -- Since V is a neighborhood of f(x),
    -- ∃ ε > 0, B(f(x), ε) ⊆ V.
    rw [Metric.mem_nhds_iff] at hV
    -- Fix such ε > 0. Then B(f(x), ε) ⊆ V.
    rcases hV with ⟨ε, hεpos, h'⟩
    -- Since ε > 0, ∃ δ > 0 s.t. f(B(x, δ)) ⊆ B(f(x), ε).
    -- Fix such δ > 0. Then f(B(x, δ)) ⊆ B(f(x), ε).
    rcases h ε hεpos with ⟨δ, hδpos, h⟩
    -- We can show V ∈ f(𝓝(x)) if
    -- we show f⁻¹(V) is a neighborhood of x.
    apply mem_map.mpr
    -- This is equivalent to
    -- show ∃ δ > 0, B(x, δ) ⊆ f⁻¹(V).
    rw [Metric.mem_nhds_iff]
    -- Let δ be the same as before.
    -- Show B(x, δ) ⊆ f⁻¹(V).
    use δ, hδpos
    -- This is equivalent to
    -- Show f(B(x, δ)) ⊆ V.
    apply image_subset_iff.mp
    -- Since f(B(x, δ)) ⊆ B(f(x), ε) and B(f(x), ε) ⊆ V,
    -- f(B(x, δ)) ⊆ V.
    intro _ hy
    exact h' (h hy)

-- 10.2.3. Compactness

-- Many properties of finite sets
-- can be extended to infinite sets that are "compact".

-- `IsCompact` is a typeclass for compact sets.
-- In Lean, compactness is defined using filters:
-- A set is compact if every non-trivial filter that contains the set
-- has a cluster point in the set.
-- A cluster point is a point whose neighborhoods intersects the filter non-trivially.
example {s : Set X} :
  IsCompact s = ∀ F [NeBot F], F ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x F := rfl

-- The closed unit interval in ℝ, [0, 1], is a closed set.
example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

-- Any sequence taking values in a compact set has
-- a subsequence that converges to a point in the set.
-- Intuition: No sequence can escape a compact set to infinity.
-- Relevant lemma: `IsCompact.tendsto_subseq`
-- Given
--   a set s
--   a sequence (u(n))
-- If
--   s is compact
--   ∀ n ∈ ℕ, u(n) ∈ s
-- Then:
--   there exists an a ∈ s
--   there exists a subsequence indexed by φ : ℕ → ℕ
--   such that φ is strictly increasing
--   and the subsequence ((u ∘ φ)(n)) converges to a
example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

-- Extreme value theorem:
-- Any continuous function on a non-empty compact set with values in ℝ
-- is bounded and attains its bounds somewhere.
-- Relevant lemma: `IsCompact.exists_isMinOn` and `IsCompact.exists_isMaxOn`
-- Given
--   a set s
--   a function f : X → ℝ
-- If
--   s is compact and non-empty
--   f is continuous on s
-- Then:
--   there exists a point x ∈ s s.t. ∀ y ∈ s, f(x) ≤ f(y)
example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs
-- Same as above but for the maximum.
example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_isMaxOn hs' hfs

-- Compact sets are closed.
-- Relevant lemma: `IsCompact.isClosed`
example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

-- A metric space is compact if the entire space is compact.
-- In Lean, `CompactSpace` is a typeclass for compact spaces.

-- In a compact space, the universe set is compact.
example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ

-- In a compact space, any closed set is compact.
#check IsClosed.isCompact

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
