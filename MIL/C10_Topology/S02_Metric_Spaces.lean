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
-- This is essentially the epsilon-delta definition of continuity.
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} {x : X} :
  ContinuousAt f x ↔ ∀ ε > 0, ∃ δ > 0, f '' Metric.ball x δ ⊆ Metric.ball (f x) ε :=
  by
  -- By the epsilon-delta definition of continuity,
  -- f is continuous at x iff ∀ ε > 0, ∃ δ > 0 s.t.
  -- ∀ x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
  rw [Metric.continuousAt_iff]
  constructor
  · -- Suppose ∀ ε > 0, ∃ δ > 0, ∀ x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
    -- Show ∀ ε > 0, ∃ δ > 0, f(B(x, δ)) ⊆ B(f(x), ε).
    intro h
    -- Let ε > 0.
    -- Show ∃ δ > 0, f(B(x, δ)) ⊆ B(f(x), ε).
    intro ε hεpos
    -- By the hypothesis, ∃ δ > 0 s.t. ∀ x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
    -- Fix such δ > 0. Then, ∀ x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
    rcases h ε hεpos with ⟨δ, hδpos, h⟩
    -- Use δ > 0.
    -- Show f(B(x, δ)) ⊆ B(f(x), ε).
    use δ, hδpos
    -- Let y ∈ f(B(x, δ)).
    -- Show y ∈ B(f(x), ε).
    intro y hy
    -- Since y ∈ f(B(x, δ)), ∃ x' ∈ B(x, δ) s.t. y = f(x').
    -- Fix such x'. Then, dist(x', x) < δ and y = f(x').
    rcases hy with ⟨x', hx', rfl⟩
    -- Then, dist(y, f(x)) = dist(f(x'), f(x)) < ε.
    -- Or, equivalently, y ∈ B(f(x), ε).
    exact h hx'
  · -- Suppose ∀ ε > 0, ∃ δ > 0, f(B(x, δ)) ⊆ B(f(x), ε).
    -- Show ∀ ε > 0, ∃ δ > 0, ∀ x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
    intro h
    -- Let ε > 0.
    -- Show ∃ δ > 0, ∀ x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
    intro ε hεpos
    -- By the hypothesis, ∃ δ > 0 s.t. f(B(x, δ)) ⊆ B(f(x), ε).
    -- Fix such δ > 0. Then, f(B(x, δ)) ⊆ B(f(x), ε).
    rcases h ε hεpos with ⟨δ, hδpos, h⟩
    -- Use δ > 0.
    -- Show ∀ x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
    use δ, hδpos
    -- Let x' ∈ X. Suppose dist(x', x) < δ.
    -- Show dist(f(x'), f(x)) < ε.
    intro x' hx'
    -- Since dist(x', x) < δ, x' ∈ B(x, δ). Then, f(x') ∈ f(B(x, δ)).
    have : f x' ∈ f '' Metric.ball x δ := mem_image_of_mem f hx'
    -- Then, since f(B(x, δ)) ⊆ B(f(x), ε), f(x') ∈ B(f(x), ε).
    -- Or, equivalently, dist(f(x'), f(x)) < ε.
    exact h this

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

-- 10.2.4. Uniformly continuous functions

-- Uniform continuity requires a single δ to work for all points.
-- Continuity:
--   ∀ x ∈ X, ∀ ε > 0, ∃ δ > 0, ∀ x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
-- Uniform continuity:
--   ∀ ε > 0, ∃ δ > 0, ∀ x, x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff

-- Example: f(x) = ax + b (a ≠ 0) is uniformly continuous on ℝ.
-- Proof:
-- Fix ε > 0.
-- Let δ = ε / |a|. Then, δ > 0.
-- Suppose for all x, x' ∈ ℝ, |x' - x| < δ.
-- Then, |f(x') - f(x)| = |a(x' - x)| = |a||x' - x| < |a|δ = ε.
example {a b : ℝ} (ha : a ≠ 0) : UniformContinuous fun x : ℝ ↦ a * x + b :=
  by
  rw [Metric.uniformContinuous_iff]
  intro ε hεpos
  let δ := ε / abs a
  have hδpos : δ > 0 := div_pos hεpos (abs_pos.mpr ha)
  use δ, hδpos
  intro x x' hx
  calc
    dist (a * x + b) (a * x' + b) = ‖a * x + b - (a * x' + b)‖ := rfl
    _ = ‖a * x - a * x'‖ := by rw [add_tsub_add_eq_tsub_right]
    _ = ‖a * (x - x')‖ := by rw [mul_sub]
    _ = abs a * ‖x - x'‖ := IsAbsoluteValue.abv_mul norm a (x - x')
    _ = abs a * dist x x' := rfl
    _ < abs a * δ := mul_lt_mul_of_pos_left hx (abs_pos.mpr ha)
    _ = abs a * (ε / abs a) := rfl
    _ = ε := mul_div_cancel₀ ε (abs_ne_zero.mpr ha)

-- Example: f(x) = √x is uniformly continuous on [0, ∞).
-- Proof:
-- Fix ε > 0.
-- Let δ = ε². Then, δ > 0.
-- Suppose ∀ x, x' ∈ [0, ∞), |x' - x| < δ.
-- First, |√x' - √x| ≤ |√x'| + |√x| = √x' + √x ≤ |√x' + √x|
-- Then, |√x' - √x|² ≤ |√x' - √x| * |√x' + √x| = |x' - x| < δ = ε².
-- So, |√x' - √x| < ε.
example : UniformContinuousOn (fun x : ℝ ↦ √x) (Ici (0 : ℝ)) :=
  by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hεpos
  let δ := ε ^ 2
  have hδpos : δ > 0 := pow_pos hεpos 2
  use δ, hδpos
  intro x hx x' hx' h
  have := calc
    (dist (√x) (√x')) ^ 2 = |√x - √x'| ^ 2 := rfl
    _ ≤ |√x - √x'| * |√x + √x'| := by
      rw [sq]
      apply mul_le_mul_of_nonneg_left
      · calc
          |√x - √x'| = |√x - 0 + 0 - √x'| := by rw [add_zero, sub_zero]
          _ = |(√x - 0) + (0 - √x')| := by rw [add_sub_assoc]
          _ ≤ |√x - 0| + |0 - √x'| := by exact abs_add_le (√x - 0) (0 - √x')
          _ = |√x| + |√x'| := by rw [sub_zero, zero_sub, abs_neg]
          _ = √x + √x' := by rw [abs_of_nonneg (Real.sqrt_nonneg x), abs_of_nonneg (Real.sqrt_nonneg x')]
          _ ≤ |√x + √x'| := le_abs_self (√x + √x')
      · exact abs_nonneg (√x - √x')
    _ = |(√x - √x') * (√x + √x')| := Eq.symm (abs_mul (√x - √x') (√x + √x'))
    _ = |√x ^ 2 - √x' ^ 2| := by rw [pow_two_sub_pow_two, mul_comm]
    _ ≤ |x - x'| := by
      rw [sq, sq]
      rw [← Real.sqrt_mul hx]
      rw [← Real.sqrt_mul hx']
      rw [← sq, ←sq]
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
      rw [abs_eq_self.mpr hx, abs_eq_self.mpr hx']
    _ < δ := h
    _ = ε ^ 2 := rfl
  rw [← abs_eq_self.mpr dist_nonneg, ← abs_eq_self.mpr (le_of_lt hεpos)]
  exact sq_lt_sq.mp this

-- Example: f(x) = x² is not uniformly continuous on ℝ.
-- Proof:
-- Suppose f is uniformly continuous for a proof by contradiction.
-- Then, for ε = 1, ∃ δ > 0 s.t. ∀ x, x' ∈ ℝ, |x' - x| < δ → |x'² - x²| < 1.
-- Let x = 2 / δ and x' = 2 / δ + δ / 2.
-- Then, |x' - x| = δ / 2 < δ. So, |x'² - x²| < 1.
-- However, |x'² - x²| = 1 + (1 + δ² / 4) ≥ 1.
-- This is the contradiction.
example : ¬ UniformContinuous (fun x : ℝ ↦ x ^ 2) :=
  by
  by_contra h
  rw [Metric.uniformContinuous_iff] at h
  rcases h 1 zero_lt_one with ⟨δ, hδpos, h⟩
  let x := 2 / δ
  let x' := 2 / δ + δ / 2
  have hdx'x := by
    calc
      x' - x = 2 / δ + δ / 2 - 2 / δ := rfl
      _ = δ / 2 := by rw [sub_eq_iff_eq_add']
  have hxx' : dist x x' < δ := by
    calc
      dist x x' = abs (x - x') := rfl
      _ = abs (δ / 2) := by rw [abs_sub_comm x x', hdx'x]
      _ = δ / 2 := abs_of_nonneg (le_of_lt (half_pos hδpos))
      _ < δ := half_lt_self hδpos
  have hdxx'δ := h hxx'
  have : dist (x ^ 2) (x' ^ 2) ≥ 1 := by
    have hax'x := by
      calc
        x' + x = 2 / δ + δ / 2 + 2 / δ := rfl
        _ = 4 / δ + δ / 2 := by ring
    have hdx'xpos : x' - x > 0 := by rw [hdx'x]; exact half_pos hδpos
    have hax'xpos : x' + x > 0 := by rw [hax'x]; exact add_pos (div_pos zero_lt_four hδpos) (half_pos hδpos)
    have had : (x' + x) * (x' - x) = 2 + δ ^ 2 / 4 := by
      calc
        (x' + x) * (x' - x) = (4 / δ + δ / 2) * (δ / 2) := by rw [hax'x, hdx'x]
        _ = ((4 / δ) * (δ / 2) + (δ / 2) * (δ / 2)) := by ring
        _ = 2 + δ ^ 2 / 4 := by
          have : (4 / δ) * (δ / 2) = 2 := by
            calc
              (4 / δ) * (δ / 2) = 4 * ((1 / 2) * (δ / δ)) := by ring
              _ = 4 * ((1 / 2) * 1) := by rw [div_self (ne_of_gt hδpos)]
              _ = 2 := by ring
          rw [this]
          have : (δ / 2) * (δ / 2) = δ ^ 2 / 4 := by ring
          rw [this]
    calc
      dist (x ^ 2) (x' ^ 2) = abs (x ^ 2 - x' ^ 2) := rfl
      _ = abs (x' ^ 2 - x ^ 2) := abs_sub_comm (x ^ 2) (x' ^ 2)
      _ = abs ((x' + x) * (x' - x)) := by rw [pow_two_sub_pow_two]
      _ = abs (x' + x) * abs (x' - x) := IsAbsoluteValue.abv_mul norm (x' + x) (x' - x)
      _ = (x' + x) * (x' - x) := by rw [abs_of_nonneg (le_of_lt hdx'xpos), abs_of_nonneg (le_of_lt hax'xpos)]
      _ = 2 + δ ^ 2 / 4 := by rw [had]
      _ = 1 + (1 + δ ^ 2 / 4) := by ring
      _ ≥ 1 := by
        have : 1 + δ ^ 2 / 4 ≥ 0 := add_nonneg zero_le_one (div_nonneg (pow_two_nonneg δ) zero_le_four)
        exact le_add_of_nonneg_right this
  exact not_le_of_gt hdxx'δ this

-- A continuous function from a compact metric space
-- to a metric space is uniformly continuous.
-- Given:
--   metric spaces X and Y
--   function f : X → Y
-- If:
--   X is compact
--   f is continuous
-- Then:
--   f is uniformly continuous
example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f :=
  by
  -- By the definition of uniform continuity,
  -- show ∀ ε > 0, ∃ δ > 0, ∀ x, x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
  rw [Metric.uniformContinuous_iff]
  -- Let ε > 0.
  -- Show ∃ δ > 0, ∀ x, x' ∈ X, dist(x', x) < δ → dist(f(x'), f(x)) < ε.
  intro ε hεpos
  -- Let φ : X × X → ℝ s.t. φ(x, x') = dist(f(x), f(x')).
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  -- From before, φ is continuous.
  have hφ : Continuous φ := hf.fst'.dist hf.snd'
  -- Let K = { (x, x') ∈ X × X | ε ≤ φ(x, x') }.
  let K := { p : X × X | ε ≤ φ p }
  -- Since X is compact, X × X is compact.
  -- Since φ is continuous and ε is a constant function, which is continuous,
  -- K is closed. Hence, K is compact since X × X is compact.
  have hK : IsCompact K := (isClosed_le continuous_const hφ).isCompact
  -- K is either empty or non-empty.
  rcases eq_empty_or_nonempty K with (hKemp | hKnemp)
  · -- Suppose K is empty.
    -- Use δ = 1.
    use 1
    -- Show δ > 0 and ∀ x, x' ∈ X, dist(x', x) < δ → φ(x', x) < ε.
    constructor
    · -- δ = 1 > 0.
      exact zero_lt_one
    · -- Let x, x' ∈ X. Suppose dist(x', x) < δ = 1.
      -- Show φ(x', x) < ε.
      intro x x' _
      -- Suppose φ(x', x) ≥ ε for a proof by contradiction.
      by_contra! h
      -- Then, (x, x') ∈ K.
      have : (x, x') ∈ K := h
      -- Since K is empty, this is a contradiction.
      rw [hKemp] at this
      exact this
  · -- Suppose K is non-empty.
    -- Using the Extreme Value Theorem, there exists
    -- a minimum (x, x') ∈ K of φ.
    rcases hK.exists_isMinOn hKnemp continuous_dist.continuousOn with ⟨⟨x, x'⟩, hxK, hxinf⟩
    -- Let δ = dist(x, x').
    use dist x x'
    -- Show δ > 0 and ∀ a, b ∈ X, dist(a, b) < δ → φ(a, b) < ε.
    constructor
    · -- Show δ > 0.
      -- Since δ = dist(x, x'), show x ≠ x'.
      apply dist_pos.mpr
      -- Suppose x = x' for a proof by contradiction.
      intro h
      -- ε ≤ φ(x, x') (∵ (x, x') ∈ K)
      --   = dist(f(x), f(x')) = dist(f(x), f(x)) = 0.
      have : ε ≤ 0 := by
        calc
          ε ≤ φ (x, x') := hxK
          _ = dist (f x) (f x') := rfl
          _ = dist (f x) (f x) := by rw [h]
          _ = 0 := dist_self (f x)
      -- Since ε > 0, this is a contradiction.
      exact not_le_of_gt hεpos this
    · -- Show ∀ a, b ∈ X, dist(a, b) < δ → φ(a, b) < ε.
      -- Let a, b ∈ X. Suppose dist(a, b) < δ.
      -- Show φ(a, b) < ε.
      intro a b h
      -- Suppose φ(a, b) ≥ ε for a proof by contradiction.
      by_contra! h'
      -- Then, (a, b) ∈ K.
      have : (a, b) ∈ K := h'
      -- Since we know that (x, x') is the minimum of φ,
      -- dist(a, b) ≥ φ(x, x') = δ.
      rw [isMinOn_iff] at hxinf
      have : dist a b ≥ dist x x' := hxinf (a, b) this
      -- Since dist(a, b) < δ, this is a contradiction.
      exact not_le_of_gt h this

-- 10.2.5. Completeness

-- A Cauchy sequence is a sequence where terms get arbitrarily close to each other.

-- A sequence is Cauchy iff for every ε > 0, there exists an N s.t.
-- for all m, n ≥ N, dist(uₘ, uₙ) < ε.
--   ∀ ε > 0, ∃ N ∈ ℕ, ∀ m, n ≥ N, dist(uₘ, uₙ) < ε
example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

-- A sequence is Cauchy iff for every ε > 0, there exists an N s.t.
-- for all n ≥ N, dist(uₙ, u_N) < ε.
--   ∀ ε > 0, ∃ N ∈ ℕ, ∀ n ≥ N, dist(uₙ, u_N) < ε
example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

-- Convergent sequences (with limit in the space) are Cauchy.
-- Intuition: If a sequence converges to a point in the space,
--            then the terms get arbitrarily close to the limit,
--            and hence to each other.
example [MetricSpace X] {u : ℕ → X} {a : X} (hu : Tendsto u atTop (𝓝 a)) : CauchySeq u :=
  Tendsto.cauchySeq hu

-- The converse is not true in general.
-- Example: The sequence (uₙ) where uₙ = 1 / n in ℝ \ {0}
--          is Cauchy but does not converge in ℝ \ {0}.

-- A space is complete if every Cauchy sequence converges to a point *in the space*.
-- Intuition: the space has no "holes" or "gaps".
-- Example: ℝ with the usual metric is complete.
example : CompleteSpace ℝ := Real.instCompleteSpace

-- In a complete space, every Cauchy sequence converges to a point in the space.
-- Given:
--   metric space X
--   sequence (uₙ)
-- If:
--   X is complete
--   (uₙ) is Cauchy
-- Then:
--   there exists a limit x s.t. uₙ converges to x.
example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ (x : X), Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

-- Compact metric spaces are complete.
example [CompactSpace X] : CompleteSpace X := complete_of_compact

open BigOperators

open Finset

-- A sequence (uₙ) s.t. ∀ n ∈ ℕ, dist(uₙ, uₙ₊₁) ≤ (1 / 2)ⁿ is Cauchy.
-- Proof sketch:
--   1. Consider arbitrarily small ε > 0.
--   2. Show that there is an N s.t. 1 / 2 ^ N * 2 < ε.
--   3. dist(u_N, u_{N+k}) ≤ ∑_{n=N..N+k-1} dist(uₙ, u_{n+1})
--                         ≤ ∑_{i=0..k-1} (1 / 2) ^ {N + i}
--                         = 1 / 2 ^ N * ∑_{i=0..k-1} (1 / 2) ^ i
--                         ≤ 1 / 2 ^ N * 2 < ε
theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  -- Using the definition of a Cauchy sequence,
  -- Show ∀ ε > 0, ∃ N ∈ ℕ, ∀ n ≥ N, dist(uₙ, u_N) < ε.
  rw [Metric.cauchySeq_iff']
  -- Let ε > 0.
  -- Show ∃ N ∈ ℕ, ∀ n ≥ N, dist(uₙ, u_N) < ε.
  intro ε ε_pos
  -- Lemma: ∃ N ∈ ℕ, 1 / 2 ^ N < ε.
  -- Let N be such that 1 / 2 ^ N < ε.
  -- log2(1 / ε) < N-1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    -- Show ∃ N ∈ ℕ, 1 / 2 ^ N < ε.
    -- First, we can show that the sequence (1 / 2 ^ n) converges to 0.
    have : Tendsto (fun n : ℕ ↦ (1 / 2 ^ n : ℝ)) atTop (𝓝 0) := by
      -- Show the sequence (1 / 2 ^ n) converges to 0.
      -- Equivalently, show ((1 / 2) ^ n) converges to 0.
      simp_rw [← one_div_pow]
      -- Since 0 ≤ 1 / 2 < 1, (1 / 2) ^ n converges to 0.
      have h₁ : 1 / (2 : ℝ) ≥ 0 := one_div_nonneg.mpr zero_le_two
      have h₂ : 1 / (2 : ℝ) < 1 := one_half_lt_one
      exact tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂
    -- This means ∀ ε > 0, ∃ N ∈ ℕ, ∀ n ≥ N, dist(1 / 2 ^ n, 0) < ε.
    rw [Metric.tendsto_atTop] at this
    -- Using this with ε / 2 > 0, we can find N s.t.
    -- ∀ n ≥ N, dist(1 / 2 ^ n, 0) < ε / 2.
    rcases this (ε / 2) (half_pos ε_pos) with ⟨N, hN⟩
    -- Use N. Show  1 / 2 ^ N * 2 < ε.
    use N
    -- Since N ≥ N, dist(1 / 2 ^ N, 0) < ε / 2.
    have := hN N (le_refl N)
    -- Then, |1 / 2 ^ N| < ε / 2.
    rw [Real.dist_0_eq_abs] at this
    -- Since 1 / 2 ^ N > 0, 1 / 2 ^ N < ε / 2.
    have h : 0 ≤ 1 / (2 : ℝ) ^ N := one_div_nonneg.mpr (pow_nonneg zero_le_two N)
    rw [abs_of_nonneg h] at this
    -- Then 1 / 2 ^ N * 2 < (ε / 2) * 2 = ε.
    calc
      1 / 2 ^ N * 2 < (ε / 2) * 2 := by apply mul_lt_mul_of_pos_right this two_pos
      _ = ε := div_mul_cancel_of_invertible ε 2
  -- Use N.
  -- Show ∀ n ≥ N, dist(uₙ, u_N) < ε.
  use N
  -- Let n ≥ N.
  -- Show dist(uₙ, u_N) < ε.
  intro n hn
  -- Since n ≥ N, ∃ k ∈ ℕ s.t. n = N + k. Fix such k.
  -- Show dist(u_{N + k}, u_N) < ε.
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  -- dist(u_{N + k}, u_N) = dist(u_{N + 0}, u_{N + k})
  --                      ≤ ∑_{i=0..k-1}, dist(u_{N + i}, u_{N + (i + 1)})
  --                      ≤ ∑_{i=0..k-1}, (1 / 2) ^ (N + i)
  --                      = 1 / 2 ^ N * ∑_{i=0..k-1}, (1 / 2) ^ i
  --                      ≤ 1 / 2 ^ N * 2
  --                      < ε.
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by
      -- Show dist(u_{N + k}, u_N) = dist(u_{N + 0}, u_{N + k}).
      -- Since dist is symmetric, dist(u_{N + k}, u_N) = dist(u_N, u_{N + k}).
      rw [dist_comm]
      -- Since N = N + 0, dist(u_N, u_{N + k}) = dist(u_{N + 0}, u_{N + k}).
      rw [add_zero N]
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) :=
      -- Show dist(u_{N + 0}, u_{N + k}) ≤ ∑_{i=0..k-1} dist(u_{N + i}, u_{N + (i + 1)}).
      -- Using the triangle inequality,
      -- dist(u_{N + 0}, u_{N + k})
      -- = ‖ u_{N + 0} - u_{N + k} ‖
      -- = ‖ (u_{N + 0} - u_{N + 1}) + (u_{N + 1} - u_{N + 2}) + ... + (u_{N + (k - 1)} - u_{N + k}) ‖
      -- = ‖ ∑_{i=0..k-1} (u_{N + i} - u_{N + (i + 1)}) ‖
      -- ≤ ∑_{i=0..k-1} ‖ u_{N + i} - u_{N + (i + 1)} ‖
      -- = ∑_{i=0..k-1} dist(u_{N + i}, u_{N + (i + 1)}).
      dist_le_range_sum_dist (fun i => u (N + i)) k
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) :=
      -- Show ∑_{i=0..k-1} dist(u_{N + i}, u_{N + (i + 1)}) ≤ ∑_{i=0..k-1} (1 / 2) ^ (N + i).
      -- Since ∀ i = 0..k-1, dist(u_{N + i}, u_{N + (i + 1)}) ≤ (1 / 2) ^ (N + i),
      -- ∑_{i=0..k-1} dist(u_{N + i}, u_{N + (i + 1)}) ≤ ∑_{i=0..k-1} (1 / 2) ^ (N + i).
      sum_le_sum fun i _ => hu (N + i)
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by
      -- Show ∑_{i=0..k-1} (1 / 2) ^ (N + i) = 1 / 2 ^ N * ∑_{i=0..k-1} (1 / 2) ^ i.
      -- ∑_{i=0..k-1} (1 / 2) ^ (N + i)
      -- = ∑_{i=0..k-1} (1 / 2) ^ N * (1 / 2) ^ i
      -- = (1 / 2) ^ N * ∑_{i=0..k-1} (1 / 2) ^ i.
      -- = 1 / 2 ^ N * ∑_{i=0..k-1} (1 / 2) ^ i.
      simp_rw [← one_div_pow, pow_add, mul_sum]
    _ ≤ 1 / 2 ^ N * 2 := by
      -- Show 1 / 2 ^ N * ∑_{i=0..k-1} (1 / 2) ^ i ≤ 1 / 2 ^ N * 2.
      apply mul_le_mul_of_nonneg_left
      · -- Show ∑_{i=0..k-1} (1 / 2) ^ i ≤ 2.
        -- Since k ∈ ℕ, ∑_{i=0..k-1} (1 / 2) ^ i ≤ ∑_{i=0..∞} (1 / 2) ^ i = 2.
        exact sum_geometric_two_le k
      · -- Show 0 ≤ 1 / 2 ^ N.
        -- Since N ∈ ℕ and 2 ≥ 0, 2 ^ N > 0, 1 / 2 ^ N > 0.
        exact one_div_nonneg.mpr (pow_nonneg zero_le_two N)
    _ < ε :=
      -- From above, 1 / 2 ^ N * 2 < ε.
      hN

open Metric

-- A set is dense in a space if every point in the space is in the closure of the set.
-- Intuition: the set is "everywhere" in the space.
example (s : Set X) : Dense s = ∀ (x : X), x ∈ closure s := rfl

-- Example: ℚ is dense in ℝ.
-- Proof: there is a rational number between any two real numbers.
example : Dense (range ((↑) : ℚ → ℝ) : Set ℝ) := by
  rw [dense_iff_exists_between]
  intro a b hab
  rcases exists_rat_btwn hab with ⟨q, hq⟩
  use q
  exact ⟨mem_range_self q, hq⟩

-- The intersection of a family of open and dense sets in a complete space is dense.
-- Given:
--   metric space X
--   family of sets (fₙ)
-- If:
--   X is complete
--   ∀ n, fₙ is open
--   ∀ n, fₙ is dense
-- Then:
--   ⋂ fₙ is dense
-- Proof sketch:
--   1. For each index n, point x, and radius δ,
--      we can find a center y and a positive radius r s.t.
--      the closed ball centered at y with radius r is included in
--      both fₙ and the closed ball centered at x with radius δ.
--   2. To show that ⋂ fₙ is dense, we have to show that every point x in ⋂ fₙ
--      is in the closure of ⋂ fₙ.
--   3. Since closed balls centered at x form a basis of the neighborhood filter at x,
--      we have to find, for every positive radius ε, a point y in the closed ball of radius ε around x
--      belonging to all fₙ.
--   4. We construct inductively a sequence Fₙ = (cₙ, rₙ) such that
--      the closed ball cB(cₙ, rₙ) is included in the previous ball and in fₙ
--   5. The sequence of centers (cₙ) is Cauchy, and hence converges to a point y.
--   6. This point y is the point we want to find.
--        y belongs to all fₙ, and hence to ⋂ fₙ.
--        y belongs to all closed balls centered at x.
example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  -- Let B : ℕ → ℝ s.t. B(n) = (1 / 2) ^ n.
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  -- Then, since 1 / 2 > 0, ∀ n ∈ ℕ, B(n) > 0.
  have Bpos : ∀ n, 0 < B n := fun n => pow_pos (one_half_pos) n
  -- Since fₙ is dense ∀ n ∈ ℕ, we can find for each index n, point x, and δ > 0
  -- a center y and a positive radius r s.t. the closed ball centered at c with radius r
  --   is included in both fₙ and the closed ball centered at x with radius δ
  --   r ≤ B(n + 1) = (1 / 2) ^ (n + 1) (to ensure that the sequence (cₙ) is Cauchy)
  -- Formally, ∀ n ∈ ℕ, ∀ x ∈ X, ∀ δ > 0,
  --           ∃ y ∈ X, ∃ r > 0, r ≤ B(n + 1) ∧ cB(y, r) ⊆ cB(x, δ) ∩ fₙ
  have :
    ∀ (n : ℕ) (x : X), ∀ δ > 0,
    ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by
    -- Let n ∈ ℕ, x ∈ X, and δ > 0.
    -- Show ∃ y ∈ X, ∃ r > 0, r ≤ B(n + 1) and cB(y, r) ⊆ cB(x, δ) ∩ fₙ.
    intro n x δ hδpos
    -- Since fₙ is dense, ∀ x ∈ X, ∀ r > 0, ∃ y ∈ fₙ, y ∈ cB(x, r).
    have hdn := hd n
    rw [dense_iff] at hdn
    -- Use with center x and radius δ / 2 > 0,
    -- we get a point y ∈ fₙ s.t. y ∈ cB(x, δ / 2).
    rcases hdn x (δ / 2) (half_pos hδpos) with ⟨y, hyb, hyfn⟩
    -- Since fₙ is open, ∀ y ∈ fₙ, ∃ ε > 0 s.t. B(y, ε) ⊆ fₙ.
    have hon := ho n
    rw [Metric.isOpen_iff] at hon
    -- Use with y, we get ε > 0 s.t. B(y, ε) ⊆ fₙ.
    rcases hon y hyfn with ⟨ε, hεpos, hbyεfn⟩
    -- Let r = min(B(n + 1), δ / 2, ε / 2).
    -- Motivation:
    --   small enough radius r ≤ B(n + 1) as required
    --   since y ∈ cB(x, δ / 2), r ≤ δ / 2 to ensure cB(y, r) ⊆ cB(x, δ)
    --   since B(y, ε) ⊆ fₙ, r < ε to ensure cB(y, r) ⊆ fₙ
    let r := min (B (n + 1)) (min (δ / 2) (ε / 2))
    -- Then, r > 0
    have hrpos : r > 0 :=
      -- B(n + 1) > 0, δ / 2 > 0, ε / 2 > 0, so r > 0
      lt_min (Bpos (n + 1)) (lt_min (half_pos hδpos) (half_pos hεpos))
    -- and r ≤ B(n + 1)
    have hrB : r ≤ B (n + 1) :=
      -- r ≤ B(n + 1)
      min_le_left _ _
    -- and r ≤ δ / 2
    have hrδ : r ≤ δ / 2 :=
      -- r ≤ min(δ / 2, ε / 2) ≤ δ / 2
      le_trans (min_le_right _ _) (min_le_left _ _)
    -- and r < ε
    have hrε : r < ε :=
      -- r ≤ min(δ / 2, ε / 2) ≤ ε / 2 < ε
      lt_of_le_of_lt (min_le_right _ _)
        (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hεpos))
    use y, r, hrpos, hrB
    -- Show cB(y, r) ⊆ cB(x, δ) ∩ fₙ.
    -- Let z ∈ cB(y, r).
    intro z hz
    -- Show z ∈ cB(x, δ) and z ∈ fₙ.
    constructor
    · -- Show z ∈ cB(x, δ).
      -- Equivalently, show dist(z, x) ≤ δ.
      rw [mem_closedBall]
      -- dist(z, x) ≤ dist(z, y) + dist(y, x) (∵ triangle inequality)
      --            ≤ δ / 2 + δ / 2 (∵ z ∈ cB(y, r) with r ≤ δ / 2 and y ∈ cB(x, δ / 2))
      --            ≤ δ / 2 + δ / 2 = δ
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle z y x
        _ ≤ δ / 2 + δ / 2 := add_le_add (le_trans hz hrδ) (le_of_lt hyb)
        _ = δ := add_halves δ
    · -- Show z ∈ fₙ.
      -- Since B(y, ε) ⊆ fₙ, it suffices to
      -- show z ∈ B(y, ε).
      apply hbyεfn
      -- Equivalently, show dist(z, y) < ε.
      rw [mem_ball]
      -- Since z ∈ cB(y, r) with r < ε,
      -- dist(z, y) ≤ r < ε.
      exact lt_of_le_of_lt hz hrε
  -- Let `center` and `radius` be functions s.t.
  -- `center`(n, c, δ) = y and `radius`(n, c, δ) = r s.t.
  --   cB(y, r) ⊆ cB(c, δ) ∩ fₙ
  --   r ≤ B(n + 1)
  choose! center radius Hpos HB Hball using this
  -- Let x ∈ X.
  -- Show x ∈ cl(⋂ fₙ).
  intro x
  -- Since closed balls form a basis of the neighborhood filter at x, to show x ∈ cl(⋂ fₙ)
  -- we have to find, for every positive radius ε,
  -- a point y in the closed ball of radius ε around x
  -- belonging to all fₙ.
  -- Show ∀ ε > 0, ∃ y ∈ ⋂ fₙ, y ∈ cB(x, ε).
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  -- Let ε > 0.
  -- Show ∃ y ∈ ⋂ fₙ, y ∈ cB(x, ε).
  intro ε εpos
  -- We construct inductively a sequence Fₙ = (cₙ, rₙ) such that
  -- the closed ball cB(cₙ, rₙ)
  --   is included in the previous ball and in fₙ
  --     i.e., cB(cₙ, rₙ) ⊆ cB(c_{n-1}, r_{n-1}) ∩ fₙ
  --   the radius is positive and small enough that cₙ is a Cauchy sequence
  --     i.e., 0 < rₙ ≤ B(n)
  -- Specifically,
  --   F₀ = (c₀, r₀)      Fₙ₊₁ = (cₙ₊₁, rₙ₊₁)
  -- where
  --   c₀ = x             cₙ₊₁ = `center`(n, cₙ, rₙ)
  --   r₀ = B(0)          rₙ₊₁ = `radius`(n, cₙ, rₙ)
  -- By the definition of `center` and `radius`, the properties are satisfied.
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n
      (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  -- We show that rₙ > 0 for all n.
  have rpos : ∀ n, 0 < r n := by
    -- Let n ∈ ℕ.
    intro n
    -- We prove by induction on n.
    -- IH: If rₙ > 0, then rₙ₊₁ > 0.
    induction' n with n hn
    · -- Show r₀ = min(ε, B(0)) > 0.
      -- Since ε > 0 and B(0) > 0 (∵ B(n) > 0 for all n),
      -- r₀ > 0.
      exact lt_min εpos (Bpos 0)
    · -- Show rₙ₊₁ = `radius`(n, cₙ, rₙ) > 0.
      -- By the IH, rₙ > 0.
      -- Then, `radius`(n, cₙ, rₙ) > 0.
      -- Thus, rₙ₊₁ > 0.
      exact Hpos n (c n) (r n) hn
  -- We show that rₙ ≤ B(n) for all n.
  have rB : ∀ n, r n ≤ B n := by
    -- Let n ∈ ℕ.
    intro n
    -- We prove by induction on n.
    -- IH: If rₙ ≤ B(n), then rₙ₊₁ ≤ B(n + 1).
    induction' n with n hn
    · -- Show r₀ = min(ε, B(0)) ≤ B(0).
      -- Since r₀ = min(ε, B(0)), r₀ ≤ B(0).
      exact min_le_right ε (B 0)
    · -- Show rₙ₊₁ = `radius`(n, cₙ, rₙ) ≤ B(n + 1).
      -- Since rₙ > 0 (∵ rₙ > 0 for all n),
      -- `radius`(n, cₙ, rₙ) ≤ B(n + 1).
      exact HB n (c n) (r n) (rpos n)
  -- We show that cB(cₙ₊₁, rₙ₊₁) ⊆ cB(cₙ, rₙ) ∩ fₙ for all n.
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    -- Let n ∈ ℕ.
    intro n
    -- By the definition of `center` and `radius`,
    -- with rₙ > 0 (∵ rₙ > 0 for all n),
    -- cB(cₙ₊₁, rₙ₊₁) = cB(`center`(n, cₙ, rₙ), `radius`(n, cₙ, rₙ))
    --                ⊆ cB(cₙ, rₙ) ∩ fₙ.
    exact Hball n (c n) (r n) (rpos n)
  -- We show that dist(cₙ, cₙ₊₁) ≤ B(n) for all n.
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by
    -- Let n ∈ ℕ.
    intro n
    -- Since rₙ₊₁ > 0 (∵ rₙ₊₁ > 0 for all n), rₙ₊₁ ≥ 0.
    -- Then, cₙ₊₁ ∈ cB(cₙ₊₁, rₙ₊₁) (∵ cₙ₊₁ is the center of the ball).
    -- Since cB(cₙ₊₁, rₙ₊₁) ⊆ cB(cₙ, rₙ) ∩ fₙ, cₙ₊₁ ∈ cB(cₙ, rₙ) ∩ fₙ.
    -- Thus, cₙ₊₁ ∈ cB(cₙ, rₙ).
    have : c (n + 1) ∈ closedBall (c n) (r n) :=
      (rpos (n + 1) |> le_of_lt |> mem_closedBall_self |> incl n).left
    -- Then, dist(cₙ, cₙ₊₁) ≤ rₙ.
    rw [mem_closedBall'] at this
    -- Since rₙ ≤ B(n), dist(cₙ, cₙ₊₁) ≤ B(n).
    exact le_trans this (rB n)
  -- Using that and the above result, we show that the sequence (cₙ) is Cauchy.
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- As (cₙ) is Cauchy in a complete space, it converges to a limit y.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- Use y.
  -- Show y ∈ ⋂ fₙ and y ∈ cB(x, ε).
  use y
  -- We have that ∀ n ∈ ℕ, ∀ m ≥ n, cB(cₘ, rₘ) ⊆ cB(cₙ, rₙ).
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    -- Let n ∈ ℕ.
    intro n
    -- We prove by induction on m.
    apply Nat.le_induction
    · -- Show cB(cₙ, rₙ) ⊆ cB(cₙ, rₙ).
      exact subset_refl (closedBall (c n) (r n))
    · -- Show ∀ m ≥ n, cB(cₘ, rₘ) ⊆ cB(cₙ, rₙ) → cB(cₘ₊₁, rₘ₊₁) ⊆ cB(cₙ, rₙ).
      -- Let m ≥ n. Suppose cB(cₘ, rₘ) ⊆ cB(cₙ, rₙ).
      -- Show cB(cₘ₊₁, rₘ₊₁) ⊆ cB(cₙ, rₙ).
      intro m _ hss
      -- cB(cₘ₊₁, rₘ₊₁) ⊆ cB(cₘ, rₘ) ∩ fₘ ⊆ cB(cₘ, rₘ) ⊆ cB(cₙ, rₙ)
      exact ((incl m).trans Set.inter_subset_left).trans hss
  -- Then, ∀ n ∈ ℕ, y ∈ cB(cₙ, rₙ).
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by
    -- Let n ∈ ℕ.
    -- Show y ∈ cB(cₙ, rₙ).
    intro n
    -- Since cB(cₙ, rₙ) is closed,
    -- for the limit y of the sequence (cₙ) to be in cB(cₙ, rₙ),
    -- it suffices to show that cₘ ∈ cB(cₘ, rₘ) for sufficiently large m.
    apply isClosed_ball.mem_of_tendsto ylim
    -- Equivalently, show that for all m ≥ n, cₘ ∈ cB(cₙ, rₙ).
    apply (eventually_ge_atTop n).mono
    -- Let m ≥ n.
    intro m hnm
    -- Since m ∈ ℕ, r(m) > 0 and hence r(m) ≥ 0.
    -- Then, c(m) ∈ cB(c(m), r(m)).
    -- Since m ≥ n, cB(c(m), r(m)) ⊆ cB(c(n), r(n)),
    -- i.e., c(m) ∈ cB(c(n), r(n)).
    exact rpos m |> le_of_lt |> mem_closedBall_self |> I n m hnm
  constructor
  · -- Show y ∈ ⋂ fₙ.
    -- Equivalently, show ∀ n ∈ ℕ, y ∈ fₙ.
    rw [mem_iInter]
    -- Let n ∈ ℕ.
    intro n
    -- Since y ∈ cB(cₙ₊₁, rₙ₊₁) (∵ y ∈ cB(cₙ, rₙ) for all n),
    -- and cB(cₙ₊₁, rₙ₊₁) ⊆ cB(cₙ, rₙ) ∩ fₙ ⊆ fₙ,
    -- y ∈ fₙ.
    exact ((n + 1) |> yball |> incl n).right
  · -- Show y ∈ cB(x, ε).
    -- Equivalently, show dist(y, x) ≤ ε.
    rw [mem_closedBall]
    -- We have y ∈ cB(c₀, r₀) = cB(x, min(ε, B(0))).
    -- Then, dist(y, x) ≤ r₀ = min(ε, B(0)).
    -- Thus, dist(y, x) ≤ min(ε, B(0)) ≤ ε.
    exact le_trans (yball 0) (min_le_left ε (B 0))
