import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Data.Real.Irrational

open Set Filter Topology

-- 10.3. Topological spaces

-- 10.3.1. Fundamentals

-- There is no need to rely on a metric to define a topology.

-- First point of view: using open sets

-- A topological space is a set X and a topology on X.
-- A topology on X is a collection of subsets of X, called open sets, s.t.
--   1. The empty set and X are open.
--   2. The union of any collection of open sets is open.
--   3. The intersection of any finite collection of open sets is open.

-- Intuition: an open set contains a neighborhood of each of its points.
-- Intuition: an open set is a neighborhood around each of its points.

section

-- Let X be a topological space.
variable {X : Type*} [TopologicalSpace X]

-- X is open.
-- Intuition: X contains all neighborhoods,
--            including all neighborhoods of its points.
example : IsOpen (univ : Set X) :=
  isOpen_univ

-- The empty set ∅ is open.
-- Intuition: the empty set contains no points,
--            so it trivially contains all neighborhoods of its points.
example : IsOpen (∅ : Set X) :=
  isOpen_empty

-- The union of any collection of open sets is open.
-- Note that there is no restriction on the index set ι.
-- Intuition: the union of neighborhoods is a neighborhood.
example {ι : Type*} {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) :=
  isOpen_iUnion hs

-- The intersection of any finite collection of open sets is open.
-- Note that the index set ι is finite.
-- Intuition: finite intersection of neighborhoods is a neighborhood.
--            however, if there are infinitely many neighborhoods,
--            the intersection may "zoom in" too much and not be a neighborhood.
example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) :=
  isOpen_iInter_of_finite hs

-- Example: ⋂ₙ (-1/(n+1), 1/(n+1)) is closed
-- Proof: the intersection is {0}, which is closed.
example : IsClosed (⋂ n : ℕ, Ioo (-(1 : ℝ) / (n + 1)) ((1 : ℝ) / (n + 1))) := by
  -- Show ⋂ₙ (-1/(n+1), 1/(n+1)) = {0}.
  have : (⋂ n : ℕ, Ioo (-(1 : ℝ) / (n + 1)) ((1 : ℝ) / (n + 1))) = {0} := by
    ext x
    constructor
    · -- Suppose x ∈ ⋂ₙ (-1/(n+1), 1/(n+1)).
      -- Show x = 0.
      intro h
      -- Then, ∀ n ∈ ℕ, x ∈ (-1/(n+1)) (1/(n+1)).
      rw [mem_iInter] at h
      -- Suppose for contradiction x ≠ 0.
      by_contra! hxne0
      by_cases hx : 0 < x
      · -- Case 1: x > 0.
        -- Then, ∃ n ∈ ℕ, x > 1/(n+1).
        rcases exists_nat_one_div_lt hx with ⟨n, hxn⟩
        -- Fix such n. We have x ∈ (-1/(n+1), 1/(n+1)).
        have := h n
        -- This is a contradiction.
        exact not_lt_of_le (le_of_lt this.right) hxn
      · -- Case 2: x < 0.
        push_neg at hx
        have hx := lt_of_le_of_ne hx hxne0
        -- Then, ∃ n ∈ ℕ, x < -1/(n+1).
        rcases exists_nat_one_div_lt (neg_pos.mpr hx) with ⟨n, hxn⟩
        -- Fix such n. We have x ∈ (-1/(n+1), 1/(n+1)).
        have := h n
        -- This is a contradiction.
        have := this.left
        rw [neg_div, neg_lt] at this
        exact not_lt_of_lt hxn this
    · -- Suppose x = 0.
      -- Show x ∈ ⋂ n, (-1/(n+1), 1/(n+1)).
      intro h
      -- Show ∀ n ∈ ℕ, x ∈ (-1/(n+1), 1/(n+1)).
      rw [mem_iInter]
      -- Let n ∈ ℕ.
      -- show x ∈ (-1/(n+1), 1/(n+1)).
      intro n
      -- Show -1/(n+1) < x < 1/(n+1).
      rw [mem_Ioo]
      constructor
      · -- Show -1/(n+1) < x.
        -- Since x = 0, this is trivial.
        rw [h]
        rw [neg_div]
        exact neg_neg_of_pos Nat.one_div_pos_of_nat
      · -- Show x < 1/(n+1).
        -- Since x = 0, this is trivial.
        rw [h]
        exact Nat.one_div_pos_of_nat
  -- The intersection is {0}, which is closed.
  rw [this]
  exact isClosed_singleton

-- Some view this collection of axioms as redundant:
--   The empty set is open because it is the union of no open sets.
--   The universe is open because it is the intersection of no open sets.

-- Let Y be a topological space.
variable {Y : Type*} [TopologicalSpace Y]

-- A set is closed if its complement is open.
example {S : Set X} : IsOpen Sᶜ ↔ IsClosed S := isOpen_compl_iff

-- A function between two topological spaces is continuous
-- if the preimage of every open set in the codomain is open in the domain.
-- Intuition: continuous function preserves "neighborhoods",
--            i.e., points that are close together in the domain
--                  are mapped to points that are close together in the codomain.
example {f : X → Y} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

-- A topological structure determines which functions (with domain
-- and codomain in the topological space) are continuous.
-- Two topological structures on the same set are the same
-- if they have the same continuous functions.
-- The identity function is used as a witness of equivalence:
--   if the identity function is continuous in both directions,
--   then an open set in one topology has to be open in the other topology,
--   thus the two topologies are the same.

-- Second point of view: using neighborhoods

-- A topological space is a set equipped with
-- a neighborhood filter 𝓝(x) attached to each point x,
-- i.e., there is a neighborhood function mapping each point x to a filter 𝓝(x)
--       called the neighborhood of x.
-- Two roles of this neighborhood filter (as previously studied):
-- 1. 𝓝(x) is the generalized set of points of X close to x.
-- 2. 𝓝(x) gives a way to say a predicate `P : X → Prop` holds
--    for points close enough to x.

-- Motivation: easier to talk about continuity at a point

-- Continuity at a point:

-- Filter
-- A function f : X → Y is continuous at x if
-- the direct image under f of the generalized set of points close to x
-- is contained in the generalized set of points close to f(x).
-- Formally, f(𝓝(x)) ≤ 𝓝(f(x))
-- i.e., 𝓝(f(x)) ⊆ f(𝓝(x)) (not expressible in Lean)
-- i.e., ∀ V ∈ 𝓝(f(x)), V ∈ f(𝓝(x))
-- i.e., ∀ V ∈ 𝓝(f(x)), f⁻¹(V) ∈ 𝓝(x)
-- i.e., ∀ V ∈ 𝓝(f(x)), ∃ U ∈ 𝓝(x), f(U) = V
-- Note: it does not mean any neighborhood of x is mapped to a neighborhood of f(x)
--       more like there exists a neighborhood of x mapped to any neighborhood of f(x)
example {f : X → Y} {x : X} : ContinuousAt f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) :=
  Iff.rfl

-- Ordinary set
-- A function f is continuous at x iff
-- for every neighborhood U of f(x), all points sufficiently close to x
-- are sent to U.
example {f : X → Y} {x : X} : ContinuousAt f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U :=
  Iff.rfl

-- Recall there are two points of view: open sets and neighborhood filters
-- We can go between two points of view.

-- From open sets to neighborhood filters:
-- Constructing neighborhood filters from open sets:
-- Given a point x in a topological space X equipped with a topology,
-- the neighborhood filter is defined as follows:
-- A set S ∈ 𝓝(x) (S is a neighborhood of x) iff
-- S contains an open set containing x.
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff

-- From neighborhood filters to open sets:
-- The function `𝓝 : X → Filter X` needs to satisfy some properties
-- to define a topology on X.

-- The `pure x` filter:
--   generated by {x}
--   containing all sets containing x
example {x : X} : 𝓟 {x} = pure x := principal_singleton x

-- All subsets in 𝓟({x}) contains x
-- since each of them contains {x} as a subset.
example {x : X} {S : Set X} : S ∈ 𝓟 {x} → x ∈ S := fun hSPx ↦ hSPx rfl

-- Property 1: a point is close to itself
--   𝓝(x) contains {x}
--   `pure x` ≤ 𝓝(x)
example (x : X) : pure x ≤ 𝓝 x :=
  pure_le_nhds x

-- Any property that holds for points close enough to x also holds for x itself.
-- Given a point x ∈ X and a proposition P(⬝) on X
-- If P(y) holds for y sufficiently close to x
-- then P(x) holds
example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x :=
  h.self_of_nhds

-- Property 2: nearness is transitive
-- Given a point x ∈ X and a proposition P(·) on X
-- If P(y) holds for y sufficiently close to x
-- then for y sufficiently close to x and z sufficiently close to y, P(z) holds.
-- Intuition: if y is in a neighborhood of x and z is in a neighborhood of y,
--            then z is in a (potentially larger) neighborhood of x.
-- Note: this actually goes both way
example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
  eventually_eventually_nhds.mpr h

-- Construct a topological space from a neighborhood function
-- However it only produces a topology where the neighborhood function
-- satisfies the two properties.
#check TopologicalSpace.mkOfNhds

-- If a neighborhood function satisfies two properties
-- then it is the same as the "true" neighborhood function.
#check TopologicalSpace.nhds_mkOfNhds

-- A neighborhood function (mapping each point to a filter)
-- satisfying the two properties above will also satisfy:
-- for any point x ∈ X and any neighborhood S of x
-- there exists a neighborhood T ⊆ S such that any point x' ∈ T
-- S is also a neighborhood of x'.
-- Given:
--   neighborhood function n : X → Filter X
-- If:
--   (property 1) ∀ x ∈ X, 𝓟({x}) ≤ n(x)
--   (property 2) ∀ x ∈ X, ∀ proposition P(·) on X,
--                if ∀ᶠ y ∈ n(x), P(y) holds then ∀ᶠ y ∈ n(x), ∀ᶠ z ∈ n(y), P(z) holds
-- Then
--   ∀ x ∈ X, ∀ S ∈ n(x), ∃ T ∈ n(x) s.t. T ⊆ S and ∀ x' ∈ T, S ∈ n(x')
example {X : Type*} (n : X → Filter X) (H₁ : ∀ x, pure x ≤ n x)
    (H₂ : ∀ x : X, ∀ P : X → Prop, (∀ᶠ y in n x, P y) → ∀ᶠ y in n x, ∀ᶠ z in n y, P z) :
    ∀ x, ∀ S ∈ n x, ∃ T ∈ n x, T ⊆ S ∧ ∀ y ∈ T, S ∈ n y := by
  -- Let x ∈ X, S ⊆ X s.t. S ∈ n(x).
  -- Show: ∃ T ∈ n(x) s.t. T ⊆ S and ∀ x' ∈ T, S ∈ n(x')
  intro x S hSnx
  -- Let T = {x | S ∈ n(x)}
  -- i.e., T contains all points x having S as its neighborhood.
  use {y | S ∈ n y}
  -- Show T ∈ n(x)
  have hT₁ : {y | S ∈ n y} ∈ n x :=
    -- In Lean, we can just write:
    -- `H₂ x S hSnx`
    -- but that is not clear to me.
    by
    -- Since S ∈ n(x), ∀ᶠ y ∈ n(x), y ∈ S, read,
    -- for y sufficiently close to x, y ∈ S.
    have : S ∈ n x ↔ (∀ᶠ y in n x, y ∈ S) := Iff.rfl
    rw [this] at hSnx
    -- The goal of T ∈ n(x) can be equivalently written as
    -- ∀ᶠ y ∈ n x, S ∈ n(y), read,
    -- for y sufficiently close to x, S ∈ n(y)
    -- or, equivalently,
    -- ∀ᶠ y ∈ n x, ∀ᶠ z ∈ n y, z ∈ S, read,
    -- for y sufficiently close to x, for z sufficiently close to y, z ∈ S.
    have : ({y | S ∈ n y} ∈ n x) ↔ (∀ᶠ y in n x, ∀ᶠ z in n y, z ∈ S) := eventually_iff
    rw [this]
    -- We apply the "transitivity of nearness" property with x and P(⬝) = ⬝ ∈ S.
    exact H₂ x S hSnx
  -- Show T ⊆ S
  have hT₂ : {y | S ∈ n y} ⊆ S :=
    -- Let y ∈ T. Then, S ∈ n(y).
    -- Since n(y) ⊆ 𝓟({y}), S ∈ 𝓟({y}).
    -- Thus, y ∈ S.
    fun y hSny ↦ H₁ y hSny
  -- Show ∀ x' ∈ T, S ∈ n(x')
  have hT₃ : ∀ y ∈ {y | S ∈ n y}, S ∈ n y :=
    -- Let y ∈ T. Then, S ∈ n(y).
    fun y a ↦ a
  -- We complete the proof.
  exact ⟨hT₁, hT₂, hT₃⟩

end

-- Let X and Y be two spaces.
variable {X Y : Type*}

-- Comparing between topological spaces and metric spaces

-- Functoriality: ability to construct new structures from existing ones
-- for spaces, define structures on subsets, quotients, products, etc.

-- Metric space has limited functoriality
-- A metric space structure can be induced on a subset or,
-- equivalently, it can be pulled back by an injective map.

-- Inducing a metric space on a subset
-- Let (X, d) be a metric space. Let A ⊆ X.
-- Then, (A, dA) where dA(a₁, a₂) = d(a₁, a₂) ∀ a₁, a₂ ∈ A, is a metric space.
def SubsetMetricSpace {X : Type*} [MetricSpace X] (A : Set X) :
  MetricSpace A where
  eq_of_dist_eq_zero := by
    intro a₁ a₂ h
    exact eq_of_dist_eq_zero h

-- Inducing a metric space by pulling back an injective map
-- Let f : A → X be an injective map from a set A to a metric space (X, d).
-- Then, (A, df) where df(a₁, a₂) = d(f(a₁), f(a₂)) ∀ a₁, a₂ ∈ A, is a metric space.
-- Injective is necessary to ensure df(a₁, a₂) = 0 → a₁ = a₂.
def PullbackMetricSpace {A X : Type*} (hX: MetricSpace X) (f : A → X) (hf : Function.Injective f)
  : MetricSpace A where
  dist := fun a₁ a₂ => hX.dist (f a₁) (f a₂)
  dist_self := fun a => hX.dist_self (f a)
  dist_comm := fun a₁ a₂ => hX.dist_comm (f a₁) (f a₂)
  dist_triangle := fun a₁ a₂ a₃ => hX.dist_triangle (f a₁) (f a₂) (f a₃)
  eq_of_dist_eq_zero := by
    intro a₁ a₂ h
    exact hf (hX.eq_of_dist_eq_zero h)

-- Inducing a metric space on a subset is pulling back by the inclusion map.
def SubsetMetricSpace' {X : Type*} [hX: MetricSpace X] (A : Set X) : MetricSpace A :=
  PullbackMetricSpace hX ((↑) : A → X) Subtype.coe_injective

-- The two metric space structures are the same.
example {X : Type*} [MetricSpace X] (A : Set X)
  : SubsetMetricSpace A = SubsetMetricSpace' A :=
  MetricSpace.ext rfl

-- Pulling back a metric space by an injective map is inducing a metric space on the image.
def PullbackMetricSpace' {A X : Type*} (hX : MetricSpace X) (f : A → X) (hf : Function.Injective f)
  : MetricSpace A where
  dist := fun a₁ a₂ ↦
    (SubsetMetricSpace (Set.range f)).dist (rangeFactorization f a₁) (rangeFactorization f a₂)
  dist_self := fun x ↦
    hX.dist_self (rangeFactorization f x)
  dist_comm := fun x y ↦
    hX.dist_comm (rangeFactorization f x) (rangeFactorization f y)
  dist_triangle := fun x y z ↦
    hX.dist_triangle (rangeFactorization f x) (rangeFactorization f y) (rangeFactorization f z)
  eq_of_dist_eq_zero := by
    intro a₁ a₂ h
    exact hf (hX.eq_of_dist_eq_zero h)

-- The two metric space structures are the same.
example {A X : Type*} (hX : MetricSpace X) (f : A → X) (hf : Function.Injective f)
  : PullbackMetricSpace hX f hf = PullbackMetricSpace' hX f hf :=
  MetricSpace.ext rfl

-- But that is pretty much everything for metric spaces.

-- For topological spaces, arbitrary functions can induce a new topology.

-- Given f : X → Y, a topology T_X on X can be pushed forward to a topology on Y,
-- denoted by f_* T_X.
example (f : X → Y) : TopologicalSpace X → TopologicalSpace Y :=
  TopologicalSpace.coinduced f

-- V is open in (Y, T_Y) if its preimage is open in (X, T_X).
def PushforwardTopologicalSpace {X Y : Type*} (T_X : TopologicalSpace X) (f : X → Y)
  : TopologicalSpace Y where
  IsOpen V := T_X.IsOpen (f ⁻¹' V)
  isOpen_univ := T_X.isOpen_univ
  isOpen_inter V V' := T_X.isOpen_inter (f ⁻¹' V) (f ⁻¹' V')
  isOpen_sUnion S := by
    intro hS
    rw [preimage_sUnion]
    exact isOpen_biUnion hS

example [hX : TopologicalSpace X] (f : X → Y) (V : Set Y)
  : (hX.coinduced f).IsOpen V ↔ hX.IsOpen (f ⁻¹' V)
  := isOpen_coinduced

-- Given f : X → Y, a topology T_Y on Y can be pulled back to a topology on X,
-- denoted by f^* T_Y.
example (f : X → Y) : TopologicalSpace Y → TopologicalSpace X :=
  TopologicalSpace.induced f

-- U is open in (X, T_X) iff U is the preimage of some open set in (Y, T_Y).
def PullbackTopologicalSpace {X Y : Type*} (T_Y : TopologicalSpace Y) (f : X → Y)
  : TopologicalSpace X where
  IsOpen := fun U => ∃ (V : Set Y), T_Y.IsOpen V ∧ f ⁻¹' V = U
  isOpen_univ := by
    use univ
    exact ⟨T_Y.isOpen_univ, rfl⟩
  isOpen_inter U U' := by
    rintro ⟨V, hV, rfl⟩ ⟨V', hV', rfl⟩
    use V ∩ V'
    exact ⟨T_Y.isOpen_inter V V' hV hV', rfl⟩
  isOpen_sUnion S := by
    intro hS
    choose! g h₁ h₂ using hS
    use ⋃₀ (g '' S)
    constructor
    · apply T_Y.isOpen_sUnion
      rintro _ ⟨U, hU, rfl⟩
      exact h₁ U hU
    · rw [preimage_sUnion, biUnion_image, sUnion_eq_biUnion]
      exact iUnion₂_congr h₂

example [hY : TopologicalSpace Y] (f : X → Y) (U : Set X)
  : (hY.induced f).IsOpen U ↔ ∃ (V : Set Y), hY.IsOpen V ∧ f ⁻¹' V = U
  := isOpen_induced_iff

-- Push and pull operations form a Galois connection.
--   f_* T_X ≤ T_Y ↔ T_X ≤ f^* T_Y
example (f : X → Y) (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) :
    TopologicalSpace.coinduced f T_X ≤ T_Y ↔ T_X ≤ TopologicalSpace.induced f T_Y :=
  coinduced_le_iff_le_induced

-- Given f : X → Y and g : Y → Z, (g ∘ f)_* T_X = g_* (f_* T_X).
-- (pushing forward is covariant)
#check coinduced_compose

-- Given f : X → Y and g : Y → Z, (g ∘ f)^* T_Z = f^* (g^* T_Z).
-- (pulling back is contravariant)
#check induced_compose

-- Order on topologies
-- Want:
--   f(T) = 𝓝_T(x) is order preserving
--   i.e., ∀ x ∈ X, if T ≤ T' then 𝓝_T(x) ≤ 𝓝_T'(x)
--   i.e., every neighborhood of a point according to T'
--         is a neighborhood of that point according to T
--         but there may be more neighborhoods of the point according to T
--   Intuition: T' has a stricter requirement regarding neighborhoods of a point
-- Therefore:
--   T ≤ T' if any open V in T' is open in T
example {T T' : TopologicalSpace X} : T ≤ T' ↔ ∀ s, T'.IsOpen s → T.IsOpen s :=
  Iff.rfl

-- T ≤ T' iff for all X, 𝓝_T(x) ≤ 𝓝_T'(x)
-- reads as "T is finer than T'"
example {T T' : TopologicalSpace X} : T ≤ T' ↔ ∀ x, @nhds X T x ≤ @nhds X T' x :=
  le_iff_nhds T T'

-- f is continuous wrt T_X and T_Y iff f_* T_X ≤ T_Y
-- Note: f_* T_X is the finest/"smallest"/"has the most sets" topology on Y making f continuous
example (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) (f : X → Y) :
    Continuous f ↔ TopologicalSpace.coinduced f T_X ≤ T_Y :=
  continuous_iff_coinduced_le

-- f is continuous wrt T_X and T_Y iff T_X ≤ f^* T_Y
-- f^* T_Y is the coarsest/"largest"/"has the fewest sets" topology on X making f continuous
-- (related to the Galois connection: f_* T_X ≤ T_Y ↔ T_X ≤ f^* T_Y)
example (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) (f : X → Y) :
    Continuous f ↔ T_X ≤ TopologicalSpace.induced f T_Y :=
    continuous_iff_coinduced_le.trans coinduced_le_iff_le_induced
    -- or, `continuous_iff_le_induced`

-- Universal property of the pushforward topology:
-- Given:
--   f : X → Y, g : Y → Z
--   topology T_X on X
-- Then:
--   for every topology T_Z on Z,
--   g is continuous wrt f_* T_X and T_Z iff
--   g ∘ f is continuous wrt T_X and T_Z
-- Proof: g is continuous ↔ g_* (f_* T_X) ≤ T_Z ↔ (g ∘ f)_* T_X ≤ T_Z ↔ g ∘ f is continuous
example {Z : Type*} (f : X → Y) (g : Y → Z) (T_X : TopologicalSpace X) (T_Z : TopologicalSpace Z)
  : Continuous[T_X.coinduced f, T_Z] g ↔ Continuous[T_X, T_Z] (g ∘ f) := by
  rw [continuous_iff_coinduced_le, coinduced_compose, continuous_iff_coinduced_le]
  -- or, `continuous_coinduced_dom`

-- Universal property of the pullback topology:
-- Given:
--   g : X → Y, g : Y → Z
--   topology T_Z on Z
-- Then:
--   for every topology T_X on X,
--   f is continuous wrt T_X and g^* T_Z iff
--   g ∘ f is continuous wrt T_X and T_Z
-- Proof: f is continuous ↔ T_X ≤ f^*(g^* T_Z) ↔ T_X ≤ (g ∘ f)^* T_Z ↔ g ∘ f is continuous
example {Z : Type*} (f : X → Y) (g : Y → Z) (T_X : TopologicalSpace X) (T_Z : TopologicalSpace Z)
  : Continuous[T_X, T_Z.induced g] f ↔ Continuous[T_X, T_Z] (g ∘ f) := by
  rw [continuous_iff_le_induced, induced_compose, continuous_iff_le_induced]
  -- or, `continuous_induced_rng`

-- Given a topological space (X, T) and an equivalence relation ~ on X,
-- the quotient space X / ~ is a topological space with topology f_* T,
-- where f : X → X / ~ is the projection map.
-- Intuition: the topology on the quotient space is the finest topology
--            making the projection map continuous
instance QuotientTopologicalSpace (T : TopologicalSpace X) (S : Setoid X) :
    TopologicalSpace (Quotient S) := T.coinduced (Quotient.mk S)

example (T : TopologicalSpace X) (S : Setoid X) :
    QuotientTopologicalSpace T S = @instTopologicalSpaceQuotient X S T := rfl

-- Example:
--   X = ℝ, T = standard topology on ℝ
--   ∀ x, y ∈ X, x ~ y iff x - y ∈ ℤ
--   ----------------------------------------------
--   quotient space ℝ / ~
--   projection map f : ℝ → ℝ / ~ (f(x) = fraction part of x)
--   quotient (topological) space (ℝ / ~, f_* T)

-- Define a relation on ℝ
def r_intdiff : ℝ → ℝ → Prop := fun x x' => ∃ z : ℤ, x - x' = z

def r_trivial : ℝ → ℝ → Prop := fun _ _ => True

def r_trivial2 : ℝ → ℝ → Prop := fun x y => x = y

-- Prove that the relation is an equivalence relation
instance eq_intdiff : Equivalence r_intdiff where
  refl x := by
    use 0
    rw [Int.cast_zero]
    exact sub_eq_zero_of_eq rfl
  symm := by
    intro x y
    rintro ⟨z, h⟩
    use -z
    rw [Int.cast_neg, ← h]
    exact (neg_sub x y).symm
  trans := by
    intro x y z
    rintro ⟨z₁, h₁⟩ ⟨z₂, h₂⟩
    use z₁ + z₂
    rw [Int.cast_add, ← h₁, ← h₂]
    exact (sub_add_sub_cancel x y z).symm

instance eq_trivial : Equivalence r_trivial where
  refl := by
    intro _
    trivial
  symm := by
    intro x y _
    trivial
  trans := by
    intro x y z _ _
    trivial

instance eq_trivial2 : Equivalence r_trivial2 where
  refl := by
    intro _
    trivial
  symm := by
    intro x y h
    exact h.symm
  trans := by
    intro x y z h₁ h₂
    exact h₁.trans h₂

-- Define the bundle of equivalence relation
def setoid_ℝ_intdiff : Setoid ℝ where
  iseqv := eq_intdiff

def setoid_ℝ_trivial : Setoid ℝ where
  iseqv := eq_trivial

def setoid_ℝ_trivial2 : Setoid ℝ where
  iseqv := eq_trivial2

-- Define the quotient space based on the equivalence relation
def quotient_ℝ_intdiff := Quotient setoid_ℝ_intdiff

def quotient_ℝ_trivial := Quotient setoid_ℝ_trivial

def quotient_ℝ_trivial2 := Quotient setoid_ℝ_trivial2

-- Define the projection map (not necessary)
def proj_ℝ_intdiff : ℝ → quotient_ℝ_intdiff := Quotient.mk setoid_ℝ_intdiff

def proj_ℝ_trivial : ℝ → quotient_ℝ_trivial := Quotient.mk setoid_ℝ_trivial

def proj_ℝ_trivial2 : ℝ → quotient_ℝ_trivial2 := Quotient.mk setoid_ℝ_trivial2

-- Prove that the equivalence relation defines
-- a topological space on the quotient space
instance T_quotient_ℝ_intdiff [T_ℝ : TopologicalSpace ℝ]
  : TopologicalSpace quotient_ℝ_intdiff
  := QuotientTopologicalSpace T_ℝ setoid_ℝ_intdiff

instance T_quotient_ℝ_trivial [T_ℝ : TopologicalSpace ℝ]
  : TopologicalSpace quotient_ℝ_trivial
  := QuotientTopologicalSpace T_ℝ setoid_ℝ_trivial

instance T_quotient_ℝ_trivial2 [T_ℝ : TopologicalSpace ℝ]
  : TopologicalSpace quotient_ℝ_trivial2
  := QuotientTopologicalSpace T_ℝ setoid_ℝ_trivial2

-- Product topology
-- Given a family of topological spaces {(Xᵢ, Tᵢ) : i ∈ ι}
-- where the index set ι is arbitrary, the product space ∏ᵢ Xᵢ
-- is a topological space with topology ⨅ᵢ pᵢ^* Tᵢ
-- where pᵢ : ∏ᵢ Xᵢ → Xᵢ is the projection map.
-- (infimum of the pullback topologies)
--
-- Motivation:
--   we want a topology such that
--   for any topological space (Z, T_Z) and
--       any function f : Z → ∏ᵢ Xᵢ
--   f is continuous wrt (Z, T_Z) and (∏ᵢ Xᵢ, ⨅ᵢ pᵢ^* Tᵢ)
--   iff ∀ i ∈ ι, pᵢ ∘ f is continuous wrt (Z, T_Z) and (Xᵢ, Tᵢ)
example (ι : Type*) (X : ι → Type*) (T_X : ∀ i, TopologicalSpace (X i)) :
    (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) =
      ⨅ i, TopologicalSpace.induced (fun x ↦ x i) (T_X i) :=
  rfl

-- Proof:
--   ∀ i ∈ ι, (pᵢ ∘ f) is continuous wrt (Z, T_Z) and (Xᵢ, Tᵢ)
--   ⇔ ∀ i ∈ ι, (pᵢ ∘ f)_* T_Z ≤ Tᵢ
--   ⇔ ∀ i ∈ ι, pᵢ_* (f_* T_Z) ≤ Tᵢ
--   ⇔ ∀ i ∈ ι, f_* T_Z ≤ pᵢ^* Tᵢ
--   ⇔ f_* T_Z ≤ ⨅ᵢ pᵢ^* Tᵢ
--   ⇔ f is continuous wrt (Z, T_Z) and (∏ᵢ Xᵢ, ⨅ᵢ pᵢ^* Tᵢ)
example {Z : Type*} {ι : Type*} (X : ι → Type*) (f : Z → Π i, X i) (T_Z : TopologicalSpace Z) (T_X : ∀ i, TopologicalSpace (X i))
  : Continuous[T_Z, Pi.topologicalSpace] f ↔ ∀ i, Continuous[T_Z, T_X i] ((fun x ↦ x i) ∘ f) :=
  -- continuous_pi_iff
  by
  rw [continuous_iff_coinduced_le]
  rw [Pi.topologicalSpace]
  rw [le_iInf_iff]
  simp_rw [← coinduced_le_iff_le_induced]
  simp_rw [coinduced_compose]
  simp_rw [← continuous_iff_coinduced_le]

-- 10.3.2. Separation and countability

-- Separation axioms are properties of topological spaces
-- that impose constraints on the topology of the space
-- to ensure that points and sets can be separated from each other.

-- T2 (Hausdorff) space:
-- A topological space X is Hausdorff if for any two distinct points x, y ∈ X,
-- there exist disjoint open sets U, V ∈ X such that x ∈ U and y ∈ V.
example [TopologicalSpace X] [T2Space X] {x y : X} (hxy : x ≠ y) :
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V :=
  t2_separation hxy

-- The indiscrete topology on a space X
def IndiscreteTopology {X : Type*} : TopologicalSpace X where
  IsOpen U := U = ∅ ∨ U = univ
  isOpen_univ := Or.inr rfl
  isOpen_inter U V := by
    rintro (rfl | rfl) (rfl | rfl)
    constructor
    · exact empty_inter ∅
    · exact Or.inl (empty_inter univ)
    constructor
    · exact inter_empty univ
    · exact Or.inr (univ_inter univ)
  isOpen_sUnion S := fun h => sUnion_mem_empty_univ h

-- The indiscrete topology on a space with at least two points is not Hausdorff.
example {X : Type*} (h' : ∃ x y : X, x ≠ y) :
    ¬ @T2Space X IndiscreteTopology := by
  -- Let T be the indiscrete topology on X.
  -- Suppose T is Hausdorff.
  intro hT2
  -- Let x, y ∈ X be distinct points.
  rcases h' with ⟨x, y, hxy⟩
  -- Since T is Hausdorff, there exist disjoint open sets U, V ∈ X
  -- such that x ∈ U and y ∈ V.
  rcases hT2.t2 hxy with ⟨U, V, hU, hV, hxU, hyV, hUV⟩
  -- Since T is the indiscrete topology, U = ∅ or U = univ
  -- and V = ∅ or V = univ.
  -- If U = ∅, then x ∈ U is contradictory.
  -- If U = univ,
  --   if V = ∅, then y ∈ V is contradictory.
  --   if V = univ, then U and V being disjoint is contradictory.
  rcases hU with (rfl | rfl)
  · exact hxU
  · rcases hV with (rfl | rfl)
    · exact hyV
    · rw [univ_disjoint] at hUV
      rw [hUV] at hxU
      exact hxU

-- In a Hausdorff space, the limit of a sequence is unique.
example [TopologicalSpace X] [T2Space X] {u : ℕ → X} {a b : X} (ha : Tendsto u atTop (𝓝 a))
    (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

-- In the topological space X with the indiscrete topology,
-- every sequence converges to every point.
-- (thus, the limit of a sequence is not unique)
example [T : TopologicalSpace X] {u : ℕ → X} {a : X} {h : T = IndiscreteTopology} :
  Tendsto u atTop (𝓝 a) := by
  rw [tendsto_nhds]
  intro S hS
  rw [h] at hS
  rcases hS with (rfl | rfl)
  · exact False.elim
  · exact fun _ => univ_mem

-- T3 (Regular) space:
-- A topological space X is regular if for any point x ∈ X and any closed set F ⊆ X
-- such that x ∉ F, x and F admit disjoint neighborhoods.
example [TopologicalSpace X] [T3Space X] {x : X} {F : Set X} (hx : x ∉ F) (hF : IsClosed F) :
  Disjoint (𝓝ˢ F) (𝓝 x) :=
  RegularSpace.regular hF hx

-- A regular space is Hausdorff.
example [TopologicalSpace X] [T3Space X] : T2Space X :=
  T3Space.t25Space.t2Space

-- Additionally, in a regular space, each point has a basis of closed neighborhoods.
example [TopologicalSpace X] [RegularSpace X] (a : X) :
    (𝓝 a).HasBasis (fun s : Set X ↦ s ∈ 𝓝 a ∧ IsClosed s) id :=
  closed_nhds_basis a

-- On the other hand, a topological space only has a basis of open neighborhoods.
example [TopologicalSpace X] {x : X} :
    (𝓝 x).HasBasis (fun t : Set X ↦ t ∈ 𝓝 x ∧ IsOpen t) id :=
  nhds_basis_opens' x

-- Example: K-topology
def KTopologicalSpace [StdTopo : TopologicalSpace X] (K : Set X) : TopologicalSpace X where
  IsOpen s :=
    -- An open set in the K-topology can be written in the form U \ B
    -- where U is open in the standard topology and B ⊆ K.
    ∃ U B, (IsOpen[StdTopo] U) ∧ (B ⊆ K) ∧ (s = U \ B)
  isOpen_univ := by
    -- Let U = ℝ and B = ∅.
    use univ, ∅
    -- We have:
    --   U = ℝ is open in the standard topology,
    --   B = ∅ ⊆ K, and
    --   ℝ = ℝ \ ∅ = U \ B.
    -- Thus, ℝ is open in the K-topology.
    exact ⟨StdTopo.isOpen_univ, empty_subset K, diff_empty.symm⟩
  isOpen_inter := by
    -- Suppose two sets Uₛ \ Bₛ and Uₜ \ Bₜ are open in the K-topology
    -- where Uₛ, Uₜ be open sets in the standard topology
    -- and Bₛ, Bₜ ⊆ K.
    rintro s t ⟨Us, Bs, hUs, hBsK, rfl⟩ ⟨Ut, Bt, hUt, hBtK, rfl⟩
    -- Let U = Us ∩ Ut and B = Bs ∪ Bt.
    use Us ∩ Ut, Bs ∪ Bt
    constructor
    · -- Since a finite intersection of open sets is open,
      -- U = Uₛ ∩ Uₜ is open in the standard topology
      exact StdTopo.isOpen_inter Us Ut hUs hUt
    · constructor
      · -- Since Bₛ, Bₜ ⊆ K, B = Bₛ ∪ Bₜ ⊆ K.
        exact union_subset hBsK hBtK
      · -- (Uₛ \ Bₛ) ∩ (Uₜ \ Bₜ) = (Uₛ ∩ Bₛᶜ) ∩ (Uₜ ∩ Bₜᶜ)
        --                       = (Uₛ ∩ Uₜ) ∩ (Bₛᶜ ∩ Bₜᶜ)
        --                       = (Uₛ ∩ Uₜ) ∩ (Bₛ ∪ Bₜ)ᶜ
        --                       = (Uₛ ∩ Uₜ) \ (Bₛ ∪ Bₜ)
        rw [diff_eq, diff_eq, inter_inter_inter_comm, ← compl_union, ← diff_eq]
  isOpen_sUnion := by
    -- Let S be a collection of subsets of ℝ.
    -- Suppose each s ∈ S is of the form Uₛ \ Bₛ
    -- for some open set Uₛ and some subset Bₛ ⊆ K.
    intro S hS
    choose! U B hU hB hUB using hS
    -- Let U = ⋃ s ∈ S, Uₛ and B = K \ ⋃ S.
    use (⋃ s ∈ S, U s), K \ (⋃₀ S)
    -- We need to show 3 things:
    --   1. U is open in the standard topology.
    --   2. B ⊆ K.
    --   3. ⋃ S = U \ B.
    constructor
    · -- 1. Show: U is open in the standard topology.
      -- Since each Uₛ is open in the standard topology,
      -- U = ⋃ s ∈ S, Uₛ is open in the standard topology.
      rw [← sUnion_image]
      apply StdTopo.isOpen_sUnion
      rintro V ⟨U', hU'S, rfl⟩
      exact hU U' hU'S
    · constructor
      · -- 2. Show: B ⊆ K.
        -- B = K \ ⋃ S, so B ⊆ K.
        exact diff_subset
      · -- 3. Show: ⋃ S = U \ B.
        -- U \ B = (⋃ s ∈ S, Uₛ) \ (K \ ⋃ S)
        --       = (⋃ s ∈ S, Uₛ) ∩ (K \ ⋃ S)ᶜ
        --       = (⋃ s ∈ S, Uₛ) ∩ (K ∩ (⋃ S)ᶜ)ᶜ
        --       = (⋃ s ∈ S, Uₛ) ∩ (Kᶜ ∪ (⋃ S)ᶜᶜ)
        --       = (⋃ s ∈ S, Uₛ) ∩ (Kᶜ ∪ ⋃ S)
        --       = (⋃ s ∈ S, Uₛ) ∩ Kᶜ ∪ (⋃ s ∈ S, Uₛ) ∩ ⋃ S
        --       = (⋃ s ∈ S, Uₛ) \ K ∪ (⋃ s ∈ S, Uₛ) ∩ ⋃ S
        rw [diff_eq, diff_eq, compl_inter, compl_compl, inter_union_distrib_left, ← diff_eq]

        -- Show: ⋃ S ⊆ ⋃ s ∈ S, Uₛ
        have h₁ : ⋃₀ S ⊆ ⋃ s ∈ S, U s := by
          -- Let x ∈ ⋃ S. Then, ∃ s ∈ S, x ∈ Uₛ \ Bₛ.
          rintro x ⟨s, hsS, hxs⟩
          rw [hUB s hsS] at hxs
          -- Then, ∃ s ∈ S, x ∈ Uₛ. Thus, x ∈ ⋃ s ∈ S, Uₛ.
          rw [← sUnion_image]
          use U s, mem_image_of_mem U hsS, mem_of_mem_diff hxs
        -- U \ B = (⋃ s ∈ S, Uₛ) \ K ∪ ⋃ S
        rw [inter_eq_self_of_subset_right h₁]

        -- Show: (⋃ s ∈ S, Uₛ) \ K ⊆ ⋃ S
        have h₂ : (⋃ s ∈ S, U s) \ K ⊆ ⋃₀ S := by
          -- Let x ∈ (⋃ s ∈ S, Uₛ) \ K. Then, x ∈ ⋃ s ∈ S, Uₛ and x ∉ K.
          -- Thus, ∃ s ∈ S, x ∈ Uₛ. Consider this s.
          intro x hx
          rw [← sUnion_image] at hx
          rcases hx with ⟨⟨_, ⟨s, hsS, rfl⟩, hxUs⟩, hnxK⟩
          -- We can show that x ∉ Bₛ since x ∉ K and Bₛ ⊆ K.
          have hxnBs : x ∉ B s := fun hxBs ↦ hnxK (hB s hsS hxBs)
          -- Thus, x ∈ Uₛ \ Bₛ.
          -- In other words, ∃ s ∈ S, x ∈ Uₛ \ Bₛ ∈ S.
          -- Therefore, x ∈ ⋃ S.
          use s, hsS
          rw [hUB s hsS]
          exact mem_diff_of_mem hxUs hxnBs
        -- U \ B = ⋃ S
        rw [union_eq_self_of_subset_left h₂]

-- The K-topology on ℝ is Hausdorff.
example [StdTopo: TopologicalSpace X] [StdT2: T2Space X] (K : Set X)
  : @T2Space X (KTopologicalSpace K) := by
  -- A topological space is Hausdorff if for any two distinct points x, y ∈ X,
  -- there exist disjoint open sets U, V ∈ X such that x ∈ U and y ∈ V.
  rw [t2Space_iff]
  -- Let x, y ∈ X be distinct points.
  -- Show: there exist disjoint sets U, V ∈ X such that
  -- U, V are open with respect to the K-topology and
  -- x ∈ U and y ∈ V.
  intro x y hxy
  -- Since X with the standard topology is Hausdorff,
  -- there exist disjoint sets U, V ∈ X such that
  -- U, V are open with respect to the standard topology and
  -- x ∈ U and y ∈ V.
  rcases StdT2.t2 hxy with ⟨U, V, hU, hV, hxU, hyV, hUV⟩
  -- Since U, V are open with respect to the standard topology,
  -- U, V are open with respect to the K-topology.
  have hK {S : Set X} (h : IsOpen[StdTopo] S) : IsOpen[KTopologicalSpace K] S :=
    ⟨S, ∅, h, empty_subset K, diff_empty.symm⟩
  -- Thus, U, V are the sets we are looking for.
  use U, V, hK hU, hK hV, hxU, hyV, hUV

-- Define K = {1 / (n + 1) : n ∈ ℕ}.
def K : Set ℝ := Set.range (fun (n : ℕ) => 1 / (n + 1))

-- Show that there is no irrational number in K.
lemma Irrat_notin_K : ∀ x : ℝ, Irrational x → x ∉ K := by
  -- Let x ∈ ℝ be an irrational number.
  intro x hx
  -- Suppose x ∈ K.
  by_contra! hxK
  -- Then, x can be written as 1 / (n + 1) for some natural number n.
  rcases Set.mem_range.mp hxK with ⟨n, rfl⟩
  -- Then, 1 / (n + 1) is irrational. This is a contradiction.
  rw [Irrational] at hx
  apply hx
  use 1 / (n + 1)
  rw [Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_one, Rat.cast_natCast]

example : ¬ @RegularSpace ℝ (KTopologicalSpace K) := by
  -- We prove by contradiction.
  -- Suppose the K-topology on ℝ is regular.
  by_contra! h
  -- Then, for all closed set F in the K-topology and all x ∉ F,
  -- x and F admit disjoint neighborhoods.
  rw [regularSpace_iff] at h

  -- We show that K is closed in the K-topology.
  have hK : IsClosed[KTopologicalSpace K] K := by
    -- Note that Kᶜ = ℝ \ K =: U \ B.
    -- We have
    --   U = ℝ is open in the standard topology,
    --   K ⊆ K, and
    --   Kᶜ = ℝ \ K.
    -- Thus, Kᶜ is open in the K-topology,
    -- which implies K is closed in the K-topology.
    use univ, K
    exact ⟨isOpen_univ, Subset.refl K, compl_eq_univ_diff K⟩

  -- We show that 0 is not in K.
  have h0nK : 0 ∉ K := by
    -- Suppose 0 ∈ K.
    by_contra! h0K
    -- Then, 0 can be written as 1 / (n + 1) for some natural number n.
    rcases Set.mem_range.mp h0K with ⟨n, hn⟩
    -- Since 1 / (n + 1) = 0, either 1 = 0 or n + 1 = 0.
    rcases (div_eq_zero_iff.mp hn) with (h' | h')
    · -- 1 = 0 is contradictory.
      exact one_ne_zero h'
    · -- n + 1 is the successor of a natural number.
      -- Thus, n + 1 ≠ 0. So n + 1 = 0 is contradictory.
      rw [← Nat.cast_succ, Nat.cast_eq_zero] at h'
      exact Nat.succ_ne_zero n h'

  -- Since K is closed in the K-topology and 0 ∉ K,
  -- 0 and K admit disjoint neighborhoods.
  -- Then, there exist disjoint sets U, V
  -- such that K is in the neighborhood of U
  -- and 0 is in the neighborhood of V.
  rcases Filter.disjoint_iff.mp (h hK h0nK) with ⟨U, hU, ⟨V, hV, hUV⟩⟩

  -- We show that if a set U is in the neighborhood of a point x,
  -- then there exists a radius ε > 0 such that the open interval (x - ε, x + ε)
  -- excluding points of K, i.e. (x - ε, x + ε) \ K, is a subset of U.
  have aux {x : ℝ} {U : Set ℝ} (hUx : U ∈ @nhds ℝ (KTopologicalSpace K) x) :
    ∃ ε > 0, Ioo (x - ε) (x + ε) \ K ⊆ U := by
    -- Let U be in the neighborhood of x.
    -- Then, there exists an open set U' ⊆ U in the K-topology such that x ∈ U'.
    rw [@mem_nhds_iff ℝ x U (KTopologicalSpace K)] at hUx
    rcases hUx with ⟨U', hU'U, hU', hxU'⟩
    -- Since U' is open in the K-topology,
    -- there exists an open set U'' in the standard topology
    -- and a subset B'' ⊆ K such that U' = U'' \ B''.
    rw [isOpen_mk] at hU'
    rcases hU' with ⟨U'', B'', hU'', hB''K, rfl⟩
    -- We show that there exists ε > 0 such that (x - ε, x + ε) ⊆ U''.
    have : ∃ ε > 0, Ioo (x - ε) (x + ε) ⊆ U'' := by
      -- Since x ∈ U' = U'' \ B'', x ∈ U''.
      -- Since U'' is open in the standard topology and x ∈ U'',
      -- U'' is in the neighborhood of x.
      have : U'' ∈ 𝓝 x := (IsOpen.mem_nhds_iff hU'').mpr (mem_of_mem_diff hxU')
      -- On ℝ, this implies there exists l < u
      -- such that x ∈ (l, u) ⊆ U''.
      rw [mem_nhds_iff_exists_Ioo_subset] at this
      rcases this with ⟨l, u, ⟨hl, hu⟩, hIluU'⟩
      -- Let ε = min {x - l, u - x}. Then ε ≤ x - l and ε ≤ u - x.
      use min (x - l) (u - x)
      constructor
      · -- Since l < x, x - l > 0. Similarly, u - x > 0. Thus, ε > 0.
        exact lt_min (sub_pos.mpr hl) (sub_pos.mpr hu)
      · -- Let y ∈ (x - ε, x + ε).
        rintro y ⟨hyleft, hyright⟩
        -- Then, l = x - (x - l) ≤ x - ε < y.
        have hly := calc
          l = x - (x - l) := (sub_sub_self x l).symm
          _ ≤ x - min (x - l) (u - x) := sub_le_sub_left (min_le_left (x - l) (u - x)) x
          _ < y := hyleft
        -- On the other hand, y < x + ε ≤ x + (u - x) = u.
        have hyu := calc
          y < x + min (x - l) (u - x) := hyright
          _ ≤ x + (u - x) := add_le_add_left (min_le_right (x - l) (u - x)) x
          _ = u := add_sub_cancel x u
        -- Thus, y ∈ (l, u) ⊆ U''.
        exact hIluU' ⟨hly, hyu⟩
    rcases this with ⟨ε, hε, hIU''⟩
    -- Use this ε as the radius.
    use ε, hε
    -- Let y ∈ (x - ε, x + ε) \ K. Then, y ∈ (x - ε, x + ε) and y ∉ K.
    rintro y ⟨hyI, hynK⟩
    -- Since y ∈ (x - ε, x + ε), y ∈ U''.
    -- Since y ∉ K ⊇ B'', y ∉ B''.
    -- Thus, y ∈ U'' \ B'' = U' ⊆ U.
    exact hU'U (mem_diff_of_mem (hIU'' hyI) (fun hyB'' ↦ hynK (hB''K hyB'')))

  -- Apply the auxiliary lemma to V, which is in the neighborhood of 0.
  -- Then, there exists ε > 0 such that
  -- (-ε, ε) \ K ⊆ V.
  rcases aux hV with ⟨ε, hε, hIdKV⟩
  rw [zero_sub, zero_add] at hIdKV
  -- Since ε > 0, there exists a natural number n such that 1 / (n + 1) < ε.
  rcases exists_nat_one_div_lt hε with ⟨n, hn⟩
  -- Let x = 1 / (n + 1).
  let x := 1 / ((n : ℝ) + 1)
  -- Then, x ∈ K.
  have hxK : x ∈ K := Set.mem_range.mpr ⟨n, rfl⟩

  -- Since U is in the neighborhood of K,
  -- there exists an open set U' in the K-topology such that
  -- K ⊆ U' ⊆ U.
  rw [@mem_nhdsSet_iff_exists ℝ (KTopologicalSpace K) U K] at hU
  rcases hU with ⟨U', hU', hKU', hU'U⟩
  -- Since U' is open in the K-topology,
  -- for every point y ∈ U', U' is in the neighborhood of y.
  rw [@isOpen_iff_mem_nhds] at hU'
  -- Since x ∈ K ⊆ U' ⊆ U, x ∈ U. Thus, U' is in the neighborhood of x.
  -- Apply the auxiliary lemma to U', there exists ε' > 0 such that
  -- (x - ε', x + ε') \ K ⊆ U'.
  rcases aux (hU' x (hKU' hxK)) with ⟨ε', hε', hIdKU'⟩

  -- If (x - ε', x + ε') and (-ε, ε) intersect
  -- at a point t that is not in K, i.e.,
  -- ∃ t ∈ (x - ε', x + ε') ∩ (-ε, ε) \ K, then
  -- t ∈ (x - ε', x + ε') \ K ⊆ U' ⊆ U and
  -- t ∈ (-ε, ε) \ K ⊆ V and so
  -- U and V are not disjoint, which is a contradiction.
  have aux2 {t : ℝ} (htnK : t ∉ K) :
    ¬ (t ∈ Ioo (x - ε') (x + ε') ∧ t ∈ Ioo (-ε) ε) := by
    push_neg
    intro htUK htVK
    rw [disjoint_left] at hUV
    apply hUV
      (hU'U (hIdKU' (mem_diff_of_mem htUK htnK)))
      (hIdKV (mem_diff_of_mem htVK htnK))

  -- We show that such a point t exists.
  -- Consider two cases: x - ε' ≤ -ε and x - ε' > -ε.
  by_cases hεε' : x - ε' ≤ -ε
  · -- Case 1: x - ε' ≤ -ε.
    -- We know that 0 ∉ K.
    -- Since x - ε' ≤ -ε < 0, x - ε' < 0.
    -- Since x = 1 / (n + 1) > 0, x + ε' > 0.
    -- Thus, 0 ∈ (x - ε', x + ε').
    -- On the other hand, it is obvious that 0 ∈ (-ε, ε).
    -- Thus, 0 ∈ (x - ε', x + ε') ∩ (-ε, ε) and 0 ∉ K.
    exact aux2 h0nK ⟨
      ⟨
        lt_of_le_of_lt hεε' (neg_neg_iff_pos.mpr hε),
        gt_trans (lt_add_of_pos_right x hε') (Nat.one_div_pos_of_nat)
      ⟩,
      ⟨neg_neg_iff_pos.mpr hε, hε⟩
    ⟩
  · -- Cases 2: x - ε' > -ε.
    push_neg at hεε'
    -- Since x - ε' < x, there exists an irrational number r ∈ (x - ε', x).
    rcases exists_irrational_btwn (sub_lt_self x hε') with ⟨r, hr, h1r, hr1⟩
    -- An irrational number cannot be in the form 1 / (n + 1). Thus, r ∉ K.
    -- Since r ∈ (x - ε', x) ⊆ (x - ε', x + ε'), r ∈ (x - ε', x + ε').
    -- Since r > x - ε' > -ε, r > -ε. On the other hand, r < x < ε. Thus, r ∈ (-ε, ε).
    -- Therefore, r ∈ (x - ε', x + ε') ∩ (-ε, ε) and r ∉ K.
    exact aux2 (Irrat_notin_K r hr) ⟨
      ⟨h1r, lt_add_of_lt_of_pos hr1 hε'⟩,
      ⟨gt_trans h1r hεε', gt_trans hn hr1⟩
    ⟩

theorem aux {X Y A : Type*} [TopologicalSpace X] {c : A → X}
      {f : A → Y} {x : X} {F : Filter Y}
      (h : Tendsto f (comap c (𝓝 x)) F) {V' : Set Y} (V'_in : V' ∈ F) :
    ∃ V ∈ 𝓝 x, IsOpen V ∧ c ⁻¹' V ⊆ f ⁻¹' V' := by
  rcases h V'_in with ⟨U, hUinNx, hcinvUssfinvV'⟩
  rw [mem_nhds_iff] at hUinNx
  rcases hUinNx with ⟨V, hVssU, hopenV, hxinV⟩
  use V
  exact ⟨
    IsOpen.mem_nhds hopenV hxinV,
    hopenV,
    fun _ hxincinvV => hcinvUssfinvV' (hVssU hxincinvV),
  ⟩

example [TopologicalSpace X] [TopologicalSpace Y] [T3Space Y] {A : Set X}
    (hA : ∀ x, x ∈ closure A) {f : A → Y} (f_cont : Continuous f)
    (hf : ∀ x : X, ∃ c : Y, Tendsto f (comap (↑) (𝓝 x)) (𝓝 c)) :
    ∃ φ : X → Y, Continuous φ ∧ ∀ a : A, φ a = f a := by
  choose φ hφ using hf
  use φ
  constructor
  · rw [continuous_iff_continuousAt]
    intro x
    suffices ∀ V' ∈ 𝓝 (φ x), IsClosed V' → φ ⁻¹' V' ∈ 𝓝 x by
      rw [continuousAt_def]
      intro A hAinNφx
      rcases (closed_nhds_basis (φ x)).mem_iff.mp hAinNφx with ⟨V', ⟨hV'inNφx, hclosedV'⟩, hV'ssA⟩
      exact mem_of_superset (this V' hV'inNφx hclosedV') (preimage_mono hV'ssA)
    intro V' hV'inNφx hclosedV'
    rcases aux (hφ x) hV'inNφx with ⟨V, hVinNx, hopenV, hcinvVssfinvV'⟩
    apply mem_of_superset hVinNx
    intro y hyV
    have hVinNy: V ∈ 𝓝 y := hopenV.mem_nhds hyV
    have := mem_closure_iff_comap_neBot.mp (hA y)
    apply hclosedV'.mem_of_tendsto (hφ y)
    exact mem_of_superset (preimage_mem_comap hVinNy) hcinvVssfinvV'
  · intro a
    apply tendsto_nhds_unique _ f_cont.continuousAt
    rw [nhds_induced]
    exact hφ a

#check HasBasis.tendsto_right_iff

example [TopologicalSpace X] [FirstCountableTopology X]
      {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 a) :=
  mem_closure_iff_seq_limit

variable [TopologicalSpace X]

example {F : Filter X} {x : X} : ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) :=
  Iff.rfl

example {s : Set X} :
    IsCompact s ↔ ∀ (F : Filter X) [NeBot F], F ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a F :=
  Iff.rfl

example [FirstCountableTopology X] {s : Set X} {u : ℕ → X} (hs : IsCompact s)
    (hu : ∀ n, u n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

variable [TopologicalSpace Y]

example {x : X} {F : Filter X} {G : Filter Y} (H : ClusterPt x F) {f : X → Y}
    (hfx : ContinuousAt f x) (hf : Tendsto f F G) : ClusterPt (f x) G :=
  ClusterPt.map H hfx hf

example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
  intro F F_ne F_le
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by
    rw [Filter.push_pull]
    rw [map_principal]
  have Hne : (𝓟 s ⊓ comap f F).NeBot := by
    apply NeBot.of_map
    rw [map_eq]
    rw [inf_of_le_right F_le]
    exact F_ne
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
  rcases hs Hle with ⟨x, hxs, hclsptx⟩
  use f x
  constructor
  · exact mem_image_of_mem f hxs
  · apply hclsptx.map hf.continuousAt
    rw [Tendsto, map_eq]
    exact inf_le_right

example {ι : Type*} {s : Set X} (hs : IsCompact s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
    (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_finite_subcover U hUo hsU
