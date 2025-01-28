import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

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

example [TopologicalSpace X] [T2Space X] {u : ℕ → X} {a b : X} (ha : Tendsto u atTop (𝓝 a))
    (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

example [TopologicalSpace X] [RegularSpace X] (a : X) :
    (𝓝 a).HasBasis (fun s : Set X ↦ s ∈ 𝓝 a ∧ IsClosed s) id :=
  closed_nhds_basis a

example [TopologicalSpace X] {x : X} :
    (𝓝 x).HasBasis (fun t : Set X ↦ t ∈ 𝓝 x ∧ IsOpen t) id :=
  nhds_basis_opens' x

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
