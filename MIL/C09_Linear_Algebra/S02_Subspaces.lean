import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

-- K is a field
-- V is a K-vector space
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

-- U is a K-linear subspace of V
--   U is a subset of V
--   U contains 0
--   U is closed under addition and scalar mul
-- Subspaces in Lean are represented as bundled structures `Submodule K V`
--   store the proofs of closure properties
--   coercion to `Set V` (can act as a set, proving equality with `ext`, etc.)

-- Subspace is closed under addition
example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

-- Subspace is closed under scalar mul
example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx

-- ℝ is a subspace of ℂ (a vector space over ℝ)
noncomputable example : Submodule ℝ ℂ where
  -- Image of the coercion (↑) from ℝ to ℂ:
  --   set of all complex numbers obtained from a real number
  carrier := Set.range ((↑) : ℝ → ℂ)
  -- Proof of closure of addition
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  -- Proof of 0 being in the subspace
  zero_mem' := by
    use 0
    simp
  -- Proof of closure of scalar mul
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp

-- Give
--   φ: K-linear map from V to W
--   H: subspace of W
-- then φ⁻¹(H) is a subspace of V
def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    dsimp
    rw [Set.mem_preimage]
    rw [φ.map_zero]
    exact H.zero_mem
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_preimage] at *
    rw [φ.map_add]
    exact H.add_mem ha hb
  smul_mem' := by
    dsimp
    intro c x hx
    rw [Set.mem_preimage] at *
    rw [φ.map_smul]
    exact H.smul_mem c hx

-- Subspace is a vector space
-- and Lean can automatically infer this.
example (U : Submodule K V) : Module K U := inferInstance

-- Here, `U` is not a type (`Type*`) but has type `Submodule K V`.
-- Lean automatically coerces U to the subtype `{x : V // x ∈ U}`
example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance

-- Set of all subspaces of V (submodules): complete lattice
--   partial order: inclusion
--   infimum (meet): intersection
--   supremum (join): sum
-- (complete: any collection, not just finite ones, has an inf and a sup)

-- The infimum of two subspaces H and H' of V is
--   a subspace of V
--   intersection of the carrier of H and the carrier of H'
example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl

-- The supremum of two subspaces H and H' of V is
--   a subspace of V
--   smallest subspace containing the union (i.e., sum) of the two subspaces
-- `Submodule.span M s`: smallest submodule of M containing s
--                       called the submodule generated by s
-- In Lean, `H ⊔ H' = H + H'` by definition.
example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]

-- V is a subspace of itself.
-- But, `V` is a type, sot it cannot be of type `Submodule K V`.

-- V is the top element in the lattice of subspaces.
example (x : V) : x ∈ (⊤ : Submodule K V) := trivial

-- The zero subspace {0} is the bottom element.
example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K

-- `IsCompl U V`: U and V are "complements" of each other
--                in the lattice of submodules.
-- "Complement" is general for any bounded partially ordered type.
-- "In internal direct sum" is specific for subspaces.

-- If two subspaces are in direct sum then they span the whole space.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

-- If two subspaces are in direct sum then they intersect only at zero.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum

-- Consider an index set ι with decidable equality.
variable {ι : Type*} [DecidableEq ι]

-- The following examples deal with a family of subspaces {Uᵢ : i ∈ ι} of V.
-- `DirectSum.IsInternal U`: The family is in internal direct sum.

-- If subspaces are in internal direct sum then they span the whole space.
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- If subspaces are in internal direct sum then they pairwise intersect only at zero.
-- `.submodule_independent`: if the direct sum of the submodules is internal
--                           then the submodules are independent.
-- `.pairwiseDisjoint`: if the submodules are independent
--                      then the submodules are pairwise disjoint.
-- `.eq_bot`: if the submodules are pairwise disjoint
--            then the infimum of two different submodules is the bottom elem.
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_independent.pairwiseDisjoint hij).eq_bot

-- The direct sum is internal iff
--   the sum is the whole space
--   the pairwise intersection is the bottom element
#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

-- `⨁ i, U i`: external direct sum
-- Internal direct sum: decompose an existing space
--   Start with vector space V
--   A collection of subspaces {Uᵢ} within V
--   V is the indirect sum of {Uᵢ} if every vector in V can be
--   written uniquely as a finite sum of vectors from each of {Uᵢ}.
-- External direct sum: build a new space from existing ones
--   Start with a collection of independent vector spaces {Uᵢ}
--   Construct a new vector space ⨁ᵢ Uᵢ
--     each elem is a tuple of vectors from each of {Uᵢ},
--     only finitely many of them are non-zero.

-- `coeLinearMap U`: canonical linear map from the external direct sum to V
--   map a tuple of vectors (in the external direct sum)
--   to their sum (as vectors in V)

-- If {Uᵢ : i ∈ ι} is in internal direct sum
-- then the canonical linear map is bijective.
-- Proof: By definition, each v ∈ V can be uniquely written as a sum.
--   1) Since the sum is unique, ∑ᵢ uᵢ = 0 ⇒ ∀ i, uᵢ = 0
--      So the kernal is {0} and thus the map is injective.
--   2) Surjectivity is obvious from the definition.
-- Therefore, the external direct sum are linearly isomorphic to V.
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end

-- Given set s
-- `Submodule.span K s`: smallest submodule of K containing s
--                       called the submodule generated by s
-- Common: all linear combinations of vectors of s.
-- Often more efficient: universal property with `.span_le`
-- `.span_le`: span of s ≤ submodule E iff s ⊆ E (as set)
example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

-- Ex: span(S₁ ∪ S₂) = span(S₁) ⊔ span(S₂)
-- Proof:
-- (≤) Only need to show S₁ ∪ S₂ ⊆ span(S₁) ⊔ span(S₂)
-- (≥) S₁ ⊆ S₁ ∪ S₂ ⇒ span(S₁) ≤ span(S₁ ∪ S₂)

-- Galois connection: pair of functions l : A → B, u : B → A
--                    where (A, ≤[A]) and (B, ≤[B]) are posets
--   ∀ a ∈ A, b ∈ B, l(a) ≤[B] b ↔ a ≤[A] u(b)
-- l and u are adjoint functors, l/u: lower/upper adjoint
-- Ex: A = ℝ, B = ℤ, l(a) = ⌈a⌉, u(b) = b
-- Ex: A = 𝒫(X), B = all closed subset of X
--     l: 𝒫(X) → B, S ↦ closure(S) (smallest closed set containing S)
--     u: B → 𝒫(X), S ↦ S (as a subset of X)
--     l(S) ≤[B] S' ↔ l(S) ⊆ S' ↔ S ⊆ S' ↔ S ≤[A] u(S')

-- Galois insertion: Galois connection where l ∘ u = id (i.e., l(u(b)) = b)
-- Ex: (continue) l(u(S)) = l(S) = S (since S ∈ B is closed)

-- l = `.span K`: map set to subspace
-- u = `(↑) : Submodule K V → Set V`: map subspace to set (coercion)
-- `.gi K V`: proof that l and u form a Galois insertion
example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V

example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  -- `h : x ∈ Submodule.span K (↑S ∪ ↑T)` (x ∈ span(S ∪ T))
  -- allows proof by induction using `.span_induction`
  induction h using Submodule.span_induction with
  -- Base case: x = 0
  | zero =>
      use 0, S.zero_mem
      use 0, T.zero_mem
      rw [zero_add]
  -- Base case: x ∈ S ∪ T
  | mem x h =>
      rcases h with (hS | hT)
      · use x, hS
        use 0, T.zero_mem
        rw [add_zero]
      · use 0, S.zero_mem
        use x, hT
        rw [zero_add]
  -- Inductive step: x ← x + y
  | add x y hx hy hx' hy' =>
      rcases hx' with ⟨sx, hsx, tx, htx, rfl⟩
      rcases hy' with ⟨sy, hsy, ty, hty, rfl⟩
      use sx + sy, S.add_mem hsx hsy
      use tx + ty, T.add_mem htx hty
      rw [add_add_add_comm]
  -- Inductive step: x ← a • x
  | smul a x hx hx' =>
      rcases hx' with ⟨s, hs, t, ht, rfl⟩
      use a • s, S.smul_mem a hs
      use a • t, T.smul_mem a ht
      rw [DistribMulAction.smul_add]

section

-- Let W be a K-vector space.
-- Let φ be a linear map from V to W.
variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

-- Let E be a subspace of V.
-- Image of E under φ, φ(E), is a subspace of W.
-- `.map φ E` or `E.map φ` pushes E from V to W.
variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

-- Let F be a subspace of W.
-- Preimage of F under φ, φ⁻¹(F), is a subspace of V.
-- `.comap φ F` or `F.comap φ` pulls F from W to V.
variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)

-- Range of φ is the image of V
-- We cannot use `φ.range/ker` is not limited to linear maps.
-- However, since `LinearMap.range/ker φ` has type `Submodule K V`
-- so `.map φ ⊤` works because `Submodule.map` can be inferred.
example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

-- Kernel of φ is (definitionally) the preimage of the zero subspace
example : LinearMap.ker φ = .comap φ ⊥ := rfl -- Submodule.comap_bot φ

open Function LinearMap

-- φ is injective iff its kernal is the bottom element (zero subspace).
example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

-- φ is surjective iff its range is the top element (entire space).
example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm

-- x ∈ E → φ(x) ∈ φ(E)
#check Submodule.mem_map_of_mem
-- y ∈ φ(E) ↔ ∃ x ∈ E, y = φ(x)
#check Submodule.mem_map
-- x ∈ φ⁻¹(F) ↔ φ(x) ∈ F
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
  constructor
  · -- Suppose φ(E) ≤ F.
    -- Let x ∈ E.
    intro hφEleF _ hxE
    -- Then φ(x) ∈ φ(E).
    -- Then φ(x) ∈ F or x ∈ φ⁻¹(F).
    exact hφEleF (Submodule.mem_map_of_mem hxE)
  · -- Suppose E ≤ φ⁻¹(F).
    -- Let y ∈ φ(E).
    intro hEleφinvF _ hyφE
    -- Then, ∃ x ∈ E, φ(x) = y.
    rcases hyφE with ⟨_, hxE, rfl⟩
    -- Then, x ∈ φ⁻¹(F) so y = φ(x) ∈ F.
    exact hEleφinvF hxE

-- Let E be a subspace of V.
variable (E : Submodule K V)

-- The quotient vector space is a K-vector space
-- whose elements are equiv classes of vectors in V
--   u and v are equivalent if u - v ∈ E
--   denoted [v] or v + E
example : Module K (V ⧸ E) := inferInstance

-- `E.mkQ`: Canonical projection map
--   V → V ⧸ E
--   v ↦ v + E
example : V →ₗ[K] V ⧸ E := E.mkQ

-- The kernel of the canonical projection map is the subspace.
example : ker E.mkQ = E := E.ker_mkQ

-- The range of the canonical projection map is the entire space.
-- Thus, the canonical projection map is surjective.
example : range E.mkQ = ⊤ := E.range_mkQ

-- Universal property
-- Recall: φ is a linear map from V to W
-- `hφ`: E is contained in the kernel of φ
-- `E.liftQ φ hφ`: linear map from V ⧸ E to W
-- φE(v + E) = φ(v)
-- φE is well-defined with `hφ`
--   For v, v' ∈ v + E or v - v' ∈ E ⇒ v - v' ∈ ker(φ)
--   φE(v + E) = φ(v) = φ(v - v' + v')
--                    = φ(v - v') + φ(v')
--                    = 0 + φ(v') = φ(v') = φE(v' + E)
example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

-- Given
--   subspace F of W
--   E ≤ φ⁻¹(F)
-- `E.mapQ F φ hφ`: linear map from V ⧸ E to W ⧸ F
-- φEF(v + E) = φ(v) + F
-- φEF is well-defined with `hφ`
--   Since E ≤ φ⁻¹(F), φ(E) ≤ F. (Galois connection)
--   Let v, v' ∈ v + E.
--   Then, v - v' ∈ E.
--   Then, φ(v - v') ∈ φ(E).
--   Then, φ(v) - φ(v') ∈ F.
--   So φEF(v + E) = φ(v) + F = φ(v') + F = φEF(v' + E).
example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

-- First isomorphism theorem: V ⧸ ker(φ) is isomorphic to im(φ)
--   ker(φ) is a subspace of V
--   use the universal property => linear map from V ⧸ ker(φ) to W
--   restrict it to linear map φ' from V ⧸ ker(φ) to im(φ)
--   prove φ' is injective
--     Let v, v' s.t φ'(v + ker(φ)) = φ'(v' + ker(φ)).
--     Then, φ(v) = φ(v') or φ(v - v') = 0 or v - v' ∈ ker(φ).
--     Thus, v + ker(φ) = v' + ker(φ).
--   prove φ' is surjective (obvious)
noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange

open Submodule

-- φ(φ⁻¹(F)) = im(φ) ⊓ F
#check Submodule.map_comap_eq
-- φ⁻¹(φ(E)) = E ⊔ ker(φ)
#check Submodule.comap_map_eq

-- Each subspace in V / E corresponds to a subspace of V that contains E
-- `Submodule K (V ⧸ E)`: set of subspaces in V ⧸ E
-- `{ F : Submodule K V // E ≤ F }`: set of subspaces of V that contains E
--
-- Quotienting out E creates a new space where
--    E is "squashed" to the "zero vector"/"0"
--    any subspace containing E has a "squashed" version
--    any subspace not containing E won't have its "squashed" version having "0"
--
-- Ex: V = ℝ³, E = {(x, 0, 0) : x ∈ ℝ} (x-axis)
--     V ⧸ E = {[y, z] : y, z ∈ ℝ} where [y, z] = {(x, y, z) : x ∈ ℝ}
--     the "0" in quotient space (V ⧸ E) is the x-axis in V
--     each "point" [y, z] in V ⧸ E is a line through (0, y, z) parallel to the x-axis
--     each subspace in V ⧸ E ("line" passing through "0")
--     corresponds to a subspace of V containing E = plane containing x-axis in V
example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
  toFun L := ⟨
    -- `E.mkQ`: canonical map φ from V to V ⧸ E
    -- `.comap E.mkQ`: pull-back function L ↦ φ⁻¹(L)
    -- `.comap E.mkQ L`: for a subspace L of V ⧸ E, pull S back to a subspace in V
    -- Ex: pull back a line in V ⧸ E to a plane in V
    .comap E.mkQ L,
    -- Prove: E ≤ `.comap E.mkQ L`
    --   E = ker(φ) (E is "squashed" to "0" so E is the kernel of φ)
    --     = φ⁻¹(⊥) (kernel of φ contains elements that φ maps to ⊥)
    --     ≤ φ⁻¹(L) (⊥ ≤ L)
    calc
      E = ker E.mkQ := by rw [E.ker_mkQ]
      _ = .comap E.mkQ ⊥ := by rw [comap_bot]
      _ ≤ .comap E.mkQ L := fun _ h => (OrderBot.bot_le L) h
  ⟩
  invFun R := map E.mkQ R
  left_inv := by
    -- Prove: `invFun` is the left inverse of `toFun`
    rw [leftInverse_iff_comp]
    -- Prove: `invFun` ∘ `toFun` = id
    -- Prove: ∀ subspace L of V ⧸ E, ∀ x ∈ V ⧸ E
    --        x ∈ φ(φ⁻¹(L)) ↔ x ∈ L
    -- Fix a subspace L of V ⧸ E and x ∈ V ⧸ E
    ext L x
    dsimp
    -- φ(φ⁻¹(L)) = im(φ) ⊓ L = ⊤ ⊓ L = L
    have := calc
      map E.mkQ (comap E.mkQ L) = range E.mkQ ⊓ L := by rw [map_comap_eq]
      _ = ⊤ ⊓ L := by rw [E.range_mkQ]
      _ = L := by rw [top_inf_eq]
    rw [this]
  right_inv := by
    -- Prove: `invFun` is the right inverse of `toFun`
    rw [rightInverse_iff_comp]
    -- Prove: `toFun` ∘ `invFun` = id
    -- Prove: ∀ R ≤ E, x ∈ V
    --        x ∈ φ⁻¹(φ(R)) ↔ x ∈ R
    ext R x
    dsimp
    -- φ⁻¹(φ(L)) = L ⊔ ker(φ) = L ⊔ E = L (E ≤ L)
    have := calc
      comap E.mkQ (map E.mkQ ↑R) = ↑R ⊔ ker E.mkQ := by rw [comap_map_eq]
      _ = ↑R ⊔ E := by rw [E.ker_mkQ]
      _ = ↑R := sup_eq_left.mpr R.2
    rw [this]
