import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


-- Let K be a field.
--   Field = Ring + multiplicative inverse
-- Let V be an Abelian group.
-- Suppose V is a module over K.
-- Vector space = an Abelian group which is a module over a field
-- Therefore, here we introduce a K-vector space V
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

example (a b : K) (u : V) : (a + b) • u = a • u + b • u :=
  add_smul a b u

example (a b : K) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u

-- Setup
--   Commutative semiring R
--   Additive commutative monoid M
--   M forms a module over R
-- Set of submodules of M forms a module over the set of ideals of R
example {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module (Ideal R) (Submodule R M) :=
  inferInstance

-- We introduce another K-vector space W.
variable {W : Type*} [AddCommGroup W] [Module K W]

-- φ is a linear map between V and W.
-- `[K]` is necessary because it can be linear wrt one field but not another
-- Ex: φ(z) = z* is ℝ-linear but not ℂ-linear
--     i.e., we cannot have `φ : ℂ →ₗ[ℂ] ℂ`
variable (φ : V →ₗ[K] W)

-- φ preserves scalar mul
example (a : K) (v : V) : φ (a • v) = a • φ v :=
  map_smul φ a v

-- φ preserves addition
example (v w : V) : φ (v + w) = φ v + φ w :=
  map_add φ v w

-- We introduce another K-linear map ψ from V to W.
variable (ψ : V →ₗ[K] W)

-- Set of K-linear maps between two K-vector spaces
-- forms a K-vector space itself.
-- The operations (add, smul) are point-wise.
#check (2 • φ + ψ : V →ₗ[K] W)

-- We introduce another K-linear map from W to V.
variable (θ : W →ₗ[K] V)

-- We can compose linear maps using `LinearMap.comp` or `∘ₗ`.
-- `φ.comp θ` or `φ ∘ₗ θ` gives (φ ∘ θ)(u) = φ(θ(u))
#check (φ.comp θ : W →ₗ[K] W)
#check (φ ∘ₗ θ : W →ₗ[K] W)

-- One way to define a linear map is to
-- provide the underlying function (`toFun`)
-- and proofs of the linearity properties (`map_add'`, `'map_smul'`)
example : V →ₗ[K] V where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..

-- `.map_add'` is defined before the coercion from `LinearMap` to a function
-- and needs to use `.toFun` to refer to the underlying function.
#check (φ.map_add' : ∀ x y : V, φ.toFun (x + y) = φ.toFun x + φ.toFun y)
-- `.map_add` is after the coercion, so notations are cleaner.
#check (φ.map_add : ∀ x y : V, φ (x + y) = φ x + φ y)
-- `map_add` is the general version applied to all bundled maps that preserves addition.
-- `.map_add` seems redundant with the general `map_add`
-- but it allows dot notation (`φ.map_add` when `φ` is a `LinearMap`)
#check (map_add φ : ∀ x y : V, φ (x + y) = φ x + φ y)

-- Another way is `.lsmul`.
-- Given
--    field `K`,
--    K-vector space `V`,
--    scalar `3 : K`
-- `.lsmul K V 3` produces a K-linear map from V to V
-- that scales vectors in V by 3.
#check (LinearMap.lsmul K V 3 : V →ₗ[K] V)
-- Interestingly, `.lsmul K V` is a K-linear map
--   from vector space K over K
--   to vector space of linear maps from V to V over K
#check (LinearMap.lsmul K V : K →ₗ[K] V →ₗ[K] V)
-- `.lsmul 3` will not work since it is not clear what K and V are.

-- Composing a K-linear isomorphism with its inverse gives the identity isomorphism.
-- `f: V ≃ₗ[K] W`: f is a K-linear isomorphism (bijection) from/between V to/and W
-- `f.symm`: inverse f⁻¹ of f, which is also a K-linear map
-- `.refl K V`: identity (K-linear) isomorphism of V
-- `≪≫ₗ` or `.trans`: composition of linear isomorphisms
example (f : V ≃ₗ[K] W) : f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
  f.self_trans_symm

-- A bijective K-linear map induces a K-linear isomorphism.
-- `noncomputable`: An inverse function exists but may not be computable.
-- `.ofBijective` is automatically infered to be `LinearEquiv.ofBijective`.
noncomputable example (f : V →ₗ[K] W) (h : Function.Bijective f) : V ≃ₗ[K] W :=
  .ofBijective f h

section binary_product

-- We introduce 3 K-vector spaces W, U, T.
variable {W : Type*} [AddCommGroup W] [Module K W]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {T : Type*} [AddCommGroup T] [Module K T]

-- Given two K-vector spaces V and W,
-- their direct sum (also their direct product, since there are finite spaces)
-- is also a K-vector space denoted V ⊕ W (also V × W) and
-- consists of ordered pairs (v, w) where v ∈ V, w ∈ W.
-- Add and smul are component-wise.

-- First projection map:
--   `.fst`: K-linear map from (V × W) to V
--   `.fst`(v, w) = v
example : V × W →ₗ[K] V := LinearMap.fst K V W

-- Second projection map:
--   `.snd`: K-linear map from (V × W) to W
--   `.snd`(v, w) = w
example : V × W →ₗ[K] W := LinearMap.snd K V W

-- Universal property of the product
-- Gives
--   φ: K-linear map from U to V
--   ψ: K-linear map from U to W
-- `.prod φ ψ`: K-linear map from U to (V × W)
-- `.prod φ ψ`(u) = (`φ`(u), `ψ`(u))
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ

-- The product map does the expected thing
--   (`.fst` ∘ `.prod φ ψ`)(u) = `.fst`(`.prod φ ψ`(u)) = `.fst`(v, w) = v = `φ`(u)
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl

-- Gives
--   φ: K-linear map from V to U
--   ψ: K-linear map from W to T
-- `.prodMap φ ψ` constructs a K-linear map from (V × W) to (U × T)
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ
-- This is simply done by combining the projections with the universal property
--   `.fst K V W`: K-linear map from (V × W) to V
--   `φ`: K-linear map from V to U
--   `φ.comp .fst K V W`: K-linear map from (V × W) to U
--
--   `.snd K V W`: K-linear map from (V × W) to W
--   `ψ`: K-linear map from W to T
--   `ψ.comp .snd K V W`: K-linear map from (V × W) to T
--
--   `.prod` combines them into a K-linear map from (V × W) to (U × T)
--    i.e., `.prodMap φ ψ`(v, w) = ((`φ` ∘ `.fst`)(v, w), (`ψ` ∘ `.snd`)(v, w))
--                               = (`φ`(`.fst`(v, w)), `ψ`(`.snd`(v, w)))
--                               = (`φ`(v), `ψ`(w))
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
  φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ .snd K V W) := rfl

-- First inclusion map:
--   `.inl`: K-linear map from V to (V × W)
--   `.inl`(v) = (v, 0)
example : V →ₗ[K] V × W := LinearMap.inl K V W

-- Second inclusion map:
--   `.inr`: K-linear map from W to (V × W)
--   `.inr`(w) = (0, w)
example : W →ₗ[K] V × W := LinearMap.inr K V W

-- Universal property of the sum (aka coproduct)
-- Gives
--   φ: K-linear map from V to U
--   ψ: K-linear map from W to U
-- `.coprod φ ψ`: K-linear map from (V × W) to U
-- `.coprod φ ψ`(v, w) = φ(v) + ψ(w)
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ

-- The coproduct map does the expected thing
--   (`.coprod φ ψ` ∘ `.inl`)(v, w) = `.coprod φ ψ`(`.inl`(v))
--                                  = `.coprod φ ψ`(v, 0)
--                                  = `φ`(v) + `ψ`(0) = `φ`(v)
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
  LinearMap.coprod_inl φ ψ
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
  LinearMap.coprod_inr φ ψ

-- The coproduct map is defined in the expected way
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) (v : V) (w : W) :
    φ.coprod ψ (v, w) = φ v + ψ w :=
  rfl

end binary_product

section families
open DirectSum

-- ι: index set (can be infinite)
--    `DecidableEq`: able to decide if two elements are equal or not.
-- {Vᵢ: i ∈ ι}: family of K-vector spaces
variable {ι : Type*} [DecidableEq ι]
         (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

-- Direct sum ⨁ᵢ Vᵢ: tuples where only finitely many entries are non-zero
-- Direct prod Πᵢ Vᵢ: all tuples

-- The universal property of the direct sum
-- Given
--   {φᵢ: Vᵢ → W : i ∈ ι}: family of K-linear maps from Vᵢ to W
-- `DirectSum.toModule K ι W φ`:
--   K-linear map from the direct sum to W
example (φ : Π i, (V i →ₗ[K] W)) : (⨁ i, V i) →ₗ[K] W :=
  DirectSum.toModule K ι W φ

-- The universal property of the direct product
-- Given
--   {φᵢ: Vᵢ → W : i ∈ ι}: family of K-linear maps from W to Vᵢ
-- `LinearMap.pi φ`:
--   K-linear map from W to the direct product
example (φ : Π i, (W →ₗ[K] V i)) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ

-- The projection maps from the product
--   `LinearMap.prod i`: K-linear map from the direct product to the ith component
example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i

-- The inclusion maps into the sum
-- `DirectSum.lof K ι V i`: K-linear map from the i-th K-vector space to the direct sum
--     (v) = create a tuple where the ith component is v, other components are 0
example (i : ι) : V i →ₗ[K] (⨁ i, V i) := DirectSum.lof K ι V i

-- The inclusion maps into the product
-- `LinearMap.single K V i`: K-linear map from the i-th K-vector space to the direct product
-- Defined such that (`.prod i` ∘ `.single K V i`)(vᵢ) = vᵢ
--                   (`.prod j` ∘ `.single K V i`)(vᵢ) = 0 for j ≠ i
example (i : ι) : V i →ₗ[K] (Π i, V i) := LinearMap.single K V i

-- If ι is finite, direct sum and direct product are isomorphic.
example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
  linearEquivFunOnFintype K ι V

end families
