import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


section matrices

-- Adding vectors
#eval ![1, 2] + ![3, 4]  -- `![4, 6]`

-- Adding matrices
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- `!![4, 6; 8, 10]`

-- Multiplying matrices
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- `!![13, 16; 29, 36]`

open Matrix

-- matrices acting on vectors on the left
#eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- `![3, 7]`

-- matrices acting on vectors on the left, resulting in a size one matrix
#eval !![1, 2] *ᵥ ![1, 1]  -- `![3]`

-- matrices acting on vectors on the right
#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- `![9, 12]`

#eval row (Fin 3) ![1, 2] -- `!![1, 2; 1, 2; 1, 2]`

#eval col (Fin 4) ![1, 2] -- `!![1, 1, 1, 1; 2, 2, 2, 2]`

-- vector dot product
#eval ![1, 2] ⬝ᵥ ![3, 4] -- `11`

-- matrix transpose
#eval !![1, 2; 3, 4]ᵀ -- `!![1, 3; 2, 4]`

-- determinant
#eval !![(1 : ℤ), 2; 3, 4].det -- `-2`

-- trace
#eval !![(1 : ℤ), 2; 3, 4].trace -- `5`

#simp !![(1 : ℝ), 2; 3, 4].det -- `4 - 2*3`
#simp !![(1 : ℝ), 2; 3, 4].trace -- `1 + 4`

#norm_num !![(1 : ℝ), 2; 3, 4].det -- `-2`
#norm_num !![(1 : ℝ), 2; 3, 4].trace -- `5`

variable (a b c d : ℝ) in
#simp !![a, b; c, d].det -- `a * d – b * c`

variable (a b c d : ℝ) in
#simp !![a, b; c, d].trace -- `a + d`

-- `A⁻¹ = Ring.inverse A.det • A.adjugate`: Cramer's rule
-- `Ring.inverse 0 = 0`
#norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 4]⁻¹ -- `!![-2, 1; 3 / 2, -(1 / 2)]`

-- `Invertible`: typeclass of invertible matrices
-- `Matrix.invertibleOfIsUnitDet`:
--   a matrix is invertible if its determinant is unit
--     unit: has multiplicative inverse
example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  have : Invertible !![(1 : ℝ), 2; 3, 4] := by
    apply Matrix.invertibleOfIsUnitDet
    norm_num
  simp

-- `one_fin_two`: `1 = !![1, 0; 0, 1]`
example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  norm_num [Matrix.inv_def]
  exact one_fin_two.symm

section

-- Matrix can also be defined using the `m → n → α` type
-- where `m`: type indexing of the rows
--       `n`: type indexing of the columns
--       `α`: type of the entries
-- However, for a ring `R`, `m → n → R` will have point-wise multiplication
--          that does not match matrix multiplication
-- Therefore, `Matrix m n α` is preferred.

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) * (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : !![1, 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
  norm_num

-- `Matrix.of` defines a matrix using a function of row and column indices
-- Ex: Vandermonde matrix M corresponding to (vᵢ : i ∈ [n]) has
--       Mᵢⱼ = (vᵢʲ : j ∈ [n])
example {n : ℕ} (v : Fin n → ℝ) :
    Matrix.vandermonde v = Matrix.of (fun i j : Fin n ↦ v i ^ (j : ℕ)) :=
  rfl
end

end matrices

-- Let V be a vector space.
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section

-- Basis: multiple equivalent definitions
-- A basis B of a vector space V satisfies
-- 1) Universal property:
--      for any vector space W and function f : B → W
--      there exists a unique linear map φ : V → W that extends f
-- 2) Linear independence and spanning:
--      linearly independence: no non-trivial linear combination of basis vectors equals 0
--      spanning: every vector in V can be written as linear combination of basis vectors
-- 3) Unique linear combination: combine linearly independence and spanning
--      each vector in V can be written uniquely as a linear combination of basis vectors
-- 4) Linear isomorphism with a power of K
-- Lean uses (4).

-- Infinite-dimensional vector spaces cannot use direct product of copies of K
-- Reason: vectors are *finite* linear combinations of basis vectors
--         infinite sums require topology and convergence
-- Solution: function with finite support `ι →₀ K` or `Finsupp`
--   f : ι → K has finite support if {i ∈ ι | f(i) ≠ 0} is finite
-- (Alternative: direct sum `⨁ i : ι, K`)

-- Let B be a basis of V indexed by ι.
-- Let v be a vector in V.
-- Let i be an index in ι.
variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

-- `B i`: the basis vector with index i, bᵢ
#check (B i : V)

-- Each vector v ∈ V is ∑ (i : ι) fᵥ(i) bᵢ
-- where fᵥ : ι → K gives the coordinates

-- `B.repr`: the linear isomorphism between
--   `V`: the vector space V
--   `ι →₀ K`: space of finitely supported functions ι → K
--   each v ∈ V corresponds to an fᵥ : ι → K
#check (B.repr : V ≃ₗ[K] ι →₀ K)

-- `B.repr v`: the coordinate function fᵥ of v wrt B
#check (B.repr v : ι →₀ K)

-- `B.repr v i`: the coordinate of v along the i-th basis vector
-- projecting v along the subspace spanned by the i-th basis vector
#check (B.repr v i : K)

-- `Basis.mk`: Construct a basis B from
--   `b`: family of vectors {bᵢ ∈ V : i ∈ ι}
--   `b_indep`: proof of linear independence of {bᵢ}
--     `LinearIndependent K b`: {bᵢ} is linearly independent over K
--       no non-trivial linear combination of {bᵢ} with coeffs in K that is 0
--   `b_spans`: proof of spanning of {bᵢ}
--     `∀ v, v ∈ Submodule.span K (Set.range b)`: {bᵢ} spans V
--       the smallest subspace containing {bᵢ}m denoted span({bᵢ}), is V
--       for all v ∈ V, v is also in this smallest subspace
--       V ≤ span({bᵢ})
-- Note: `noncomputable`
noncomputable example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)

-- `Basis.mk_apply`: The basis B constructed above
-- has exactly the same vectors as the family of vectors {bᵢ}.
example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
    Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
  Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i

variable [DecidableEq ι]

-- `Finsupp.basisSingleOne`: canonical basis of the space of finitely supported functions ι → K
--   `.repr = LinearEquiv.refl`: identity isomorphism
-- The basis is *defined* as the basis induced by the identity isomorphism.
-- This derives that the basis vectors are the indicator functions.
example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

-- The i-th basis vector is the indicator function eᵢ : ι → K
--   eᵢ : ι → K s.t eᵢ(i) = 1, eᵢ(j) = 0 ∀ j ≠ i
--   eᵢ takes value 1 at i and 0 everywhere else.
-- `Finsupp.single i 1`: eᵢ
example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl

-- If the index set is finite, then we can directly use the full function space `ι → K`.
-- `Pi.basisFun` is the finite counterpart of `Finsupp.basisSingleOne`
--   canonical basis indexed by ι
example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
  simp

-- Express any vector as a linear combination of basis vectors.
--   `∑ i : ι, B.repr v i • (B i)` = ∑_{i ∈ ι} fᵥ(i) bᵢ = v
-- where
--   `B i` = bᵢ: the i-th basis vector
--   `B.repr v i` = fᵥ(i): coordinate of v along bᵢ
example [Fintype ι] : ∑ i : ι, B.repr v i • (B i) = v :=
  B.sum_repr v

-- `c`: "finitely supported function"/coeffs of the linear combination {cᵢ}
-- `f`: family of vectors {fᵢ} (can be infinite)
-- `s`: finite set of indices s
-- `h`: support of c is contained in s
--   sum over s includes all non-zero terms
-- `Finsupp.linearCombination K f c`: linear combination of {fᵢ} with coeffs {cᵢ}
-- `∑ i ∈ s, c i • f i`: finite sum over i ∈ s of cᵢ fᵢ
-- `Finsupp.linearCombination_apply_of_mem_supported`: if the support of c is contained in s
-- then the finitely supported linear combination is equal to the sum over the finite set
example (c : ι →₀ K) (f : ι → V) (s : Finset ι) (h : c.support ⊆ s) :
    Finsupp.linearCombination K f c = ∑ i ∈ s, c i • f i :=
  Finsupp.linearCombination_apply_of_mem_supported K h

-- `B.linearCombination_repr`: generalization of `B.sum_repr`
-- `B : Basis ι K V` is coerced to `ι → V` (not necessarily finitely supported)
-- only requires `B.repr v : ι →₀ K` to be finitely supported (which it is by design)
example : Finsupp.linearCombination K B (B.repr v) = v :=
  B.linearCombination_repr v

-- `Finsupp.linearCombination K f` (without `c`) is a linear map
--   takes a finitely supported function (e.g., coordinates `c`)
--   gives a vector in V
-- given the coordinates in the basis, produce the vector at that coordinate
variable (f : ι → V) in
#check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)

section

-- Let W be a K-vector space.
-- Let φ be a K-linear map from V to W.
-- Let {uᵢ : i ∈ ι} be a family of vectors in W.
variable {W : Type*} [AddCommGroup W] [Module K W]
         (φ : V →ₗ[K] W) (u : ι → W)

-- Given a basis B.
-- `B.constr K`: linear isomorphism between
--   space of family of vectors ι → W
--   space of K-linear maps from V to W
#check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))

-- `u` = {uᵢ}: images of the basis vectors
-- `B.constr K u`: K-linear map from V to W specified by {uᵢ}
--   (we know where other vectors are mapped to from where the bases are mapped to)
#check (B.constr K u : V →ₗ[K] W)

-- The constructed K-linear map maps bᵢ to uᵢ
example (i : ι) : B.constr K u (B i) = u i :=
  B.constr_basis K u i

-- The linear maps are uniquely determined by their values on a basis.
-- If two linear maps agree on the basis vectors then they are the same map.
example (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h

-- Let B' be a basis of W, indexed by ι'.
-- Consider ι, ι' to be finite and have decidable equality property.
variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

open LinearMap

-- `toMatrix B B'`: K-linear isomorphism between
--   space of linear maps from V to W
--   space of matrices indexed by ι' and ι over K
-- each linear map from V to W corresponds to a matrix relative to B and B'
-- "change-of-basis" matrix from B to B'
#check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

open Matrix -- get access to the ``*ᵥ`` notation for multiplication between matrices and vectors.

-- `φ`: linear map φ from V to W
-- `v`: vector in V
-- `toMatrix B B' φ`: matrix representation of φ (relative to B and B')
-- `B.repr v`: coordinate representation of v (relative to B)
-- `φ v`: image of v in W by φ
-- `B'.repr (φ v)`: coordinate representation of φ v (relative to B')
example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v

-- Let B'' be another basis on W, indexed by ι''.
-- Consider ι'' to also be finite and have the decidable equality property
variable {ι'' : Type*} (B'' : Basis ι'' K W) [Fintype ι''] [DecidableEq ι'']

-- `toMatrix B' B'' .id`: "change-of-basis" matrix
example (φ : V →ₗ[K] W) : (toMatrix B B'' φ) = (toMatrix B' B'' .id) * (toMatrix B B' φ) := by
  simp

end

open Module LinearMap Matrix

-- Some lemmas coming from the fact that `LinearMap.toMatrix` is an algebra morphism.
-- `toMatrix B B'' (f ∘ₗ g) = (toMatrix B' B'' f) * (toMatrix B B' g)`
-- the matrix of a composition (`toMatrix B B'' (f ∘ₗ g) `)
-- is the multiplication of the matrices (`toMatrix B' B'' f` and `toMatrix B B' g`)
#check toMatrix_comp
-- id ∘ φ = φ
#check id_comp
-- φ ∘ id = φ
#check comp_id
-- `toMatrix B B id = 1`: matrix representation of the identity map
--                        is the identity matrix
#check toMatrix_id

-- Some lemmas coming from the fact that ``Matrix.det`` is a multiplicative monoid morphism.
-- det(A * B) = det(A) * det(B)
#check Matrix.det_mul
-- det(1) = 1
#check Matrix.det_one

-- Let B' be a basis indexed by the same ι as B.
-- Let φ be an endomorphism of V over K.
example [Fintype ι] (B' : Basis ι K V) (φ : End K V) :
    (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
  -- Let M and M' be the matrices of φ with respect to B and B' respectively.
  set M := toMatrix B B φ
  set M' := toMatrix B' B' φ
  -- Let P and P' be the chang-of-basis matrix from B' to B and from B to B' respectively
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
  -- We can rewrite M = P' * (M' * P) since
  have hM := calc
    M = toMatrix B B φ := rfl
    _ = toMatrix B B (LinearMap.id ∘ₗ φ ∘ₗ LinearMap.id) := by rw [comp_id, id_comp]
    _ = toMatrix B' B LinearMap.id * toMatrix B B' (φ ∘ₗ LinearMap.id) := by rw [toMatrix_comp B B' B]
    _ = toMatrix B' B LinearMap.id * (toMatrix B' B' φ * toMatrix B B' LinearMap.id) := by rw [toMatrix_comp B B' B']
    _ = P' * (M' * P) := rfl
  have hP'P := calc
    P' * P = (toMatrix B' B) LinearMap.id * (toMatrix B B') LinearMap.id := rfl
    _ = toMatrix B B (LinearMap.id ∘ₗ LinearMap.id) := by rw [toMatrix_comp B B' B]
    _ = toMatrix B B LinearMap.id := by rw [comp_id]
    _ = 1 := by rw [toMatrix_id]
  have hP'Pdet := calc
    P'.det * P.det = (P' * P).det := by rw [det_mul]
    _ = (1: Matrix ι ι K).det := by rw [hP'P]
    _ = 1 := by rw [det_one]
  calc
    M.det = (P' * (M' * P)).det := by rw [hM]
    _ = P'.det * (M'.det * P.det) := by repeat rw [det_mul]
    _ = P'.det * M'.det * P.det := by rw [mul_assoc]
    _ = M'.det * P'.det * P.det := by rw [mul_comm M'.det]
    _ = M'.det * (P'.det * P.det) := by rw [mul_assoc]
    _ = M'.det * 1 := by rw [hP'Pdet]
    _ = M'.det := by rw [mul_one]

end

section

-- Rank of a module over a ring
-- Dimension of a vector space over a field
-- Equal to 0 if infinite rank/dimension (convention for `finrank` only)
#check (Module.finrank K V : ℕ)

-- `Fin n → K`: space of functions from a finite type with n elements to K
--              essentially K^n, n-d vector space over K
-- `Fin n → K` has dimension n.
example (n : ℕ) : Module.finrank K (Fin n → K) = n :=
  Module.finrank_fin_fun K

-- `ℂ`: space of complex numbers
-- `ℂ`, seen as a vector space over itself, has dimension 1.
-- A basis is {1}:
--   any complex number a + bi can be expressed as (a + bi: ℂ) * 1.
example : Module.finrank ℂ ℂ = 1 :=
  Module.finrank_self ℂ

-- `ℂ`, seen as a vector space over `ℝ`, has dimension 2.
-- A basis is {1, i}:
--  any complex number a + bi can be expressed as (a : ℝ) * 1 + (b : ℝ) * i.
example : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

-- Thus, we need to specify the field.

-- A nontrivial vector space has a positive dimension.
-- `Nontrivial V`: V has non-empty basis/more than just the 0 vector
-- `Nontrivial V → 0 < Module.finrank K V` requires `FiniteDimensional K V`
--   infinite-dimension vector space (nontrivial) has `finrank` 0 by convention
example [FiniteDimensional K V] : 0 < Module.finrank K V ↔ Nontrivial V  :=
  Module.finrank_pos_iff

-- `Module.finrank_pos_iff.mpr` requires specifying the ring (here, `R := K`)
-- because it cannot be inferred from `Nontrivial V`.
example [FiniteDimensional K V] (h : 0 < Module.finrank K V) : Nontrivial V := by
  apply (Module.finrank_pos_iff (R := K)).1
  exact h

-- Let B be a basis of the K-vector space V indexed by ι.
variable {ι : Type*} (B : Basis ι K V)

-- Any vector space having a finite basis is finite-dimensional.
--   finite basis: is indexed by a finite index set
-- If ι is finite, V is finite-dimensional.
example [Finite ι] : FiniteDimensional K V := FiniteDimensional.of_fintype_basis B

-- Any basis of a finite-dimensional vector space is finite.
-- If V is finite-dimensional, ι is finite.
-- `FiniteDimensional.fintypeBasisIndex B`: ι is a finite type
-- `.finite`: ι is finite
example [FiniteDimensional K V] : Finite ι :=
  (FiniteDimensional.fintypeBasisIndex B).finite
end

section

-- Let E, F be linear subspaces of V.
-- Supose that V is finite-dimensional.
variable (E F : Submodule K V) [FiniteDimensional K V]

open Module

-- dim(E + F) + dim(E ∩ F) = dim(E) + dim(F)
-- `: Submodule K V`: lead Lean to interpret as a Submodule first, instead of, say, Set
example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
    finrank K E + finrank K F :=
  Submodule.finrank_sup_add_finrank_inf_eq E F

-- dim(E) ≤ dim(V)
example : finrank K E ≤ finrank K V := Submodule.finrank_le E

-- If dim(E) + dim(F) > dim(V) then E ∩ F is non-trivial.
example (h : finrank K V < finrank K E + finrank K F) :
    Nontrivial (E ⊓ F : Submodule K V) := by
  -- Goal: `Nontrivial ↥(E ⊓ F)`
  -- E ∩ F is nontrivial ⇔ E ∩ F ≠ ⊥
  rw [Submodule.nontrivial_iff_ne_bot]
  -- Goal: `E ⊓ F ≠ ⊥`
  -- Suppose E ∩ F = ⊥.
  by_contra h'
  -- Then dim(E ∩ F) = 0.
  have h' := Submodule.finrank_eq_zero.mpr h'
  -- Then dim(E) + dim(F) = dim(E + F) + dim(E ∩ F) ∵ above
  --                      = dim(E + F) ∵ dim(E ∩ F) = 0
  --                      ≤ dim(V) ∵ E + F ≤ V
  --                      < dim(E) + dim(F) ∵ assumption
  -- Contradiction!
  have := calc
    finrank K E + finrank K F = finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) :=
      (Submodule.finrank_sup_add_finrank_inf_eq E F).symm
    _ = finrank K (E ⊔ F : Submodule K V) := by rw [h', add_zero]
    _ ≤ finrank K V := Submodule.finrank_le (E ⊔ F : Submodule K V)
    _ < finrank K E + finrank K F := h
  exact (lt_self_iff_false (finrank K ↥E + finrank K ↥F)).mp this

end

-- Finite-dimensional space: dimension is a natural number.
-- Infinite-dimensional space: cardinality
-- Cardinality: "size" of a set (even for infinite sets)
--              two sets of the same cardinality if there is a bijection between them

-- Each type in Lean belongs to a universe level.
-- `Type u` has type `Type (u + 1)`.
-- Universe levels are not types themselves.
--   cannot compare them or perform arithmetic on them

-- `Cardinal.{u}`: type of cardinal numbers within universe level u
-- `Cardinal.mk α`: creates the cardinal corresponding to the type `α` (must be in `Type u`)
-- Curly braces `{u}` indicate that `u` is a universe variable.

-- `Module.rank K V`: rank of vector space V
--   defined as the supremum of the cardinals of
--   all linearly independent subsets of V
-- If `V` has type `Type u` then `Module.rank K V` has type `Cardinal.{u}`

#check V -- Type u_2
#check Module.rank K V -- Cardinal.{u_2}

-- Lean provides a `max` operation on universe levels.
--   `max u v`: larger of the two levels (not a number)
-- `Cardinal.lift.{u, v} : Cardinal.{v} → Cardinal.{max v u}`
--   lifts cardinal from universe v to universe `max v u`

universe u v -- `u` and `v` will denote universe levels

-- Let ι, ι' be types in universe u and v, respectively.
-- Let B, B' be bases indexed by ι, ι', respectively.
variable {ι : Type u} (B : Basis ι K V)
         {ι' : Type v} (B' : Basis ι' K V)

-- The cardinals of the indexing types, after lifted, are equal.
-- (Any two bases for the same vector space have the same cardinality.)
example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
  mk_eq_mk_of_basis B B'

-- Generalization of finite-dimensional cases by coercion from natural number to cardinal.
example [FiniteDimensional K V] :
    (Module.finrank K V : Cardinal) = Module.rank K V :=
  Module.finrank_eq_rank K V
