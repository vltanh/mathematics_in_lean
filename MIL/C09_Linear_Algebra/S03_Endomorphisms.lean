import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

-- Let V, W be vector spaces over a field K.
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {W : Type*} [AddCommGroup W] [Module K W]

open Polynomial Module LinearMap

-- Endormorphism: linear map from a vector space to itself
-- Set of all endomorphisms of V over K forms a K-algebra
--   vector space over K
--   has a mul operation between endomorphisms

-- `φ ψ : End K V`: φ, ψ are endomorphisms of V over K
-- multiplication of endomorphisms is defined as composition
example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  LinearMap.mul_eq_comp φ ψ -- `rfl` would also work

-- evaluate polynomials on endomorphisms
-- `P: K[X]`: P is a polynomial with coeffs in K
-- `φ: End K V`: φ is an endomorphism of V over K
-- `aeval φ P : V →ₗ[K] V`: evaluate P at φ
--   the result is another endomorphism
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating X on φ gives back φ
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ

-- The bottom subspace is the zero subspace
-- p = ⊥ ↔ ∀ x ∈ p, x = 0
#check Submodule.eq_bot_iff
-- Infimum of two subspaces is their intersection
-- x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q
#check Submodule.mem_inf
-- Kernel of a linear map consists of all elements mapped to 0
-- x ∈ ker(f) ↔ f x = 0
#check LinearMap.mem_ker

-- `IsCoprime P Q` is defined as `∃ U V, U * P + V * Q = 1`

-- Intersection of the kernel of two polynomial evaluations is the zero subspace
-- Key idea:    x is in the kernel of both P(φ) and Q(φ)
--           => x is in the kernel of (UP + VQ)(φ)
--           => x is in the kernel of (1)(φ) which is the identity map
--           => x = 0 or equivalently, x ∈ ⊥
example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  -- Let e = `aeval φ` be the polynomial evaluation homomorphism.
  -- `Goal`: ker(e(P)) ⊓ ker(e(Q)) = ⊥
  -- Since ker(e(P)) ⊓ ker(e(Q)) = ⊥ ↔ ∀ x ∈ ker(e(P)) ⊓ ker(e(Q)), x = 0
  rw [Submodule.eq_bot_iff]
  -- `Goal`: ∀ x ∈ ker(e(P)) ⊓ ker(e(Q)), x = 0
  -- Fix x ∈ ker(e(P)) ⊓ ker(e(Q)) (`hx`)
  intro x hx
  -- `Goal`: x = 0
  -- Then x ∈ ker(e(P)) and x ∈ ker(e(Q)).
  rw [Submodule.mem_inf] at hx
  -- Then e(P)(x) = 0 (`hP`) and e(Q)(x) = 0 (`hQ`).
  repeat rw [LinearMap.mem_ker] at hx
  rcases hx with ⟨hP, hQ⟩
  -- Since P and Q are coprime, there exists U, V s.t. UP + VQ = 1 (`h`).
  rcases h with ⟨U, V, h⟩
  -- x = e(1)(x) (∵ e(1) gives the identity endomorphism)
  --   = e(UP + VQ)(x)
  --   = (e(U) * e(P) + e(V) * e(Q))(x)
  --   = e(U)(e(P)(x)) + e(V)(e(Q)(x))
  --   = e(U)(0) + e(V)(0) = 0
  calc
    x = aeval φ (1 : K[X]) x := by rw [aeval_one, one_apply]
    _ = aeval φ (U * P + V * Q) x := by rw [h]
    _ = (aeval φ (U * P) + aeval φ (V * Q)) x := by rw [aeval_add]
    _ = (aeval φ U * aeval φ P + aeval φ V * aeval φ Q) x := by repeat rw [aeval_mul]
    _ = (aeval φ U * aeval φ P) x + (aeval φ V * aeval φ Q) x := by rw [add_apply]
    _ = (aeval φ U) (aeval φ P x) + (aeval φ V) (aeval φ Q x) := by repeat rw [mul_apply]
    _ = (aeval φ U) 0 + (aeval φ V) 0 := by rw [hP, hQ]
    _ = 0 + 0 := by repeat rw [map_zero]
    _ = 0 := by rw [zero_add]

-- Sum of an element in S and an element in T is in S ⊔ T
-- ∀ s ∈ S, t ∈ T, s + t ∈ S ⊔ T
#check Submodule.add_mem_sup
-- Homomorphism preserves multiplication
-- f(x * y) = f(x) * f(y)
#check map_mul
-- Multiplication of linear maps is composition
-- (f * g)(x) = f(g(x))
#check LinearMap.mul_apply
-- Kernel of composition contains kernel of the first function for linear maps
-- f: A → B, g: B → C, ker(f) ≤ ker(g ∘ f)
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  -- Let e be the polynomial evaluation homomorphism `aeval φ`.
  -- (given a polynomial P, evaluated P at φ to get another endomorphism)
  -- `Goal`: ker(e(P)) ⊔ ker(e(Q)) = ker(e(PQ))
  apply le_antisymm
  -- `Goal`: ker(e(P)) ⊔ ker(e(Q)) ≤ ker(e(PQ))
  · apply sup_le
    -- `Goal`: ker(e(P)) ≤ ker(e(PQ))
    · -- ker(e(P)) ≤ ker(e(Q) ∘ e(P)) = ker(e(QP)) = ker(e(PQ))
      rw [mul_comm, map_mul]
      apply ker_le_ker_comp
    -- `Goal`: ker(e(Q)) ≤ ker(e(PQ))
    · -- ker(e(Q)) ≤ ker(e(P) ∘ e(Q)) = ker(e(PQ))
      rw [map_mul]
      apply ker_le_ker_comp
  -- `Goal`: ker(e(PQ)) ≤ ker(e(P)) ⊔ ker(e(Q))
  · -- Since P and Q are coprime, there exists U, V s.t. UP + VQ = 1
    rcases h with ⟨U, V, hUV⟩
    -- Let x ∈ ker(e(PQ)). We show that x ∈ ker(e(P)) ⊔ ker(e(Q)).
    intro x h
    -- x = e(1)(x) = e(UP+VQ)(x) = (e(UP) + e(VQ))(x) = e(UP)(x) + e(VQ)(x) = e(VQ)(x) + e(UP)(x)
    have := calc
      x = aeval φ (1 : K[X]) x := by rw [aeval_one, one_apply]
      _ = aeval φ (U * P + V * Q) x := by rw [hUV]
      _ = (aeval φ (U * P) + aeval φ (V * Q)) x := by rw [aeval_add]
      _ = aeval φ (U * P) x + aeval φ (V * Q) x := by rw [add_apply]
      _ = aeval φ (V * Q) x + aeval φ (U * P) x := by rw [add_comm]
    rw [this]
    -- If e(VQ)(x) ∈ ker(e(P)) and e(UP)(x) ∈ ker(e(Q)) then we get what we need to prove.
    apply Submodule.add_mem_sup
    -- `Goal`: e(VQ)(x) ∈ ker(e(P)) or, equivalently, e(P)(e(VQ)(x)) = 0
    -- e(P)(e(VQ)(x)) = e(PVQ)(x) = e(VPQ)(x) = e(V)(e(PQ)(x)) = e(V)(0) = 0
    · calc
        aeval φ P (aeval φ (V * Q) x) = (aeval φ P * aeval φ (V * Q)) x := by rw [← mul_apply]
        _ = aeval φ (P * (V * Q)) x := by rw [← aeval_mul]
        _ = aeval φ (V * (P * Q)) x := by rw [mul_left_comm]
        _ = (aeval φ V * aeval φ (P * Q)) x := by rw [aeval_mul]
        _ = aeval φ V (aeval φ (P * Q) x) := by rw [mul_apply]
        _ = aeval φ V 0 := by rw [h]
        _ = 0 := by rw [map_zero]
     -- `Goal`: e(UP)(x) ∈ ker(e(Q)) or, equivalently, e(Q)(e(UP)(x)) = 0
    -- e(Q)(e(UP)(x)) = e(QUP)(x) = e(UPQ)(x) = e(U)(e(PQ)(x)) = e(U)(0) = 0
    · calc
        aeval φ Q (aeval φ (U * P) x) = (aeval φ Q * aeval φ (U * P)) x := by rw [← mul_apply]
        _ = aeval φ (Q * (U * P)) x := by rw [← aeval_mul]
        _ = aeval φ (U * (P * Q)) x := by rw [mul_left_comm, mul_comm P]
        _ = (aeval φ U * aeval φ (P * Q)) x := by rw [aeval_mul]
        _ = aeval φ U (aeval φ (P * Q) x) := by rw [mul_apply]
        _ = aeval φ U 0 := by rw [h]
        _ = 0 := by rw [map_zero]

-- Given an endomorphism φ of V over K
-- Eigenspace: For all scalar a ∈ K, the eigenspace of φ associated with a
--   set of all vectors v ∈ V s.t. φ(v) = av
--   a subspace of V
--   only interesting when it is not the 0 subspace
-- i.e., the kernel of (φ - a Id) where Id is the identity endomorphism
-- In Lean: `φ.eigenspace a` is defined as `.ker (φ - a • 1)`
example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def

-- Eigenvalue: A scalar a ∈ K is an eigenvalue of φ if
--   the eigenspace associated with a in non-zero (contains a non-zero vector)
-- `End.HasEigenvalue φ a`: a is an eigenvalue of φ
--   iff eigenspace of φ associated with a is non-zero
example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

-- Eigenvector: a non-zero vector v ∈ V is an eigenvector of φ if
--   ∃ a ∈ K s.t. φ(v) = av
--   non-zero element of an eigenspace
-- `End.HasEigenvector φ a v`: v is an eigvec of φ with eigval a
-- φ has an eigval a iff there is an eigvec v of φ with eigval a
-- `End.HasEigenvalue.exists_hasEigenvector`:
--   if φ has eigval a then there exists an eigvec v corresponding to a
-- `φ.hasEigenvalue_of_hasEigenvector hv`:
--   if φ has an eigvec v (`hv`) corresponding to eigval a then φ has eigval a
example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

-- `φ.Eigenvalues`: set of all eigenvalues of φ
--                  = subtypes of scalars a that are eigvals of φ
example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalues are roots of the minimal polynomial
-- `minpoly K φ`: the minimal polynomial of φ over K
--   monic polynomial: leading coeff (coeff of the highest-deg term) is 1
--   of least degree
--   annihilates φ (gives the zero endomorphism when evaluated at φ)
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true
-- (roots of the minimal polynomial are eigenvalues)
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton: the characteristic polynomial of φ annihilates φ
--                  (evaluating it at φ gives the zero endomorphism)
-- `φ.charpoly`: the characteristic polynomial of φ
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
