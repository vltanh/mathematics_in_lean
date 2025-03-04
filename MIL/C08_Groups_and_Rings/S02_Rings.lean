import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ZMod.Quotient
import MIL.Common

noncomputable section

example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

-- x is a unit if x has a multiplicative inverse

-- in ℤ, the units are 1 and -1
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

-- a unit x has inverse x⁻¹
example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x

-- units form a group
example {M : Type*} [Monoid M] : Group Mˣ := inferInstance

-- Ring homomorphism:
--   preserve addition
--   preserve multiplication
--   preserve multiplicative identity

-- Ring homomorphism preserves addition
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y := f.map_add x y

-- Ring homomorphism induces group homomorphism between unit groups
-- φ(x)⁻¹ = φ(x⁻¹) where φ := Units.map f
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f

-- Subring is another ring
example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance

-- Range of a ring homomorphism is a subring of the codomain
-- f : R →+* S then f(R) is a subring of S

-- Ideal I of comm ring R:
--   contains 0 (additive identity)
--   closed under addition
--   absorption prop.: i ∈ I, r ∈ R, r * i ∈ I
-- (Ideal is an R-submodule of R)

-- Quotient ring R/I: partition of R into equiv. classes (cosets)
-- Equivalence: a ~ b iff a - b ∈ I, notation: a ≃ b (mod I)
-- Equiv. class: a + I for a ∈ R
-- Add/Mult: (a + I) +/* (b + I) = (a +/* b) + I (a, b: representative)
-- Absorption prop. ensures add/mult are well-defined

-- Canonical quotient map (ring homomorphism)
example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

-- Quotient map maps elements in I to 0 ("ignore" I)
example {R : Type*} [CommRing R] {a : R} {I : Ideal R} :
    Ideal.Quotient.mk I a = 0 ↔ a ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

-- Universal property
-- If
--   R, S: comm rings
--   I: ideal of R
--   f: ring homomorphism R →+* S
--   I is contained in Ker f
-- then f = π ∘ f' where
--   π: R →+* R / I: canonical quotient map
--   f': R / I →+* S: induced homomorphism
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (H : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
  Ideal.Quotient.lift I f H

-- If
--    R, S: comm rings
--    f: ring homomorphism R →+* S
-- then R / Ker f ≃+* Im f
--
-- Proof idea:
--   1) Ker f is an ideal ≤ Ker f == universal property ==> φ
--   2) Prove φ is injective
example {R S : Type*} [CommRing R] [CommRing S](f : R →+* S) :
    R ⧸ RingHom.ker f ≃+* f.range :=
  RingHom.quotientKerEquivRange f

-- Fun example: Prove ℤ[i] / (a + bi) ≃+* ℤ / (a² + b²) ℤ
-- Key idea: let φ(x + yi) = x - a b y⁻¹
--   1) prove φ is a ring homomorphism
--   2) prove Ker φ = ⟨a + bi⟩
--   3) prove Im φ = ℤ / (a² + b²) ℤ
--   2) use the first isomorphism theorem

section
variable {R : Type*} [CommRing R] {I J : Ideal R}

-- Ideals form
--   1) complete lattice structure with partial order ⊆ (≤)
--        join/sup: I ⊔ J = smallest ideal containing I and J
--        meet/inf: I ⊓ J = I ∩ J
--   2) semiring:
--        add: I + J = {i + j | i ∈ I, j ∈ J}
--        mul: I * J = ideal generated by all i * j, i ∈ I, j ∈ J

-- Ideal addition = Ideal join
-- Proof:
-- 1) I + J is an ideal
--      1a) contains 0: 0 ∈ I, 0 ∈ J => 0 = 0 + 0 ∈ I + J
--      1b) closed under addition: x = i + j, x' = i' + j'
--                                 => x + x' = (i + i') + (j + j')
--      1c) absorption: r * (i + j) = r * i + r * j
-- 2) I + J contains I and J: i ∈ I => i = i + 0 ∈ I + J
-- 3) I + J is the smallest ideal
--      Let K be an ideal containing both I and J (I, J ≤ K)
--      x = i + j ∈ I + J
--      i ∈ I => i ∈ K, j ∈ I => j ∈ K
--      x = i + j ∈ K => I + J ≤ K
-- Note: actually, since ideal is a submodule, sum = sup
example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ J := Ideal.mul_le_left

example : I * J ≤ I := Ideal.mul_le_right

example : I * J ≤ I ⊓ J := Ideal.mul_le_inf

end

-- naive: φ(r + I) = f(r) + J
-- but it depends on the representative element r
-- or there can be r, r' that r - r' ∈ I but φ(r + I) ≠ φ(r' + I)
-- so if we additionally have f(I) ≤ J
-- then f(r) - f(r') = f(r - r') ∈ f(I) ≤ J => f(r) + J = f(r') + J
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J f H

-- even with I = J you cannot have R / I ≃+* R / J definitionally
example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq h

-- Two ideals I and J of R are coprime if I + J = R
example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  Ideal.quotientInfRingEquivPiQuotient f hf

open BigOperators PiNotation

example {ι : Type*} [Fintype ι] (a : ι → ℕ) (coprime : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  ZMod.prodEquivPi a coprime

section
variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

#check Pi.ringHom
#check ker_Pi_Quotient_mk

/-- The homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i`` featured in the Chinese
  Remainder Theorem. -/
def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i := by
  -- Sequence of homomorphisms (R →+* R ⧸ I i : i ∈ ι)
  -- Homomorphism R →+* Π i, R ⧸ I i (from Pi.ringHom)
  let f := Pi.ringHom (fun i ↦ Ideal.Quotient.mk (I i))
  -- Universal property: R ⧸ ⨅ i, I i →+* Π i, R ⧸ I i
  apply Ideal.Quotient.lift (⨅ i, I i) f
  -- In order to use the universal property,
  -- need to show ⨅ i, I i ≤ Ker f
  -- but ⨅ i, I i = Ker f (from ker_Pi_Quotient_mk)
  intro a ha
  rw [← ker_Pi_Quotient_mk] at ha
  exact ha

lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (mk _ x) = fun i : ι ↦ mk (I i) x :=
  rfl

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x :=
  rfl

#check injective_lift_iff

lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
  rw [chineseMap, injective_lift_iff, ker_Pi_Quotient_mk]

#check IsCoprime
#check isCoprime_iff_add
#check isCoprime_iff_exists
#check isCoprime_iff_sup_eq
#check isCoprime_iff_codisjoint

-- Ideals I and J are coprime iff
-- 1) I + J = R
-- 2) ∃ i ∈ I, ∃ j ∈ J, i + j = 1
-- 3) I ⊔ J = ⊤ = R
-- 4) I and J are codisjoint
--      Ann(I) + Ann(J) = R
--      Ann(I) = {r ∈ R : r * i = 0, ∀ i ∈ I}

-- Prove (1) <=> (2)
-- (=>) Suppose I + J = R. Since 1 ∈ R, 1 ∈ I + J.
-- (<=) Fix r ∈ R. r = r * 1 = r * (i + j) = r * i + r * j ∈ I + J.
--      So R ≤ I + J. But I + J ≤ R. So I + J = R.

#check Finset.mem_insert_of_mem
#check Finset.mem_insert_self

-- Setup:
--   Ideal I
--   Sequence of ideals (J j: j ∈ ι)
--   Finite subsequence s ≤ ι
-- If: I is coprime with each ideal J j, j ∈ s
-- Then: I is coprime with ⊓ (j ∈ s), J j
--
-- Key idea:
--   1) If: ∀ j ∈ s, I + J j = 1
--   2) Then: I + ⊓ (j ∈ s), J j = 1
--   3) Induction on s:
--     3a) Base case: s = ∅
--     3b) Assume IH: (∀ j ∈ s, I + J j = 1) → I + ⊓ (j ∈ s), J j = 1
--     3c) Assume ∀ j ∈ s ∪ {i}, I + J j = 1,
--         prove I + ⊓ (j ∈ s ∪ {i}), J j = 1
theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s _ hs =>
      rw [
        -- I + ⨅ j ∈ s ∪ {i}, J j = 1
        Finset.iInf_insert,
        -- I + (J i) ⊓ (⊓ j ∈ s, J j) = 1
        inf_comm,
        -- I + (⊓ j ∈ s, J j) ⊓ (J i) = 1
        one_eq_top,
        -- I + (⊓ j ∈ s, J j) ⊓ (J i) = ⊤
        eq_top_iff,
        -- ⊤ ≤ I + (⊓ j ∈ s, J j) ⊓ (J i)
        ← one_eq_top,
        -- 1 ≤ I + (⊓ j ∈ s, J j) ⊓ (J i)
      ]
      set K := ⨅ j ∈ s, J j
      calc
        1 = I + K                  :=
          (hs (fun j hjs => hf j (Finset.mem_insert_of_mem hjs))).symm
        _ = I + K * (I + J i)      := by
          rw [hf i (Finset.mem_insert_self i s), mul_one]
        _ = (1 + K) * I + K * J i  := by ring
        _ ≤ I + K ⊓ J i            :=
          add_le_add mul_le_left mul_le_inf

-- Setup
--   ι: finite set
--   I: sequence of ideals
-- If: all pairs of different ideals are coprime
-- Then: the homomorphism φ induced from I is surjective
--       (φ: R ⧸ ⨅ i, I i →+* Π i, R ⧸ I i)
lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
    (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  -- Goal: ∀ g ∈ Πᵢ R ⧸ Iᵢ, ∃ a ∈ R ⧸ ⨅ᵢ Iᵢ, φ(a) = g
  -- Fix (gᵢ ∈ R ⧸ Iᵢ : i ∈ ι)
  intro g
  -- Goal: ∃ a ∈ R ⧸ ⨅ᵢ Iᵢ, φ(a) = g
  -- For i ∈ ι, let φᵢ: R →+* R ⧸ Iᵢ (canonical quotient map)
  -- For i ∈ ι, φᵢ is surjective, so let fᵢ ∈ R be s.t. φᵢ(fᵢ) = gᵢ.
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  -- For all i, there is an eᵢ ∈ R s.t.
  -- 1) φᵢ(eᵢ) = 1
  -- 2) for all j ≠ i, φⱼ(eᵢ) = 0
  -- e acts like a "indicator"
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    -- Goal: For all i, ∃ e ∈ R s.t.
    -- 1) φᵢ(e) = 1
    -- 2) for all j ≠ i, φⱼ(e) = 0
    -- Fix i ∈ ι.
    intro i
    -- Goal: 1) φᵢ(e) = 1, 2) for all j ≠ i, φⱼ(e) = 0
    -- For all j ∈ ι \ {i}, Iᵢ and Iⱼ are coprime.
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      -- Fix j ∈ {i}ᶜ.
      intro j hjic
      -- Goal: Iᵢ and Iⱼ are coprime
      -- We know i ≠ j → Iᵢ and Iⱼ are coprime (assumption)
      apply hI i j
      -- Goal: i ≠ j
      -- j ∈ {i}ᶜ <=> j ∉ {i} <=> j ≠ i <=> i ≠ j
      rw [Finset.mem_compl, Finset.not_mem_singleton] at hjic
      exact hjic.symm
    -- Then Iᵢ is coprime with ⨅ j ∈ {i}ᶜ, Iⱼ.
    -- Then ∃ u ∈ Iᵢ, ∃ v ∈ (⨅ j ∈ {i}ᶜ, Iⱼ), u + v = 1.
    rcases isCoprime_iff_exists.mp (isCoprime_Inf hI') with ⟨u, huIi, v, hjneieIj, hvj1⟩
    -- Then v ∈ Iⱼ, ∀ j ≠ i
    replace hjneieIj : ∀ j, j ≠ i → v ∈ I j := by simpa using hjneieIj
    -- Set e = v.
    use v
    -- Goal: 1) φᵢ(e) = 1, 2) for all j ≠ i, φⱼ(e) = 0
    constructor
    · -- Goal: φᵢ(e) = 1
      -- φᵢ(u) = 0 since u ∈ Iᵢ
      -- φᵢ(e) = φᵢ(1 - u) = φᵢ(1) - φᵢ(u) = 1 - 0 = 1
      rw [← eq_sub_iff_add_eq'] at hvj1
      rw [hvj1, map_sub, map_one, sub_eq_self]
      exact eq_zero_iff_mem.mpr huIi
    · -- Goal: for all j ≠ i, φⱼ(e) = 0
      -- Fix j ≠ i.
      intro j hjnei
      -- Since j ≠ i, v ∈ Iⱼ. Thus, φⱼ(e) = 0.
      exact eq_zero_iff_mem.mpr (hjneieIj j hjnei)
  choose e he using key
  -- Let φ' : R →+* R ⧸ ⨅ᵢ Iᵢ (canonical quotient map)
  -- Set a = φ'(∑ᵢ fᵢ eᵢ) ∈ R ⧸ ⨅ᵢ Iᵢ
  use mk (⨅ i, I i) (∑ i, f i * e i)
  -- Goal: φ(a) = g
  -- Fix i ∈ ι.
  ext i
  -- Goal: [φ(a)]ᵢ = gᵢ
  rw [
    -- φᵢ : R         →+* R ⧸ Iᵢ
    -- φ' : R         →+* R ⧸ ⨅ᵢ Iᵢ
    -- φ :  R ⧸ ⨅ᵢ Iᵢ →+* Πᵢ R ⧸ Iᵢ
    -- [φ(a)]ᵢ = [φ(φ'(∑ᵢ fᵢ eᵢ))]ᵢ = φᵢ(∑ₖ fₖ eₖ)
    -- due to the definition of φ through lifting φ' (universal prop.)
    -- which combines sequence of morphisms φᵢ (Pi.ringHom)
    chineseMap_mk',
    -- Goal: φᵢ(∑ₖ fₖ eₖ) = gᵢ
    map_sum,
    -- Goal: ∑ₖ φᵢ(fₖ eₖ) = gᵢ
    -- Only one term in this sum is non-zero
    -- due to the "indicator".
    Fintype.sum_eq_single i,
    -- Goal: 1) φᵢ(fᵢ eᵢ) = gᵢ
    --       2) for all j ≠ i, φᵢ(fⱼ eⱼ) = 0
  ]
  · -- φᵢ(fᵢ eᵢ) = φᵢ(fᵢ) φᵢ(eᵢ) = gᵢ * 1 = gᵢ
    rw [RingHom.map_mul, hf i, (he i).left, mul_one]
  · -- Fix j ≠ i.
    intro j hjnei
    -- φᵢ(fⱼ eⱼ) = φᵢ(fⱼ) φᵢ(eⱼ) = φᵢ(fⱼ) * 0 = 0
    rw [RingHom.map_mul, (he j).right i hjnei.symm, mul_zero]

noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
    chineseMap f with }

end

-- Algebra is similar to Module but for Ring.
-- Algebra (resp. Module) is a semiring (resp. Abelian monoid)
-- equipped with scalar multiplication
-- with scalar coming from a comm semiring (resp. semiring).
-- Module:
--   Elements: Abelian monoid (e.g. vector ℝⁿ)
--   Scalar: semiring (e.g. matrix Mₙ(ℝ))
-- Algebra:
--   Elements: semiring (e.g. complex ℂ, polynomial ℝ[x], matrix Mₙ(ℝ))
--   Scalar: comm semiring (e.g. real ℝ)
-- Wording: A is an algebra over B.
-- Key difference: internal multiplication
--   Ex: in module, vectors cannot multiply each other
-- Note: same A and R can have different algebras based on the structure map

-- Scalar multiplication
-- Algebra A over commutative ring R
-- Scaling a ∈ A by r ∈ R is φ(r) * a where φ : R →+* A.
-- φ(r) * a = a * φ(r) (note that this is not generally true if not CommRing)
-- Ex: R = ℝ, A = M₂(ℝ), φ(r) = [[r, 0], [0, r]]

-- Algebra homomorphism between R-algebras A and B: A →ₐ[R] B
--   ring homomorphism: preserve addition, multiplication, identity
--   commute with scalar multiplication: f(r ⬝ a) = r ⬝ f(a)

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r + r') • a = r • a + r' • a :=
  add_smul r r' a

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r * r') • a = r • r' • a :=
  mul_smul r r' a

section Polynomials
open Polynomial

example {R : Type*} [CommRing R] : R[X] := X

-- C (constant): algebra structure map from R to R[X]
-- C(r : R) = r : R[X] (constant polynomial)
example {R : Type*} [CommRing R] (r : R) := X - C r

-- C is a ring homomorphism => C preserves power
example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X ^ 2 - C (r ^ 2) := by
  rw [C.map_pow]
  ring

example {R : Type*} [CommRing R] (r:R) : (C r).coeff 0 = r := by simp

-- type inference can guess X, no need type hint (_ : R[X])
example {R : Type*} [CommRing R] : (X ^ 2 + 2 * X + C 3 : R[X]).coeff 1 = 2 := by simp

-- degree (C 0) = ⊥ = -∞
-- degree : R[X] → WithBot ℕ = ℕ ∪ {-∞}
example : degree (C 0) = ⊥ := by simp
-- degree p * q = degree p + degree q holds always
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    degree (p * q) = degree p + degree q :=
  Polynomial.degree_mul

-- natDegree (C 0) = 0
example : natDegree (C 0) = 0 := by simp
-- natDegree p * q = natDegree p + natDegree q IF p * q ≠ 0
-- (e.g. (0 * x).natDegree = 0 ≠ x.natDegree = 0.natDegree + x.natDegree for x ≠ 0)
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  Polynomial.natDegree_mul hp hq

-- but...
-- ℕ is nicer to work with than ℕ ∪ {-∞}
-- (p ∘ q).natDegree = p.natDegree * q.natDegree even when p * q = 0
-- Ex: if q = 0 then
--     degree (p ∘ q) = 0 ≠ (degree p) * ⊥ if p ≠ 0 => problem
--     degree (p ∘ q) = 0 = 0 * ⊥ (by convention) if p = 0
--     meanwhile, ⊥ becomes 0 and everything works for natDegree
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    natDegree (comp p q) = natDegree p * natDegree q :=
  Polynomial.natDegree_comp

example {R : Type*} [CommRing R] (P: R[X]) (x : R) := P.eval x

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp

-- r is a root of the polynomial P if P(x) = 0
example {R : Type*} [CommRing R] (P : R[X]) (r : R) : IsRoot P r ↔ P.eval r = 0 := Iff.rfl

-- Polynomial.roots P returns a multiset of roots of P
-- If P = 0: empty multiset
-- If P ≠ 0: multiset with roots and their multiplicity

-- If R is a domain then number of roots ≤ degree
-- else number of roots can be greater
-- Ex: ℤ₆ is not a domain because 2 * 3 = 0 (mod 6) (zero has divisors)
--     x(x - 1) has 4 roots 0, 1, 3, and 4 but degree 2
-- Thus, Polynomial.roots requires R being a domain.

-- The multiset of roots of P(x) = x - r is {r}
example {R : Type*} [CommRing R] [IsDomain R] (r : R) : (X - C r).roots = {r} :=
  roots_X_sub_C r

-- The multiset of roots of P(x) = (x - r)ⁿ is {r, ..., r} (n r's)
example {R : Type*} [CommRing R] [IsDomain R] (r : R) (n : ℕ):
    ((X - C r) ^ n).roots = n • {r} :=
  by simp

-- Given an R-algebra A. Fix a ∈ A.
-- There is exactly one R-algebra morphism evalₐ: R[X] →ₐ[R] A that evalₐ(x) = a
-- because φₐ is completely determined by evalₐ(x):
--   evalₐ(c₀ + c₁ x + c₂ x² + ...) = φ(c₀) + φ(c₁) evalₐ(x) + φ(c₂) evalₐ(x)² + ...
--                                  = φ(c₀) + φ(c₁) a + φ(c₂) a² + ...
--   where φ is the structure map of A
-- evalₐ is called the "R-algebra morphism of evaluation at a"
-- and is of type `aeval R A a` in Lean.
-- Moreover, evalₐ(p) = `aeval a p` in Lean.
example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp

open Complex Polynomial

-- Roots of x^2 + 1 in ℂ is i and -i
example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {Complex.I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    have key : (C I * C I : ℂ[X]) = -1 := by simp [← C_mul]
    rw [C_neg]
    linear_combination key
  have p_ne_zero : (X - C I) * (X - C (-I)) ≠ 0 := by
    intro H
    apply_fun eval 0 at H
    simp [eval] at H
  simp only [factored, roots_mul p_ne_zero, roots_X_sub_C]
  rfl

-- D'Alembert-Gauss theorem: ``ℂ`` is algebraically closed.
-- (all polynomials with complex coeffs have at least one complex root)
example : IsAlgClosed ℂ := inferInstance

#check (Complex.ofRealHom : ℝ →+* ℂ)

-- Setup:
--   Ring homomorphism f : R →+* S
--   Element s ∈ S at which to evaluate
--   Polynomial p ∈ R[x] (i.e. coefficients ∈ R)
-- eval₂ f s p evaluates p at s using f to map coeffs from R to S
-- can also write p.eval₂ f s

-- Does not require S to be an R-algebra
-- When S is an R-algebra with structure map S:
--   p.eval₂ f s = aeval s p
example : (X ^ 2 + 1 : ℝ[X]).eval₂ Complex.ofRealHom Complex.I = 0 := by simp

open MvPolynomial

def circleEquation : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2 - 1

-- `![...]` denotes Fin n → X, `![0, 1]` means (0, 1)
example : MvPolynomial.eval ![0, 1] circleEquation = 0 := by simp [circleEquation]

end Polynomials
