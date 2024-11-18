import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem

-- Define a Subgroup₁ structure
@[ext]
structure Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier

-- Endow it with a SetLike instance
instance [Group G] : SetLike (Subgroup₁ G) G where
  coe := fun H ↦ H.toSubmonoid₁.carrier
  coe_injective' _ _ := Subgroup₁.ext
--               a SubmonoidClass₁ instance
instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem := fun H ↦ H.toSubmonoid₁.mul_mem
  one_mem := fun H ↦ H.toSubmonoid₁.one_mem

-- Put a Group instance on the subtype associated to a Subgroup₁
instance [Group G] (H : Subgroup₁ G) : Group H :=
{ SubMonoid₁Monoid H.toSubmonoid₁ with
  inv := fun x ↦ ⟨x⁻¹, H.inv_mem x.property⟩
  inv_mul_cancel := fun x ↦ SetCoe.ext (inv_mul_cancel (x : G)) }

-- Define a SubgroupClass₁ class
class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G]
    extends SubmonoidClass₁ S G  : Prop where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G where
  inv_mem := Subgroup₁.inv_mem

-- Inf is deprecated, replaced by Min
instance [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      rintro x y z ⟨w, hwN, t, htN, h⟩ ⟨w', hw'N, t', ht'N, h'⟩
      use w * w'
      constructor
      · exact N.mul_mem hwN hw'N
      · use t * t'
        constructor
        · exact N.mul_mem htN ht'N
        · rw [← mul_assoc, mul_comm t t', ← mul_assoc]
          rw [h, ← h']
          rw [mul_assoc, mul_comm t w', ← mul_assoc]
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      rintro a b ⟨w, hwN, z, hzN, h⟩ c d ⟨w', hw'N, z', hz'N, h'⟩
      dsimp
      use w * w'
      constructor
      · exact N.mul_mem hwN hw'N
      · use z * z'
        constructor
        · exact N.mul_mem hzN hz'N
        · calc
            a * c * (w * w') = a * (c * (w * w')) := by rw [mul_assoc]
            _ = a * (c * w * w') := by rw [mul_assoc]
            _ = a * (w * c * w') := by rw [mul_comm c w]
            _ = a * (w * (c * w')) := by rw [mul_assoc]
            _ = a * w * (c * w') := by rw [mul_assoc]
            _ = b * z * (d * z') := by rw [h, h']
            _ = b * (z * (d * z')) := by rw [mul_assoc]
            _ = b * (z * d * z') := by rw [mul_assoc]
            _ = b * (d * z * z') := by rw [mul_comm z d]
            _ = b * (d * (z * z')) := by rw [mul_assoc]
            _ = b * d * (z * z') := by rw [mul_assoc]
        )
  mul_assoc := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
      apply Quotient.sound
      dsimp
      rw [mul_assoc]
      apply @Setoid.refl M N.Setoid
  one := QuotientMonoid.mk N 1
  one_mul := by
      rintro ⟨a⟩
      apply Quotient.sound
      dsimp
      rw [one_mul]
      apply @Setoid.refl M N.Setoid
  mul_one := by
      rintro ⟨a⟩
      apply Quotient.sound
      dsimp
      rw [mul_one]
      apply @Setoid.refl M N.Setoid
