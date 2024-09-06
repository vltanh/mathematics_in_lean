import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · show x ⊓ y ≤ y ⊓ x
    apply le_inf
    · show x ⊓ y ≤ y
      apply inf_le_right
    · show x ⊓ y ≤ x
      apply inf_le_left
  · show y ⊓ x ≤ x ⊓ y
    apply le_inf
    · show y ⊓ x ≤ x
      apply inf_le_right
    · show y ⊓ x ≤ y
      apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
    apply le_inf
    · show x ⊓ y ⊓ z ≤ x
      apply le_trans
      · show x ⊓ y ⊓ z ≤ x ⊓ y
        apply inf_le_left
      · show x ⊓ y ≤ x
        apply inf_le_left
    · show x ⊓ y ⊓ z ≤ y ⊓ z
      apply le_inf
      · show x ⊓ y ⊓ z ≤ y
        apply le_trans
        · show x ⊓ y ⊓ z ≤ x ⊓ y
          apply inf_le_left
        · show x ⊓ y ≤ y
          apply inf_le_right
      · show x ⊓ y ⊓ z ≤ z
        apply inf_le_right
  · show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    apply le_inf
    · show x ⊓ (y ⊓ z) ≤ x ⊓ y
      apply le_inf
      · show x ⊓ (y ⊓ z) ≤ x
        apply inf_le_left
      · show x ⊓ (y ⊓ z) ≤ y
        apply le_trans
        · show x ⊓ (y ⊓ z) ≤ y ⊓ z
          apply inf_le_right
        · show y ⊓ z ≤ y
          apply inf_le_left
    · show x ⊓ (y ⊓ z) ≤ z
      apply le_trans
      · show x ⊓ (y ⊓ z) ≤ y ⊓ z
        apply inf_le_right
      · show y ⊓ z ≤ z
        apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · show x ⊔ y ≤ y ⊔ x
    apply sup_le
    · show x ≤ y ⊔ x
      apply le_sup_right
    · show y ≤ y ⊔ x
      apply le_sup_left
  · show y ⊔ x ≤ x ⊔ y
    apply sup_le
    · show y ≤ x ⊔ y
      apply le_sup_right
    · show x ≤ x ⊔ y
      apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    · show x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le
      · show x ≤ x ⊔ (y ⊔ z)
        apply le_sup_left
      · show y ≤ x ⊔ (y ⊔ z)
        apply le_trans
        · show y ≤ y ⊔ z
          apply le_sup_left
        · show y ⊔ z ≤ x ⊔ (y ⊔ z)
          apply le_sup_right
    · show z ≤ x ⊔ (y ⊔ z)
      apply le_trans
      · show z ≤ y ⊔ z
        apply le_sup_right
      · show y ⊔ z ≤ x ⊔ (y ⊔ z)
        apply le_sup_right
  · show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z
    apply sup_le
    · show x ≤ x ⊔ y ⊔ z
      apply le_trans
      · show x ≤ x ⊔ y
        apply le_sup_left
      · show x ⊔ y ≤ x ⊔ y ⊔ z
        apply le_sup_left
    · show y ⊔ z ≤ x ⊔ y ⊔ z
      apply sup_le
      · show y ≤ x ⊔ y ⊔ z
        apply le_trans
        · show y ≤ x ⊔ y
          apply le_sup_right
        · show x ⊔ y ≤ x ⊔ y ⊔ z
          apply le_sup_left
      · show z ≤ x ⊔ y ⊔ z
        apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    · show x ≤ x
      apply le_refl
    · show x ≤ x ⊔ y
      apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · show x ⊔ x ⊓ y ≤ x
    apply sup_le
    · show x ≤ x
      apply le_refl
    · show x ⊓ y ≤ x
      apply inf_le_left
  · show x ≤ x ⊔ x ⊓ y
    apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [
    h,
    inf_comm (a ⊔ b),
    inf_sup_self,
    inf_comm (a ⊔ b),
    h,
    ← sup_assoc,
    inf_comm c a,
    sup_inf_self,
    inf_comm
  ]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [
    h,
    sup_comm (a ⊓ b),
    sup_inf_self,
    sup_comm (a ⊓ b),
    h,
    ← inf_assoc,
    sup_comm c a,
    inf_sup_self,
    sup_comm
  ]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [sub_eq_add_neg]
  rw [add_comm]
  rw [← neg_add_cancel a]
  apply add_le_add_left h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a]
  rw [← sub_add_cancel b a]
  rw [add_comm (b - a)]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ b - a := by
    rw [sub_eq_add_neg]
    rw [add_comm]
    rw [← neg_add_cancel a]
    apply add_le_add_left h

  have h2 := mul_nonneg h1 h'
  rw [sub_mul] at h2

  rw [← add_zero (a * c)]
  rw [← sub_add_cancel (b * c) (a * c)]
  rw [add_comm (b * c - a * c)]
  apply add_le_add_left h2

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h := dist_triangle x y x
  rw [dist_self, dist_comm y x] at h
  linarith

end
