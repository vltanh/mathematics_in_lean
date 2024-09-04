import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    apply le_max_right
    apply le_max_left
  · show max b a ≤ max a b
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · show min (min a b) c ≤ a
      apply le_trans
      · show min (min a b) c ≤ min a b
        apply min_le_left
      · show min a b ≤ a
        apply min_le_left
    · show min (min a b) c ≤ min b c
      apply le_min
      · show min (min a b) c ≤ b
        apply le_trans
        · show min (min a b) c ≤ min a b
          apply min_le_left
        · show min a b ≤ b
          apply min_le_right
      · show min (min a b) c ≤ c
        apply min_le_right
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · show min a (min b c) ≤ min a b
      apply le_min
      · show min a (min b c) ≤ a
        apply min_le_left
      · show min a (min b c) ≤ b
        apply le_trans
        · show min a (min b c) ≤ min b c
          apply min_le_right
        · show min b c ≤ b
          apply min_le_left
    · show min a (min b c) ≤ c
      apply le_trans
      · show min a (min b c) ≤ min b c
        apply min_le_right
      · show min b c ≤ c
        apply min_le_right

#check add_neg_cancel_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · show min a b + c ≤ a + c
    apply add_le_add_right
    apply min_le_left
  · show min a b + c ≤ b + c
    apply add_le_add_right
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · show min a b + c ≤ min (a + c) (b + c)
    apply aux
  · show min (a + c) (b + c) ≤ min a b + c
    calc
      min (a + c) (b + c) = min (a + c) (b + c) + -c + c := by linarith
      _ ≤ min (a + c + -c) (b + c + -c) + c := by
        apply add_le_add_right
        apply aux
      _ = min a b + c := by repeat rw [add_neg_cancel_right]

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| :=
  calc
    |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right
      apply abs_add
    _ ≤ |a - b| := by rw [add_sub_cancel_right]
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · show x ∣ y * (x * z) + x ^ 2
    apply dvd_add
    · show x ∣ y * (x * z)
      apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    · show x ∣ x ^ 2
      apply dvd_mul_left
  · show x ∣ w ^ 2
    apply dvd_trans
    · show x ∣ w
      apply h
    · show w ∣ w ^ 2
      rw [pow_two]
      apply dvd_mul_right
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  · show Nat.gcd m n ∣ Nat.gcd n m
    apply Nat.dvd_gcd
    · show Nat.gcd m n ∣ n
      apply Nat.gcd_dvd_right
    · show Nat.gcd m n ∣ m
      apply Nat.gcd_dvd_left
  · show Nat.gcd n m ∣ Nat.gcd m n
    apply Nat.dvd_gcd
    · show Nat.gcd n m ∣ m
      apply Nat.gcd_dvd_right
    · show Nat.gcd n m ∣ n
      apply Nat.gcd_dvd_left
end
