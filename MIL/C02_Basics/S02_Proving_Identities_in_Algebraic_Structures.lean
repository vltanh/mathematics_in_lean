import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, MyRing.add_right_neg, MyRing.add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← MyRing.neg_add_cancel_left a b, h, MyRing.neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← MyRing.add_neg_cancel_right a b, h, MyRing.add_neg_cancel_right]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, zero_add, MyRing.add_zero]
  rw [MyRing.add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← MyRing.neg_add_cancel_left a b, h, MyRing.add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← MyRing.add_neg_cancel_right a b, h, zero_add]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply MyRing.neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, MyRing.add_right_neg]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

-- theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
--   rw [← one_mul (a * a⁻¹)]
--   nth_rw 1 [← inv_mul_cancel (a * a⁻¹)]
--   rw [mul_assoc]
--   rw [mul_assoc a]
--   rw [← mul_assoc (a⁻¹)]
--   rw [inv_mul_cancel]
--   rw [one_mul]
--   rw [inv_mul_cancel]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 :=
  calc
    a * a⁻¹ = 1 * (a * a⁻¹) := by rw [one_mul]
    _ = (a * a⁻¹)⁻¹ * (a * a⁻¹) * (a * a⁻¹) := by rw [inv_mul_cancel]
    _ = (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) := by rw [mul_assoc]
    _ = (a * a⁻¹)⁻¹ * (a * (a⁻¹ * (a * a⁻¹))) := by rw [mul_assoc]
    _ = (a * a⁻¹)⁻¹ * (a * ((a⁻¹ * a) * a⁻¹)) := by rw [mul_assoc]
    _ = (a * a⁻¹)⁻¹ * (a * (1 * a⁻¹)) := by rw [inv_mul_cancel]
    _ = (a * a⁻¹)⁻¹ * (a * a⁻¹) := by rw [one_mul]
    _ = 1 := by rw [inv_mul_cancel]

-- theorem mul_one (a : G) : a * 1 = a := by
--   rw [← inv_mul_cancel a]
--   rw [← mul_assoc]
--   rw [MyGroup.mul_inv_cancel]
--   rw [one_mul]

theorem mul_one (a : G) : a * 1 = a :=
  calc
    a * 1 = a * (a⁻¹ * a) := by rw [inv_mul_cancel]
    _ = (a * a⁻¹) * a := by rw [mul_assoc]
    _ = 1 * a := by rw [MyGroup.mul_inv_cancel]
    _ = a := by rw [one_mul]

-- theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
--   rw [← one_mul (a * b)⁻¹]
--   rw [← inv_mul_cancel b]
--   nth_rw 2 [← one_mul b]
--   rw [← inv_mul_cancel a]
--   rw [mul_assoc a⁻¹]
--   rw [← mul_assoc b⁻¹]
--   rw [mul_assoc]
--   rw [MyGroup.mul_inv_cancel]
--   rw [MyGroup.mul_one]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  calc
    (a * b)⁻¹ = 1 * (a * b)⁻¹ := by rw [one_mul]
    _ = b⁻¹ * b * (a * b)⁻¹ := by rw [inv_mul_cancel]
    _ = b⁻¹ * (1 * b) * (a * b)⁻¹ := by rw [one_mul]
    _ = b⁻¹ * (a⁻¹ * a * b) * (a * b)⁻¹ := by rw [inv_mul_cancel]
    _ = b⁻¹ * (a⁻¹ * (a * b)) * (a * b)⁻¹ := by rw [mul_assoc (a⁻¹)]
    _ = b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹ := by rw [← mul_assoc (b⁻¹)]
    _ = b⁻¹ * a⁻¹ * (a * b * (a * b)⁻¹) := by rw [mul_assoc]
    _ = b⁻¹ * a⁻¹ * 1 := by rw [MyGroup.mul_inv_cancel]
    _ = b⁻¹ * a⁻¹ := by rw [MyGroup.mul_one]

end MyGroup

end
