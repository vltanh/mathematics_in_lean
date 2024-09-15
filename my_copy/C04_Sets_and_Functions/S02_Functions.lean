import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro hfsv _ hs
    exact hfsv (mem_image_of_mem _ hs)
  · intro hsfinvv _ hyfs
    rcases hyfs with ⟨x, hxs, hfxy⟩
    rw [← hfxy]
    apply hsfinvv hxs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, hys, hfyfx⟩
  rw [← (h hfyfx)]
  exact hys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, hxfinvu, hfxy⟩
  rw [← hfxy]
  exact hxfinvu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hyu
  rcases (h y) with ⟨x, hfxy⟩
  rw [← hfxy] at hyu
  exact ⟨x, hyu, hfxy⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, hxs, hfxy⟩
  use x
  exact ⟨h hxs, hfxy⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hxfinvu
  exact h hxfinvu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro _ ⟨x, hxst, rfl⟩
  exact ⟨mem_image_of_mem _ hxst.left, mem_image_of_mem _ hxst.right⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x, hxs, hfxy⟩, ⟨x', hx't, hfx'y⟩⟩
  rw [← hfx'y] at hfxy
  rw [← h hfxy] at hx't
  use x
  constructor
  · exact ⟨hxs, hx't⟩
  · rw [← hfx'y]
    exact hfxy

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, hxs, hfxy⟩, hynft⟩
  use x
  constructor
  · constructor
    · exact hxs
    · intro hxt
      apply hynft
      use x
  · exact hfxy

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  exact fun _ => id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  apply Subset.antisymm
  · rintro y ⟨⟨x, hxs, rfl⟩, hyv⟩
    use x, ⟨hxs, hyv⟩
  · rintro y ⟨x, ⟨hxs, hxfinvv⟩, rfl⟩
    exact ⟨mem_image_of_mem f hxs, hxfinvv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨hxs, hxfinvu⟩, rfl⟩
  exact ⟨mem_image_of_mem _ hxs, hxfinvu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨hxs, hfinvu⟩
  exact ⟨mem_image_of_mem _ hxs, hfinvu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (hxs | hxfinvu)
  · exact Or.inl (mem_image_of_mem _ hxs)
  · exact Or.inr hxfinvu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  apply Subset.antisymm
  · rintro y ⟨x, hxuAi, rfl⟩
    rw [mem_iUnion] at *
    rcases hxuAi with ⟨i, hAi⟩
    use i
    exact mem_image_of_mem f hAi
  · rintro y hyufAi
    rw [mem_iUnion] at hyufAi
    rcases hyufAi with ⟨i, ⟨x, hxAi, rfl⟩⟩
    use x
    constructor
    · rw [mem_iUnion]
      use i
    · rfl

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y ⟨x, hxiAi, rfl⟩
  rw [mem_iInter] at *
  intro i
  exact mem_image_of_mem _ (hxiAi i)

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro y hyifAi
  rw [mem_iInter] at hyifAi
  rcases (hyifAi i) with ⟨x, hxAi, rfl⟩
  use x
  constructor
  · rw [mem_iInter]
    intro j
    rcases (hyifAi j) with ⟨x', hx'Aj, hfx'fx⟩
    have hx'x := injf hfx'fx
    rw [hx'x] at hx'Aj
    exact hx'Aj
  · rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  apply Subset.antisymm
  · rintro x hxfinvuBi
    have hfxuBi : f x ∈ ⋃ i, B i := hxfinvuBi
    rw [mem_iUnion] at *
    rcases hfxuBi with ⟨i, hfxBi⟩
    use i
    exact hfxBi
  · rintro x hxufinvBi
    show f x ∈ ⋃ i, B i
    rw [mem_iUnion] at *
    rcases hxufinvBi with ⟨i, hxfinvBi⟩
    use i
    exact hxfinvBi

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  apply Subset.antisymm
  · rintro x hxfinviBi
    have hfxiBi : f x ∈ ⋂ i, B i := hxfinviBi
    rw [mem_iInter] at *
    intro i
    exact hfxiBi i
  · rintro x hxifinvBi
    show f x ∈ ⋂ i, B i
    rw [mem_iInter] at *
    intro i
    exact hxifinvBi i

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x1 x1pos x2 x2pos hsqrtx1sqrtx2
  calc
    x1 = (sqrt x1) ^ 2 := by rw [sq_sqrt x1pos]
    _ = (sqrt x2) ^ 2 := by rw [hsqrtx1sqrtx2]
    _ = x2 := by rw [sq_sqrt x2pos]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x1 x1pos x2 x2pos hsqx1sqx2
  dsimp at hsqx1sqx2
  calc
    x1 = sqrt (x1 ^ 2) := by rw [sqrt_sq x1pos]
    _ = sqrt (x2 ^ 2) := by rw [hsqx1sqx2]
    _ = x2 := by rw [sqrt_sq x2pos]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  apply Subset.antisymm
  · rintro y ⟨x, hxpos, rfl⟩
    exact sqrt_nonneg x
  · rintro y hypos
    use y ^ 2
    exact ⟨sq_nonneg y, sqrt_sq hypos⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  apply Subset.antisymm
  · intro y ⟨x, hsqxy⟩
    rw [← hsqxy]
    exact sq_nonneg x
  · intro y hypos
    use sqrt y
    dsimp
    rw [sq_sqrt hypos]

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro hinjf
    intro x
    apply hinjf
    apply inverse_spec (f x)
    use x
  · intro hlinvinvff
    intro x1 x2 hfx1fx2
    calc
      x1 = inverse f (f x1) := by rw [hlinvinvff]
      _ = inverse f (f x2) := by rw [hfx1fx2]
      _ = x2 := by rw [hlinvinvff]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro hsurf
    intro y
    exact inverse_spec y (hsurf y)
  · intro hrinvinvff
    intro y
    use inverse f y
    exact hrinvinvff y

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

-- COMMENTS: TODO: improve this
end
