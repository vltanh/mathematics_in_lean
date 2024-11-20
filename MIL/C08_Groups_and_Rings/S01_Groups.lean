import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x

-- You can prove identity preservation by operation preservation
-- and group properties regarding inverse
example {G H : Type*} [Group G] [Group H] (f : G → H)
  (h_mul : ∀ x y, f (x * y) = f x * f y) : G →* H :=
{
    map_mul' := h_mul,
    map_one' := calc
      f 1 = f 1 * f 1 * (f 1)⁻¹ := by group
      _ = f (1 * 1) * (f 1)⁻¹ := by rw [h_mul]
      _ = f 1 * (f 1)⁻¹ := by group
      _ = 1 := by group
}

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm

noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h

example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx

example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    exact Rat.intCast_add n m
  zero_mem' := by
    use 0
    rfl
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    rfl

example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance

-- H is a term of type Subgroup G
-- Lean automatically coerces H to the subtype {x : G // x ∈ H}
example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]

example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial

example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1, H.one_mem, by group
  inv_mem' := by
    dsimp
    rintro x_inv ⟨h, hH, hxinvconj⟩
    use h⁻¹
    constructor
    · apply H.inv_mem hH
    · rw [hxinvconj]
      group
  mul_mem' := by
    dsimp
    intro a b ⟨ha, haH, ahaconj⟩ ⟨hb, hbH, bhbconj⟩
    use (ha * hb)
    constructor
    · apply H.mul_mem haH hbH
    · rw [ahaconj, bhbconj]
      group

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  intro x hxcomapS
  exact hST hxcomapS

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  intro x ⟨y, hyS, hφyx⟩
  use y
  exact ⟨hST hyS, hφyx⟩

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  ext x
  rw [mem_comap, mem_comap, mem_comap]
  rw [MonoidHom.comp_apply]

-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  -- (prety weird to write S.map φ, should just write map φ S)
  ext y
  constructor
  · rintro ⟨x, hxS, hψφxy⟩
    use φ x
    constructor
    · use x
    · exact hψφxy
  · rintro ⟨t, ⟨x, hxS, rfl⟩, hφty⟩
    use x
    exact ⟨hxS, hφty⟩

end exercises

open scoped Classical

-- More readable
-- card G' | card G because card G = card G' * G'.index
-- from G'.index_mul_card
example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G := by
  rw [dvd_def]
  use G'.index
  rw [mul_comm]
  rw [G'.index_mul_card]

example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
  ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

open Subgroup

example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd

-- A subgroup H is equal to the bottom subgroup ⊥
-- iff its cardinality is 1
lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
    H = ⊥ ↔ Nat.card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
  constructor
  · intro hxHx1
    use 1
    exact ⟨H.one_mem, hxHx1⟩
  · intro ⟨x, _, haHax⟩
    intro x' hx'H
    rw [haHax x' hx'H, haHax 1 H.one_mem]

#check card_dvd_of_le

-- If two subgroups have cardinalities that are coprimes
-- then their intersection (infimum) is the bottom subgroup ⊥
-- Key idea 1: show that card (H ⊓ K) = 1
-- Key idea 2: if A ≤ B then card A | card B for subgroups A, B
lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
  rw [Subgroup.eq_bot_iff_card]
  have : H ⊓ K ≤ H := inf_le_left
  have hHinfKdvdH := card_dvd_of_le this
  have : H ⊓ K ≤ K := inf_le_right
  have hHinfKdvdK := card_dvd_of_le this
  exact Nat.eq_one_of_dvd_coprimes h hHinfKdvdH hHinfKdvdK

open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle

#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]

section FreeGroup

inductive S | a | b | c

open S

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹

def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]


def myGroup := PresentedGroup {.of () ^ 3} deriving Group

def myMap : Unit → Perm (Fin 5)
| () => c[1, 2, 3]

lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp
  decide

def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap

end FreeGroup

noncomputable section GroupActions

example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm

example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
    g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
  (add_vadd g g' x).symm

open MulAction

example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X

def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G

example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω)) :=
  MulAction.selfEquivSigmaOrbits G X

example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup

variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  ext x
  constructor
  · intro hxconj1H
    rcases hxconj1H with ⟨x', hx'H, rfl⟩
    convert hx'H
    group
  · intro hxH
    rw [conjugate, mem_mk, Set.mem_setOf]
    use x, hxH
    group

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := conjugate_one
  mul_smul := by
    intro x y H
    ext z
    constructor
    · rintro ⟨h, hhH, rfl⟩
      use y * h * y⁻¹
      constructor
      · use h
      · group
    · rintro ⟨h, ⟨t, htH, rfl⟩, rfl⟩
      use t, htH
      group

end GroupActions

noncomputable section QuotientGroup

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H

example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h

example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ

example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
  QuotientGroup.map N N' φ h

example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
    [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h

section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
  have : 0 < Nat.card {x // x ∈ H} := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left this
  convert h'
  rw [← Subgroup.index_eq_card, mul_comm, Subgroup.index_mul_card]

variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

def iso₁ : K ≃* G ⧸ H := by
  apply MulEquiv.ofBijective ((QuotientGroup.mk' H).restrict K)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff]
    rw [(QuotientGroup.mk' H).ker_restrict K]
    apply subgroupOf_eq_bot.mpr
    rw [QuotientGroup.ker_mk']
    exact h
  · rw [aux_card_eq h']

def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
  apply MulEquiv.ofBijective ((QuotientGroup.mk' K).prod (QuotientGroup.mk' H))
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff]
    rw [ker_prod]
    repeat rw [QuotientGroup.ker_mk']
    exact h.symm.eq_bot
  · rw [Nat.card_prod]
    rw [aux_card_eq h']
    rw [← Subgroup.index_eq_card]
    rw [Subgroup.index_mul_card]

#check MulEquiv.prodCongr

def finalIso : G ≃* H × K := by
  have hK : K ≃* (G ⧸ H) := iso₁ h h'
  have hH : H ≃* (G ⧸ K) := by
    apply iso₁ h.symm
    rw [h', mul_comm]
  have hHK : H × K ≃* (G ⧸ K) × (G ⧸ H) := MulEquiv.prodCongr hH hK
  have hG : G ≃* (G ⧸ K) × (G ⧸ H) := iso₂ h h'
  exact hG.trans hHK.symm
