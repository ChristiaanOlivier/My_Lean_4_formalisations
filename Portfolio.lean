import Mathlib.Basic.Logic.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.CategoryTheory.Category.Basic

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Defs


import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Complex.Exponential

/-

                Formalisation of proof that Zhegalkin polynomials form a preorder.

I realise that this polynomial ring is slightly more general than the usual Zhegalkin polynomials,
since I didn't quotient out X^2-X for every variable X, but the polynomials evaluate to the same
Boolean values either way.

-/

section Zhegalkin

variable {n : ℕ}

open MvPolynomial

abbrev zhegalkinPoly (n : ℕ) : Type := MvPolynomial (Fin n) (ZMod 2)

def zhegalkinEval (n : ℕ) (x : Fin n → ZMod 2) (y : zhegalkinPoly n) : ZMod 2 :=
MvPolynomial.eval x y

def implies {n : ℕ} (p q : zhegalkinPoly n) : Prop :=
  ∀ a : Fin n → ZMod 2, zhegalkinEval n a p = 1 → zhegalkinEval n a q = 1

instance {n : ℕ} : Preorder (zhegalkinPoly n) where
  le := implies
  le_refl := by
    intro p a hp
    exact hp
  le_trans := by
    intro p q r hpq hqr a hp
    exact hqr a (hpq a hp)

end Zhegalkin


/-

                Showing that Lean types form a category

-/

section

-- Our objects are types
variable {α β γ δ : Type}

-- Our morphisms are functions
variable {f : α → β} {g : β → γ} {h : γ → δ}

-- We define the identity morphism as the identity function
def id_m : α → α := id

-- Composition is defined as follows:
def comp_m (f : α → β) (g : β → γ) : α → γ := fun x => g (f x)


theorem left_unit_law : f = comp_m id_m f := by
  rfl

theorem right_unit_law : comp_m f id_m = f := by
  rfl

theorem associative_law : comp_m f (comp_m g h) = comp_m (comp_m f g) h := by
  rfl

open CategoryTheory

instance leanCat : Category (Type) where
  Hom α β := α → β
  id _ := id_m
  comp f g := comp_m f g
  id_comp _ := left_unit_law
  comp_id _ := right_unit_law
  assoc _ _ _ := associative_law

end

/-

                Formalisations of logic

-/

-- Tactic-style proof that LEM can not be proven false.
theorem not_not_LEM (p : Prop) : ¬¬(p ∨¬p) := by
  intro h
  have np : ¬p := fun x => h (Or.inl x)
  exact h (Or.inr np)

-- Term-style proof that a proposition can not be equivalent to its negation.
lemma not_p_iff_np : ¬(p ↔ ¬p) :=
  fun h => (fun n : p => h.mp n n) (h.mpr (fun m : p => h.mp m m))

-- Applying not_p_iff_np to formalise the Barber paradox.
section barber_paradox

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

theorem barber_paradox (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  not_p_iff_np (h barber)
end barber_paradox

-- No axioms used
#print axioms not_not_LEM
#print axioms not_p_iff_np
#print axioms barber_paradox



/-

                Some formalisations in group theory

-/

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

/- Using the above axioms, we can prove the following three theorems:

mul_inv_cancel'
mul_one'
mul_inv_rev'

-/

theorem mul_inv_cancel' (a : G) : a * a⁻¹ = 1 := by
  let b := a⁻¹
  calc a * b = 1 * (a * b)        := (one_mul _).symm
    _ = (b⁻¹ * b) * (a * b)       := by rw [inv_mul_cancel b]
    _ = b⁻¹ * (b * (a * b))       := mul_assoc _ _ _
    _ = b⁻¹ * ((b * a) * b)       := by rw [← mul_assoc b a b]
    _ = b⁻¹ * ((a⁻¹ * a) * a⁻¹)   := rfl -- since b := a⁻¹
    _ = a⁻¹⁻¹ * (1 * a⁻¹)         := by rw [inv_mul_cancel a]
    _ = a⁻¹⁻¹ * a⁻¹               := by rw [one_mul]
    _ = 1                         := inv_mul_cancel a⁻¹

lemma helper₁ (a : G) : ( a * a⁻¹ ) * a = a * 1 := by
  have h₁ : ( a * a⁻¹ ) * a = a * ( a⁻¹ * a ) := mul_assoc a a⁻¹ a
  have h₂ : a * ( a⁻¹ * a ) = a * 1 := by
    rw [inv_mul_cancel]
  exact h₁.trans h₂

theorem mul_one' (a : G) : a * 1 = a  := by
  calc a * 1 = ( a * a⁻¹ ) * a        := (helper₁ a).symm
    _ = 1 * a                         := by rw [mul_inv_cancel']
    _ = a                             := one_mul _

lemma helper₂ (a b : G) : a * (b* (a * b)⁻¹) = 1    := by
  calc a * (b * (a * b)⁻¹) = (a * b) * (a * b)⁻¹    := (mul_assoc _ _ _).symm
  _ = 1                                             := mul_inv_cancel' _

theorem mul_inv_rev' (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h₁ : b⁻¹ * a⁻¹ = (a * b)⁻¹                      := by
    calc b⁻¹ * a⁻¹ = (b⁻¹ * a⁻¹) * 1                      := (mul_one' (b⁻¹ * a⁻¹)).symm
    _ = (b⁻¹ * a⁻¹) * (a * (b* (a * b)⁻¹))                := by rw [helper₂]
    _ = (b⁻¹ * a⁻¹ * a) * (b* (a * b)⁻¹)                  := (mul_assoc _ _ _).symm
    _ = (b⁻¹ * (a⁻¹ * a)) * (b* (a * b)⁻¹)                := by rw [mul_assoc b⁻¹]
    _ = (b⁻¹ * 1) * (b* (a * b)⁻¹)                        := by rw [inv_mul_cancel a]
    _ = b⁻¹ * (b* (a * b)⁻¹)                              := by rw [mul_one']
    _ = b⁻¹ * b * (a * b)⁻¹                               := (mul_assoc _ _ _).symm
    _ = 1 * (a * b)⁻¹                                     := by rw [inv_mul_cancel b]
    _ = (a * b)⁻¹                                         := one_mul _
  exact h₁.symm
