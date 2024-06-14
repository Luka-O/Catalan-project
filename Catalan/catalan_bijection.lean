import Mathlib
import «Catalan».definitions
import «Catalan».commutativity_fin_sigma
open BigOperators
open Finset
open Finset.antidiagonal

/- Large task 2 -/
/- Construction of a recursive bijection for Catalan numbers. This allows us to count Catalan numbers. -/

/- First we construct an auxilary bijection between ∑ Fin * and ∑ × Fin -/
/- The bijection works in general for any functions f1, f2 where f2 is never zero. Its use is not limited to Catalan numbers. -/
/- Maps ∑ Fin * to ∑ × Fin -/
/- (i, r) → (i, (r / (f2 i), r % (f2 i))) -/
def sum_prod_Fin_of_sum_Fin_prod :
∀ (f1 : Fin n → ℕ) (f2 : Fin n → ℕ), (∀ i, f2 i > 0) → (Σ i : Fin n, Fin (f1 i * f2 i)) → (Σ i : Fin n, Fin (f1 i) × Fin (f2 i))
| f1, f2, h3, ⟨i, r⟩ =>
  let a := r.val / f2 i
  let b := r.val % f2 i
  have h1 : ↑r < f2 i * f1 i := by
    linarith [r.is_lt]
  have h2 : b < f2 i := by
    exact Nat.mod_lt r.val (h3 i)
  ⟨i, (⟨a, Nat.div_lt_of_lt_mul h1⟩, ⟨b, h2⟩)⟩

/- Maps ∑ × Fin to ∑ Fin * -/
/- (i, (a, b)) → (i, a * (f2 i) + b) -/
def sum_Fin_prod_of_sum_prod_Fin :
∀ (f1 : Fin n → ℕ) (f2 : Fin n → ℕ), (∀ i, f2 i > 0) →  (Σ i : Fin n, Fin (f1 i) × Fin (f2 i)) → (Σ i : Fin n, Fin (f1 i * f2 i))
| f1, f2, h3, ⟨i, ⟨⟨a_val, ha⟩, ⟨b_val, hb⟩⟩⟩ =>
  have h : a_val * f2 i + b_val < f1 i * f2 i := by  -- Proof that the result is still in set
    have : f1 i * f2 i = (f1 i - 1) * f2 i + f2 i := by
      calc
          f1 i * f2 i
              = (f1 i - 1 + 1) * f2 i := by
                rw [Nat.sub_add_cancel]
                linarith
            _ = (f1 i - 1) * f2 i + f2 i := by
                rw [Nat.add_mul]
                rw [Nat.one_mul]
    rw [this]  -- Separate part of (f1 i) : a * (f2 i) + b < (f1 i - 1) * f2 i + f2 i
    have h1 : (f1 i - 1) * f2 i + f2 i - 1 = (f1 i - 1) * f2 i + (f2 i - 1) := by
      rw [Nat.add_sub_assoc]
      linarith
    have h2 := Nat.add_le_add ((mul_le_mul_right (h3 i)).mpr (Nat.le_sub_one_of_lt ha)) (Nat.le_sub_one_of_lt hb)  -- Correct result with ≤
    apply Nat.lt_succ_of_le at h2
    rw [Nat.succ_eq_add_one, ←h1] at h2  -- Change ≤ to <
    have : (f1 i - 1) * f2 i + f2 i - 1 + 1 = (f1 i - 1) * f2 i + f2 i := by
      rw [Nat.add_sub_assoc]
      · rw [Nat.add_assoc]
        rw [Nat.sub_add_cancel]
        linarith
      · linarith
    rw [this] at h2
    exact h2
  ⟨i, ⟨a_val * f2 i + b_val, h⟩⟩

/- Maps ∑ × Fin back to ∑ × Fin -/
lemma sum_prod_Fin_to_sum_prod_Fin_inverse (f1 : Fin n → ℕ) (f2 : Fin n → ℕ) :
(hi2 : ∀ i, f2 i > 0) → ∀ x, (sum_prod_Fin_of_sum_Fin_prod f1 f2 hi2) (sum_Fin_prod_of_sum_prod_Fin f1 f2 hi2 x) = x := by
  intro h3 ⟨i, ⟨⟨a_val, ha⟩, ⟨b_val, hb⟩⟩⟩
  unfold sum_prod_Fin_of_sum_Fin_prod
  unfold sum_Fin_prod_of_sum_prod_Fin
  simp
  constructor
  · calc  -- Case for /
      (a_val * f2 i + b_val) / f2 i
          = a_val * f2 i / f2 i + b_val / f2 i := by
          rw [Nat.add_div]
          · simp
            ring_nf
            exact Nat.mod_lt b_val (h3 i)
          · exact (h3 i)
        _ = (a_val * f2 i) / f2 i := by
          simp
          rw [Nat.div_eq]
          simp
          intro
          exact hb
        _ = a_val := by
          rw [Nat.mul_div_left]
          exact (h3 i)
  · rw [Nat.add_mod]  -- Case for %
    simp
    apply Nat.mod_eq_of_lt
    exact hb

/- Maps ∑ Fin * to ∑ Fin * -/
lemma sum_Fin_prod_to_sum_Fin_prod_inverse (f1 : Fin n → ℕ) (f2 : Fin n → ℕ) :
(hi2 : ∀ i, f2 i > 0) → ∀ x, (sum_Fin_prod_of_sum_prod_Fin f1 f2 hi2) (sum_prod_Fin_of_sum_Fin_prod f1 f2 hi2 x) = x := by
  intro hi2 ⟨i, ⟨a, b⟩⟩
  unfold sum_prod_Fin_of_sum_Fin_prod
  unfold sum_Fin_prod_of_sum_prod_Fin
  simp
  rw [mul_comm]
  exact Nat.div_add_mod a (f2 i)

/- Theorem about bijection between sums of sets with multiplication -/
theorem bijection_sum_prod_Fin_sum_Fin_prod (f1 : Fin n → ℕ) (f2 : Fin n → ℕ) (hi2 : ∀ i, f2 i > 0) :
(Σ i : Fin n, Fin (f1 i * f2 i)) ≃ (Σ i : Fin n, Fin (f1 i) × Fin (f2 i)) := by
  refine Equiv.mk ?_ ?_ ?_ ?_
  · exact sum_prod_Fin_of_sum_Fin_prod f1 f2 hi2
  · exact sum_Fin_prod_of_sum_prod_Fin f1 f2 hi2
  · exact sum_Fin_prod_to_sum_Fin_prod_inverse f1 f2 hi2
  · exact sum_prod_Fin_to_sum_prod_Fin_inverse f1 f2 hi2


/- Functions for application of above bijections to Catalan numbers -/
def my_catalan_fin : (n : ℕ) → (i : Fin n) → ℕ
| n, i => my_catalan i * my_catalan (n - 1 - i)

def my_catalan_part1 : (n : ℕ) → (i : Fin n) → ℕ
| _, i => my_catalan i

def my_catalan_part2 : (n : ℕ) → (i : Fin n) → ℕ
| n, i => my_catalan (n - 1 - i)

/- Theorem stating that Catalan numbers are greater than 0 -/
theorem catalan_gt_0_all : (i : ℕ) → (my_catalan i > 0) := by
  intro i
  induction i with
  | zero =>  -- Base case
      unfold my_catalan
      linarith
  | succ i_pred hi =>  -- Induction
      unfold my_catalan
      simp
      rw [Fin.sum_univ_succ]
      simp
      constructor
      constructor
      · unfold my_catalan
        linarith
      · exact hi

/- Application of above theorem to function my_catalan_part2 -/
lemma catalan_gt_0 : (n : ℕ) → ∀ (i : Fin (Nat.succ n)), my_catalan_part2 (Nat.succ n) i > 0 := by
  intro n i
  unfold my_catalan_part2
  simp
  exact catalan_gt_0_all (n - i.val)

/- Theorem about bijection between Catalan numbers based on their recursive formula -/
theorem catalan_recursion_bijection : Fin (my_catalan (Nat.succ n)) ≃ Σ i : Fin (Nat.succ n), Fin (my_catalan i) × Fin (my_catalan (n - i)) := by
  have h1 : Fin (my_catalan (Nat.succ n)) ≃ Fin (∑ i : Fin (n + 1), my_catalan (i) * my_catalan (n - i)) := by
    rfl  -- Use recursive definition of Catalan numbers
  have h2 : Fin (∑ i : Fin (n + 1), my_catalan ↑i * my_catalan (n - ↑i)) ≃ Fin (∑ i : Fin (Nat.succ n), my_catalan_fin (Nat.succ n) i) := by
    unfold my_catalan_fin  -- Convert product of functions into a single function my_catalan_fin
    simp
    rfl
  have h3 : Fin (∑ i : Fin (Nat.succ n), my_catalan_fin (Nat.succ n) i) ≃ (i : Fin (Nat.succ n)) × Fin (my_catalan_fin (Nat.succ n) i) :=
    bijection_Fin_sum_sum_Fin (my_catalan_fin (Nat.succ n))  -- Use bijection_Fin_sum_sum_Fin to swap ∑ and Fin
  have h4 : (i : Fin (Nat.succ n)) × Fin (my_catalan_fin (Nat.succ n) i) ≃ (i : Fin (Nat.succ n)) × Fin (my_catalan (i) * my_catalan (n - i)) := by
    unfold my_catalan_fin  -- Convert function back to product of my_catalan functions
    simp
    rfl
  have h5 : (i : Fin (Nat.succ n)) × Fin (my_catalan ↑i * my_catalan (n - ↑i)) ≃ (i : Fin (Nat.succ n)) ×
    (Fin (my_catalan_part1 (Nat.succ n) i * my_catalan_part2 (Nat.succ n) i)) := by
    unfold my_catalan_part1  --Convert my_catalan functions to functions that map from Fin
    unfold my_catalan_part2
    simp
    rfl
  have h6 : (i : Fin (Nat.succ n)) × (Fin (my_catalan_part1 (Nat.succ n) i * my_catalan_part2 (Nat.succ n) i)) ≃ (i : Fin (Nat.succ n)) × Fin (my_catalan_part1 (Nat.succ n) i) ×
    Fin (my_catalan_part2 (Nat.succ n) i) :=
    bijection_sum_prod_Fin_sum_Fin_prod (my_catalan_part1 (Nat.succ n)) (my_catalan_part2 (Nat.succ n)) (catalan_gt_0 n)  -- use bijection_sum_prod_Fin_sum_Fin_prod to swap Fin * for × Fin
  have h7 : (i : Fin (Nat.succ n)) × Fin (my_catalan_part1 (Nat.succ n) i) × Fin (my_catalan_part2 (Nat.succ n) i) ≃ (i : Fin (Nat.succ n)) × Fin (my_catalan (i)) × Fin (my_catalan (n - i)) := by
    unfold my_catalan_part1  -- Convert functions back to my_catalan functions
    unfold my_catalan_part2
    simp
    rfl
  apply Equiv.trans h1  -- Use transitivity of bijectivity
  apply Equiv.trans h2
  apply Equiv.trans h3
  apply Equiv.trans h4
  apply Equiv.trans h5
  apply Equiv.trans h6
  apply Equiv.trans h7
  rfl
