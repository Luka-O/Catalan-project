import Mathlib
open BigOperators
open Finset
open Finset.antidiagonal

/- Large task 1 -/
/- Proof of commutativity of Fin and ∑ with construction of a bijection -/

/- Remove first element from function -/
def next_element : (Fin (Nat.succ n) → ℕ) → (Fin n → ℕ)
| l, m => l (Nat.succ m)

/- Removing first element equals adding 1 to argument of function -/
lemma next_element_eq_add_1 : next_element l i = l (Fin.succ i) := by
  unfold next_element
  simp

/- Maps index of an element to a pair of indices -/
/- k → (t, k - l₀ - l₁ - ... - lₜ₋₁) -/
def sum_Fin_of_Fin_sum : ∀ (l : Fin n → ℕ), Fin (∑ i : Fin n, l i) → Σ i : Fin n, Fin (l i)
| l, k =>
  match n with
  | 0 =>
    nomatch k  -- Impossible case
  | Nat.succ m =>
    if h : k.val < l 0
      then
        ⟨0, ⟨k.val, h⟩⟩  -- k → (0, k)
      else
        have h1 : k.val - l 0 < (∑ i : Fin m, (next_element l) i) := by  -- Proof that k - l₀ is a valid argument for this function
          have : k.val < l 0 + ∑ i : Fin m, (next_element l) i := by
            have h2 : l 0 + ∑ i : Fin m, (next_element l) i = ∑ i : Fin (Nat.succ m), l i := by
              rw [Fin.sum_univ_succ]
              unfold next_element
              simp
            rw [h2]
            exact k.is_lt
          have : k.val - l 0 + l 0 ≤ k.val := by
            rw [Nat.sub_add_cancel]
            linarith
          linarith
        let ⟨i, j⟩ := sum_Fin_of_Fin_sum (next_element l) ⟨k.val - l 0, h1⟩  -- (k - l₀) → (t - 1, (k - l₀) - l₁ - ... - lₜ₋₁)
        have h3 : j.val < l ⟨i + 1, add_lt_add_right i.is_lt 1⟩ := by  -- Proof that k - l₀ - l₁ - ... - lₜ₋₁ < lₜ
          let h4 := j.is_lt
          unfold next_element at h4
          simp at h4
          unfold Fin.succ at h4
          linarith
        ⟨⟨i.val + 1, Nat.succ_lt_succ i.is_lt⟩, ⟨j.val, h3⟩⟩  -- x → (t, x - k₀ - k₁ - ... - kₜ₋₁)

/- If j is smaller than some element of a sum of natural numbers then j is smaller than the sum -/
lemma j_lt_elt_then_j_lt_sum : (l : Fin n → ℕ) → (j < l i) → j < (∑ i : Fin n, l i) := by
  intro l h
  induction n with
  | zero =>
    nomatch i
  | succ m hn =>
    if hi : i = 0
    then  -- Smaller than first element of sum
      rw [Fin.sum_univ_succ]
      apply Nat.lt_add_right
      rw [hi] at h
      exact h
    else  -- Smaller than some other element of sum => use induction
      rw [Fin.sum_univ_succ]
      apply Nat.lt_add_left
      have h1 : j < (next_element l) (Fin.pred i hi) := by  -- Required for induction
        rw [next_element_eq_add_1]
        simp
        exact h
      have : j < ∑ i : Fin m, (next_element l) i := hn (next_element l) h1
      unfold next_element at this
      simp at this
      exact this

/- Maps a pair of indices to an index -/
/- (iw, jw) → ∑ (i in Fin (iw - 1)), kᵢ + jw -/
def Fin_sum_of_sum_Fin : ∀ (l : Fin n → ℕ), (Σ i : Fin n, Fin (l i)) → Fin (∑ i : Fin n, l i)
| l, ⟨iw, jw⟩ =>
  match n with
  | 0 =>
    nomatch iw
  | Nat.succ m =>
    match iw with
    | ⟨0, h⟩ =>
      ⟨jw.val, j_lt_elt_then_j_lt_sum l jw.is_lt⟩  -- (0, jw) → jw
    | ⟨i_prev + 1, h⟩ =>
      have ha : 0 < Nat.succ m := by
        linarith
      have h1 : i_prev < Nat.succ m - 1 := by
        simp
        linarith
      have h2 : jw.val < next_element l ⟨i_prev, h1⟩ := by
        rw [next_element_eq_add_1]
        simp
      let ⟨b, hb⟩ := Fin_sum_of_sum_Fin (next_element l) ⟨⟨i_prev, h1⟩, ⟨jw.val, h2⟩⟩  -- (iw - 1, jw) → ∑ (i in Fin (1, iw - 1)), kᵢ + jw
      have h3 : l ⟨0, ha⟩ + b < ∑ i : Fin (Nat.succ m), l i := by  -- Proof that the result is still contained in set
        rw [Fin.sum_univ_succ]
        simp
        unfold next_element at hb
        simp at hb
        exact hb
      ⟨l ⟨0, ha⟩ + b, h3⟩  -- (iw, jw) → ∑ (i in Fin (iw - 1)), kᵢ + jw

/- Second function is the left inverse of first function -/
lemma Fin_sum_to_Fin_sum_inverse : ∀ (l : Fin n → Nat), ∀ x, (Fin_sum_of_sum_Fin l) (sum_Fin_of_Fin_sum l x) = x := by
  intro l x
  induction n with
    | zero =>
      nomatch x
    | succ m hn =>
      unfold sum_Fin_of_Fin_sum
      if h : x.val < l 0
      then  -- Base case
        simp
        rw [dif_pos h]
        unfold Fin_sum_of_sum_Fin
        simp
        constructor
      else  -- Induction
        simp
        rw [dif_neg h]
        unfold Fin_sum_of_sum_Fin
        dsimp
        rw [hn]
        simp
        cases x with
        | mk xn xh =>
          simp
          simp at h
          exact Nat.add_sub_cancel' h

/- If k.val = t.val then sum_Fin_of_Fin_sum l k = sum_Fin_of_Fin_sum l t -/
/- This is required to simplify some expression below -/
lemma sum_Fin_of_Fin_sum_invar :
(l : Fin n → ℕ) → (k : Fin (∑ i : Fin n, l i)) → (t : Fin (∑ i : Fin n, l i)) → (k.val = t.val) →
(sum_Fin_of_Fin_sum l k = sum_Fin_of_Fin_sum l t) := by
  intro l k t h
  cases n with
  | zero =>
    nomatch k
  | succ m =>
    unfold sum_Fin_of_Fin_sum
    simp
    if hif : ↑k < l 0  -- Split cases
    then
      have hif2 : ↑t < l 0 := by  -- Values of k and t are equal by assumption
        linarith
      rw [dif_pos hif]
      rw [dif_pos hif2]
      simp
      exact h
    else
      rw [dif_neg hif]
      have hif2 : ¬↑t < l 0 := by  -- Values of k and t are equal by assumption
        linarith
      rw [dif_neg hif2]
      simp
      simp_rw [h]
      simp
      apply (Fin.heq_ext_iff _).mpr
      · simp
        cases k with
        | mk k_val hk =>
          cases t with
          | mk t_val ht =>
            simp at h
            subst h
            rfl
      · simp_rw [h]

/- First function is the left inverse of the second function -/
lemma sum_Fin_to_sum_Fin_inverse : ∀ (l : Fin n → ℕ), ∀ x, (sum_Fin_of_Fin_sum l) (Fin_sum_of_sum_Fin l x) = x := by
  intro l ⟨z, t⟩
  induction n with
    | zero =>
      nomatch z
    | succ m hn =>
      match z with
        | ⟨0, h⟩ =>  -- Base case
          unfold Fin_sum_of_sum_Fin
          unfold sum_Fin_of_Fin_sum
          simp
        | ⟨z_prev + 1, h⟩ =>  -- Induction
          unfold Fin_sum_of_sum_Fin
          unfold sum_Fin_of_Fin_sum
          simp
          rw [hn (next_element l)]
          simp
          apply (Fin.heq_ext_iff _).mpr  -- Break down complicated expression step by step
          · simp
            have h1 : z_prev < m := by linarith
            have h2 : t < next_element l ⟨z_prev, h1⟩ := by
              rw [next_element_eq_add_1]
              simp
            have h3 : t.1 = (sum_Fin_of_Fin_sum (next_element l) (Fin_sum_of_sum_Fin (next_element l) ⟨⟨z_prev, h1⟩, ⟨t.1, h2⟩⟩)).2.1 := by
              rw [hn]
            simp_rw [h3]
            have h4 : (a : (Σ i : Fin (m), Fin (next_element l i))) → (b : (Σ i : Fin (m), Fin (next_element l i))) → a = b → a.2.1 = b.2.1 := by
              intro a b h0
              rw [h0]
            apply h4
            apply sum_Fin_of_Fin_sum_invar  -- Use the fact that elements with same values give same results
            simp
          · simp
            simp_rw [hn (next_element l)]  -- Use inductive hypothesis

/- Theorem about bijection -/
theorem bijection_Fin_sum_sum_Fin (l : Fin n → ℕ) : Fin (∑ i : Fin n, l i) ≃ Σ i : Fin n, Fin (l i) := by
  refine Equiv.mk ?_ ?_ ?_ ?_
  · exact sum_Fin_of_Fin_sum l
  · exact Fin_sum_of_sum_Fin l
  · exact Fin_sum_to_Fin_sum_inverse l
  · exact sum_Fin_to_sum_Fin_inverse l
