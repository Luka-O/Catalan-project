import Mathlib

/- Large task 6 -/
/- Proof that (n + 1) divides choose(2n, n). This shows that Cₙ = choose(2n, n) / (n + 1) ∈ ℕ. -/

lemma nplus1_div_2nplus1_times_binomial_2n_n : (n + 1) ∣ (Nat.succ (2 * n)) * (Nat.choose (2 * n) n) := by
  rw [Nat.succ_mul_choose_eq]  /- Use well known combinatorial equality Nat.succ n * Nat.choose n k = Nat.choose (Nat.succ n) (Nat.succ k) * Nat.succ k -/
  apply dvd_mul_of_dvd_right
  rfl

/- Proven with gcd(2 * n + 1, n + 1) = gcd((2 * n + 1) % (n + 1), n + 1) = gcd(n, n + 1) = gcd(n + 1 % n, n) = gcd(1, n) = 1 -/
lemma nplus1_coprime_n_n_geq_2 : (n ≥ 2) → Nat.Coprime (n + 1) (2 * n + 1) := by
  intro h0
  rw [Nat.Coprime]  -- gcd(2 * n + 1, n + 1)
  rw [Nat.gcd_rec (n + 1) (2 * n + 1)]  -- gcd((2 * n + 1) % (n + 1), n + 1)
  have h_mod : (2 * n + 1) % (n + 1) = n := by
    rw [Nat.mod_eq]
    simp
    have : n ≤ 2 * n := by linarith
    rw [if_pos this]
    rw [two_mul]
    simp
  rw [h_mod]  -- gcd(n, n + 1)
  rw [Nat.gcd_rec n (n + 1)]  -- gcd(n + 1 % n, n)
  have h2_mod : (n + 1) % n = 1 := by
    rw [Nat.mod_eq]
    simp
    have : 0 < n := by linarith
    rw [if_pos this]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_succ_le h0
  rw [h2_mod]  -- gcd(1, n)
  exact Nat.gcd_one_left n  -- 1

/- Cases n = 0, n = 1 are handled here, for n ≥ 2 call nplus1_coprime_n_n_geq_2 -/
lemma nplus1_coprime_n : Nat.Coprime (n + 1) (2 * n + 1) := by
  cases n with
  | zero =>
    simp
  | succ m =>
    cases m with
    | zero =>
      simp
      intro h
      contradiction
    | succ k =>
      have : k + 2 ≥ 2 := by linarith
      exact nplus1_coprime_n_n_geq_2 this

/- (n + 1) | choose(2n, n) -/
theorem nplus1_div_binomial_2n_n (n : ℕ) : (n + 1) ∣ Nat.choose (2 * n) n := by
  apply Nat.Coprime.dvd_of_dvd_mul_left nplus1_coprime_n nplus1_div_2nplus1_times_binomial_2n_n
