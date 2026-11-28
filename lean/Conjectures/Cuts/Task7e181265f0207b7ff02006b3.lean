import Mathlib

open scoped ComplexConjugate

/-!
# The deep-minor cross integral of the (1,3) Type-II cell is real

The frozen statement is a `let`-chain defining `E, S, Q, Q₁, H, wideArcs, Λ, μ, U, B₁, B₂, B₃,
τ₁, τ₃, Jdeep` and then asking that `|Im (Jdeep n (τ₁ n) (τ₃ n))| ≤ e·n/2`.

The integral `Jdeep` is conjugated into itself by the substitution `x ↦ 1 - x`:
`wideArcs n` is symmetric under this map (`a/q ↦ (q-a)/q`), the exponential sum satisfies
`S n u (1 - x) = conj (S n u x)`, and `E (-(n)(1-x)) = conj (E (-(n)x))`.  Hence
`Jdeep = conj Jdeep` and the imaginary part vanishes identically; the bound follows.
-/

namespace GoldbachDeepImaginary

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), ((u k : ℝ) : ℂ) * E ((k : ℝ) * t)

noncomputable def Q (n : ℕ) : ℕ := Nat.log 2 (n + 2) ^ 2

noncomputable def Q1 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

noncomputable def H (n : ℕ) : ℕ := 256 * Q1 n * Q n

noncomputable def wideArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q1 n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))}

noncomputable def U (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊

noncomputable def B1 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

noncomputable def B2 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

noncomputable def B3 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊

noncomputable def mu (d : ℕ) : ℝ := ((ArithmeticFunction.moebius d : ℤ) : ℝ)

noncomputable def tau1 (n : ℕ) : ℕ → ℝ := fun m =>
  ∑ a ∈ m.divisors.filter (fun a => U n < a ∧ a ≤ B1 n ∧ U n < m / a),
    (∑ d ∈ a.divisors.filter (fun d => U n < d), mu d) * ArithmeticFunction.vonMangoldt (m / a)

noncomputable def tau3 (n : ℕ) : ℕ → ℝ := fun m =>
  ∑ a ∈ m.divisors.filter (fun a => B2 n < a ∧ a ≤ B3 n ∧ U n < m / a),
    (∑ d ∈ a.divisors.filter (fun d => U n < d), mu d) * ArithmeticFunction.vonMangoldt (m / a)

noncomputable def Jdeep (n : ℕ) (u v : ℕ → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n : ℝ) * x)) t

lemma E_add (a b : ℝ) : E (a + b) = E a * E b := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma E_int (z : ℤ) : E (z : ℝ) = 1 := by
  unfold E
  rw [show (((2 * Real.pi * (z : ℝ) : ℝ)) : ℂ) * Complex.I
      = (z : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

lemma E_nat (k : ℕ) : E (k : ℝ) = 1 := by
  simpa using E_int (k : ℤ)

lemma E_neg_nat (k : ℕ) : E (-(k : ℝ)) = 1 := by
  have := E_int (-(k : ℤ))
  simpa using this

lemma E_neg_conj (x : ℝ) : conj (E x) = E (-x) := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul]
  simp only [Complex.conj_ofReal, Complex.conj_I, mul_neg]
  push_cast
  ring

lemma E_one_sub (k : ℕ) (x : ℝ) : E ((k : ℝ) * (1 - x)) = conj (E ((k : ℝ) * x)) := by
  rw [show (k : ℝ) * (1 - x) = (k : ℝ) + -((k : ℝ) * x) by ring, E_add, E_nat k, one_mul,
    ← E_neg_conj]

lemma E_nat_one_sub (n : ℕ) (x : ℝ) :
    E (-(n : ℝ) * (1 - x)) = conj (E (-(n : ℝ) * x)) := by
  rw [show -(n : ℝ) * (1 - x) = -(n : ℝ) + (n : ℝ) * x by ring, E_add, E_neg_nat n, one_mul]
  rw [show -(n : ℝ) * x = -((n : ℝ) * x) by ring]
  simpa using (E_neg_conj (-((n : ℝ) * x))).symm

lemma S_one_sub (n : ℕ) (u : ℕ → ℝ) (x : ℝ) : S n u (1 - x) = conj (S n u x) := by
  simp only [S, map_sum, map_mul, Complex.conj_ofReal, E_one_sub]

lemma f_one_sub (n : ℕ) (u v : ℕ → ℝ) (x : ℝ) :
    S n u (1 - x) * S n v (1 - x) * E (-(n : ℝ) * (1 - x))
      = conj (S n u x * S n v x * E (-(n : ℝ) * x)) := by
  rw [S_one_sub, S_one_sub, E_nat_one_sub, map_mul, map_mul]

lemma coprime_sub_cast {q a : ℕ} (ha : a ≤ q) (hcop : Nat.Coprime a q) :
    Nat.Coprime (q - a) q := by
  have h2 : Nat.Coprime (q - a) ((q - a) + a) := by
    rw [Nat.coprime_self_add_right, Nat.coprime_sub_self_left ha, Nat.coprime_comm]
    exact hcop
  simpa [Nat.sub_add_cancel ha] using h2

lemma mem_wideArcs_sub (n : ℕ) (x : ℝ) : x ∈ wideArcs n ↔ 1 - x ∈ wideArcs n := by
  have hcast : ∀ (q a : ℕ), a ≤ q → ((q - a : ℕ) : ℝ) = (q : ℝ) - (a : ℝ) := by
    intro q a ha
    rw [Nat.cast_sub ha]
  have hqne : ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≠ 0 := by
    intro q hq1
    have h : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    linarith
  constructor
  · rintro ⟨q, a, hq1, hq2, ha, hcop, habs⟩
    refine ⟨q, q - a, hq1, hq2, Nat.sub_le q a, coprime_sub_cast ha hcop, ?_⟩
    have heq : 1 - x - ((q - a : ℕ) : ℝ) / (q : ℝ) = -(x - (a : ℝ) / (q : ℝ)) := by
      rw [hcast q a ha]
      field_simp
      ring
    rw [heq, abs_neg]
    exact habs
  · rintro ⟨q, a, hq1, hq2, ha, hcop, habs⟩
    refine ⟨q, q - a, hq1, hq2, Nat.sub_le q a, coprime_sub_cast ha hcop, ?_⟩
    have heq : x - ((q - a : ℕ) : ℝ) / (q : ℝ) = -(1 - x - (a : ℝ) / (q : ℝ)) := by
      rw [hcast q a ha]
      field_simp
      ring
    rw [heq, abs_neg]
    exact habs

lemma indicator_one_sub (n : ℕ) (u v : ℕ → ℝ) (x : ℝ) :
    (wideArcs n)ᶜ.indicator (fun y => S n u y * S n v y * E (-(n : ℝ) * y)) (1 - x)
      = conj ((wideArcs n)ᶜ.indicator (fun y => S n u y * S n v y * E (-(n : ℝ) * y)) x) := by
  by_cases hx : x ∈ wideArcs n
  · have hx' : 1 - x ∈ wideArcs n := (mem_wideArcs_sub n x).mp hx
    rw [Set.indicator_of_notMem (by simpa using hx'),
      Set.indicator_of_notMem (by simpa using hx), map_zero]
  · have hx' : 1 - x ∉ wideArcs n := fun h => hx ((mem_wideArcs_sub n x).mpr h)
    rw [Set.indicator_of_mem (by simpa using hx'), Set.indicator_of_mem (by simpa using hx)]
    exact f_one_sub n u v x

lemma Jdeep_im (n : ℕ) (u v : ℕ → ℝ) : (Jdeep n u v).im = 0 := by
  set g : ℝ → ℂ := fun y => (wideArcs n)ᶜ.indicator
    (fun y => S n u y * S n v y * E (-(n : ℝ) * y)) y with hgdef
  have hstep : (∫ y in (0 : ℝ)..1, g y) = ∫ y in (0 : ℝ)..1, g (1 - y) := by
    simpa using (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 : ℝ))
      (d := (1 : ℝ)) (f := g)).symm
  have hstep2 : (∫ y in (0 : ℝ)..1, g (1 - y)) = ∫ y in (0 : ℝ)..1, conj (g y) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with y _
    exact indicator_one_sub n u v y
  have hstep3 : (∫ y in (0 : ℝ)..1, conj (g y)) = conj (∫ y in (0 : ℝ)..1, g y) :=
    intervalIntegral.intervalIntegral_conj
  have hz : Jdeep n u v = conj (Jdeep n u v) := by
    unfold Jdeep
    change (∫ y in (0 : ℝ)..1, g y) = conj (∫ y in (0 : ℝ)..1, g y)
    calc (∫ y in (0 : ℝ)..1, g y) = ∫ y in (0 : ℝ)..1, g (1 - y) := hstep
      _ = ∫ y in (0 : ℝ)..1, conj (g y) := hstep2
      _ = conj (∫ y in (0 : ℝ)..1, g y) := hstep3
  have := congrArg Complex.im hz
  simp only [Complex.conj_im] at this
  linarith

end GoldbachDeepImaginary

open GoldbachDeepImaginary

theorem Conjectures.Cuts.Task7e181265f0207b7ff02006b3 :
    ∀ (x16 : ℝ), (0 : ℝ) < x16 → ∃ (x18 : ℕ), ∀ (x19 : ℕ), x18 ≤ x19 → Even x19 → |(Jdeep x19 (tau1 x19) (tau3 x19)).im| ≤ x16 * (↑x19 : ℝ) / (2 : ℝ) := by
  intro e he
  refine ⟨0, ?_⟩
  intro n _ _
  rw [Jdeep_im n (tau1 n) (tau3 n), abs_zero]
  have h1 : (0 : ℝ) ≤ e := le_of_lt he
  have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h3 : (0 : ℝ) ≤ e * (n : ℝ) := mul_nonneg h1 h2
  linarith
