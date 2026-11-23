module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Characters graded by the sign `χ(−1)`

* `sum_char_neg_one_mul_char_eq` (graded orthogonality): `∑_χ χ(−1) χ(b) = φ(n)` if `b = −1` and
  `0` otherwise.
* `card_even_eq_card_odd`, `card_odd_eq_card_nontrivial_even_add_one`: when `−1 ≠ 1` there are as
  many even as odd characters, so the odd characters outnumber the nontrivial even ones by one.
* `isPrimitive_of_ne_one`: every nontrivial Dirichlet character modulo a prime is primitive.
* `le_of_natCast_eq_neg_one`: a positive integer congruent to `−1` modulo `q` is at least `q − 1`.
-/

@[expose] public noncomputable section

open Classical Complex

namespace RiemannMasullo

/-! ### The prime side: graded orthogonality -/

/-- **Graded orthogonality.** Weighting by the sign `χ(−1)` picks out the class of `−1`:
`∑_χ χ(−1) χ(b) = φ(n)` if `b = −1` and `0` otherwise. -/
theorem sum_char_neg_one_mul_char_eq (n : ℕ) [NeZero n] (b : ZMod n) :
    ∑ χ : DirichletCharacter ℂ n, χ (-1) * χ b = if b = -1 then (n.totient : ℂ) else 0 := by
  have hmul (χ : DirichletCharacter ℂ n) : χ (-1) * χ b = χ (-b) := by
    rw [← map_mul, neg_one_mul]
  simp_rw [hmul, DirichletCharacter.sum_characters_eq, neg_eq_iff_eq_neg]

/-- **Parity balance.** If `−1 ≠ 1` mod `n`, there are as many even as odd characters. -/
theorem card_even_eq_card_odd (n : ℕ) [NeZero n] (hn : (-1 : ZMod n) ≠ 1) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ n ↦ χ.Even).card =
      (Finset.univ.filter fun χ : DirichletCharacter ℂ n ↦ χ.Odd).card := by
  have hsum := DirichletCharacter.sum_characters_eq_zero ℂ hn
  have hval (χ : DirichletCharacter ℂ n) : χ (-1) = if χ.Even then 1 else -1 := by
    rcases χ.even_or_odd with h | h
    · rw [ite_eq_left_iff.mpr (fun h' ↦ absurd h h')]; exact h
    · have : ¬ χ.Even := fun h' ↦ by
        have := h'.symm.trans h
        norm_num at this
      rw [ite_eq_right_iff.mpr (fun h' ↦ absurd h' this)]; exact h
  have hodd : (Finset.univ.filter fun χ : DirichletCharacter ℂ n ↦ χ.Odd) =
      Finset.univ.filter fun χ ↦ ¬ χ.Even := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h h'
      have := h'.symm.trans h
      norm_num at this
    · intro h
      exact (χ.even_or_odd).resolve_left h
  have hsplit : ∑ χ : DirichletCharacter ℂ n, χ (-1) =
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ n ↦ χ.Even).card : ℂ) -
        ((Finset.univ.filter fun χ : DirichletCharacter ℂ n ↦ χ.Odd).card : ℂ) := by
    simp_rw [hval, hodd, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
    ring
  rw [hsplit, sub_eq_zero] at hsum
  exact_mod_cast hsum


/-- **Counting the graded family.** If `−1 ≠ 1` mod `n`, the odd characters outnumber the
nontrivial even characters by exactly one (the trivial character is even). -/
theorem card_odd_eq_card_nontrivial_even_add_one (n : ℕ) [NeZero n] (hn : (-1 : ZMod n) ≠ 1) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ n ↦ χ.Odd).card =
      (Finset.univ.filter fun χ : DirichletCharacter ℂ n ↦ χ.Even ∧ χ ≠ 1).card + 1 := by
  rw [← card_even_eq_card_odd n hn]
  have h1 : (1 : DirichletCharacter ℂ n).Even := by
    simp [DirichletCharacter.Even, MulChar.one_apply (isUnit_neg_one (α := ZMod n))]
  have hsplit : (Finset.univ.filter fun χ : DirichletCharacter ℂ n ↦ χ.Even) =
      insert 1 (Finset.univ.filter fun χ : DirichletCharacter ℂ n ↦ χ.Even ∧ χ ≠ 1) := by
    ext χ
    by_cases hχ : χ = 1 <;> simp [hχ, h1]
  rw [hsplit, Finset.card_insert_of_notMem (by simp)]

/-! ### Primitivity and the support condition -/

/-- Every nontrivial Dirichlet character modulo a prime is primitive. -/
theorem isPrimitive_of_ne_one {q : ℕ} [Fact q.Prime] {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R q) (hχ : χ ≠ 1) : χ.IsPrimitive := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hdvd := DirichletCharacter.conductor_dvd_level χ
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hdvd with h | h
  · exact absurd ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mpr h) hχ
  · exact h

/-- A positive integer congruent to `−1` modulo `q` is at least `q − 1`. -/
theorem le_of_natCast_eq_neg_one {q n : ℕ} (h : (n : ZMod q) = -1) : q ≤ n + 1 := by
  have h0 : ((n + 1 : ℕ) : ZMod q) = 0 := by push_cast; rw [h]; ring
  exact Nat.le_of_dvd (Nat.succ_pos n) ((ZMod.natCast_eq_zero_iff _ _).mp h0)

end RiemannMasullo
