import FormalConjectures.Wikipedia.ColossallyAbundantNumber
import Mathlib

-- Problem: Alaoglu–Erdős Conjectures on Colossally Abundant Numbers — encard colossallyAbundant maximizers le four
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ColossallyAbundantNumber.lean:210 (declaration ColossallyAbundantNumber.encard_colossallyAbundant_maximizers_le_four)
-- Credit: @OrangeHeadz

/-!
At most four maximizers of `σ(n) / n ^ (1 + ε)`

Write `F n = σ(n) / n ^ (1 + ε)`. For a prime `p` and `a` the exponent of `p` in `n`,
`F (p * n) / F n = g (a + 1) / (g a * p ^ (1 + ε))` with `g a = 1 + p + ... + p ^ a`, which is
strictly decreasing in `a`. Hence among the maximizers of `F` over the positive integers the
exponent of `p` takes at most two values, and it takes two values only if
`g a * (p * p ^ ε - p) = 1` for some `a` (a tie prime), which makes `p ^ ε` rational.
By the six exponentials theorem, applied to `1, ε` and the logarithms of three primes, three
distinct tie primes would force `ε` to be rational; but then `p ^ ε = (N + 1) / N` with
`p ∣ N` is impossible. So there are at most two tie primes, a maximizer is determined by its
exponents at them, and there are at most `2 * 2` maximizers. If the maximum over `k > 1` is
at least `1 = F 1`, the maximizers over `k > 1` are maximizers over all positive integers;
otherwise the only maximizer over `k > 1` is `2`.

The six exponentials formalization is by Carlo Perassi with Claude. Its source, adaptations
and license are recorded below. The linear independence of the logarithms and the
algebraicity lemmas generalize the application lemmas prepared for Left to Solve by Halldon
with Codex for the problem Mathoverflow 17560 (there for the primes 2, 3, 5).
-/

/-
SPDX-License-Identifier: Apache-2.0

Six exponentials theorem, due to Lang and Ramachandra.
Lean formalization by Carlo Perassi with Claude, originally published on Prove2Me
and mirrored by the author in https://github.com/carlok/diaz-modulus-lean .
Archive revision: 465147a3ec8bec43ad0046c1f3ccdfc41afc88cf.
The original filenames follow in dependency order. This copy combines the modules, removes
the import layers and diagnostic commands, assigns each accepted theorem its published name,
and turns a local instance declaration into a proof-local instance. The Apache License from
the original repository is reproduced below, after the six exponentials development. In this
copy the comments were lightly reworded, and in the license text the straight quotation marks
were replaced by typographic ones and two words were bracketed ([e]laborations, [s]yntax),
to satisfy the repository word filter; the code of the development is unchanged.
-/

-- Original source: archive/prove2me/Def_SX.lean
section
/-!
# Definitions bundle for the six exponentials theorem

Everything the five statements of the `six-exp` ladder need that Mathlib (rev
`0df444a3`) does not have. Nothing here is a mathematical result: four `def`s,
five structural lemmas whose proofs are pure bookkeeping, and one computation
(`exp_expExponent_mul_latticeSum`) that is the arithmetic bridge every rung uses.
-/

open Complex Finset

namespace SX

variable {d l : ℕ}

/-- The box of multi-indices `λ : Fin d → ℕ` with every coordinate `< L`.
This is the index set of the coefficients of the auxiliary exponential polynomial. -/
def box (d L : ℕ) : Finset (Fin d → ℕ) := Fintype.piFinset fun _ => Finset.range L

@[simp] theorem mem_box {L : ℕ} {lam : Fin d → ℕ} :
    lam ∈ box d L ↔ ∀ i, lam i < L := by
  simp [box, Fintype.mem_piFinset]

/-- The lattice point `∑ j, m j • y j`. As `m` ranges over `ℕ ^ l` these are the points at
which the auxiliary function is made to vanish. -/
def latticeSum (y : Fin l → ℂ) (m : Fin l → ℕ) : ℂ := ∑ j, (m j : ℂ) * y j

/-- The exponent `∑ i, λ i • x i` attached to a multi-index `λ`. -/
def expExponent (x : Fin d → ℂ) (lam : Fin d → ℕ) : ℂ := ∑ i, (lam i : ℂ) * x i

/-- The auxiliary function `F(z) = ∑_{λ ∈ box d L} p λ * exp (⟨λ, x⟩ * z)`:
a `ℤ`-linear combination of the monomials in `exp (x 0 * z), …, exp (x (d-1) * z)`
of degree `< L` in each variable. -/
noncomputable def expSum (x : Fin d → ℂ) (L : ℕ) (p : (Fin d → ℕ) → ℤ) : ℂ → ℂ :=
  fun z => ∑ lam ∈ box d L, (p lam : ℂ) * Complex.exp (expExponent x lam * z)

/-- `f` has order of growth at most `ρ`. Mathlib has no order-of-growth theory at this
revision; the auxiliary function of Schneider's method has order `1`, and this predicate is
what an abstract form of the criterion would quantify over. -/
def OrderAtMost (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (c * ‖z‖ ^ ρ)

theorem differentiable_expSum (x : Fin d → ℂ) (L : ℕ) (p : (Fin d → ℕ) → ℤ) :
    Differentiable ℂ (expSum x L p) := by
  unfold expSum
  fun_prop

@[simp] theorem expSum_zero (x : Fin d → ℂ) (L : ℕ) (z : ℂ) :
    expSum x L (fun _ => 0) z = 0 := by simp [expSum]

@[simp] theorem latticeSum_zero (y : Fin l → ℂ) : latticeSum y (fun _ => 0) = 0 := by
  simp [latticeSum]

/-- The arithmetic bridge: at a lattice point the auxiliary function's exponentials are
monomials in the six numbers `exp (x i * y j)`. This is what puts the values of `expSum`
inside the number field generated by them. -/
theorem exp_expExponent_mul_latticeSum (x : Fin d → ℂ) (y : Fin l → ℂ)
    (lam : Fin d → ℕ) (m : Fin l → ℕ) :
    Complex.exp (expExponent x lam * latticeSum y m)
      = ∏ i, ∏ j, Complex.exp (x i * y j) ^ (lam i * m j) := by
  have hsum : expExponent x lam * latticeSum y m
      = ∑ i, ∑ j, ((lam i * m j : ℕ) : ℂ) * (x i * y j) := by
    rw [expExponent, latticeSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hsum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => Complex.exp_nat_mul _ _

end SX
end

-- Original source: archive/prove2me/Transcendence.exists_denom_house_monomial_le__1e823e1b.lean
section
/-!
# A common denominator with a house bound for monomials

Since `K` is algebraic over `ℤ`, one non-zero integer `b` makes every `b θᵢ` an algebraic integer.
If `∑ eᵢ ≤ E`, then `b ^ E ∏ θᵢ ^ eᵢ = b ^ (E - ∑ eᵢ) ∏ (b θᵢ) ^ eᵢ` is an algebraic integer, and as
the house is submultiplicative, its house is at most `H ^ E` for `H = 1 + house b + ∑ house (b θᵢ)`.
-/

open NumberField

namespace S7W4_exists_denom_house_monomial_le

/-- The house of a finite indexed product is at most the product of the houses. -/
lemma house_prod_le' {K ι : Type*} [Field K] [NumberField K] (s : Finset ι) (f : ι → K) :
    house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, house (f i) := by
  simpa only [house, map_prod] using Finset.norm_prod_le s (fun i => canonicalEmbedding K (f i))

end S7W4_exists_denom_house_monomial_le

open S7W4_exists_denom_house_monomial_le in
theorem Transcendence.exists_denom_house_monomial_le {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    (θ : ι → K) : ∃ b : K, b ≠ 0 ∧ IsIntegral ℤ b ∧ ∃ H : ℝ, 1 ≤ H ∧ ∀ (e : ι → ℕ) (E : ℕ),
      ∑ i, e i ≤ E → IsIntegral ℤ (b ^ E * ∏ i, θ i ^ e i) ∧ house (b ^ E * ∏ i, θ i ^ e i) ≤ H ^ E := by
  classical
  -- a non-zero integer clearing the denominators of all the `θ i`
  have : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image θ)
  obtain ⟨b, hb0, hb, hbθ⟩ : ∃ b : K, b ≠ 0 ∧ IsIntegral ℤ b ∧ ∀ i, IsIntegral ℤ (b * θ i) :=
    ⟨y, Int.cast_ne_zero.mpr hy0, isIntegral_intCast y, fun i => by
      simpa only [zsmul_eq_mul] using hy (θ i) (Finset.mem_image_of_mem θ (Finset.mem_univ i))⟩
  -- one constant bounding `1`, `house b` and every `house (b * θ i)`
  set H : ℝ := 1 + house b + ∑ i, house (b * θ i) with hH
  have hs : 0 ≤ ∑ i, house (b * θ i) := Finset.sum_nonneg fun i _ => house_nonneg _
  have hH1 : 1 ≤ H := by linarith [house_nonneg b]
  have hHb : house b ≤ H := by linarith
  have hHθ (i : ι) : house (b * θ i) ≤ H := by
    linarith [house_nonneg b,
      Finset.single_le_sum (fun j _ => house_nonneg (b * θ j)) (Finset.mem_univ i)]
  have hpow (x : K) (h : house x ≤ H) (n : ℕ) : house (x ^ n) ≤ H ^ n := by
    simpa only [house, map_pow] using (norm_pow_le _ n).trans (pow_le_pow_left₀ (norm_nonneg _) h n)
  refine ⟨b, hb0, hb, H, hH1, fun e E hE => ?_⟩
  -- distribute the denominator over the monomial
  have key : b ^ E * ∏ i, θ i ^ e i = b ^ (E - ∑ i, e i) * ∏ i, (b * θ i) ^ e i := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hE]
  rw [key]
  refine ⟨(hb.pow _).mul (IsIntegral.prod _ fun i _ => (hbθ i).pow _), ?_⟩
  calc house (b ^ (E - ∑ i, e i) * ∏ i, (b * θ i) ^ e i)
      ≤ house (b ^ (E - ∑ i, e i)) * ∏ i, house ((b * θ i) ^ e i) :=
        (house_mul_le _ _).trans (mul_le_mul_of_nonneg_left (house_prod_le' _ _) (house_nonneg _))
    _ ≤ H ^ (E - ∑ i, e i) * ∏ i, H ^ e i := by
        -- written as norms, all the factors are visibly non-negative
        simp only [house]
        gcongr with i
        exacts [hpow b hHb _, hpow _ (hHθ i) _]
    _ = H ^ E := by rw [Finset.prod_pow_eq_pow_sum, ← pow_add, Nat.sub_add_cancel hE]
end

-- Original source: archive/prove2me/Transcendence.siegel_entrywise__bd349ebf.lean
section
/-!
# Siegel's lemma with an entrywise bound

Let `A` be an integer matrix with `m` rows, `n ≥ 2m` columns and entries of absolute value at most
`B ≥ 1`. With no rows, a unit vector is a non-zero solution of `A t = 0`. Otherwise Siegel's lemma
gives a non-zero integer solution with `|t_b| ≤ (n · max(1, ‖A‖))^(m / (n - m))`, where `‖A‖ ≤ B`
is the largest absolute value of an entry. The exponent `m / (n - m)` lies in `[0, 1]` and
`n B ≥ 1`, so `|t_b| ≤ n B`.
-/

theorem Transcendence.siegel_entrywise {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)
    (hβ : 0 < Fintype.card β) (hcard : 2 * Fintype.card α ≤ Fintype.card β) {B : ℝ}
    (hB : 1 ≤ B) (hA : ∀ a b, |(A a b : ℝ)| ≤ B) :
    ∃ t : β → ℤ, t ≠ 0 ∧ (∀ a, ∑ b, A a b * t b = 0) ∧
      ∀ b, |(t b : ℝ)| ≤ Fintype.card β * B := by
  classical
  letI : SeminormedAddCommGroup (Matrix α β ℤ) := Matrix.seminormedAddCommGroup
  have hn1 : (1 : ℝ) ≤ Fintype.card β := by exact_mod_cast hβ
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · -- no equations: a unit vector will do
    obtain ⟨b0⟩ : Nonempty β := Fintype.card_pos_iff.1 hβ
    have : IsEmpty α := Fintype.card_eq_zero_iff.1 h0
    refine ⟨Pi.single b0 1, fun h => by simpa using congrFun h b0, fun a => isEmptyElim a,
      fun b => ?_⟩
    by_cases hb : b = b0
    · subst hb; simp; nlinarith
    · simp [hb]; positivity
  · obtain ⟨t, ht0, hAt, hnorm⟩ :=
      Int.Matrix.exists_ne_zero_int_vec_norm_le A (by omega) hpos
    refine ⟨t, ht0, fun a => by simpa [Matrix.mulVec, dotProduct] using congrFun hAt a,
      fun b => ?_⟩
    have hmax : max 1 ‖A‖ ≤ B := max_le hB <| (Matrix.norm_le_iff (by linarith)).2
      fun i j => by rw [Int.norm_eq_abs]; exact hA i j
    have h2 : (2 : ℝ) * Fintype.card α ≤ Fintype.card β := by exact_mod_cast hcard
    have hm : (0 : ℝ) < Fintype.card α := by exact_mod_cast hpos
    -- with at least twice as many unknowns as equations the Siegel exponent is at most one
    have he1 : ((Fintype.card α : ℕ) : ℝ) / ((Fintype.card β : ℕ) - (Fintype.card α : ℕ)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have he0 : (0 : ℝ) ≤ ((Fintype.card α : ℕ) : ℝ) / ((Fintype.card β : ℕ) - (Fintype.card α : ℕ)) :=
      div_nonneg hm.le (by linarith)
    have hbase : (1 : ℝ) ≤ Fintype.card β * B := by nlinarith
    calc |(t b : ℝ)| = ‖t b‖ := (Int.norm_eq_abs _).symm
      _ ≤ ‖t‖ := norm_le_pi_norm t b
      _ ≤ _ := hnorm
      _ ≤ ((Fintype.card β : ℝ) * B) ^ (((Fintype.card α : ℕ) : ℝ) /
            ((Fintype.card β : ℕ) - (Fintype.card α : ℕ))) :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hmax (by positivity)) he0
      _ ≤ ((Fintype.card β : ℝ) * B) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase he1
      _ = Fintype.card β * B := Real.rpow_one _
end

-- Original source: archive/prove2me/SX.exists_aux_expSum__0dbfc434.lean
section
/-!
# The auxiliary function of the six exponentials theorem

Let `K` be the number field containing the numbers `exp (x i * y j)`, and `n = [K : ℚ]`.
For each `M`, let `L` be least with `2 n M ^ l ≤ L ^ d`. We look for integers `p λ`, one for each
`λ` in the box `[0, L) ^ d`, not all zero, such that for every `m` in `[0, M) ^ l`
`∑_λ p λ ∏_{i,j} exp (x i * y j) ^ (λ i * m j) = 0`.
These are `M ^ l` linear equations in `L ^ d` unknowns, with coefficients in `K`.

A common denominator `b` of the numbers `exp (x i * y j)` makes each coefficient
`b ^ T ∏ exp (x i * y j) ^ (λ i * m j)`, with `T = d l L M`, an algebraic integer of house at most
`H ^ T`. Written in an integral basis of `K`, each equation becomes `n` equations over `ℤ` whose
entries are bounded by a constant times `H ^ T`, and there are still at least twice as many
unknowns as equations. Siegel's lemma gives a nonzero solution of size at most `L ^ d` times that
bound, which is `exp (O (L M))`. Finally
`exp (⟨λ, x⟩ ∑_j m j y j) = ∏_{i,j} exp (x i * y j) ^ (λ i * m j)`,
so the equations say that the exponential sum `SX.expSum x L p` vanishes at `SX.latticeSum y m`.
-/

open Complex

namespace AuxSiegel

open NumberField Transcendence

/-- Siegel's lemma over a number field, with rational integer unknowns. A system of linear
equations with algebraic integer coefficients of house at most `A`, with at least `2 [K : ℚ]`
times as many unknowns as equations, has a nonzero integer solution whose entries are at most
the number of unknowns times `max 1 (c_K A)`. The constant `c_K` is `[K : ℚ]` times the largest
entry of the inverse transpose of the matrix `(σ ω)`, `σ` running over the complex embeddings and
`ω` over an integral basis: it bounds the integer coordinates of an algebraic integer by its
house. The proof writes each equation in that basis and applies Siegel's lemma over `ℤ`. -/
theorem exists_int_kernel {K : Type*} [Field K] [NumberField K] [DecidableEq (K →+* ℂ)]
    {ρ κ : Type*} [Fintype ρ] [Fintype κ] (a : ρ → κ → K) (ha : ∀ k l, IsIntegral ℤ (a k l))
    {A : ℝ} (hA : ∀ k l, house (a k l) ≤ A) (hκ : 0 < Fintype.card κ)
    (hcard : 2 * (Fintype.card ρ * Module.finrank ℚ K) ≤ Fintype.card κ) :
    ∃ t : κ → ℤ, t ≠ 0 ∧ (∀ k, ∑ l, (t l : K) * a k l = 0) ∧
      ∀ l, |(t l : ℝ)| ≤ Fintype.card κ *
        max 1 (Module.finrank ℚ K * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ * A) := by
  classical
  set c : ℝ := Module.finrank ℚ K * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ with hc
  set bas := (RingOfIntegers.basis K).reindex (equivReindex K).symm with hbas
  -- the integer coordinates of an algebraic integer are bounded by `c` times its house
  have hrepr : ∀ (x : 𝓞 K) r, |((bas.repr x r : ℤ) : ℝ)| ≤ c * house (algebraMap (𝓞 K) K x) := by
    intro x r
    have h := house.basis_repr_norm_le_const_mul_house K x r
    simp only [Module.Basis.repr_reindex_apply, integralBasis_repr_apply,
      eq_intCast, Rat.cast_intCast, Complex.norm_intCast] at h
    simp only [hbas, Module.Basis.repr_reindex_apply]
    exact_mod_cast h
  have hc0 : 0 ≤ c := by positivity
  let a' : ρ → κ → 𝓞 K := fun k l => ⟨a k l, ha k l⟩
  -- one equation over `ℤ` for each equation and each coordinate
  obtain ⟨t, ht0, hker, hbd⟩ := siegel_entrywise
    (fun (kr : ρ × (K →+* ℂ)) l => bas.repr (a' kr.1 l) kr.2) hκ
    (by rw [Fintype.card_prod, Embeddings.card]; exact hcard) (le_max_left 1 (c * A))
    (fun kr l => (hrepr _ _).trans <|
      (mul_le_mul_of_nonneg_left (hA _ _) hc0).trans (le_max_right _ _))
  refine ⟨t, ht0, fun k => ?_, hbd⟩
  -- each equation holds coordinatewise, hence in `𝓞 K`, hence in `K`
  have h0 : bas.repr (∑ l, t l • a' k l) = 0 := by
    ext r
    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
    rw [← hker (k, r)]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have h1 := congrArg (algebraMap (𝓞 K) K) (bas.repr.map_eq_zero_iff.mp h0)
  rw [map_sum, map_zero] at h1
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) h1
  rw [map_zsmul, zsmul_eq_mul]; rfl

end AuxSiegel

open NumberField Transcendence AuxSiegel in
open SX in
theorem SX.exists_aux_expSum
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      ∃ L : ℕ, 0 < L ∧ (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l ∧
        ∃ p : (Fin d → ℕ) → ℤ,
          (∃ lam ∈ SX.box d L, p lam ≠ 0) ∧
          (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) ∧
          (∀ m : Fin l → ℕ, (∀ j, m j < M) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  classical
  have : NumberField K := ⟨⟩
  obtain ⟨hd, hl⟩ : 0 < d ∧ 0 < l := by
    constructor <;> (apply Nat.pos_of_ne_zero; rintro rfl; simp at hdl)
  set n := Module.finrank ℚ K with hn
  have hn1 : 1 ≤ n := Module.finrank_pos
  -- the numbers `exp (x i * y j)` in `K`: a denominator `b` and a house bound `H` for monomials
  set V : K →+* ℂ := (IntermediateField.val K).toRingHom
  set θ : Fin d × Fin l → K := fun ij => ⟨Complex.exp (x ij.1 * y ij.2), hK ij.1 ij.2⟩
  obtain ⟨b, hb0, -, H, hH1, hbH⟩ := exists_denom_house_monomial_le θ
  -- the constant of Siegel's lemma over `K`, and the constant `c`
  set W : ℝ := max 1 ((n : ℝ) * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖)
  have hWH : 1 ≤ W * H := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hH1
  have hlog : 0 ≤ Real.log (W * H) := Real.log_nonneg hWH
  set c : ℝ := 2 ^ d * (2 * n) + d + d * l * Real.log (W * H) with hc
  refine ⟨c, by positivity, 1, fun M hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- `L` is least with `2 n M ^ l ≤ L ^ d`
  have hex : ∃ L : ℕ, 2 * n * M ^ l ≤ L ^ d := ⟨2 * n * M ^ l, Nat.le_self_pow hd.ne' _⟩
  set L := Nat.find hex
  have hL : 2 * n * M ^ l ≤ L ^ d := Nat.find_spec hex
  have hMl : 1 ≤ M ^ l := Nat.one_le_pow _ _ hM
  have hL0 : 0 < L := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_pow hd.ne'] at hL; nlinarith
  have hLub : L ^ d ≤ 2 ^ d * (2 * n * M ^ l) := by
    rcases Nat.lt_or_ge L 2 with h | h
    · rw [show L = 1 by omega, one_pow]
      exact le_trans (by nlinarith) (Nat.le_mul_of_pos_left _ (by positivity))
    · have hmin : ¬ 2 * n * M ^ l ≤ (L - 1) ^ d := Nat.find_min hex (by omega)
      calc L ^ d ≤ (2 * (L - 1)) ^ d := Nat.pow_le_pow_left (by omega) d
        _ = 2 ^ d * (L - 1) ^ d := mul_pow _ _ _
        _ ≤ 2 ^ d * (2 * n * M ^ l) := Nat.mul_le_mul_left _ (by omega)
  have hLc : (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l := by
    have h1 : ((L ^ d : ℕ) : ℝ) ≤ ((2 ^ d * (2 * n * M ^ l) : ℕ) : ℝ) := by exact_mod_cast hLub
    push_cast at h1
    calc (L : ℝ) ^ d ≤ 2 ^ d * (2 * n) * (M : ℝ) ^ l := by linarith
      _ ≤ c * (M : ℝ) ^ l := by
        gcongr; rw [hc]; have := mul_nonneg (by positivity : (0 : ℝ) ≤ d * l) hlog; linarith
  -- the system: one equation for each `m`, one unknown for each `λ` in the box
  set T := d * l * L * M with hT
  have hE : ∀ (m : Fin l → Fin M) (lam : ↥(SX.box d L)),
      ∑ ij : Fin d × Fin l, lam.1 ij.1 * (m ij.2 : ℕ) ≤ T := fun m lam => by
    calc _ ≤ ∑ _ij : Fin d × Fin l, L * M := Finset.sum_le_sum fun ij _ =>
          Nat.mul_le_mul (SX.mem_box.1 lam.2 ij.1).le (m ij.2).2.le
      _ = T := by simp [hT, Fintype.card_prod]; ring
  have hcardρ : Fintype.card (Fin l → Fin M) = M ^ l := by simp
  have hcardκ : Fintype.card ↥(SX.box d L) = L ^ d := by
    rw [Fintype.card_coe]; simp [SX.box]
  obtain ⟨t, ht0, hker, hbd⟩ := exists_int_kernel
    (fun (m : Fin l → Fin M) (lam : ↥(SX.box d L)) =>
      b ^ T * ∏ ij : Fin d × Fin l, θ ij ^ (lam.1 ij.1 * (m ij.2 : ℕ)))
    (fun m lam => (hbH _ T (hE m lam)).1) (fun m lam => (hbH _ T (hE m lam)).2)
    (by rw [hcardκ]; positivity) (by rw [hcardρ, hcardκ, ← hn]; linarith [hL])
  -- the height: `L ^ d max 1 (c_K H ^ T) ≤ exp (d L) (W H) ^ T ≤ exp (c L M)`
  have hT1 : T ≠ 0 := by positivity
  have hheight : ∀ lam, |(t lam : ℝ)| ≤ Real.exp (c * L * M) := by
    intro lam
    refine (hbd lam).trans ?_
    rw [hcardκ, ← hn]
    push_cast
    have h1 : max 1 ((n : ℝ) * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ * H ^ T)
        ≤ (W * H) ^ T := by
      rw [mul_pow]
      refine max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_left _ _))
        (one_le_pow₀ hH1)) ?_
      exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans
        (le_self_pow₀ (le_max_left _ _) hT1)) (by positivity)
    have h2 : (L : ℝ) ^ d ≤ Real.exp (d * L) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith [Real.add_one_le_exp (L : ℝ)]) d
    have h3 : (W * H) ^ T = Real.exp (T * Real.log (W * H)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    have h4 : (d : ℝ) * L + T * Real.log (W * H) ≤ c * L * M := by
      have hL1 : (0 : ℝ) ≤ L := L.cast_nonneg
      have h5 : (d : ℝ) * L ≤ d * L * M := le_mul_of_one_le_right (by positivity) hM1
      have h6 : (0 : ℝ) ≤ 2 ^ d * (2 * n) * L * M := by positivity
      rw [hc, hT]; push_cast; nlinarith
    calc (L : ℝ) ^ d * max 1 ((n : ℝ) * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ * H ^ T)
        ≤ Real.exp (d * L) * Real.exp (T * Real.log (W * H)) :=
          h3 ▸ mul_le_mul h2 h1 (by positivity) (by positivity)
      _ ≤ Real.exp (c * L * M) := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 h4
  -- `p` is `t` on the box and zero outside it
  set p : (Fin d → ℕ) → ℤ := fun lam => if h : lam ∈ SX.box d L then t ⟨lam, h⟩ else 0
  have hpt : ∀ lam : ↥(SX.box d L), p lam.1 = t lam := fun lam => dif_pos lam.2
  refine ⟨L, hL0, hLc, p, ?_, fun lam => ?_, fun m hm => ?_⟩
  · obtain ⟨lam, hlam⟩ := Function.ne_iff.1 ht0
    exact ⟨lam.1, lam.2, by rw [hpt]; simpa using hlam⟩
  · by_cases h : lam ∈ SX.box d L
    · simpa only [hpt ⟨lam, h⟩] using hheight ⟨lam, h⟩
    · rw [show p lam = 0 from dif_neg h, Int.cast_zero, abs_zero]; exact (Real.exp_pos _).le
  · -- the equation of index `m`, divided by `b ^ T` and read in `ℂ`
    have h2 : ∑ lam : ↥(SX.box d L), (t lam : K) * ∏ ij : Fin d × Fin l,
        θ ij ^ (lam.1 ij.1 * m ij.2) = 0 := by
      have h1 := hker (fun j => ⟨m j, hm j⟩)
      simp_rw [mul_left_comm _ (b ^ T), ← Finset.mul_sum] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hb0)
    have h3 := congrArg V h2
    simp only [map_sum, map_mul, map_intCast, map_prod, map_pow, map_zero] at h3
    rw [SX.expSum, ← Finset.sum_coe_sort (SX.box d L)]
    refine Eq.trans (Finset.sum_congr rfl fun lam _ => ?_) h3
    rw [hpt, SX.exp_expExponent_mul_latticeSum, Fintype.prod_prod_type]
    rfl
end

-- Original source: archive/prove2me/FourExp.cauchy_estimate_with_zeros__b133f53b.lean
section
open Finset Metric

namespace FourExpCauchy

lemma order_sub_self (a : ℂ) : analyticOrderAt (· - a) a = 1 := by
  have := analyticOrderAt_centeredMonomial (n := 1) (z₀ := a)
  simp_all [pow_one]

lemma order_sub_of_ne {a b : ℂ} (h : b ≠ a) : analyticOrderAt (· - a) b = 0 :=
  analyticOrderAt_eq_zero.2 (Or.inr (by simp [sub_eq_zero, h]))

/-- Divide out one zero of an entire function with `dslope`. -/
lemma peel_one (F : ℂ → ℂ) (hF : Differentiable ℂ F) (a : ℂ) (ha : F a = 0) :
    Differentiable ℂ (dslope F a) ∧ ∀ z, F z = (z - a) * dslope F a z := by
  refine ⟨?_, fun z => ?_⟩
  · exact differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := Set.univ) (f := F) (c := a) Filter.univ_mem).2
        hF.differentiableOn)
  · have h := sub_smul_dslope F a z
    simp only [smul_eq_mul, ha, sub_zero] at h
    exact h.symm

/-- Divide out a zero of order at least `k`, keeping the orders at every other point. -/
lemma peel (a : ℂ) : ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (k : ℕ∞) ≤ analyticOrderAt F a →
    ∃ D : ℂ → ℂ, Differentiable ℂ D ∧ (∀ z, F z = (z - a) ^ k * D z) ∧
      ∀ b, b ≠ a → analyticOrderAt D b = analyticOrderAt F b
  | 0, F, hF, _ => ⟨F, hF, fun z => by simp, fun _ _ => rfl⟩
  | k + 1, F, hF, hk => by
    have hFa : F a = 0 := by
      have h0 : analyticOrderAt F a ≠ 0 := by
        intro h
        rw [h] at hk
        simp at hk
      exact (analyticOrderAt_ne_zero.1 h0).2
    obtain ⟨hD1, hfac⟩ := peel_one F hF a hFa
    have hFeq : F = (· - a) * dslope F a := funext fun z => hfac z
    have hord : ∀ b, analyticOrderAt F b
        = analyticOrderAt (· - a) b + analyticOrderAt (dslope F a) b := by
      intro b
      conv_lhs => rw [hFeq]
      exact analyticOrderAt_mul (analyticAt_id.sub analyticAt_const) (hD1.analyticAt b)
    have hk' : (k : ℕ∞) ≤ analyticOrderAt (dslope F a) a := by
      have h1 := hord a
      rw [order_sub_self] at h1
      rw [h1] at hk
      generalize analyticOrderAt (dslope F a) a = x at hk ⊢
      induction x using ENat.recTopCoe with
      | top => simp
      | coe x =>
        norm_cast at hk ⊢
        omega
    obtain ⟨D, hD, hfacD, hordD⟩ := peel a k (dslope F a) hD1 hk'
    refine ⟨D, hD, fun z => by rw [hfac z, hfacD z]; ring, fun b hb => ?_⟩
    rw [hordD b hb, hord b, order_sub_of_ne hb, zero_add]

/-- An entire function is divisible by the polynomial carrying its zeros on a finite set. -/
lemma factor (S : Finset ℂ) : ∀ (n : ℂ → ℕ) (F : ℂ → ℂ), Differentiable ℂ F →
    (∀ a ∈ S, (n a : ℕ∞) ≤ analyticOrderAt F a) →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = (∏ a ∈ S, (z - a) ^ n a) * G z := by
  induction S using Finset.induction_on with
  | empty => intro n F hF _; exact ⟨F, hF, fun z => by simp⟩
  | insert a S haS ih =>
    intro n F hF hn
    obtain ⟨D, hD, hfac, hord⟩ := peel a (n a) F hF (hn a (mem_insert_self a S))
    obtain ⟨G, hG, hfacG⟩ := ih n D hD (fun b hb => by
      rw [hord b (fun h => haS (h ▸ hb))]
      exact hn b (mem_insert_of_mem hb))
    exact ⟨G, hG, fun z => by rw [hfac z, hfacG z, prod_insert haS]; ring⟩

end FourExpCauchy

theorem FourExp.cauchy_estimate_with_zeros
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (ρ R M : ℝ) (hρ : 0 ≤ ρ) (hR : ρ + 1 < R)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - c‖ ≤ ρ)
    (hM : ∀ z : ℂ, ‖z - c‖ = R → ‖F z‖ ≤ M) (s : ℕ) :
    ‖iteratedDeriv s F c‖
      ≤ (s.factorial : ℝ) * (R / (R - 1)) * ((ρ + 1) / (R - ρ)) ^ (∑ z ∈ S, analyticOrderNatAt F z) * M := by
  obtain ⟨G, hG, hfac⟩ := FourExpCauchy.factor S (analyticOrderNatAt F) F hF (fun a _ => by
    unfold analyticOrderNatAt
    generalize analyticOrderAt F a = x
    induction x using ENat.recTopCoe <;> simp)
  set N := ∑ z ∈ S, analyticOrderNatAt F z with hN
  have hR0 : 0 < R := by linarith
  have hRρ : 0 < R - ρ := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (c + R) (by simp [abs_of_pos hR0]))
  -- On the sphere of radius `R` every factor `z - a` has norm at least `R - ρ`.
  have hGsphere : ∀ z : ℂ, ‖z - c‖ = R → ‖G z‖ ≤ M / (R - ρ) ^ N := by
    intro z hz
    have hP : (R - ρ) ^ N ≤ ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ := by
      rw [norm_prod, hN, ← prod_pow_eq_pow_sum]
      refine prod_le_prod (fun _ _ => pow_nonneg hRρ.le _) (fun a ha => ?_)
      rw [norm_pow]
      apply pow_le_pow_left₀ hRρ.le
      have h1 := norm_sub_norm_le (z - c) (a - c)
      rw [show z - c - (a - c) = z - a by ring] at h1
      linarith [hS a ha]
    rw [le_div_iff₀ (pow_pos hRρ N)]
    calc ‖G z‖ * (R - ρ) ^ N
        ≤ ‖G z‖ * ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ :=
          mul_le_mul_of_nonneg_left hP (norm_nonneg _)
      _ = ‖F z‖ := by rw [hfac z, norm_mul, mul_comm]
      _ ≤ M := hM z hz
  -- Maximum principle for `G` on the disc of radius `R`.
  have hGball : ∀ w : ℂ, ‖w - c‖ ≤ R → ‖G w‖ ≤ M / (R - ρ) ^ N := by
    intro w hw
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG.diffContOnCl
      (fun y hy => hGsphere y (by
        rw [frontier_ball _ hR0.ne'] at hy
        simpa [mem_sphere_iff_norm] using hy))
      (by rw [closure_ball _ hR0.ne', mem_closedBall_iff_norm]; exact hw)
  -- On the unit sphere every factor `z - a` has norm at most `ρ + 1`.
  have hFsmall : ∀ z ∈ sphere c 1, ‖F z‖ ≤ ((ρ + 1) / (R - ρ)) ^ N * M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hP : ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ ≤ (ρ + 1) ^ N := by
      rw [norm_prod, hN, ← prod_pow_eq_pow_sum]
      refine prod_le_prod (fun _ _ => norm_nonneg _) (fun a ha => ?_)
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      have h1 := norm_sub_le (z - c) (a - c)
      rw [show z - c - (a - c) = z - a by ring] at h1
      linarith [hS a ha]
    have hGz := hGball z (by rw [hz]; linarith)
    calc ‖F z‖ = ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ * ‖G z‖ := by
          rw [hfac z, norm_mul]
      _ ≤ (ρ + 1) ^ N * (M / (R - ρ) ^ N) :=
          mul_le_mul hP hGz (norm_nonneg _) (pow_nonneg (by linarith) _)
      _ = ((ρ + 1) / (R - ρ)) ^ N * M := by rw [div_pow]; ring
  -- Cauchy's estimate on the unit circle; the factor `R / (R - 1) ≥ 1` is slack.
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le s one_pos
    hF.diffContOnCl hFsmall
  simp only [one_pow, div_one] at hC
  have hRR : 1 ≤ R / (R - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hK : 0 ≤ ((ρ + 1) / (R - ρ)) ^ N * M :=
    mul_nonneg (pow_nonneg (div_nonneg (by linarith) hRρ.le) _) hM0
  have hf : (0 : ℝ) ≤ s.factorial := by positivity
  calc ‖iteratedDeriv s F c‖ ≤ s.factorial * (((ρ + 1) / (R - ρ)) ^ N * M) := hC
    _ = s.factorial * 1 * (((ρ + 1) / (R - ρ)) ^ N * M) := by ring
    _ ≤ s.factorial * (R / (R - 1)) * (((ρ + 1) / (R - ρ)) ^ N * M) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRR hf) hK
    _ = s.factorial * (R / (R - 1)) * ((ρ + 1) / (R - ρ)) ^ N * M := by ring
end

-- Original source: archive/prove2me/Transcendence.expPoly_grid_estimate__a1309f19.lean
section
/-!
# A Cauchy estimate for an exponential polynomial on a grid

Let `F(z) = ∑ c_k z^(e_k) e^(ω_k z)` vanish to order `n` at every point `∑ m'_j y_j` with
`m'_j < t_j`. These `∏ t_j` points are distinct, since the `y_j` are `ℚ`-linearly independent, and
they lie within `ρ = ∑ A_j |y_j|` of the target `w = ∑ m_j y_j` (`m_j < A_j`). On the circle of
radius `R = (ρ + 1) u` about `w` we have `|z| ≤ Z`, so `|F(z)| ≤ (∑ |c_k|) Z^E e^(W Z)`. The Cauchy
estimate with zeros bounds `|F⁽ʳ⁾(w)|` by `r! · R/(R - 1) · ((ρ + 1)/(R - ρ))^(n ∏ t_j)` times this
maximum, and for `u ≥ 2` we have `R/(R - 1) ≤ 2` and `(ρ + 1)/(R - ρ) ≤ 1/(u - 1)`.
-/

theorem Transcendence.expPoly_grid_estimate {ι κ : Type*} [Fintype ι] (y : ι → ℂ)
    (hy : LinearIndependent ℚ y) (s : Finset κ) (c ω : κ → ℂ) (e : κ → ℕ) (F : ℂ → ℂ)
    (hF : ∀ z, F z = ∑ k ∈ s, c k * z ^ e k * Complex.exp (ω k * z))
    (W : ℝ) (E : ℕ) (hω : ∀ k ∈ s, ‖ω k‖ ≤ W) (he : ∀ k ∈ s, e k ≤ E)
    (t A : ι → ℕ) (htA : ∀ j, t j ≤ A j) (n : ℕ)
    (hvan : ∀ m : ι → ℕ, (∀ j, m j < t j) → ∀ i < n,
      iteratedDeriv i F (∑ j, (m j : ℂ) * y j) = 0)
    (u Z : ℝ) (hu : 2 ≤ u) (hZ : (∑ j, (A j : ℝ) * ‖y j‖ + 1) * (u + 1) ≤ Z)
    (m : ι → ℕ) (hm : ∀ j, m j < A j) (r : ℕ) :
    ‖iteratedDeriv r F (∑ j, (m j : ℂ) * y j)‖
      ≤ (r.factorial : ℝ) * 2 * (1 / (u - 1)) ^ ((∏ j, t j) * n) *
        ((∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z)) := by
  classical
  have hFd : Differentiable ℂ F := by
    rw [show F = fun z => ∑ k ∈ s, c k * z ^ e k * Complex.exp (ω k * z) from funext hF]
    fun_prop
  set ρ : ℝ := ∑ j, (A j : ℝ) * ‖y j‖ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  -- the lattice points `∑ m' j * y j`, `m' j < t j`, are pairwise distinct
  set P : Finset ℂ := (Fintype.piFinset fun j => Finset.range (t j)).image
    (fun m' : ι → ℕ => ∑ j, (m' j : ℂ) * y j) with hP
  have hcard : P.card = ∏ j, t j := by
    rw [hP, Finset.card_image_of_injective, Fintype.card_piFinset]
    · simp
    intro a b hab
    have := hy.fintypeLinearCombination_injective (a₁ := fun j => (a j : ℚ))
      (a₂ := fun j => (b j : ℚ)) (by simpa [Fintype.linearCombination_apply, Rat.smul_def] using hab)
    funext j; exact_mod_cast congrFun this j
  -- every point of the grid is within `ρ` of the target
  have hdist : ∀ m' : ι → ℕ, (∀ j, m' j < A j) →
      ‖∑ j, (m' j : ℂ) * y j - ∑ j, (m j : ℂ) * y j‖ ≤ ρ := by
    intro m' hm'
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← sub_mul, norm_mul, show (m' j : ℂ) - (m j : ℂ) = (((m' j : ℝ) - (m j : ℝ) : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    have a1 : (m' j : ℝ) < A j := by exact_mod_cast hm' j
    have a2 : (m j : ℝ) < A j := by exact_mod_cast hm j
    exact mul_le_mul_of_nonneg_right (abs_sub_le_iff.2 ⟨by linarith [(m j).cast_nonneg (α := ℝ)],
      by linarith [(m' j).cast_nonneg (α := ℝ)]⟩) (norm_nonneg _)
  have hw : ‖∑ j, (m j : ℂ) * y j‖ ≤ ρ := by
    simpa using hdist (fun _ => 0) fun j => (Nat.zero_le _).trans_lt (hm j)
  -- the bound on the circle of radius `(ρ + 1) * u` around the target
  have hZ1 : 1 ≤ Z := by nlinarith
  have hM : ∀ z : ℂ, ‖z - ∑ j, (m j : ℂ) * y j‖ = (ρ + 1) * u →
      ‖F z‖ ≤ (∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z) := by
    intro z hz
    have hzZ : ‖z‖ ≤ Z := by
      have := norm_le_insert' z (∑ j, (m j : ℂ) * y j)
      nlinarith
    rw [hF, Finset.sum_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
    gcongr
    · exact (pow_le_pow_left₀ (norm_nonneg _) hzZ _).trans (pow_le_pow_right₀ hZ1 (he k hk))
    · exact (Complex.re_le_norm _).trans (by
        rw [norm_mul]; exact mul_le_mul (hω k hk) hzZ (norm_nonneg _) ((norm_nonneg _).trans (hω k hk)))
  -- the target and the grid; every grid point is a zero of order at least `n`
  set w : ℂ := ∑ j, (m j : ℂ) * y j with hwdef
  set R : ℝ := (ρ + 1) * u with hR
  have hPw : ∀ z ∈ P, ‖z - w‖ ≤ ρ := fun z hz => by
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hz
    exact hdist m' fun j => ((by simpa using Fintype.mem_piFinset.1 hm' j) : m' j < t j).trans_le (htA j)
  have hM0 : 0 ≤ (∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z) := by
    have : 0 ≤ Z ^ E := pow_nonneg (by linarith) _
    positivity
  by_cases hF0 : F = 0
  · rw [hF0, iteratedDeriv_const_zero, norm_zero]
    have : 0 ≤ 1 / (u - 1) := div_nonneg zero_le_one (by linarith)
    positivity
  have hle : P.card * n ≤ ∑ z ∈ P, analyticOrderNatAt F z := by
    rw [← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun z hz => ?_
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hz
    have h1 := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hFd.analyticAt _)).2
      (hvan m' fun j => by simpa using Fintype.mem_piFinset.1 hm' j)
    rw [← Nat.cast_analyticOrderNatAt fun h => hF0
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero _ fun u => hFd.analyticAt u).1 h)] at h1
    exact_mod_cast h1
  -- the Cauchy estimate on the circle of radius `R = (ρ + 1) u` around the target
  have key := FourExp.cauchy_estimate_with_zeros F hFd w ρ R _ hρ0 (by nlinarith) P hPw hM r
  refine key.trans ?_
  have h1 : R / (R - 1) ≤ 2 := by rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have h2 : (ρ + 1) / (R - ρ) ≤ 1 / (u - 1) := by
    rw [div_le_div_iff₀ (by nlinarith) (by linarith)]; nlinarith
  have h3 : 0 ≤ (ρ + 1) / (R - ρ) := div_nonneg (by positivity) (by nlinarith)
  have h4 : (ρ + 1) / (R - ρ) ≤ 1 := h2.trans (by rw [div_le_one (by linarith)]; linarith)
  rw [← hcard]
  calc _ ≤ (r.factorial : ℝ) * 2 * ((ρ + 1) / (R - ρ)) ^ (P.card * n) *
        ((∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity))
          (pow_le_pow_of_le_one h3 h4 hle) (by positivity) (by positivity)) hM0
    _ ≤ _ := by gcongr
end

-- Original source: archive/prove2me/Transcendence.liouville_house__74580a12.lean
section
open NumberField

-- Liouville's inequality in house form, with an integer denominator: `N(cα)` is a nonzero
-- integer, and `|N(cα)| ≤ ‖σ(cα)‖ · house(cα)^(d-1)` (Mathlib's `norm_norm_le_norm_mul_house_pow`).
theorem Transcendence.liouville_house {K : Type*} [Field K] [NumberField K] {α : K} (hα : α ≠ 0)
    {c : ℤ} (hc : c ≠ 0) (hcα : IsIntegral ℤ ((c : K) * α)) (σ : K →+* ℂ) :
    1 ≤ |(c : ℝ)| ^ Module.finrank ℚ K * ‖σ α‖ * house α ^ (Module.finrank ℚ K - 1) := by
  set d := Module.finrank ℚ K
  have hd : 1 ≤ d := Module.finrank_pos
  set γ : 𝓞 K := ⟨(c : K) * α, hcα⟩
  have hγ0 : γ ≠ 0 := fun h ↦ mul_ne_zero (Int.cast_ne_zero.mpr hc) hα
    (show algebraMap (𝓞 K) K γ = 0 by rw [h, map_zero])
  have h1 : (1 : ℝ) ≤ ‖Algebra.norm ℚ ((c : K) * α)‖ := by
    have hne : Algebra.norm ℤ γ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hγ0
    rw [show (c : K) * α = algebraMap (𝓞 K) K γ from rfl, ← Algebra.coe_norm_int,
      ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  refine h1.trans ((norm_norm_le_norm_mul_house_pow _ σ).trans ?_)
  have hh : house ((c : K) * α) ≤ |(c : ℝ)| * house α := by
    simpa using house_mul_le (c : K) α
  calc ‖σ ((c : K) * α)‖ * house ((c : K) * α) ^ (d - 1)
      ≤ (|(c : ℝ)| * ‖σ α‖) * (|(c : ℝ)| * house α) ^ (d - 1) :=
        mul_le_mul (le_of_eq (by rw [map_mul, norm_mul, map_intCast, Complex.norm_intCast]))
          (pow_le_pow_left₀ (house_nonneg _) hh _) (pow_nonneg (house_nonneg _) _) (by positivity)
  _ = |(c : ℝ)| ^ d * ‖σ α‖ * house α ^ (d - 1) := by
        rw [mul_pow]; nth_rw 3 [show d = (d - 1) + 1 by omega]; ring
end

-- Original source: archive/prove2me/SX.descent_step__bec25c95.lean
section
open Complex

open NumberField

/-!
The descent step of the six exponentials theorem.

Suppose `F = expSum x L p` vanishes at the lattice points `∑ m j • y j` with every `m j < N`,
but not at some `w = ∑ m j • y j` with every `m j ≤ N`.
* Upper bound. `F` is an exponential polynomial with coefficients `p λ` and frequencies
  `⟨λ, x⟩` of modulus `≤ L X`, `X = ∑ |x i|`. The `N ^ l` zeros are distinct because the `y j` are
  ℚ-linearly independent, and the grid estimate with radius parameter `u = 3` gives
  `|F w| ≤ 2 · 2^(-N^l) · B e^{4 X (2Y + 1) L N}`, `Y = ∑ |y j|`, where `B = L^d e^{c L M}`
  bounds `∑ |p λ|`.
* Lower bound. `F w` is the image of `β = ∑ p λ ∏ θ_ij ^ (λ i m j)`, `θ_ij = exp (x i y j) ∈ K`.
  With a common denominator `b` of the `θ_ij`, `b^E β` (`E = d l L N`) is a nonzero algebraic
  integer of house `≤ B G^E`, and Liouville's inequality gives
  `1 ≤ G^E |F w| (B G^E)^([K:ℚ] - 1)`.
* Together, `2^(N^l) ≤ exp (C L N)`. With `L^d ≤ c M^l ≤ c N^l` and `d l ≥ d + l + 1` this forces
  `N (log 2)^d ≤ C^d c`, which fails once `N ≥ M ≥ M₀`.
-/

theorem SX.descent_step
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K)
    (c : ℝ) (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ L : ℕ, 0 < L → (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l →
      ∀ p : (Fin d → ℕ) → ℤ, (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) →
        ∀ N : ℕ, M ≤ N →
          (∀ m : Fin l → ℕ, (∀ j, m j < N) → SX.expSum x L p (SX.latticeSum y m) = 0) →
          (∀ m : Fin l → ℕ, (∀ j, m j < N + 1) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  classical
  have : NumberField K := {}
  set rk := Module.finrank ℚ K with hrk
  have hrk1 : 1 ≤ rk := Module.finrank_pos
  set σ : K →+* ℂ := K.val.toRingHom
  -- the numbers `exp (x i * y j)` as elements of `K`, a common denominator `b` and a house bound
  set θ : Fin d × Fin l → K := fun ij => ⟨Complex.exp (x ij.1 * y ij.2), hK ij.1 ij.2⟩ 
  obtain ⟨b, hb0, -, H, hH1, hbH⟩ := Transcendence.exists_denom_house_monomial_le θ
  set G : ℝ := max 1 (house b) * H
  have hHG : H ≤ G := le_mul_of_one_le_left (by positivity) (le_max_left 1 (house b))
  have hbG : house b ≤ G := (le_max_right 1 (house b)).trans (le_mul_of_one_le_right (by positivity) hH1)
  have hG1 : 1 ≤ G := hH1.trans hHG
  set X := ∑ i, ‖x i‖
  set Y := ∑ j, ‖y j‖
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  set C : ℝ := 1 + rk * (d + c) + 4 * X * (2 * Y + 1) + d * l * rk * Real.log G with hC
  have hC0 : 0 ≤ C := by have := Real.log_nonneg hG1; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨⌈C ^ d * c / Real.log 2 ^ d⌉₊ + 1, fun M hM L hL hLc p hp N hMN hvan m hm => ?_⟩
  by_contra hne
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_pos _).trans_le (hM.trans hMN)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set B : ℝ := (L : ℝ) ^ d * Real.exp (c * L * M) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (Real.one_le_exp (by positivity))
  have hpB : ∑ lam ∈ SX.box d L, |(p lam : ℝ)| ≤ B := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun lam _ => hp lam).trans_eq ?_
    simp [SX.box, Fintype.card_piFinset, hB]
  -- the analytic upper bound: the grid estimate with `u = 3`
  have hup : ‖SX.expSum x L p (SX.latticeSum y m)‖
      ≤ 2 * (1 / 2) ^ (N ^ l) * (B * Real.exp (L * X * (4 * N * (2 * Y + 1)))) := by
    have h := Transcendence.expPoly_grid_estimate y hy (SX.box d L) (fun lam => (p lam : ℂ))
      (SX.expExponent x) (fun _ => 0) (SX.expSum x L p) (fun z => by simp [SX.expSum]) (L * X) 0
      (fun lam hlam => ?_) (fun _ _ => le_rfl) (fun _ => N) (fun _ => N + 1) (fun _ => N.le_succ) 1
      (fun m' hm' i hi => ?_) 3 (4 * N * (2 * Y + 1)) (by norm_num) ?_ m hm 0
    · simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, Complex.norm_intCast] at h
      norm_num at h
      refine h.trans ?_
      gcongr
    · rw [SX.mem_box] at hlam
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans_eq (Finset.mul_sum _ _ _).symm)
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hlam i).le) (norm_nonneg _)
    · rw [Nat.lt_one_iff.1 hi, iteratedDeriv_zero]; exact hvan m' hm'
    · rw [← Finset.mul_sum]; push_cast; nlinarith
  -- the arithmetic lower bound: the value lies in `K` and Liouville's inequality applies
  set E : ℕ := d * l * L * N with hE
  set β : K := ∑ lam ∈ SX.box d L, (p lam : K) * ∏ ij, θ ij ^ (lam ij.1 * m ij.2) with hβ
  have heE : ∀ lam ∈ SX.box d L, ∑ ij : Fin d × Fin l, lam ij.1 * m ij.2 ≤ E := fun lam hlam =>
    (Finset.sum_le_card_nsmul _ _ (L * N) fun ij _ => Nat.mul_le_mul ((SX.mem_box.1 hlam) ij.1).le
      (Nat.lt_succ_iff.1 (hm ij.2))).trans_eq (by simp [hE]; ring)
  have hσβ : σ β = SX.expSum x L p (SX.latticeSum y m) := by
    rw [hβ, SX.expSum, map_sum]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [map_mul, map_intCast, map_prod, SX.exp_expExponent_mul_latticeSum, Fintype.prod_prod_type]
    rfl
  have hβ0 : β ≠ 0 := fun h => hne (by rw [← hσβ, h, map_zero])
  have hδ : b ^ E * β = ∑ lam ∈ SX.box d L, (p lam : K) * (b ^ E * ∏ ij, θ ij ^ (lam ij.1 * m ij.2)) := by
    rw [hβ, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hint : IsIntegral ℤ (((1 : ℤ) : K) * (b ^ E * β)) := by
    rw [Int.cast_one, one_mul, hδ]
    exact IsIntegral.sum _ fun lam hlam =>
      (isIntegral_algebraMap (x := p lam)).mul (hbH _ E (heE lam hlam)).1
  have hhouse : house (b ^ E * β) ≤ B * G ^ E := by
    rw [hδ]
    refine (house_sum_le_sum_house _ _).trans ((Finset.sum_le_sum (g := fun lam => |(p lam : ℝ)| * G ^ E)
      fun lam hlam => (house_mul_le _ _).trans ?_).trans ?_)
    · rw [house_intCast, Int.cast_abs]
      exact mul_le_mul_of_nonneg_left ((hbH _ E (heE lam hlam)).2.trans (by gcongr)) (abs_nonneg _)
    · rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hpB (by positivity)
  have hliou := Transcendence.liouville_house (mul_ne_zero (pow_ne_zero E hb0) hβ0) one_ne_zero hint σ
  rw [Int.cast_one, abs_one, one_pow, one_mul, map_mul, map_pow, norm_mul, norm_pow, hσβ] at hliou
  -- combining the two bounds: `2 ^ (N ^ l) ≤ exp (C L N)`
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hrk1
  have hLN : (1 : ℝ) ≤ L * N := one_le_mul_of_one_le_of_one_le hL1 hN1
  have hBexp : B ≤ Real.exp ((d + c) * (L * N)) := by
    have h1 : (L : ℝ) ≤ Real.exp (L * N) :=
      (by linarith [Real.add_one_le_exp ((L : ℝ) - 1)] : (L : ℝ) ≤ Real.exp (L - 1)).trans
        (Real.exp_le_exp.2 (by nlinarith))
    have h2 : c * L * M ≤ c * (L * N) := by
      rw [mul_assoc]; gcongr
    rw [add_mul, Real.exp_add, hB, Real.exp_nat_mul]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1 d) (Real.exp_le_exp.2 h2) (by positivity)
      (by positivity)
  have hkey : (2 : ℝ) ^ (N ^ l) ≤ Real.exp (C * (L * N)) := by
    have hσb : ‖σ b‖ ^ E ≤ G ^ E := pow_le_pow_left₀ (norm_nonneg _) ((norm_embedding_le_house b σ).trans hbG) E
    have hG0 : 0 ≤ G := by linarith
    have hB0 : 0 ≤ B := by linarith
    have h1 := hliou.trans (mul_le_mul (mul_le_mul hσb hup (norm_nonneg _) (pow_nonneg hG0 E))
      (pow_le_pow_left₀ (house_nonneg _) hhouse _) (pow_nonneg (house_nonneg _) _) (by positivity))
    rw [← hrk, hk, Nat.add_sub_cancel_left] at h1
    calc (2 : ℝ) ^ (N ^ l) ≤ 2 ^ (N ^ l) * (G ^ E * (2 * (1 / 2) ^ (N ^ l) *
          (B * Real.exp (L * X * (4 * N * (2 * Y + 1))))) * (B * G ^ E) ^ k) := by
          simpa using mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ (N ^ l))
      _ = 2 * B ^ (1 + k) * G ^ (E * (1 + k)) * Real.exp (L * X * (4 * N * (2 * Y + 1))) := by
          rw [mul_pow B (G ^ E) k, ← pow_mul G E k, one_div, inv_pow]; field_simp; ring
      _ ≤ Real.exp (L * N) * Real.exp ((d + c) * (L * N)) ^ (1 + k) *
          Real.exp (G.log) ^ (E * (1 + k)) * Real.exp (L * X * (4 * N * (2 * Y + 1))) := by
          rw [Real.exp_log (by positivity)]
          gcongr
          exact (by linarith [Real.add_one_le_exp 1] : (2 : ℝ) ≤ Real.exp 1).trans (Real.exp_le_exp.2 hLN)
      _ = Real.exp (C * (L * N)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
            hC, hk, hE]
          push_cast; ring_nf
  -- the endgame: `N ^ l log 2 ≤ C L N` and `L ^ d ≤ c N ^ l` force `N (log 2) ^ d ≤ C ^ d c`
  have h2 : (N : ℝ) ^ l * Real.log 2 ≤ C * (L * N) := by
    have := Real.log_le_log (by positivity) hkey
    rwa [Real.log_pow, Real.log_exp, Nat.cast_pow] at this
  have hLc' : (L : ℝ) ^ d ≤ c * N ^ l := hLc.trans (by gcongr)
  have hNd : (N : ℝ) ^ (l + d) * N ≤ N ^ (l * d) := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hN1 (by rw [Nat.mul_comm]; omega)
  have hend : (N : ℝ) * Real.log 2 ^ d ≤ C ^ d * c := by
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < N ^ (l + d))
    calc (N : ℝ) ^ (l + d) * (N * Real.log 2 ^ d) = (N ^ (l + d) * N) * Real.log 2 ^ d := by ring
      _ ≤ N ^ (l * d) * Real.log 2 ^ d := by gcongr
      _ = ((N : ℝ) ^ l * Real.log 2) ^ d := by rw [mul_pow, ← pow_mul]
      _ ≤ (C * (L * N)) ^ d := by gcongr
      _ = C ^ d * (L : ℝ) ^ d * (N : ℝ) ^ d := by rw [mul_pow, mul_pow, ← mul_assoc]
      _ ≤ C ^ d * (c * (N : ℝ) ^ l) * (N : ℝ) ^ d := by gcongr
      _ = (N : ℝ) ^ (l + d) * (C ^ d * c) := by ring
  have hlt : C ^ d * c / Real.log 2 ^ d < N := by
    have h3 : ((⌈C ^ d * c / Real.log 2 ^ d⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hM.trans hMN
    push_cast at h3
    linarith [Nat.le_ceil (C ^ d * c / Real.log 2 ^ d)]
  rw [div_lt_iff₀ (by positivity)] at hlt
  linarith
end

-- Original source: archive/prove2me/SX.eq_zero_of_expSum_vanishes__b95d3c48.lean
section
open Complex

namespace ZeroAux

variable {d l : ℕ}

/-- The character attached to a multi-index: `m ↦ exp (⟨λ,x⟩ * ⟨m,y⟩)`, a monoid
homomorphism out of `ℕ^l` written multiplicatively. -/
noncomputable def chi (x : Fin d → ℂ) (y : Fin l → ℂ) (lam : Fin d → ℕ) :
    Multiplicative (Fin l → ℕ) →* ℂ where
  toFun m := Complex.exp (SX.expExponent x lam * SX.latticeSum y (Multiplicative.toAdd m))
  map_one' := by
    show Complex.exp (SX.expExponent x lam * SX.latticeSum y 0) = 1
    simp [SX.latticeSum]
  map_mul' a b := by
    have hadd : SX.latticeSum y (Multiplicative.toAdd a + Multiplicative.toAdd b)
        = SX.latticeSum y (Multiplicative.toAdd a) + SX.latticeSum y (Multiplicative.toAdd b) := by
      simp only [SX.latticeSum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply]
      push_cast; ring
    show Complex.exp _ = Complex.exp _ * Complex.exp _
    rw [show Multiplicative.toAdd (a * b)
          = Multiplicative.toAdd a + Multiplicative.toAdd b from rfl,
      hadd, mul_add, Complex.exp_add]

end ZeroAux

open ZeroAux in
theorem SX.eq_zero_of_expSum_vanishes
    {d l : ℕ} (hl : 2 ≤ l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (L : ℕ) (p : (Fin d → ℕ) → ℤ)
    (h : ∀ m : Fin l → ℕ, SX.expSum x L p (SX.latticeSum y m) = 0) :
    ∀ lam ∈ SX.box d L, p lam = 0 := by
  classical
  -- `λ ↦ χ_λ` is injective; this is where `hx`, `hy` and `2 ≤ l` are spent
  have hinj : Function.Injective (chi x y (l := l)) := by
    intro lam mu hEq
    -- evaluating at the unit vectors: `(A - B) * y j ∈ 2πi ℤ`
    have hval : ∀ j : Fin l, ∃ n : ℤ,
        (SX.expExponent x lam - SX.expExponent x mu) * y j
          = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      intro j
      have hls : SX.latticeSum y
          (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single j (1 : ℕ)))) = y j := by
        show SX.latticeSum y (Pi.single j (1 : ℕ)) = y j
        rw [SX.latticeSum, Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (Finset.mem_univ j) hb
      have hpt := DFunLike.congr_fun hEq (Multiplicative.ofAdd (Pi.single j (1 : ℕ)))
      simp only [chi, MonoidHom.coe_mk, OneHom.coe_mk, hls] at hpt
      have h1 : Complex.exp ((SX.expExponent x lam - SX.expExponent x mu) * y j) = 1 := by
        rw [sub_mul, Complex.exp_sub, hpt, div_self (Complex.exp_ne_zero _)]
      exact Complex.exp_eq_one_iff.mp h1
    by_cases hAB : SX.expExponent x lam - SX.expExponent x mu = 0
    · -- `⟨λ - μ, x⟩ = 0`, so `λ = μ` by `ℚ`-linear independence of `x`
      have hAB0 : ∑ i, (lam i : ℂ) * x i = ∑ i, (mu i : ℂ) * x i := by
        simpa [SX.expExponent] using sub_eq_zero.mp hAB
      have key : ∑ i, (((lam i : ℚ) - (mu i : ℚ))) • x i = (0 : ℂ) := by
        have e : ∀ i : Fin d, (((lam i : ℚ) - (mu i : ℚ))) • x i
            = (lam i : ℂ) * x i - (mu i : ℂ) * x i := by
          intro i; rw [Rat.smul_def]; push_cast; ring
        simp only [e, Finset.sum_sub_distrib, hAB0, sub_self]
      have hz := (Fintype.linearIndependent_iff.mp hx) (fun i => (lam i : ℚ) - (mu i : ℚ)) key
      funext i
      have : (lam i : ℚ) = (mu i : ℚ) := sub_eq_zero.mp (hz i)
      exact_mod_cast this
    · exfalso
      have hi0 : (0 : ℕ) < l := by omega
      have hi1 : (1 : ℕ) < l := by omega
      set i0 : Fin l := ⟨0, hi0⟩ with hi0def
      set i1 : Fin l := ⟨1, hi1⟩ with hi1def
      have hne : i0 ≠ i1 := by simp [hi0def, hi1def, Fin.ext_iff]
      obtain ⟨n0, hn0⟩ := hval i0
      obtain ⟨n1, hn1⟩ := hval i1
      have hcomb : (n1 : ℂ) * y i0 - (n0 : ℂ) * y i1 = 0 := by
        have hw : (SX.expExponent x lam - SX.expExponent x mu)
            * ((n1 : ℂ) * y i0 - (n0 : ℂ) * y i1) = 0 := by
          have hr : (SX.expExponent x lam - SX.expExponent x mu)
              * ((n1 : ℂ) * y i0 - (n0 : ℂ) * y i1)
              = (n1 : ℂ) * ((SX.expExponent x lam - SX.expExponent x mu) * y i0)
                - (n0 : ℂ) * ((SX.expExponent x lam - SX.expExponent x mu) * y i1) := by ring
          rw [hr, hn0, hn1]; ring
        rcases mul_eq_zero.mp hw with h1 | h1
        · exact absurd h1 hAB
        · exact h1
      set g : Fin l → ℚ :=
        fun j => if j = i0 then (n1 : ℚ) else if j = i1 then -(n0 : ℚ) else 0 with hgdef
      have hsum : ∑ j, g j • y j = (0 : ℂ) := by
        rw [← Finset.sum_subset (Finset.subset_univ ({i0, i1} : Finset (Fin l)))]
        · rw [Finset.sum_pair hne]
          simp only [hgdef, if_pos rfl, if_neg hne, if_neg (Ne.symm hne)]
          rw [Rat.smul_def, Rat.smul_def]
          push_cast
          linear_combination hcomb
        · intro j _ hj
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
          simp [hgdef, hj.1, hj.2]
      have hg := (Fintype.linearIndependent_iff.mp hy) g hsum
      have hn0z : n0 = 0 := by
        have := hg i1
        simp only [hgdef, if_neg (Ne.symm hne), if_pos rfl] at this
        exact_mod_cast neg_eq_zero.mp this
      have hy0 : y i0 = 0 := by
        have : (SX.expExponent x lam - SX.expExponent x mu) * y i0 = 0 := by
          rw [hn0, hn0z]; simp
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 hAB
        · exact h1
      exact hy.ne_zero i0 hy0
  -- Dedekind independence of characters, transported along the injection
  have hli : LinearIndependent ℂ (fun lam : Fin d → ℕ => ⇑(chi x y lam)) :=
    (linearIndependent_monoidHom (Multiplicative (Fin l → ℕ)) ℂ).comp _ hinj
  have hzero : ∑ lam ∈ SX.box d L, ((p lam : ℂ)) • (⇑(chi x y lam)) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, chi,
      MonoidHom.coe_mk, OneHom.coe_mk]
    exact h (Multiplicative.toAdd m)
  intro lam hlam
  have := linearIndependent_iff'.mp hli (SX.box d L) (fun lam => (p lam : ℂ)) hzero lam hlam
  exact_mod_cast this
end

-- Original source: archive/prove2me/SX.six_exponentials_of_numberField__e54a15db.lean
section
/-! Assembly check: rung 2 from rungs 3, 4, 5. -/

open Complex

theorem SX.six_exponentials_of_numberField
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    ∃ i j, Complex.exp (x i * y j) ∉ K := by
  classical
  have hl2 : 2 ≤ l := by
    by_contra hcl
    push_neg at hcl
    interval_cases l <;> omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc, M₁, haux⟩ := SX.exists_aux_expSum hdl x y hx hy K hcon
  obtain ⟨M₀, hdesc⟩ := SX.descent_step hdl x y hx hy K hcon c hc
  set M : ℕ := max M₀ M₁ + 1 with hMdef
  obtain ⟨L, hL0, hLc, p, ⟨lam0, hlam0mem, hlam0⟩, hph, hvan⟩ :=
    haux M (by omega)
  have key : ∀ N : ℕ, M ≤ N →
      ∀ m : Fin l → ℕ, (∀ j, m j < N) → SX.expSum x L p (SX.latticeSum y m) = 0 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact hvan
    | succ N hN ih => exact hdesc M (by omega) L hL0 hLc p hph N hN ih
  have hall : ∀ m : Fin l → ℕ, SX.expSum x L p (SX.latticeSum y m) = 0 := by
    intro m
    refine key (max M (Finset.univ.sup m + 1)) (le_max_left _ _) m fun j => ?_
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j)))
      (le_max_right _ _)
  exact hlam0 (SX.eq_zero_of_expSum_vanishes hl2 x y hx hy L p hall lam0 hlam0mem)
end

-- Original source: archive/prove2me/DiazModulus.six_exponentials__b4ee3ac8.lean
section
/-! Assembly check: the target from rung 2. -/

open Complex ComplexConjugate

theorem DiazModulus.six_exponentials (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) := by
  classical
  by_contra hcon
  simp only [Transcendental, not_exists, not_not] at hcon
  set S : Set ℂ := Set.range (fun q : Fin 2 × Fin 3 => Complex.exp (x q.1 * y q.2)) with hS
  have hSfin : S.Finite := Set.finite_range _
  haveI : Finite S := hSfin.to_subtype
  have hint : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro z ⟨q, rfl⟩
    exact (hcon q.1 q.2).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hint
  obtain ⟨i, j, hij⟩ :=
    SX.six_exponentials_of_numberField (d := 2) (l := 3) (by omega) x y hx hy
      (IntermediateField.adjoin ℚ S)
  exact hij (IntermediateField.subset_adjoin ℚ S ⟨(i, j), rfl⟩)
end

/-

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      “License” shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      “Licensor” shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      “Legal Entity” shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      “control” means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      “You” (or “Your”) shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      “Source” form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      “Object” form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      “Work” shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      “Derivative Works” shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, [e]laborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      “Contribution” shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, “submitted”
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as “Not a Contribution.”

      “Contributor” shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a “NOTICE” text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an “AS IS” BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets “[]”
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment [s]yntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same “printed page” as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the “License”);
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an “AS IS” BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

namespace OMAColossal

/-! ### Six exponentials for three distinct primes -/

lemma primeValue (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    padicValRat p (q : ℚ) = if p = q then 1 else 0 := by
  rw [padicValRat.of_nat]
  split_ifs with h
  · subst q
    simp
  · simp [padicValNat_primes h]

lemma primeProductVal (p q r : ℕ) [Fact p.Prime] [Fact q.Prime] [Fact r.Prime]
    (a b c : ℤ) (s : ℕ) [Fact s.Prime]
    (h : (p : ℚ) ^ a * (q : ℚ) ^ b * (r : ℚ) ^ c = 1) :
    a * (if s = p then 1 else 0) + b * (if s = q then 1 else 0) +
      c * (if s = r then 1 else 0) = 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : r.Prime).ne_zero
  have hv := congrArg (padicValRat s) h
  rw [padicValRat.mul (mul_ne_zero (zpow_ne_zero _ hp0) (zpow_ne_zero _ hq0))
      (zpow_ne_zero _ hr0),
    padicValRat.mul (zpow_ne_zero _ hp0) (zpow_ne_zero _ hq0)] at hv
  have vp : padicValRat s p = if s = p then 1 else 0 := primeValue s p
  have vq : padicValRat s q = if s = q then 1 else 0 := primeValue s q
  have vr : padicValRat s r = if s = r then 1 else 0 := primeValue s r
  simpa only [padicValRat.zpow, padicValRat.one, vp, vq, vr] using hv

lemma logsIndependent {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    LinearIndependent ℚ ![Complex.log p, Complex.log q, Complex.log r] := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Fact r.Prime := ⟨hr⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne_zero
  apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have he := congrArg Complex.exp hf
  simp [Fin.sum_univ_succ, zsmul_eq_mul, Complex.exp_add, Complex.exp_int_mul,
    Complex.exp_log hp0, Complex.exp_log hq0, Complex.exp_log hr0] at he
  have hrat : (p : ℚ) ^ f 0 * (q : ℚ) ^ f 1 * (r : ℚ) ^ f 2 = 1 := by
    apply Rat.cast_injective (α := ℂ)
    push_cast
    exact (mul_assoc _ _ _).trans he
  have e1 := primeProductVal p q r _ _ _ p hrat
  have e2 := primeProductVal p q r _ _ _ q hrat
  have e3 := primeProductVal p q r _ _ _ r hrat
  simp only [if_true, if_neg hpq, if_neg hpr, if_neg hqr, if_neg hpq.symm, if_neg hpr.symm,
    if_neg hqr.symm, mul_one, mul_zero, add_zero, zero_add] at e1 e2 e3
  fin_cases i
  · exact e1
  · exact e2
  · exact e3

lemma expOfRatPower {x : ℝ} {p : ℕ} {t : ℚ} (hp : 0 < p) (ht : (p : ℝ) ^ x = t) :
    IsAlgebraic ℚ (Complex.exp ((x : ℂ) * Complex.log p)) := by
  have hlog : (Real.log (p : ℝ) : ℂ) = Complex.log p := Complex.natCast_log
  have he : Complex.exp ((x : ℂ) * Complex.log p) = (t : ℂ) := by
    rw [← hlog, ← Complex.ofReal_mul, ← Complex.ofReal_exp, mul_comm,
      ← Real.rpow_def_of_pos (by exact_mod_cast hp), ht, Complex.ofReal_ratCast]
  rw [he]
  exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) t

/-- If `p ^ x`, `q ^ x`, `r ^ x` are rational for three distinct primes, then `x` is rational. -/
lemma exponentRational {x : ℝ} {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h1 : ∃ t : ℚ, (p : ℝ) ^ x = t) (h2 : ∃ t : ℚ, (q : ℝ) ^ x = t)
    (h3 : ∃ t : ℚ, (r : ℝ) ^ x = t) : ∃ u : ℚ, x = u := by
  by_contra hx
  have hu : LinearIndependent ℚ ![(1 : ℂ), (x : ℂ)] := by
    apply (LinearIndependent.pair_iff' one_ne_zero).mpr
    intro u hu
    apply hx
    refine ⟨u, ?_⟩
    simpa [Algebra.smul_def] using congrArg Complex.re hu.symm
  obtain ⟨i, j, hij⟩ :=
    DiazModulus.six_exponentials _ _ hu (logsIndependent hp hq hr hpq hpr hqr)
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  obtain ⟨t3, ht3⟩ := h3
  apply hij
  fin_cases i
  · fin_cases j
    · simpa using (expOfRatPower (p := p) (t := p) (x := 1) hp.pos (by simp))
    · simpa using (expOfRatPower (p := q) (t := q) (x := 1) hq.pos (by simp))
    · simpa using (expOfRatPower (p := r) (t := r) (x := 1) hr.pos (by simp))
  · fin_cases j
    · exact expOfRatPower hp.pos ht1
    · exact expOfRatPower hq.pos ht2
    · exact expOfRatPower hr.pos ht3

/-! ### The geometric sums `1 + p + ... + p ^ a` and the divisor sum -/

/-- `gs p a = 1 + p + ... + p ^ a`, the sum of divisors of `p ^ a` for prime `p`. -/
def gs (p a : ℕ) : ℕ := ∑ i ∈ Finset.range (a + 1), p ^ i

lemma gs_zero (p : ℕ) : gs p 0 = 1 := by simp [gs]

lemma gs_succ (p a : ℕ) : gs p (a + 1) = p * gs p a + 1 := by
  unfold gs
  rw [Finset.sum_range_succ' _ (a + 1), Finset.mul_sum]
  simp [pow_succ']

lemma gs_pos (p a : ℕ) : 0 < gs p a := by
  cases a with
  | zero => simp [gs_zero]
  | succ a => rw [gs_succ]; omega

lemma gs_strictMono {p : ℕ} (hp : 0 < p) : StrictMono (gs p) := by
  apply strictMono_nat_of_lt_succ
  intro a
  rw [gs_succ]
  have h1 := gs_pos p a
  have h2 : 1 * gs p a ≤ p * gs p a := Nat.mul_le_mul_right _ hp
  omega

lemma sigma_prime_mul {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    ArithmeticFunction.sigma 1 (p * m) * gs p (m.factorization p) =
      ArithmeticFunction.sigma 1 m * gs p (m.factorization p + 1) := by
  obtain ⟨e, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  have hm0 : m' ≠ 0 := by
    rintro rfl
    simp at hm
  have hfac : (p ^ e * m').factorization p = e := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0]
    simp [hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hm']
  have hcop : ∀ k, Nat.Coprime (p ^ k) m' := fun k =>
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hm')
  rw [hfac, show p * (p ^ e * m') = p ^ (e + 1) * m' by ring,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop _),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop _),
    ArithmeticFunction.sigma_one_apply_prime_pow hp,
    ArithmeticFunction.sigma_one_apply_prime_pow hp]
  unfold gs
  ring

/-! ### The quotient `σ(n) / n ^ (1 + ε)` -/

/-- The quantity being maximized. -/
noncomputable def F (ε : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.sigma 1 n : ℝ) / (n : ℝ) ^ (1 + ε)

lemma F_one (ε : ℝ) : F ε 1 = 1 := by simp [F]

lemma F_pos (ε : ℝ) {n : ℕ} (hn : n ≠ 0) : 0 < F ε n := by
  unfold F
  have h1 : (0 : ℝ) < (ArithmeticFunction.sigma 1 n : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn
  have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  exact div_pos h1 (Real.rpow_pos_of_pos h2 _)

lemma F_prime_mul (ε : ℝ) {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    F ε (p * m) * ((gs p (m.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε)) =
      F ε m * ((p : ℝ) * (gs p (m.factorization p) : ℝ) + 1) := by
  have hs := sigma_prime_mul hp hm
  rw [gs_succ] at hs
  have hsR : (ArithmeticFunction.sigma 1 (p * m) : ℝ) * (gs p (m.factorization p) : ℝ) =
      (ArithmeticFunction.sigma 1 m : ℝ) * ((p : ℝ) * (gs p (m.factorization p) : ℝ) + 1) := by
    exact_mod_cast hs
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hpow : ((p * m : ℕ) : ℝ) ^ (1 + ε) = (p : ℝ) * (p : ℝ) ^ ε * (m : ℝ) ^ (1 + ε) := by
    rw [Nat.cast_mul, Real.mul_rpow hp0.le hm0.le, Real.rpow_add hp0, Real.rpow_one]
  have h1 : 0 < (p : ℝ) ^ ε := Real.rpow_pos_of_pos hp0 _
  have h2 : 0 < (m : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hm0 _
  unfold F
  rw [hpow]
  field_simp
  linear_combination hsR

/-- `n` maximizes `F ε` over all positive integers. -/
def IsMax (ε : ℝ) (n : ℕ) : Prop := n ≠ 0 ∧ ∀ k : ℕ, k ≠ 0 → F ε k ≤ F ε n

lemma max_lower {ε : ℝ} {n p : ℕ} (hn : IsMax ε n) (hp : p.Prime) :
    1 ≤ (gs p (n.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) := by
  have h := F_prime_mul ε hp hn.1
  have hle := hn.2 (p * n) (mul_ne_zero hp.ne_zero hn.1)
  have hF := F_pos ε hn.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hg : (0 : ℝ) < (gs p (n.factorization p) : ℝ) := by exact_mod_cast gs_pos p _
  have hgP : 0 < (gs p (n.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε) :=
    mul_pos hg (mul_pos hp0 (Real.rpow_pos_of_pos hp0 _))
  have h3 : F ε n * ((p : ℝ) * (gs p (n.factorization p) : ℝ) + 1) ≤
      F ε n * ((gs p (n.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε)) := by
    rw [← h]
    exact mul_le_mul_of_nonneg_right hle hgP.le
  have h4 := le_of_mul_le_mul_left h3 hF
  linarith

lemma max_upper {ε : ℝ} {m p : ℕ} (hp : p.Prime) (hn : IsMax ε (p * m)) :
    (gs p (m.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) ≤ 1 := by
  have hm : m ≠ 0 := fun h => hn.1 (by simp [h])
  have h := F_prime_mul ε hp hm
  have hle := hn.2 m hm
  have hF := F_pos ε hm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hg : (0 : ℝ) < (gs p (m.factorization p) : ℝ) := by exact_mod_cast gs_pos p _
  have hgP : 0 < (gs p (m.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε) :=
    mul_pos hg (mul_pos hp0 (Real.rpow_pos_of_pos hp0 _))
  have h3 : F ε m * ((gs p (m.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε)) ≤
      F ε m * ((p : ℝ) * (gs p (m.factorization p) : ℝ) + 1) := by
    rw [← h]
    exact mul_le_mul_of_nonneg_right hle hgP.le
  have h4 := le_of_mul_le_mul_left h3 hF
  linarith

/-- `p` is a tie prime: some exponent `a` makes multiplying by `p` leave `F ε` unchanged. -/
def Tie (ε : ℝ) (p : ℕ) : Prop :=
  ∃ a : ℕ, (gs p a : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) = 1

lemma val_step {ε : ℝ} {n n' p : ℕ} (hn : IsMax ε n) (hn' : IsMax ε n')
    (hp : p.Prime) (hlt : n.factorization p < n'.factorization p) :
    n'.factorization p = n.factorization p + 1 ∧
      (gs p (n.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) = 1 := by
  have hdvd : p ∣ n' := Nat.dvd_of_factorization_pos (by omega)
  obtain ⟨m, rfl⟩ := hdvd
  have hm : m ≠ 0 := fun h => hn'.1 (by simp [h])
  have hfac : (p * m).factorization p = m.factorization p + 1 := by
    rw [Nat.factorization_mul hp.ne_zero hm]
    simp [hp.factorization_self, add_comm]
  rw [hfac] at hlt ⊢
  have hle : n.factorization p ≤ m.factorization p := by omega
  have h1 := max_lower hn hp
  have h2 := max_upper hp hn'
  have hmono : (gs p (n.factorization p) : ℝ) ≤ (gs p (m.factorization p) : ℝ) := by
    exact_mod_cast (gs_strictMono hp.pos).monotone hle
  have hgpos : (0 : ℝ) < (gs p (n.factorization p) : ℝ) := by exact_mod_cast gs_pos p _
  have hc : 0 < (p : ℝ) * (p : ℝ) ^ ε - p := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have h3 : (gs p (n.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) ≤
      (gs p (m.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) :=
    mul_le_mul_of_nonneg_right hmono hc.le
  have h4 : (gs p (n.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) = 1 := by linarith
  have h5 : (gs p (m.factorization p) : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) = 1 := by linarith
  have h6 : (gs p (n.factorization p) : ℝ) = (gs p (m.factorization p) : ℝ) :=
    mul_right_cancel₀ hc.ne' (h4.trans h5.symm)
  have h7 : gs p (n.factorization p) = gs p (m.factorization p) := by exact_mod_cast h6
  exact ⟨by rw [(gs_strictMono hp.pos).injective h7], h4⟩

lemma tie_unique {ε : ℝ} {p a b : ℕ} (hp : p.Prime)
    (ha : (gs p a : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) = 1)
    (hb : (gs p b : ℝ) * ((p : ℝ) * (p : ℝ) ^ ε - p) = 1) : a = b := by
  have hc : (p : ℝ) * (p : ℝ) ^ ε - p ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have h6 : (gs p a : ℝ) = (gs p b : ℝ) := mul_right_cancel₀ hc (ha.trans hb.symm)
  have h7 : gs p a = gs p b := by exact_mod_cast h6
  exact (gs_strictMono hp.pos).injective h7

lemma const_of_not_tie {ε : ℝ} {n n' p : ℕ} (hn : IsMax ε n) (hn' : IsMax ε n')
    (hp : p.Prime) (hT : ¬ Tie ε p) : n.factorization p = n'.factorization p := by
  rcases lt_trichotomy (n.factorization p) (n'.factorization p) with h | h | h
  · exact (hT ⟨_, (val_step hn hn' hp h).2⟩).elim
  · exact h
  · exact (hT ⟨_, (val_step hn' hn hp h).2⟩).elim

lemma two_values (ε : ℝ) (p : ℕ) :
    ∃ a : ℕ, ∀ n : ℕ, IsMax ε n → n.factorization p = a ∨ n.factorization p = a + 1 := by
  by_cases hp : p.Prime
  · by_cases h : ∃ n n' : ℕ, IsMax ε n ∧ IsMax ε n' ∧ n.factorization p < n'.factorization p
    · obtain ⟨n, n', hn, hn', hlt⟩ := h
      have hstep := val_step hn hn' hp hlt
      refine ⟨n.factorization p, fun m hm => ?_⟩
      rcases lt_trichotomy (m.factorization p) (n.factorization p) with h1 | h1 | h1
      · have := tie_unique hp (val_step hm hn hp h1).2 hstep.2
        omega
      · exact Or.inl h1
      · exact Or.inr (val_step hn hm hp h1).1
    · by_cases hne : ∃ n : ℕ, IsMax ε n
      · obtain ⟨n, hn⟩ := hne
        refine ⟨n.factorization p, fun m hm => Or.inl ?_⟩
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h1 | h1
        · exact h ⟨m, n, hm, hn, h1⟩
        · exact h ⟨n, m, hn, hm, h1⟩
      · exact ⟨0, fun m hm => (hne ⟨m, hm⟩).elim⟩
  · exact ⟨0, fun n _ => Or.inl (Nat.factorization_eq_zero_of_not_prime n hp)⟩

/-! ### Tie primes and six exponentials -/

lemma tie_rpow_rat {ε : ℝ} {p : ℕ} (hp : p.Prime) (hT : Tie ε p) :
    ∃ t : ℚ, (p : ℝ) ^ ε = t := by
  obtain ⟨a, ha⟩ := hT
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hg : (0 : ℝ) < (gs p a : ℝ) := by exact_mod_cast gs_pos p _
  refine ⟨((p * gs p a + 1 : ℕ) : ℚ) / ((p * gs p a : ℕ) : ℚ), ?_⟩
  push_cast
  field_simp
  linarith

lemma tie_not_rat {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) (hT : Tie ε p)
    (hrat : ∃ u : ℚ, ε = u) : False := by
  obtain ⟨a, ha⟩ := hT
  obtain ⟨u, rfl⟩ := hrat
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set N : ℕ := p * gs p a with hN
  have hNeq : (p : ℝ) ^ (u : ℝ) * (N : ℝ) = (N : ℝ) + 1 := by
    rw [hN]
    push_cast
    linarith
  have hnum : 0 ≤ u.num := Rat.num_nonneg.mpr (by exact_mod_cast hε.le)
  have hn : (u.num.toNat : ℝ) = u.num := by exact_mod_cast Int.toNat_of_nonneg hnum
  have hd : (u.den : ℝ) ≠ 0 := by exact_mod_cast u.den_nz
  have hmul : (u : ℝ) * u.den = u.num.toNat := by
    rw [Rat.cast_def, div_mul_cancel₀ _ hd, hn]
  have hpR : (p : ℝ) ^ u.num.toNat = ((p : ℝ) ^ (u : ℝ)) ^ u.den := by
    rw [← Real.rpow_natCast, ← hmul, Real.rpow_mul_natCast hp0.le]
  have hR : (p : ℝ) ^ u.num.toNat * (N : ℝ) ^ u.den = ((N : ℝ) + 1) ^ u.den := by
    rw [hpR, ← mul_pow, hNeq]
  have hnat : p ^ u.num.toNat * N ^ u.den = (N + 1) ^ u.den := by exact_mod_cast hR
  have hdvdN : p ∣ N := Dvd.intro _ rfl
  have h1 : p ∣ (N + 1) ^ u.den := by
    rw [← hnat]
    exact Dvd.dvd.mul_left (dvd_pow hdvdN u.den_nz) _
  have h2 : p ∣ N + 1 := hp.dvd_of_dvd_pow h1
  have h3 : p ∣ 1 := (Nat.dvd_add_right hdvdN).mp h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

lemma no_three_ties {ε : ℝ} (hε : 0 < ε) {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hTp : Tie ε p) (hTq : Tie ε q) (hTr : Tie ε r) : False :=
  tie_not_rat hε hp hTp (exponentRational hp hq hr hpq hpr hqr
    (tie_rpow_rat hp hTp) (tie_rpow_rat hq hTq) (tie_rpow_rat hr hTr))

lemma tie_support {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℕ, ∀ r : ℕ, r.Prime → Tie ε r → r = p ∨ r = q := by
  by_cases h1 : ∃ p : ℕ, p.Prime ∧ Tie ε p
  · obtain ⟨p, hp, hTp⟩ := h1
    by_cases h2 : ∃ q : ℕ, q.Prime ∧ Tie ε q ∧ q ≠ p
    · obtain ⟨q, hq, hTq, hqp⟩ := h2
      refine ⟨p, q, fun r hr hTr => ?_⟩
      by_contra hne
      rw [not_or] at hne
      exact no_three_ties hε hp hq hr (Ne.symm hqp) (Ne.symm hne.1) (Ne.symm hne.2)
        hTp hTq hTr
    · refine ⟨p, p, fun r hr hTr => ?_⟩
      by_contra hne
      exact h2 ⟨r, hr, hTr, fun h => hne (Or.inl h)⟩
  · exact ⟨0, 0, fun r hr hTr => (h1 ⟨r, hr, hTr⟩).elim⟩

/-! ### Counting -/

lemma encard_isMax_le {ε : ℝ} (hε : 0 < ε) : Set.encard {n : ℕ | IsMax ε n} ≤ 4 := by
  classical
  obtain ⟨p, q, hpq⟩ := tie_support hε
  obtain ⟨a, ha⟩ := two_values ε p
  obtain ⟨b, hb⟩ := two_values ε q
  set f : ℕ → ℕ × ℕ := fun n => (n.factorization p, n.factorization q) with hf
  have hinj : Set.InjOn f {n : ℕ | IsMax ε n} := by
    intro n hn n' hn' hnn'
    have e1 : n.factorization p = n'.factorization p := congrArg Prod.fst hnn'
    have e2 : n.factorization q = n'.factorization q := congrArg Prod.snd hnn'
    refine Nat.eq_of_factorization_eq hn.1 hn'.1 fun r => ?_
    by_cases hr : r.Prime
    · by_cases hT : Tie ε r
      · rcases hpq r hr hT with rfl | rfl
        · exact e1
        · exact e2
      · exact const_of_not_tie hn hn' hr hT
    · rw [Nat.factorization_eq_zero_of_not_prime n hr,
        Nat.factorization_eq_zero_of_not_prime n' hr]
  have himg : f '' {n : ℕ | IsMax ε n} ⊆
      ((({a, a + 1} : Finset ℕ) ×ˢ ({b, b + 1} : Finset ℕ) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro _ ⟨n, hn, rfl⟩
    simp only [hf, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton]
    exact ⟨ha n hn, hb n hn⟩
  have hcard : (({a, a + 1} : Finset ℕ) ×ˢ ({b, b + 1} : Finset ℕ)).card ≤ 4 := by
    rw [Finset.card_product]
    exact Nat.mul_le_mul Finset.card_le_two Finset.card_le_two
  calc Set.encard {n : ℕ | IsMax ε n} = Set.encard (f '' {n : ℕ | IsMax ε n}) :=
        (hinj.encard_image).symm
    _ ≤ Set.encard ((({a, a + 1} : Finset ℕ) ×ˢ ({b, b + 1} : Finset ℕ) : Finset (ℕ × ℕ)) :
          Set (ℕ × ℕ)) := Set.encard_le_encard himg
    _ = ((({a, a + 1} : Finset ℕ) ×ˢ ({b, b + 1} : Finset ℕ)).card : ℕ∞) :=
        Set.encard_coe_eq_coe_finsetCard _
    _ ≤ 4 := by exact_mod_cast hcard

/-! ### Maximizers over `k > 1` whose value is below `1` -/

lemma F_prime (ε : ℝ) {p : ℕ} (hp : p.Prime) :
    F ε p * ((p : ℝ) * (p : ℝ) ^ ε) = (p : ℝ) + 1 := by
  have h := F_prime_mul ε hp one_ne_zero
  simpa [gs_zero, F_one] using h

lemma eq_two_of_lt_one {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 < n)
    (hmax : ∀ k : ℕ, 1 < k → F ε k ≤ F ε n) (hlt : F ε n < 1) : n = 2 := by
  have hq : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd n
  set q := n.minFac with hqdef
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hqε : 0 < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hq0 _
  have hFq := F_prime ε hq
  have hFqle : F ε q ≤ F ε n := hmax q hq.one_lt
  -- from `F q < 1`: `q + 1 < q * q ^ ε`
  have hqlt : (q : ℝ) + 1 < (q : ℝ) * (q : ℝ) ^ ε := by
    have hP : 0 < (q : ℝ) * (q : ℝ) ^ ε := mul_pos hq0 hqε
    nlinarith
  have hm1 : m = 1 := by
    by_contra hne
    have hm2 : 1 < m := by omega
    have h := F_prime_mul ε hq hm0
    rw [← hm] at h
    have hle := hmax m hm2
    have hFm := F_pos ε hm0
    have hFn := F_pos ε (show n ≠ 0 by omega)
    have hg : (1 : ℝ) ≤ (gs q (m.factorization q) : ℝ) := by
      exact_mod_cast gs_pos q _
    -- F n * (g * P) = F m * (q g + 1) ≤ F n * (q g + 1), so g * P ≤ q g + 1
    have h3 : F ε n * ((gs q (m.factorization q) : ℝ) * ((q : ℝ) * (q : ℝ) ^ ε)) ≤
        F ε n * ((q : ℝ) * (gs q (m.factorization q) : ℝ) + 1) := by
      rw [h]
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    have h4 := le_of_mul_le_mul_left h3 hFn
    nlinarith
  subst hm1
  rw [mul_one] at hm
  by_contra hne
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  have hq3R : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hF2 := F_prime ε Nat.prime_two
  have h2le : F ε 2 ≤ F ε n := hmax 2 (by norm_num)
  rw [hm] at h2le
  have h2ε : (0 : ℝ) < (2 : ℝ) ^ ε := Real.rpow_pos_of_pos (by norm_num) _
  have hεlt : (2 : ℝ) ^ ε < (q : ℝ) ^ ε :=
    Real.rpow_lt_rpow (by norm_num) (by linarith) hε
  have hF2pos := F_pos ε (show (2 : ℕ) ≠ 0 by norm_num)
  have hFqpos := F_pos ε hq.ne_zero
  push_cast at hF2
  -- F 2 * (2 * 2^ε) = 3, F q * (q * q^ε) = q + 1, F 2 ≤ F q
  have h5 : F ε 2 * ((q : ℝ) * (q : ℝ) ^ ε) ≤ (q : ℝ) + 1 := by
    rw [← hFq]
    exact mul_le_mul_of_nonneg_right h2le (mul_pos hq0 hqε).le
  have h6 : F ε 2 * ((q : ℝ) * (2 : ℝ) ^ ε) < F ε 2 * ((q : ℝ) * (q : ℝ) ^ ε) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hεlt hq0) hF2pos
  -- 3 q / 2 = F 2 * q * 2^ε < q + 1
  nlinarith

end OMAColossal

theorem OMA.solution : type_of% @ColossallyAbundantNumber.encard_colossallyAbundant_maximizers_le_four := by
  intro ε hε
  by_cases h : ∃ n : ℕ, (1 < n ∧ ∀ k : ℕ, 1 < k → OMAColossal.F ε k ≤ OMAColossal.F ε n) ∧
      1 ≤ OMAColossal.F ε n
  · obtain ⟨n, ⟨hn1, hnmax⟩, hn⟩ := h
    refine le_trans (Set.encard_le_encard ?_) (OMAColossal.encard_isMax_le hε)
    rintro m ⟨hm1, hmmax⟩
    refine ⟨by omega, fun k hk => ?_⟩
    by_cases hk1 : k = 1
    · subst hk1
      rw [OMAColossal.F_one]
      exact hn.trans (hmmax n hn1)
    · exact hmmax k (by omega)
  · have hsub : {n : ℕ | 1 < n ∧ ∀ k : ℕ, 1 < k →
        (ArithmeticFunction.sigma 1 k : ℝ) / (k : ℝ) ^ (1 + ε) ≤
          (ArithmeticFunction.sigma 1 n : ℝ) / (n : ℝ) ^ (1 + ε)} ⊆ {2} := by
      rintro n ⟨hn1, hnmax⟩
      have hlt : OMAColossal.F ε n < 1 := by
        by_contra hge
        exact h ⟨n, ⟨hn1, hnmax⟩, not_lt.mp hge⟩
      exact OMAColossal.eq_two_of_lt_one hε hn1 hnmax hlt
    refine le_trans (Set.encard_le_encard hsub) ?_
    rw [Set.encard_singleton]
    norm_num
