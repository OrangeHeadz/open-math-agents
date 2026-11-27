import FormalConjectures.ErdosProblems.«1100»

-- Problem: Erdős Problem 1100, variant erdos_tenenbaum_max (Erdős and Tenenbaum 1989, Theorem 4)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1100.lean (declaration Erdos1100.erdos_1100.variants.erdos_tenenbaum_max)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)

/-!
# The maximal order of the number of coprime consecutive divisors

Following the argument of Erdős and Tenenbaum for their Theorem 4. Let `n` be squarefree and
`d_0 < d_1 < ⋯` its divisors. For a consecutive pair `(d_i, d_{i+1})` with `g = gcd > 1`, the
divisor `d_i / g` has a successor at most `d_{i+1} / g`; iterating gives an index `h` with
`(d_h, d_{h+1}) = 1`, `d_h ∣ d_i` and `d_{h+1}/d_h ≤ d_{i+1}/d_i`. The indices sent to a fixed `h`
are at most `2^(k - ω(d_h))` (they are multiples of `d_h`) and at most `1 + (d_h + 1) log n`
(their divisors grow by the factor `1 + 1/d_h`). With `n` the primorial of `P` and `k = π(P)`,
splitting on `ω(d_h) ≥ r` gives `2^k - 1 ≤ τ_⊥(n) (2^(k-r) + 1 + (P^r + 1) log n)`.

Choosing `r = ⌊(k log 2 - 2 log P) / (log P + log 2)⌋` and `k log P ≥ θ(P)` gives
`log τ_⊥(n) ≥ (log 2)^2 θ(P) / (log P (log P + log 2)) - 5`. For real `x` take `P` greatest with
`primorial P ≤ x`; then `θ(P) ≤ log x ≤ θ(P) + log (P + 1)`, and Chebyshev's bound `θ(P) ≥ P / 2`
gives `log log x ≥ log P - log 2`, which is enough for the constant `(log 2)^2 - δ`.
-/

open Real
namespace E1100

/-- facts about the sorted divisors -/
structure Sorted (n N : ℕ) (a : ℕ → ℕ) : Prop where
  dvd : ∀ i < N, a i ∣ n
  mono : ∀ i j, i < j → j < N → a i < a j
  surj : ∀ x, x ∣ n → ∃ j < N, a j = x
  next : ∀ k x, x ∣ n → a k < x → a (k + 1) ≤ x
  npos : 0 < n

lemma Sorted.pos {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) {i : ℕ} (hi : i < N) : 0 < a i :=
  Nat.pos_of_dvd_of_pos (hs.dvd i hi) hs.npos

lemma exists_good {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) :
    ∀ i, i + 1 < N → ∃ h, h + 1 < N ∧ Nat.Coprime (a h) (a (h + 1)) ∧ a h ∣ a i ∧
      a (h + 1) * a i ≤ a (i + 1) * a h := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hc : Nat.Coprime (a i) (a (i + 1))
    · exact ⟨i, hi, hc, dvd_rfl, le_rfl⟩
    set g := Nat.gcd (a i) (a (i + 1)) with hg
    have hai := hs.pos (show i < N by omega)
    have hai1 := hs.pos hi
    have hlt := hs.mono i (i + 1) (by omega) hi
    have hg1 : 1 < g := by
      have : g ≠ 1 := hc
      have : 0 < g := Nat.gcd_pos_of_pos_left _ hai
      omega
    have hgi : g ∣ a i := Nat.gcd_dvd_left _ _
    have hgi1 : g ∣ a (i + 1) := Nat.gcd_dvd_right _ _
    obtain ⟨u, hu⟩ := hgi
    obtain ⟨v, hv⟩ := hgi1
    have hupos : 0 < u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · rw [h, mul_zero] at hu; omega
      · exact h
    have hudvd : u ∣ n := dvd_trans (Dvd.intro_left g hu.symm) (hs.dvd i (by omega))
    have hvdvd : v ∣ n := dvd_trans (Dvd.intro_left g hv.symm) (hs.dvd (i + 1) hi)
    obtain ⟨j, hjN, hj⟩ := hs.surj u hudvd
    have hult : u < a i := by rw [hu]; nlinarith
    have hji : j < i := by
      by_contra hcon
      rcases (show i = j ∨ i < j by omega) with h | h
      · subst h; omega
      · have := hs.mono i j h hjN; omega
    have huv : u < v := by
      rw [hu, hv] at hlt; exact Nat.lt_of_mul_lt_mul_left hlt
    have hnext : a (j + 1) ≤ v := hs.next j v hvdvd (by rw [hj]; exact huv)
    obtain ⟨h, hh1, hcop, hdvd, hratio⟩ := ih j hji (by omega)
    refine ⟨h, hh1, hcop, ?_, ?_⟩
    · rw [hu, ← hj]; exact Dvd.dvd.mul_left hdvd g
    · -- a(h+1) * a j ≤ a(j+1) * a h, and a(j+1) * a i ≤ a(i+1) * a j
      have hah := hs.pos (show h < N by omega)
      have hajpos : 0 < a j := hs.pos hjN
      have h2 : a (j + 1) * a i ≤ a (i + 1) * a j := by
        rw [hu, hv, hj]; nlinarith
      have h3 : a (h + 1) * a i * a j ≤ a (i + 1) * a h * a j := by
        calc a (h + 1) * a i * a j = (a (h + 1) * a j) * a i := by ring
          _ ≤ (a (j + 1) * a h) * a i := Nat.mul_le_mul_right _ hratio
          _ = (a (j + 1) * a i) * a h := by ring
          _ ≤ (a (i + 1) * a j) * a h := Nat.mul_le_mul_right _ h2
          _ = a (i + 1) * a h * a j := by ring
      exact Nat.le_of_mul_le_mul_right h3 hajpos

lemma chain_pow (S : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) (hc : 1 ≤ c)
    (hf : ∀ x ∈ S, ∀ y ∈ S, x < y → c * f x ≤ f y) (hpos : ∀ x ∈ S, 0 < f x) (hne : S.Nonempty) :
    c ^ (S.card - 1) * f (S.min' hne) ≤ f (S.max' hne) := by
  induction S using Finset.induction_on_max with
  | empty => exact absurd hne (by simp)
  | insert m S hlt ih =>
    by_cases hS : S.Nonempty
    · have hmS : m ∉ S := fun hm => lt_irrefl _ (hlt m hm)
      have hmin : (insert m S).min' hne = S.min' hS := by
        apply le_antisymm
        · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.min'_mem _ _))
        · apply Finset.le_min'; intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact (Finset.min'_le _ _ (Finset.min'_mem S hS)).trans
              (hlt _ (Finset.min'_mem S hS)).le
          · exact Finset.min'_le _ _ hy
      have hmax : (insert m S).max' hne = m := by
        apply le_antisymm
        · apply Finset.max'_le; intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact le_rfl
          · exact (hlt y hy).le
        · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
      have ih' := ih (fun x hx y hy hxy => hf x (Finset.mem_insert_of_mem hx) y
        (Finset.mem_insert_of_mem hy) hxy) (fun x hx => hpos x (Finset.mem_insert_of_mem hx)) hS
      rw [hmin, hmax, Finset.card_insert_of_notMem hmS]
      have hcard : S.card + 1 - 1 = (S.card - 1) + 1 := by
        have := hS.card_pos; omega
      rw [hcard, pow_succ]
      have hstep : c * f (S.max' hS) ≤ f m :=
        hf _ (Finset.mem_insert_of_mem (Finset.max'_mem _ _)) m (Finset.mem_insert_self _ _)
          (hlt _ (Finset.max'_mem _ _))
      have h0 : 0 ≤ c := by linarith
      calc c ^ (S.card - 1) * c * f (S.min' hS) = c * (c ^ (S.card - 1) * f (S.min' hS)) := by ring
        _ ≤ c * f (S.max' hS) := mul_le_mul_of_nonneg_left ih' h0
        _ ≤ f m := hstep
    · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst hS0
      simp

lemma card_le_of_chain (S : Finset ℕ) (f : ℕ → ℝ) (c M : ℝ) (hc : 1 < c) (hM : 1 ≤ M)
    (hf : ∀ x ∈ S, ∀ y ∈ S, x < y → c * f x ≤ f y) (hlow : ∀ x ∈ S, 1 ≤ f x)
    (hup : ∀ x ∈ S, f x ≤ M) :
    (S.card : ℝ) ≤ 1 + Real.log M / Real.log c := by
  have hlc : 0 < Real.log c := Real.log_pos hc
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM
  rcases S.eq_empty_or_nonempty with h | hne
  · subst h; simp; positivity
  have key := chain_pow S f c hc.le hf (fun x hx => by linarith [hlow x hx]) hne
  have h1 := hlow _ (Finset.min'_mem S hne)
  have h2 := hup _ (Finset.max'_mem S hne)
  have hcp : c ^ (S.card - 1) ≤ M := by
    have : c ^ (S.card - 1) * 1 ≤ c ^ (S.card - 1) * f (S.min' hne) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hlog := Real.log_le_log (by positivity) hcp
  rw [Real.log_pow] at hlog
  have hcard : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
    have := hne.card_pos; push_cast [Nat.cast_sub (show 1 ≤ S.card by omega)]; ring
  rw [hcard] at hlog
  rw [← sub_le_iff_le_add', le_div_iff₀ hlc]
  linarith

lemma sqfree_count (n m : ℕ) (hn : Squarefree n) (hmn : m ∣ n) :
    ((n.divisors.filter (fun d => m ∣ d)).card : ℕ) ≤ 2 ^ (n.primeFactors.card - m.primeFactors.card) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hsub : m.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hmn hn0
  calc (n.divisors.filter (fun d => m ∣ d)).card
      ≤ (n.primeFactors \ m.primeFactors).powerset.card := by
        apply Finset.card_le_card_of_injOn (fun d => d.primeFactors \ m.primeFactors)
        · intro d hd
          simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd
          simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
          exact Finset.sdiff_subset_sdiff (Nat.primeFactors_mono hd.1.1 hn0) le_rfl
        · intro d hd e he hde
          simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd he
          have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn0 hd.1.1
          have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero hn0 he.1.1
          have hsd : Squarefree d := hn.squarefree_of_dvd hd.1.1
          have hse : Squarefree e := hn.squarefree_of_dvd he.1.1
          have h1 : d.primeFactors = e.primeFactors := by
            have hmd : m.primeFactors ⊆ d.primeFactors := Nat.primeFactors_mono hd.2 hd0
            have hme : m.primeFactors ⊆ e.primeFactors := Nat.primeFactors_mono he.2 he0
            simp only at hde
            rw [← Finset.sdiff_union_of_subset hmd, ← Finset.sdiff_union_of_subset hme, hde]
          rw [← Nat.prod_primeFactors_of_squarefree hsd, ← Nat.prod_primeFactors_of_squarefree hse, h1]
    _ = 2 ^ (n.primeFactors.card - m.primeFactors.card) := by
        rw [Finset.card_powerset, Finset.card_sdiff_of_subset hsub]

lemma sqfree_le_pow (m P : ℕ) (hm : Squarefree m) (hP : ∀ p ∈ m.primeFactors, p ≤ P) :
    m ≤ P ^ m.primeFactors.card := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hm]
  exact Finset.prod_le_pow_card _ _ _ hP

open Classical in
noncomputable def psi {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (i : ℕ) : ℕ :=
  if hi : i + 1 < N then Classical.choose (exists_good hs i hi) else 0

lemma psi_spec {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (i : ℕ) (hi : i + 1 < N) :
    psi hs i + 1 < N ∧ Nat.Coprime (a (psi hs i)) (a (psi hs i + 1)) ∧ a (psi hs i) ∣ a i ∧
      a (psi hs i + 1) * a i ≤ a (i + 1) * a (psi hs i) := by
  unfold psi; rw [dif_pos hi]; exact Classical.choose_spec (exists_good hs i hi)

lemma fiber_chain {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (h : ℕ) (hh : h + 1 < N) :
    ((((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card : ℕ) : ℝ) ≤
      1 + (a h + 1) * Real.log n := by
  set F := (Finset.range (N - 1)).filter (fun i => psi hs i = h)
  have hah : 0 < a h := hs.pos (by omega)
  have hlt : a h < a (h + 1) := hs.mono h (h + 1) (by omega) hh
  set c : ℝ := ((a h : ℝ) + 1) / a h
  have hahR : (0 : ℝ) < a h := by exact_mod_cast hah
  have hc : 1 < c := by rw [lt_div_iff₀ hahR]; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hs.npos
  have key := card_le_of_chain F (fun i => (a i : ℝ)) c n hc hn1 ?_ ?_ ?_
  · have hlc : 1 / ((a h : ℝ) + 1) ≤ Real.log c := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < c by linarith)
      have e : 1 - c⁻¹ = 1 / ((a h : ℝ) + 1) := by
        simp only [c]; field_simp; ring
      linarith
    have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hpos : 0 < 1 / ((a h : ℝ) + 1) := by positivity
    have : Real.log n / Real.log c ≤ ((a h : ℝ) + 1) * Real.log n := by
      rw [div_le_iff₀ (lt_of_lt_of_le hpos hlc)]
      calc Real.log n = ((a h : ℝ) + 1) * Real.log n * (1 / ((a h : ℝ) + 1)) := by
            field_simp
        _ ≤ ((a h : ℝ) + 1) * Real.log n * Real.log c := by gcongr
    linarith
  · intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxN : x + 1 < N := by have := Finset.mem_range.mp hx'.1; omega
    have hyN : y + 1 < N := by have := Finset.mem_range.mp hy'.1; omega
    have hsp := psi_spec hs x hxN
    rw [hx'.2] at hsp
    have h1 : a (x + 1) ≤ a y := by
      rcases (show x + 1 = y ∨ x + 1 < y by omega) with e | e
      · rw [e]
      · exact (hs.mono _ _ e (by omega)).le
    have h2 : (a h + 1) * a x ≤ a (x + 1) * a h := by
      calc (a h + 1) * a x ≤ a (h + 1) * a x := Nat.mul_le_mul_right _ hlt
        _ ≤ _ := hsp.2.2.2
    have h2R : ((a h : ℝ) + 1) * a x ≤ a (x + 1) * a h := by exact_mod_cast h2
    have h1R : (a (x + 1) : ℝ) ≤ a y := by exact_mod_cast h1
    simp only [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ hahR]
    nlinarith
  · intro x hx
    have := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have : 0 < a x := hs.pos (by omega)
    exact_mod_cast this
  · intro x hx
    have := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    exact_mod_cast Nat.le_of_dvd hs.npos (hs.dvd x (by omega))

lemma fiber_div {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (h : ℕ) :
    ((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card ≤
      (n.divisors.filter (fun d => a h ∣ d)).card := by
  apply Finset.card_le_card_of_injOn a
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
    have hsp := psi_spec hs i (by omega)
    rw [hi.2] at hsp
    simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq]
    exact ⟨⟨hs.dvd i (by omega), hs.npos.ne'⟩, hsp.2.2.1⟩
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · have := hs.mono i j h1 (by omega); omega
    · have := hs.mono j i h1 (by omega); omega

lemma main_count {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (hsq : Squarefree n) (P r : ℕ)
    (hP : ∀ p ∈ n.primeFactors, p ≤ P) (hP1 : 1 ≤ P) :
    ((N - 1 : ℕ) : ℝ) ≤ ((((Finset.range (N - 1)).filter
      (fun i => Nat.Coprime (a i) (a (i + 1)))).card : ℕ) : ℝ) *
      ((2 : ℝ) ^ (n.primeFactors.card - r) + 1 + ((P : ℝ) ^ r + 1) * Real.log n) := by
  set G := (Finset.range (N - 1)).filter (fun i => Nat.Coprime (a i) (a (i + 1)))
  set B : ℝ := (2 : ℝ) ^ (n.primeFactors.card - r) + 1 + ((P : ℝ) ^ r + 1) * Real.log n
  have hmaps : ∀ i ∈ Finset.range (N - 1), psi hs i ∈ G := by
    intro i hi
    have hsp := psi_spec hs i (by have := Finset.mem_range.mp hi; omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hsp.2.1⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hs.npos)
  have hfib : ∀ h ∈ G, ((((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card : ℕ) : ℝ) ≤ B := by
    intro h hG
    have hh : h + 1 < N := by have := Finset.mem_range.mp (Finset.mem_filter.mp hG).1; omega
    have hdvd : a h ∣ n := hs.dvd h (by omega)
    set s := (a h).primeFactors.card
    by_cases hrs : r ≤ s
    · have h1 := (fiber_div hs h).trans (sqfree_count n (a h) hsq hdvd)
      have h2 : 2 ^ (n.primeFactors.card - s) ≤ 2 ^ (n.primeFactors.card - r) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : ((((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (n.primeFactors.card - r) := by exact_mod_cast h1.trans h2
      have : (0 : ℝ) ≤ ((P : ℝ) ^ r + 1) * Real.log n := by positivity
      simp only [B]; linarith
    · have hsqh : Squarefree (a h) := hsq.squarefree_of_dvd hdvd
      have hPh : ∀ p ∈ (a h).primeFactors, p ≤ P := fun p hp =>
        hP p (Nat.primeFactors_mono hdvd hsq.ne_zero hp)
      have h1 := sqfree_le_pow (a h) P hsqh hPh
      have h2 : P ^ s ≤ P ^ r := Nat.pow_le_pow_right hP1 (by omega)
      have h3 : (a h : ℝ) ≤ (P : ℝ) ^ r := by exact_mod_cast h1.trans h2
      have h4 := fiber_chain hs h hh
      have h5 : ((a h : ℝ) + 1) * Real.log n ≤ ((P : ℝ) ^ r + 1) * Real.log n := by gcongr
      have : (0 : ℝ) ≤ (2 : ℝ) ^ (n.primeFactors.card - r) := by positivity
      simp only [B]; linarith
  calc ((N - 1 : ℕ) : ℝ) = (((Finset.range (N - 1)).card : ℕ) : ℝ) := by simp
    _ = ∑ h ∈ G, ((((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card : ℕ) : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ h ∈ G, B := Finset.sum_le_sum hfib
    _ = (G.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

lemma sorted_nth (n : ℕ) (hn : 0 < n) : Sorted n n.divisors.card (Nat.nth (· ∣ n)) := by
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn.ne']
  refine ⟨?_, ?_, ?_, ?_, hn⟩
  · intro i hi; exact Nat.nth_mem_of_lt_card hf (by rw [hcard]; exact hi)
  · intro i j hij hj; exact Nat.nth_lt_nth_of_lt_card hf hij (by rw [hcard]; exact hj)
  · intro x hx
    obtain ⟨j, hj, hjx⟩ := Nat.exists_lt_card_finite_nth_eq hf hx
    exact ⟨j, by rw [← hcard]; exact hj, hjx⟩
  · intro k x hx hkx
    by_contra hc
    push Not at hc
    have := Nat.le_nth_of_lt_nth_succ hc hx
    omega

lemma tauPerp_eq (n : ℕ) : Erdos1100.tauPerp n = ((Finset.range (n.divisors.card - 1)).filter
    (fun i => Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1)))).card := by
  unfold Erdos1100.tauPerp
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range
    (fun i => if Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1)) then 1 else 0) _

lemma divisors_card_sqfree (n : ℕ) (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn.ne_zero]
  rw [Finset.prod_congr rfl (g := fun _ => 2)]
  · simp
  · intro p hp
    have h1 := Squarefree.natFactorization_le_one p hn
    have h2 : 0 < n.factorization p := Nat.Prime.factorization_pos_of_dvd
      (Nat.prime_of_mem_primeFactors hp) hn.ne_zero (Nat.dvd_of_mem_primeFactors hp)
    omega

lemma tau_lower (P r : ℕ) (hP1 : 1 ≤ P) :
    (2 : ℝ) ^ (Nat.primeCounting P) - 1 ≤ (Erdos1100.tauPerp (primorial P) : ℝ) *
      ((2 : ℝ) ^ (Nat.primeCounting P - r) + 1 + ((P : ℝ) ^ r + 1) * (Real.log 4 * P)) := by
  set n := primorial P
  have hn : 0 < n := primorial_pos P
  have hsq : Squarefree n := squarefree_primorial P
  have hpf : n.primeFactors = P.primesLE := primeFactors_primorial P
  have hk : n.primeFactors.card = Nat.primeCounting P := by
    rw [hpf, Nat.primesLE_card_eq_primeCounting]
  have hP : ∀ p ∈ n.primeFactors, p ≤ P := by
    intro p hp; rw [hpf] at hp; exact Nat.le_of_mem_primesLE hp
  have hmc := main_count (sorted_nth n hn) hsq P r hP hP1
  rw [← tauPerp_eq, divisors_card_sqfree n hsq, hk] at hmc
  have hlog : Real.log n ≤ Real.log 4 * P := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (P : ℝ)) (by positivity)
    rwa [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h
  have hpow : (1 : ℕ) ≤ 2 ^ Nat.primeCounting P := Nat.one_le_two_pow
  have hc : (((2 ^ Nat.primeCounting P - 1 : ℕ)) : ℝ) = (2 : ℝ) ^ Nat.primeCounting P - 1 := by
    push_cast [Nat.cast_sub hpow]; ring
  rw [hc] at hmc
  refine hmc.trans ?_
  gcongr

lemma log2_bounds : (0.69 : ℝ) < log 2 ∧ log 2 < 0.7 := by
  constructor
  · have := Real.log_two_gt_d9; linarith
  · have := Real.log_two_lt_d9; linarith

lemma glue_C2 (k r : ℕ) (τ X : ℝ) (hrk : r ≤ k) (hk1 : 1 ≤ k) (hX0 : 0 ≤ X)
    (hX : X ≤ (2 : ℝ) ^ (k - r)) (h : (2 : ℝ) ^ k - 1 ≤ τ * ((2 : ℝ) ^ (k - r) + 1 + X)) :
    (2 : ℝ) ^ r / 6 ≤ τ := by
  have hA : (2 : ℝ) ^ k = 2 ^ (k - r) * 2 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrk]
  have hB1 : (1 : ℝ) ≤ 2 ^ (k - r) := one_le_pow₀ (by norm_num)
  have hBle : (2 : ℝ) ^ (k - r) + 1 + X ≤ 3 * 2 ^ (k - r) := by linarith
  have hBpos : (0 : ℝ) < 2 ^ (k - r) + 1 + X := by positivity
  have hkpos : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  have hτpos : 0 < τ := by
    by_contra hc; push Not at hc
    have : τ * ((2 : ℝ) ^ (k - r) + 1 + X) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hBpos.le
    linarith
  have h3 : (2 : ℝ) ^ k / 2 ≤ τ * (3 * 2 ^ (k - r)) := by
    have := mul_le_mul_of_nonneg_left hBle hτpos.le
    linarith
  rw [hA] at h3
  rw [div_le_iff₀ (by norm_num)]
  have hpos : (0 : ℝ) < 2 ^ (k - r) := by positivity
  have : (2 : ℝ) ^ r * 2 ^ (k - r) ≤ (τ * 6) * 2 ^ (k - r) := by nlinarith
  exact le_of_mul_le_mul_right this hpos


lemma glue_C1' (P k r : ℕ) (L : ℝ) (hPge : 4 ≤ (P : ℝ)) (hPexp : (P : ℝ) = exp L) (hrk : r ≤ k)
    (h : ((r : ℝ) + 2) * L ≤ ((k : ℝ) - r) * log 2) :
    ((P : ℝ) ^ r + 1) * (log 4 * P) ≤ (2 : ℝ) ^ (k - r) := by
  have hl4 : log 4 ≤ 2 := by
    have : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := log2_bounds.2
    linarith
  have hPr1 : (1 : ℝ) ≤ (P : ℝ) ^ r := one_le_pow₀ (by linarith)
  have e1 : ((P : ℝ) ^ r + 1) * (log 4 * P) ≤ (P : ℝ) ^ (r + 2) := by
    rw [pow_add]
    have : (log 4 * P) * 2 ≤ (P : ℝ) ^ 2 := by
      nlinarith [Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)]
    nlinarith
  refine e1.trans ?_
  have h2exp : (2 : ℝ) = exp (log 2) := (Real.exp_log (by norm_num)).symm
  rw [hPexp, ← Real.exp_nat_mul, h2exp, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast [Nat.cast_sub hrk]
  linarith

lemma realA (P k : ℕ) (τ θ L : ℝ) (hP : 4 ≤ (P : ℝ)) (hPexp : (P : ℝ) = exp L) (hL1 : 1 ≤ L)
    (hθ : θ ≤ k * L) (h2 : 2 * L ≤ k * log 2)
    (htau : ∀ r : ℕ, (2 : ℝ) ^ k - 1 ≤
      τ * ((2 : ℝ) ^ (k - r) + 1 + ((P : ℝ) ^ r + 1) * (log 4 * P))) :
    exp ((log 2) ^ 2 * θ / (L * (L + log 2)) - 5) ≤ τ := by
  obtain ⟨hl2, hl2'⟩ := log2_bounds
  have hb : 0 < log 2 := by linarith
  have hL0 : 0 < L := by linarith
  have hLb : 0 < L + log 2 := by linarith
  set r : ℕ := ⌊((k : ℝ) * log 2 - 2 * L) / (L + log 2)⌋₊ with hr
  have hr1 : (r : ℝ) ≤ ((k : ℝ) * log 2 - 2 * L) / (L + log 2) :=
    Nat.floor_le (div_nonneg (by linarith) hLb.le)
  have hr2 : ((k : ℝ) * log 2 - 2 * L) / (L + log 2) < r + 1 := Nat.lt_floor_add_one _
  clear_value r
  rw [le_div_iff₀ hLb] at hr1
  rw [div_lt_iff₀ hLb] at hr2
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hrL : 0 ≤ (r : ℝ) * L := by positivity
  have hrk : r ≤ k := by
    have h3 : (r : ℝ) * log 2 ≤ k * log 2 := by nlinarith
    have h4 : (r : ℝ) ≤ k := le_of_mul_le_mul_right h3 hb
    exact_mod_cast h4
  have hk1 : 1 ≤ k := by
    have h3 : (0 : ℝ) < k := by
      by_contra hc
      have h4 : (k : ℝ) = 0 := le_antisymm (not_lt.mp hc) hk0
      rw [h4] at h2
      linarith
    exact_mod_cast h3
  have hC1 := glue_C1' P k r L hP hPexp hrk (by nlinarith)
  have hC2 := glue_C2 k r τ _ hrk hk1 (by positivity) hC1 (htau r)
  refine le_trans ?_ hC2
  have hl6 : log 6 ≤ log 2 + 2 := by
    have h6 : log 6 = log 2 + log 3 := by
      rw [show (6:ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    linarith
  have e : (2 : ℝ) ^ r / 6 = exp ((r : ℝ) * log 2 - log 6) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e]
  apply Real.exp_le_exp.mpr
  have h1 : (log 2) ^ 2 * θ / (L * (L + log 2)) ≤ (log 2) ^ 2 * k / (L + log 2) := by
    rw [div_le_div_iff₀ (by positivity) hLb]
    have := mul_le_mul_of_nonneg_left hθ (show 0 ≤ (log 2) ^ 2 * (L + log 2) by positivity)
    nlinarith
  have h3 : (log 2) ^ 2 * k / (L + log 2) ≤ (r : ℝ) * log 2 - log 6 + 5 := by
    rw [div_le_iff₀ hLb]
    have ha := mul_lt_mul_of_pos_left hr2 hb
    have hbb := mul_nonneg (show 0 ≤ 5 - log 6 - 3 * log 2 by linarith) hLb.le
    have hc := mul_pos hb hb
    nlinarith
  linarith

lemma coreB (a c η θ D Q Y Z : ℝ) (hc : 0 ≤ c) (hη : 0 < η) (hθ : 0 < θ) (hD : 0 < D)
    (hQ : 0 < Q) (h1 : Y ≤ (1 + η) * θ) (h2 : D ≤ Z) (h3 : Q ≤ (1 + η) * D)
    (h4 : c * (1 + η) ^ 2 * θ + 5 * (1 + η) * D ≤ a * θ) :
    c * Y / Z ≤ a * θ / Q - 5 := by
  have s1 : c * Y / Z ≤ c * ((1 + η) * θ) / D :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left h1 hc) hD h2
  have haθ : 0 ≤ a * θ := le_trans (by positivity) h4
  have s2 : a * θ / ((1 + η) * D) ≤ a * θ / Q := div_le_div_of_nonneg_left haθ hQ h3
  have s3 : c * ((1 + η) * θ) / D ≤ a * θ / ((1 + η) * D) - 5 := by
    rw [le_sub_iff_add_le, div_add' _ _ _ hD.ne', div_le_div_iff₀ hD (by positivity)]
    have := mul_le_mul_of_nonneg_left h4 hD.le
    nlinarith
  linarith

lemma ev_log_sq (K : ℝ) (hK : 0 < K) :
    ∀ᶠ P : ℕ in Filter.atTop, K * (log (P : ℝ)) ^ 2 ≤ P := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show 0 < 1 / K by positivity)
  have h' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  filter_upwards [h'] with P hP
  simp only [id, Real.norm_eq_abs, abs_pow, sq_abs, Nat.abs_cast] at hP
  calc K * (log (P : ℝ)) ^ 2 ≤ K * (1 / K * P) := mul_le_mul_of_nonneg_left hP hK.le
    _ = P := by field_simp

lemma ev_log (L0 : ℝ) : ∀ᶠ P : ℕ in Filter.atTop, L0 ≤ log (P : ℝ) :=
  (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop L0

lemma log_succ_le (P : ℕ) (hP : 1 ≤ P) : log ((P : ℝ) + 1) ≤ log 2 + log (P : ℝ) := by
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  rw [← Real.log_mul (by norm_num) (by linarith)]
  exact Real.log_le_log (by linarith) (by linarith)

lemma ev_theta : ∀ᶠ P : ℕ in Filter.atTop, (P : ℝ) / 2 ≤ Chebyshev.theta P := by
  filter_upwards [ev_log_sq 625 (by norm_num), ev_log 2, Filter.eventually_ge_atTop 1]
    with P h1 hL2 hP1
  obtain ⟨hl2, hl2'⟩ := log2_bounds
  have hge := Chebyshev.theta_ge P
  have hsucc := log_succ_le P hP1
  have hs0 : 0 ≤ √(P : ℝ) := Real.sqrt_nonneg _
  have hss : √(P : ℝ) ^ 2 = P := Real.sq_sqrt (by positivity)
  have hLs : 25 * log (P : ℝ) ≤ √(P : ℝ) := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hs0
    rw [hss]; nlinarith
  have h2 : 2 * √(P : ℝ) * log (P : ℝ) ≤ 0.08 * P := by nlinarith
  have h3 : log (P : ℝ) ^ 2 ≤ (P : ℝ) / 625 := by linarith
  have h4 : 2 * log (P : ℝ) ≤ log (P : ℝ) ^ 2 := by nlinarith
  have hP0 : (0 : ℝ) ≤ P := by positivity
  nlinarith

lemma aux_Q (δ L b : ℝ) (hδ : 0 < δ) (hδ' : δ < 0.49) (hb0 : 0 < b) (hb : b < 0.7)
    (hLδ : 12 ≤ L * δ) (hL0 : 0 < L) : L * (L + b) ≤ (1 + δ / 3) * (L - b) ^ 2 := by
  have hA : 12 * L ≤ L * δ * L := mul_le_mul_of_nonneg_right hLδ hL0.le
  have hδb : δ * b ≤ 0.49 * 0.7 := mul_le_mul hδ'.le hb.le hb0.le (by norm_num)
  have hB : δ * b * L ≤ 0.49 * 0.7 * L := mul_le_mul_of_nonneg_right hδb hL0.le
  have hC : b * L ≤ 0.7 * L := mul_le_mul_of_nonneg_right hb.le hL0.le
  have hD : 0 ≤ δ * b ^ 2 := by positivity
  have hE : 0 ≤ b ^ 2 := by positivity
  have e : (1 + δ / 3) * (L - b) ^ 2 - L * (L + b) =
      (L * δ * L) / 3 - 2 / 3 * (δ * b * L) + δ * b ^ 2 / 3 - 3 * (b * L) + b ^ 2 := by ring
  linarith

lemma aux_h4 (a δ θ L b : ℝ) (hδ : 0 < δ) (hδa : δ < a) (ha : a < 0.49) (hθ : 0 < θ)
    (hb0 : 0 ≤ b) (hbL : b ≤ L) (hδθ : 20 * L ^ 2 ≤ δ * θ) :
    (a - δ) * (1 + δ / 3) ^ 2 * θ + 5 * (1 + δ / 3) * (L - b) ^ 2 ≤ a * θ := by
  have hδ1 : δ < 0.49 := by linarith
  have hδ2 : δ * δ ≤ 0.49 * δ := mul_le_mul_of_nonneg_right hδ1.le hδ.le
  have e1 : (1 + δ / 3) ^ 2 ≤ 1 + δ := by
    have : (1 + δ / 3) ^ 2 = 1 + 2 / 3 * δ + (δ * δ) / 9 := by ring
    linarith
  have had : 0 ≤ a - δ := by linarith
  have e2 : (a - δ) * (1 + δ / 3) ^ 2 ≤ a - δ / 2 := by
    have h1 := mul_le_mul_of_nonneg_left e1 had
    have h2 : (a - δ) * δ ≤ 0.49 * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have h3 : (a - δ) * (1 + δ) = (a - δ) + (a - δ) * δ := by ring
    linarith
  have e3 := mul_le_mul_of_nonneg_right e2 hθ.le
  have e4 : (L - b) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have e5 : 5 * (1 + δ / 3) * (L - b) ^ 2 ≤ 6 * L ^ 2 := by
    have h1 : 5 * (1 + δ / 3) ≤ 6 := by linarith
    have h2 : 5 * (1 + δ / 3) * (L - b) ^ 2 ≤ 6 * (L - b) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    linarith
  have e6 : (a - δ / 2) * θ = a * θ - δ * θ / 2 := by ring
  have e7 : 0 ≤ δ * θ := by positivity
  linarith

lemma realC (δ θ L Y lp p : ℝ) (hδ : 0 < δ) (hδa : δ < (log 2) ^ 2) (hθ : p / 2 ≤ θ)
    (hK : (40 / δ + 6) * L ^ 2 ≤ p) (hL : 12 / δ ≤ L) (hY2 : Y ≤ θ + lp)
    (hlp : lp ≤ log 2 + L) (hlogY : L - log 2 ≤ log Y) :
    (24 ≤ L ∧ 3 * L ^ 2 ≤ θ) ∧
    ((log 2) ^ 2 - δ) * Y / (log Y) ^ 2 ≤ (log 2) ^ 2 * θ / (L * (L + log 2)) - 5 := by
  obtain ⟨hl2, hl2'⟩ := log2_bounds
  have hb0 : 0 < log 2 := by linarith
  have ha : (log 2) ^ 2 < 0.49 := by
    have : (log 2) ^ 2 ≤ 0.7 ^ 2 := pow_le_pow_left₀ hb0.le hl2'.le 2
    have h49 : (0.7 : ℝ) ^ 2 = 0.49 := by norm_num
    have : log 2 * log 2 < 0.7 * 0.7 := mul_lt_mul'' hl2' hl2' hb0.le hb0.le
    have e : (log 2) ^ 2 = log 2 * log 2 := by ring
    rw [e]; linarith
  have hδ1 : δ < 0.49 := by linarith
  have hLδ : 12 ≤ L * δ := (div_le_iff₀ hδ).mp hL
  have hL24 : 24 ≤ L := by
    by_contra hc
    have hc' : L < 24 := not_le.mp hc
    have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
    have : L * δ < 24 * 0.49 := mul_lt_mul'' hc' hδ1 hLpos.le hδ.le
    linarith
  have hL0 : 0 < L := by linarith
  have hK6 : 6 * L ^ 2 ≤ p ∧ 40 * L ^ 2 ≤ p * δ := by
    have e : (40 / δ + 6) * L ^ 2 = 40 * L ^ 2 / δ + 6 * L ^ 2 := by ring
    rw [e] at hK
    have h0 : 0 ≤ 40 * L ^ 2 / δ := by positivity
    have h1 : 0 ≤ 6 * L ^ 2 := by positivity
    refine ⟨by linarith, ?_⟩
    have : 40 * L ^ 2 / δ ≤ p := by linarith
    exact (div_le_iff₀ hδ).mp this
  obtain ⟨hK6, hK40⟩ := hK6
  have hθ0 : 0 < θ := by
    have : 0 < 6 * L ^ 2 := by positivity
    linarith
  have hδθ : 20 * L ^ 2 ≤ δ * θ := by
    have := mul_le_mul_of_nonneg_left hθ hδ.le
    linarith
  refine ⟨⟨hL24, by linarith⟩, ?_⟩
  have hLb : 0 < L - log 2 := by linarith
  have hLL : 24 * L ≤ L ^ 2 := by
    have := mul_le_mul_of_nonneg_right hL24 hL0.le
    have e : L ^ 2 = L * L := by ring
    linarith
  apply coreB ((log 2) ^ 2) ((log 2) ^ 2 - δ) (δ / 3) θ ((L - log 2) ^ 2) (L * (L + log 2)) Y
    ((log Y) ^ 2) (by linarith) (by positivity) hθ0 (pow_pos hLb 2) (by positivity)
  · have e : (1 + δ / 3) * θ = θ + δ * θ / 3 := by ring
    linarith
  · exact pow_le_pow_left₀ hLb.le hlogY 2
  · exact aux_Q δ L (log 2) hδ hδ1 hb0 hl2' hLδ hL0
  · exact aux_h4 ((log 2) ^ 2) δ θ L (log 2) hδ hδa ha hθ0 hb0.le (by linarith) hδθ

lemma main_ev (δ : ℝ) (hδ : 0 < δ) (hδa : δ < (log 2) ^ 2) :
    ∀ᶠ P : ℕ in Filter.atTop, ∀ Y : ℝ, Chebyshev.theta P ≤ Y →
      Y ≤ Chebyshev.theta P + log ((P : ℝ) + 1) →
      exp (((log 2) ^ 2 - δ) * Y / (log Y) ^ 2) ≤ (Erdos1100.tauPerp (primorial P) : ℝ) := by
  filter_upwards [ev_theta, ev_log_sq (40 / δ + 6) (by positivity), ev_log (12 / δ),
    Filter.eventually_ge_atTop 4] with P hθ hK hL h4 Y hY1 hY2
  obtain ⟨hl2, hl2'⟩ := log2_bounds
  have hPR : (4 : ℝ) ≤ P := by exact_mod_cast h4
  have hP0 : (0 : ℝ) < P := by linarith
  have hkθ := Chebyshev.theta_le_pi_mul_log P
  have hsucc := log_succ_le P (by omega)
  have hPexp : (P : ℝ) = exp (log (P : ℝ)) := (Real.exp_log hP0).symm
  have htau := fun r : ℕ => tau_lower P r (by omega)
  have hY0 : 0 < Y := by linarith
  have hlogY : log (P : ℝ) - log 2 ≤ log Y := by
    have h3 : (P : ℝ) / 2 ≤ Y := by linarith
    have h5 := Real.log_le_log (by positivity) h3
    rwa [Real.log_div hP0.ne' (by norm_num)] at h5
  obtain ⟨⟨hL24, h3L⟩, hmain⟩ := realC δ _ _ Y _ _ hδ hδa hθ hK hL hY2 hsucc hlogY
  have hL0 : 0 < log (P : ℝ) := by linarith
  have h2 : 2 * log (P : ℝ) ≤ (Nat.primeCounting P : ℝ) * log 2 := by
    have h3 : 3 * log (P : ℝ) * log (P : ℝ) ≤ (Nat.primeCounting P : ℝ) * log (P : ℝ) := by
      have e : 3 * log (P : ℝ) * log (P : ℝ) = 3 * log (P : ℝ) ^ 2 := by ring
      linarith
    have h5 : 3 * log (P : ℝ) ≤ (Nat.primeCounting P : ℝ) := le_of_mul_le_mul_right h3 hL0
    have h6 : 3 * log (P : ℝ) * 0.69 ≤ (Nat.primeCounting P : ℝ) * log 2 :=
      mul_le_mul h5 hl2.le (by norm_num) (by positivity)
    linarith
  have hτ := realA P (Nat.primeCounting P) _ _ _ hPR hPexp (by linarith) hkθ h2 htau
  exact le_trans (Real.exp_le_exp.mpr hmain) hτ

lemma primorial_succ_le (P : ℕ) : primorial (P + 1) ≤ (P + 1) * primorial P := by
  by_cases hp : (P + 1).Prime
  · have h : primorial (P + 1) = (P + 1) * primorial P := by
      unfold primorial
      rw [Finset.range_add_one (n := P + 1), Finset.filter_insert, if_pos hp,
        Finset.prod_insert (by simp)]
    exact h.le
  · have h : primorial (P + 1) = primorial P := by
      unfold primorial
      rw [Finset.range_add_one (n := P + 1), Finset.filter_insert, if_neg hp]
    rw [h]
    exact Nat.le_mul_of_pos_left _ (by omega)

lemma choose_P (x : ℝ) (hx : 1 ≤ x) : ∃ P : ℕ, (primorial P : ℝ) ≤ x ∧
    x < (primorial (P + 1) : ℝ) ∧ ∀ P0 : ℕ, (primorial P0 : ℝ) ≤ x → P0 ≤ P := by
  have hx0 : 0 ≤ x := by linarith
  set m := ⌊x⌋₊ with hm
  have hm1 : 1 ≤ m := Nat.le_floor (by simpa using hx)
  refine ⟨Nat.findGreatest (fun q => primorial q ≤ m) m, ?_, ?_, ?_⟩
  · have h := Nat.findGreatest_spec (P := fun q => primorial q ≤ m) (m := 0) (n := m)
      (Nat.zero_le _) (by simpa using hm1)
    exact (Nat.le_floor_iff hx0).mp h
  · by_cases hle : Nat.findGreatest (fun q => primorial q ≤ m) m + 1 ≤ m
    · have h := Nat.findGreatest_is_greatest (P := fun q => primorial q ≤ m)
        (Nat.lt_succ_self _) hle
      exact (Nat.floor_lt hx0).mp (not_le.mp h)
    · have h1 : m < primorial (Nat.findGreatest (fun q => primorial q ≤ m) m + 1) :=
        lt_of_lt_of_le (not_le.mp hle) le_primorial_self
      exact (Nat.floor_lt hx0).mp h1
  · intro P0 hP0
    have h1 : primorial P0 ≤ m := (Nat.le_floor_iff hx0).mpr hP0
    exact Nat.le_findGreatest (le_trans le_primorial_self h1) h1

theorem final : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in Filter.atTop, ∃ n : ℕ, (n : ℝ) ≤ x ∧
    Real.exp (((Real.log 2) ^ 2 - δ) * Real.log x / (Real.log (Real.log x)) ^ 2) ≤
      (Erdos1100.tauPerp n : ℝ) := by
  intro δ hδ
  have ha : 0 < (log 2) ^ 2 := pow_pos (Real.log_pos (by norm_num)) 2
  have hδ' : 0 < min δ ((log 2) ^ 2 / 2) := lt_min hδ (by positivity)
  have hδ'a : min δ ((log 2) ^ 2 / 2) < (log 2) ^ 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨P0, hP0⟩ := Filter.eventually_atTop.mp (main_ev _ hδ' hδ'a)
  filter_upwards [Filter.eventually_ge_atTop (max 1 (primorial P0 : ℝ))] with x hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxP : (primorial P0 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨P, hP1, hP2, hP3⟩ := choose_P x hx1
  have hPP0 := hP3 P0 hxP
  refine ⟨primorial P, hP1, ?_⟩
  have hθ : Chebyshev.theta P = log (primorial P) := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have hpos : (0 : ℝ) < primorial P := by exact_mod_cast primorial_pos P
  have hY1 : Chebyshev.theta P ≤ log x := by rw [hθ]; exact Real.log_le_log hpos hP1
  have hY2 : log x ≤ Chebyshev.theta P + log ((P : ℝ) + 1) := by
    have h1 : x ≤ ((P : ℝ) + 1) * primorial P := by
      have h2 : (primorial (P + 1) : ℝ) ≤ ((P : ℝ) + 1) * primorial P := by
        exact_mod_cast primorial_succ_le P
      linarith
    have h3 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by positivity) hpos.ne'] at h3
    rw [hθ]; linarith
  have key := hP0 P hPP0 (log x) hY1 hY2
  refine le_trans (Real.exp_le_exp.mpr ?_) key
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hx1)
  linarith [min_le_left δ ((log 2) ^ 2 / 2)]

end E1100

theorem OMA.solution : type_of% @Erdos1100.erdos_1100.variants.erdos_tenenbaum_max := by
  exact E1100.final
