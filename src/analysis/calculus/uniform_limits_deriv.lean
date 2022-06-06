/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import analysis.calculus.mean_value
import analysis.normed_space.is_R_or_C

/-!
# Swapping limits and derivatives via uniform convergence

The purpose of this file is to prove that the derivative of the pointwise limit of a sequence of
functions is the pointwise limit of the functions' derivatives when the derivatives converge
_uniformly_. The formal statement appears as `has_fderiv_at_of_tendsto_uniformly_on`.

## Main statements

* `has_fderiv_at_of_tendsto_uniformly_on` : If `f : ℕ → E → G` is a sequence of functions with
  derivatives `f' : ℕ → (E → (E →L[𝕜] G))` and the `f` converge pointwise to `g` and the `f'`
  converge _uniformly_ on some closed ball, then the derivative of `g'` is the pointwise limit
  of the `f'` on the closed ball

## Implementation notes

Our proof utilizes three major components:
  * `convex.norm_image_sub_le_of_norm_has_fderiv_within_le`: The mean value inequality for
    vector-valued functions over `ℝ` and `ℂ`
  * `norm_add_le`: The triangle inequality
  * `uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto` which allows us to upgrade pointwise
    convergence to uniform convergence by showing that the Cauchy sequences converge uniformly to 0

## Tags

uniform convergence, limits of derivatives
-/

open finset filter metric
open_locale uniformity filter topological_space

section uniform

variables {α : Type*} {β : Type*} {ι : Type*} [uniform_space β]
  {f f' : ι → α → β} {g g' : α → β} {l : filter ι} {x : α} {s : set α}

lemma tendsto.tendsto_uniformly_on_const
  {g : ι → β} {b : β} (hg : tendsto g l (𝓝 b)) (s : set α) :
  tendsto_uniformly_on (λ n : ι, λ a : α, g n) (λ a : α, b) l s :=
begin
  sorry,
end

lemma filter.eventually_diag_of_eventually_prod {p : ι × ι → Prop}
  (h : ∀ᶠ i in (l ×ᶠ l), p i) : (∀ᶠ i in l, p (i, i)) :=
begin
  rw eventually_iff,
  rw [eventually_iff, mem_prod_iff] at h,
  obtain ⟨t, ht, s, hs, hst⟩ := h,
  have ht_in_l : t ∩ s ∈ l, simp [hs, ht],
  refine l.sets_of_superset ht_in_l _,
  rw set.subset_def,
  intros x hx,
  have := calc (x, x) ∈ (t ∩ s) ×ˢ (t ∩ s) : by simpa using hx
    ... ⊆ t ×ˢ s : begin
      rw set.subset_def,
      intros y hy,
      simp at hy,
      simp [hy],
    end
    ... ⊆ {x : ι × ι | p x} : hst,
  simpa using this,
end

section add_group
variables [add_group β] [uniform_add_group β]

lemma tendsto_uniformly_on.add
  (hf : tendsto_uniformly_on f g l s)
  (hf' : tendsto_uniformly_on f' g' l s) :
  tendsto_uniformly_on (f + f') (g + g') l s :=
λ u hu, silly (((hf.prod hf').comp' uniform_continuous_add) u hu)

lemma tendsto_uniformly_on.sub
  (hf : tendsto_uniformly_on f g l s)
  (hf' : tendsto_uniformly_on f' g' l s) :
  tendsto_uniformly_on (f - f') (g - g') l s :=
λ u hu, silly (((hf.prod hf').comp' uniform_continuous_sub) u hu)

end add_group

lemma uniform_cauchy_seq_on.prod' {β' : Type*} [uniform_space β']
  {f' : ι → α → β'} {s : set α}
  (h : uniform_cauchy_seq_on f l s) (h' : uniform_cauchy_seq_on f' l s) :
  uniform_cauchy_seq_on (λ (i : ι) a, (f i a, f' i a)) l s :=
begin
  intros u hu,
  rw [uniformity_prod_eq_prod, filter.mem_map, mem_prod_iff] at hu,
  obtain ⟨t, ht, t', ht', htt'⟩ := hu,
  apply (silly ((h t ht).prod_mk (h' t' ht'))).mono,
  intros x hx y hy,
  cases hx with hxt hxt',
  specialize hxt y hy,
  specialize hxt' y hy,
  simp only at hxt hxt',
  simp only,
  have := calc ((f x.fst y, f x.snd y), (f' x.fst y, f' x.snd y)) ∈ t ×ˢ t' : by simp [hxt, hxt']
    ... ⊆ (λ (p : (β × β) × β' × β'), ((p.fst.fst, p.snd.fst), p.fst.snd, p.snd.snd)) ⁻¹' u : htt',
  simpa using this,
end

section add_group
variables [add_group β] [uniform_add_group β]

lemma uniform_cauchy_seq_on.add
  (hf : uniform_cauchy_seq_on f l s) (hf' : uniform_cauchy_seq_on f' l s) :
  uniform_cauchy_seq_on (f + f') l s :=
λ u hu, by simpa using (((hf.prod' hf').comp' uniform_continuous_add) u hu)

lemma uniform_cauchy_seq_on.sub
  (hf : uniform_cauchy_seq_on f l s) (hf' : uniform_cauchy_seq_on f' l s) :
  uniform_cauchy_seq_on (f - f') l s :=
λ u hu, by simpa using (((hf.prod' hf').comp' uniform_continuous_sub) u hu)

end add_group

lemma foo {α 𝕜 β : Type*} [normed_group β] [normed_space ℝ β]
  {f : ℕ → α → β} {s : set α} {l : filter ℕ}
  (hf : tendsto_uniformly_on (λ n : (ℕ × ℕ), λ z : α, f n.fst z - f n.snd z) 0 at_top s) :
  uniform_cauchy_seq_on f at_top s :=
begin
  rw metric.uniform_cauchy_seq_on_iff,
  rw metric.tendsto_uniformly_on_iff at hf,
  intros ε hε,
  specialize hf ε hε,
  rw eventually_at_top at hf,
  cases hf with a ha,
  use max a.fst a.snd,
  intros m hm n hn x hx,
  have : (m, n) ≥ a, sorry,
  specialize ha (m, n) this x hx,
  simp at ha,
  rw dist_eq_norm,
  exact ha,
end

lemma foobar {α β 𝕜 ι: Type*} [normed_group β] [normed_field 𝕜] [normed_space 𝕜 β]
  {f : ι → α → β} {g : α → 𝕜} {s : set α} {l : filter ι} {C : ℝ}
  (hf : tendsto_uniformly_on f 0 l s) (hg : ∀ x : α, x ∈ s → ∥g x∥ ≤ C) :
  tendsto_uniformly_on (λ n : ι, λ z : α, (g z) • f n z) 0 l s :=
begin
  rw metric.tendsto_uniformly_on_iff at hf ⊢,
  intros ε hε,

  -- C must be nonnegative
  by_cases hC : C < 0,
  { refine (hf ε hε).mono (λ i h x hx, _),
    exfalso,
    linarith [hC, calc 0 ≤ ∥g x∥ : by simp ... ≤ C : hg x hx], },
  push_neg at hC,

  cases lt_or_eq_of_le hC,
  swap,
  { -- The case C = 0 is trivial
    apply eventually_of_forall,
    intros i x hx,
    specialize hg x hx,
    simp [h.symm] at hg,
    simp [hg, hε.lt], },

  -- The case with C positive is where the work is
  apply (hf (C⁻¹ * ε) ((mul_pos (inv_pos.mpr h) hε.lt).gt)).mono,
  intros i hf' x hx,
  have := mul_lt_mul' (hg x hx) (hf' x hx) (by simp) h,
  rw [mul_inv_cancel_left₀ h.ne.symm] at this,
  rw [pi.zero_apply, dist_zero_left, norm_smul],
  simpa using this,
end

end uniform

section limits_of_derivatives

variables {E : Type*} [normed_group E] [normed_space ℝ E]
  {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {f : ℕ → E → G} {g : E → G} {f' : ℕ → (E → (E →L[𝕜] G))} {g' : E → (E →L[𝕜] G)}
  {x y z : E} {r C : ℝ}

/-- A convenience theorem for utilizing the mean value theorem for differences of
differentiable functions -/
lemma mean_value_theorem_for_differences {f : E → G} {f' : E → (E →L[𝕜] G)}
  {s : set E} (hs : convex ℝ s)
  (hf : ∀ (y : E), y ∈ s → has_fderiv_at f (f' y) y)
  (hg : ∀ (y : E), y ∈ s → has_fderiv_at g (g' y) y)
  (hbound : ∀ (y : E), y ∈ s → ∥f' y - g' y∥ ≤ C)
  (hy : y ∈ s) (hz : z ∈ s) :
  ∥y - z∥⁻¹ * ∥(f y - g y) - (f z - g z)∥ ≤ C :=
begin
  -- Differences of differentiable functions are differentiable
  have hderiv : ∀ (y : E), y ∈ s →
    has_fderiv_within_at (f - g) ((f' - g') y) s y,
  { intros y hy,
    have := ((hf y hy).sub (hg y hy)).has_fderiv_within_at,
    simp only [pi.sub_apply],
    have : (λ x : E, f x - g x) = f - g, { funext, simp only [pi.sub_apply], },
    rwa ←this, },

  -- Apply the mean value theorem
  have := convex.norm_image_sub_le_of_norm_has_fderiv_within_le
    hderiv hbound hs hz hy,

  -- Auxiliary lemmas necessary for algebraic manipulation
  have h_le : ∥y - z∥⁻¹ ≤ ∥y - z∥⁻¹, { exact le_refl _, },
  have C_nonneg : 0 ≤ C,
  { calc 0 ≤ ∥f' y - g' y∥ : norm_nonneg _ ... ≤ C : hbound y hy, },
  have h_le' : 0 ≤ C * ∥y - z∥, exact mul_nonneg C_nonneg (by simp),

  -- The case y = z is degenerate. Eliminate it
  by_cases h : y = z,
  { simp only [h, C_nonneg, sub_self, norm_zero, mul_zero], },
  have h_ne_zero : ∥y - z∥ ≠ 0,
  { simp only [ne.def, norm_eq_zero],
    exact λ hh, h (sub_eq_zero.mp hh), },

  -- Final manipulation
  have := mul_le_mul this h_le (by simp) h_le',
  simp only [pi.sub_apply] at this,
  rw mul_inv_cancel_right₀ h_ne_zero at this,
  rwa mul_comm,
end

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `∥z - y∥⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `∥z - y∥⁻¹ • (g z - g y)` -/
lemma difference_quotients_converge_uniformly
  {s : set E} (hs : convex ℝ s)
  (hf : ∀ (n : ℕ), ∀ (y : E), y ∈ s → has_fderiv_at (f n) (f' n y) y)
  (hfg : ∀ (y : E), y ∈ s → tendsto (λ n, f n y) at_top (𝓝 (g y)))
  (hfg' : tendsto_uniformly_on f' g' at_top s) :
  ∀ y : E, y ∈ s →
    tendsto_uniformly_on
      (λ n : ℕ, λ z : E, (∥z - y∥⁻¹ : 𝕜) • ((f n z) - (f n y)))
      (λ z : E, (∥z - y∥⁻¹ : 𝕜) • ((g z) - (g y))) at_top s :=
begin
  -- Rewrite the Cauchy sequence as a difference quotient of the difference of functions
  intros y hy,
  refine uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto _
    (λ z hz, ((hfg z hz).sub (hfg y hy)).const_smul _),
  simp_rw [normed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero, ←smul_sub],
  have : ∀ a b c d : G, a - b - (c - d) = a - c - (b - d),
  { intros a b c d,
    rw [←sub_add, ←sub_add, sub_sub, sub_sub],
    conv { congr, congr, congr, skip, rw add_comm, }, },
  conv { congr, funext, rw this, },

  -- We'll show this difference quotient is uniformly arbitrarily small
  rw normed_group.tendsto_uniformly_on_zero,
  intros ε hε,

  -- The uniform convergence of the derivatives allows us to invoke the mean value theorem
  have := tendsto_uniformly_on.uniform_cauchy_seq_on hfg',
  rw [normed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero, normed_group.tendsto_uniformly_on_zero] at this,

  have two_inv_pos : 0 < (2 : ℝ)⁻¹, simp,
  have ε_over_two_pos : 0 < (2⁻¹ * ε),
  { exact mul_pos two_inv_pos hε.lt, },

  refine ((this (2⁻¹ * ε) ε_over_two_pos.gt).mono (λ N h y hy, (h y hy).le)).mono _,
  intros N h z hz,

  have mvt := mean_value_theorem_for_differences hs (hf N.fst) (hf N.snd) h hz hy,
  rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
  refine lt_of_le_of_lt mvt _,
  rw ←div_eq_inv_mul,
  exact half_lt_self hε.lt,
end

lemma uniform_convergence_of_uniform_convergence_derivatives
  {s : set E} (hs : bounded s) (hsc : convex ℝ s)
  (hf : ∀ (n : ℕ), ∀ (y : E), y ∈ s → has_fderiv_at (f n) (f' n y) y)
  (hfg : ∀ (y : E), y ∈ s → tendsto (λ n, f n y) at_top (𝓝 (g y)))
  (hfg' : tendsto_uniformly_on f' g' at_top s) :
  tendsto_uniformly_on f g at_top s :=
begin
  -- Proof strategy: We have assumed that f → g pointwise, so it suffices to show that
  -- `f` is a *uniform* cauchy sequence on `s`. But for any `y`, we have
  -- `|f m y - f n y| ≤ |(f m - f n) y - (f m - f n) x| + |f m x - f n x|` by
  -- the triangle inequality and "adding zero". Here `x` is fixed

  -- The case s is empty is trivial. Elimintate it and extract a base point `x`
  by_cases hs' : ¬s.nonempty,
  { rw set.not_nonempty_iff_eq_empty at hs',
    rw hs',
    exact tendsto_uniformly_on_of_empty, },
  push_neg at hs',
  cases hs' with x hx,

  -- Get a _positive_ bound on the diameter of s
  cases hs with C' hC',
  let C := max C' 1,
  have hCpos : 0 < C, calc (0 : ℝ) < 1 : by simp ... ≤ max C' 1 : by simp,
  have hC : ∀ (x : E), x ∈ s → ∀ (y : E), y ∈ s → dist x y ≤ C,
  { intros x hx y hy,
    calc dist x y ≤ C' : hC' x hx y hy ... ≤ C : by simp [C], },

  -- Study (λ n y, f n y - f n x) instead of f
  refine uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto _ hfg,
  have : f = (λ n : ℕ, λ y : E, f n y - f n x) + (λ n : ℕ, λ y : E, f n x),
  { ext, simp, },
  rw this,
  have := (tendsto.tendsto_uniformly_on_const (hfg x hx) s).uniform_cauchy_seq_on,
  refine uniform_cauchy_seq_on.add _ this,
  rw normed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero,
  rw normed_group.tendsto_uniformly_on_zero,
  intros ε hε,
  have := tendsto_uniformly_on.uniform_cauchy_seq_on hfg',
  rw normed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero at this,
  rw normed_group.tendsto_uniformly_on_zero at this,

  have ε_over_two_pos : 0 < C⁻¹ * (2⁻¹ * ε),
  { exact mul_pos (inv_pos.mpr hCpos) (mul_pos (by simp) hε.lt), },

  refine ((this (C⁻¹ * (2⁻¹ * ε)) ε_over_two_pos.gt).mono (λ N h y hy, (h y hy).le)).mono _,
  intros N h y hy,

  -- We need to rule out the case when x = y, where the result is trivial
  by_cases hxy : x = y, simp [hxy, hε.lt],
  have hxy' : ∥y - x∥ ≠ 0, {simp, intros h, rw sub_eq_zero at h, exact hxy h.symm, },

  -- With this in hand, we can apply the mean value theorem and our final manipulations
  have mvt := mean_value_theorem_for_differences hsc (hf N.fst) (hf N.snd) h hy hx,
  simp_rw dist_eq_norm at hC,
  have := mul_le_mul (hC y hy x hx) mvt (mul_nonneg (by simp) (by simp)) hCpos.le,
  rw mul_inv_cancel_left₀ hxy' at this,
  rw mul_inv_cancel_left₀ (ne_of_lt hCpos).symm at this,
  have haaa : ∀ a b c d : G, a - b - (c - d) = a - c - (b - d),
  { intros a b c d,
    rw [←sub_add, ←sub_add, sub_sub, sub_sub],
    conv { congr, congr, congr, skip, rw add_comm, }, },
  conv { congr, funext, rw haaa, },
  refine lt_of_le_of_lt this _,
  rw ←div_eq_inv_mul,
  exact half_lt_self hε.lt,
end

/-- (d/dx) lim_{n → ∞} f_n x = lim_{n → ∞} f'_n x on a closed ball when the f'_n
converge _uniformly_ to their limit. -/
lemma has_fderiv_at_of_tendsto_uniformly_on
  (hf : ∀ (n : ℕ), ∀ (y : E), y ∈ closed_ball x r → has_fderiv_at (f n) (f' n y) y)
  (hfg : ∀ (y : E), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (𝓝 (g y)))
  (hfg' : tendsto_uniformly_on f' g' at_top (closed_ball x r)) :
  ∀ y : E, y ∈ ball x r → has_fderiv_at g (g' y) y :=
begin
  -- We do the famous "ε / 3 proof" which will involve several bouts of utilizing
  -- uniform continuity. First we setup our goal in terms of ε and δ
  intros y hy,
  rw [has_fderiv_at_iff_tendsto, tendsto_nhds_nhds],

  -- Now some important auxiliary facts such as:
  have hyc : y ∈ closed_ball x r,
  { exact (mem_ball.mp hy).le, },

  -- uniform convergence of the derivatives implies uniform convergence of the primal
  have hfguc := uniform_convergence_of_uniform_convergence_derivatives hf hfg hfg',

  -- convergence of the primal and uniform convergence of the derivatives implies
  -- uniform convergence of the difference quotients
  have hdiff := difference_quotients_converge_uniformly (convex_closed_ball x r) hf hfg hfg' y hyc,

  -- The first (ε / 3) comes from the convergence of the derivatives
  intros ε hε,
  have : 0 < (3 : ℝ)⁻¹, simp, linarith,
  have ε_over_three_pos : 0 < (3⁻¹ * ε),
  { exact mul_pos this hε.lt, },

  rw tendsto_uniformly_on_iff at hfg',
  specialize hfg' (3⁻¹ * ε) ε_over_three_pos.gt,
  rw eventually_at_top at hfg',
  rcases hfg' with ⟨N1, hN1⟩,

  -- The second (ε / 3) comes from the uniform convergence of the difference quotients
  rw tendsto_uniformly_on_iff at hdiff,
  specialize hdiff (3⁻¹ * ε) ε_over_three_pos.gt,
  rw eventually_at_top at hdiff,
  rcases hdiff with ⟨N2, hN2⟩,

  -- These two N determine our final N
  let N := max N1 N2,

  -- The final (ε / 3) comes from the definition of a derivative
  specialize hf N y hyc,
  rw [has_fderiv_at_iff_tendsto, tendsto_nhds_nhds] at hf,
  specialize hf (3⁻¹ * ε) ε_over_three_pos.gt,
  rcases hf with ⟨δ', hδ', hf⟩,

  -- Choose our final δ
  let δ := min (r - dist y x) δ',
  have hδ : δ > 0,
  { refine lt_min _ hδ'.lt,
    rw sub_pos,
    exact hy, },

  -- Start the final manipulation
  use [δ, hδ],
  intros x' hx',
  have hxc : x' ∈ closed_ball x r,
  { have foo := calc dist x' y < δ : hx' ... ≤ r - dist y x : by simp [δ],
    calc dist x' x ≤ dist x' y + dist y x : dist_triangle _ _ _ ... ≤ r : by linarith, },
  have hxy : dist x' y < δ', calc dist x' y < δ : hx' ... ≤ δ' : by simp [δ],
  specialize hf hxy,

  -- There's a technical issue where we need to rule out the case y = x'
  by_cases hy' : y = x',
  { simp [hy', hε.lt], },
  have hx'y : x' - y ≠ 0, exact λ H, hy' (sub_eq_zero.mp H).symm,
  have hx'yy : 0 < ∥x' - y∥, simp only [hx'y, norm_pos_iff, ne.def, not_false_iff],

  -- Our three inequalities come from `hf`, `hN1`, and `hN2`. Get them and the goal in
  -- shape for the final triangle inequality application
  specialize hN1 N (by simp) y hyc,
  rw dist_comm at hN1,
  have hN1 := (f' N y - g' y).le_of_op_norm_le hN1.le (x' - y),
  rw [←mul_inv_le_iff' hx'yy, mul_comm] at hN1,

  specialize hN2 N (by simp) x' hxc,
  rw [dist_eq_norm, ←smul_sub, norm_smul] at hN2,
  simp only [norm_inv, is_R_or_C.norm_coe_norm] at hN2,

  rw dist_eq_norm at hf ⊢,
  simp only [map_sub, sub_zero, norm_mul, norm_inv, norm_norm] at hf,
  simp only [algebra.id.smul_eq_mul, sub_zero, norm_mul, norm_inv, norm_norm],

  -- Final calculation
  calc  ∥x' - y∥⁻¹ * ∥g x' - g y - (g' y) (x' - y)∥ =
    ∥x' - y∥⁻¹ * ∥(g x' - g y - (f N x' - f N y)) +
    ((f N x' - f N y) - ((f' N y) x' - (f' N y) y)) +
    ((f' N y - g' y) (x' - y))∥ : by simp
  ... ≤ ∥x' - y∥⁻¹ * ∥(g x' - g y - (f N x' - f N y))∥ +
    ∥x' - y∥⁻¹ * ∥((f N x' - f N y) - ((f' N y) x' - (f' N y) y))∥ +
    ∥x' - y∥⁻¹ * ∥((f' N y - g' y) (x' - y))∥ : begin
      rw [←mul_add (∥x' - y∥⁻¹) _ _, ←mul_add (∥x' - y∥⁻¹) _ _],
      have : ∥x' - y∥⁻¹ ≤ ∥x' - y∥⁻¹, exact le_refl _,
      refine mul_le_mul this _ (by simp) (by simp),
      exact norm_add₃_le _ _ _,
    end
  ... < 3⁻¹ * ε + 3⁻¹ * ε + 3⁻¹ * ε : add_lt_add_of_lt_of_le (add_lt_add hN2 hf) hN1
  ... = ε : by ring,
end

end limits_of_derivatives
