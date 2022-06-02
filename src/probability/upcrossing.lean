/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.martingale
import probability.hitting_time

/-! # Upcrossing lemma -/

open_locale probability_theory measure_theory ennreal nnreal filter big_operators

open measure_theory

namespace probability_theory

variables {ι α β : Type*} {mα : measurable_space α} {μ : measure α}

noncomputable
def sup_norm_Iic [has_le ι] [normed_group β] (f : ι → α → β) (n : ι) : α → ℝ :=
λ x, ⨆ m ≤ n, ∥f m x∥

noncomputable
def sup_norm [normed_group β] (f : ι → α → β) : α → ℝ :=
λ x, ⨆ m, ∥f m x∥

variables {ℱ : filtration (with_top ℕ) mα} [sigma_finite_filtration μ ℱ]

noncomputable def first_gt_before (f : with_top ℕ → α → ℝ) (c : ℝ) (n : ℕ) : α → with_top ℕ :=
λ x, min (hitting_time f {y | c < y} x) (n + 1)

lemma first_gt_before_le_iff {f : with_top ℕ → α → ℝ} {c : ℝ} {i n : ℕ} (hin : i ≤ n) (x : α) :
  first_gt_before f c n x ≤ i ↔ ∃ k ≤ i, c < f k x :=
begin
  rw [first_gt_before, min_le_iff, hitting_time_le_iff (with_top.coe_ne_top : ↑i ≠ ⊤)],
  norm_cast,
  have : ¬ n + 1 ≤ i := λ h, nat.not_succ_le_self n (h.trans hin),
  simp only [this, set.mem_set_of_eq, exists_prop, or_false],
  split; rintro ⟨k, hk_le, hk_c_lt⟩,
  { obtain ⟨k_nat, hk_nat_eq⟩ := with_top.ne_top_iff_exists.mp
      (hk_le.trans_lt (with_top.coe_lt_top _)).ne,
    refine ⟨k_nat, with_top.coe_le_coe.mp (hk_nat_eq.le.trans hk_le), _⟩,
    rwa ← hk_nat_eq at hk_c_lt, },
  { exact ⟨k, with_top.coe_le_coe.mpr hk_le, hk_c_lt⟩, },
end

lemma first_gt_before_le_succ {f : with_top ℕ → α → ℝ} {c : ℝ} {n : ℕ} {x : α} :
  first_gt_before f c n x ≤ n + 1 :=
min_le_right _ _

lemma gt_of_first_gt_before_eq {f : with_top ℕ → α → ℝ} {c : ℝ} {n k : ℕ} {x : α}
  (h : first_gt_before f c n x = k) :
  c < f k x :=
begin
  sorry,
end

lemma is_stopping_time_first_gt_before (f : with_top ℕ → α → ℝ) (c : ℝ) (n : ℕ) (h : adapted ℱ f) :
  is_stopping_time ℱ (first_gt_before f c n) :=
(is_stopping_time_hitting_time h (measurable_set_lt measurable_const measurable_id)).min
  (is_stopping_time_const _ _)

lemma sup_norm_Iic_gt_iff_first_gt_before_le {f : with_top ℕ → α → ℝ} {c : ℝ} {n : ℕ} {x : α}
  [decidable_pred (λ x, (∃ (k : ℕ) (H : k ≤ n), c < f k x))]
  (hf_nonneg : ∀ n, 0 ≤ f n) :
  c < sup_norm_Iic f n x ↔ first_gt_before f c n x ≤ n :=
begin
  rw first_gt_before_le_iff le_rfl,
  rw sup_norm_Iic,
  simp only [exists_prop],
  sorry,
end

lemma of_real_integral_eq_lintegral_of_real {f : α → ℝ} (hfi : integrable f μ) (f_nn : 0 ≤ f) :
  ennreal.of_real (∫ x, f x ∂μ) = ∫⁻ x, ennreal.of_real (f x) ∂μ :=
calc ennreal.of_real (∫ x, f x ∂μ) = ennreal.of_real ∫ x, ∥f x∥ ∂μ :
  by { congr, ext1 x, rw [real.norm_eq_abs, abs_eq_self.mpr (f_nn x)], }
... = ∫⁻ x, ∥f x∥₊ ∂μ : of_real_integral_norm_eq_lintegral_nnnorm hfi
... = ∫⁻ x, ennreal.of_real (f x) ∂μ :
  by { congr, ext1 x, rw [← of_real_norm_eq_coe_nnnorm, real.norm_eq_abs,
                          abs_eq_self.mpr (f_nn x)] }

instance {α} [preorder α] [topological_space α] [order_topology α] :
  topological_space (with_top α) :=
preorder.topology (with_top α)

instance {α} [preorder α] [topological_space α] [order_topology α] :
  order_topology (with_top α) := ⟨rfl⟩

instance {α} [preorder α] [topological_space α] [order_topology α] [discrete_topology α] :
  discrete_topology (with_top α) :=
{ eq_bot := sorry }

lemma todo {f : with_top ℕ → α → ℝ} (h : submartingale f ℱ μ) (hf_nonneg : ∀ n, 0 ≤ f n)
  (c : ℝ) (n : ℕ) :
  (ennreal.of_real c) * μ {x | c < sup_norm_Iic f n x}
    ≤ ennreal.of_real (∫ x in {x | c < sup_norm_Iic f n x}, f n x ∂μ) :=
begin
  classical,
  let τ : α → with_top ℕ := first_gt_before f c n,
  have hτ_stop : is_stopping_time ℱ τ,
    from is_stopping_time_first_gt_before f c n h.adapted,
  have : ∀ i ≤ n, {x | τ x ≤ i} = ⋃ k ≤ i, {x | c < f k x},
  { intros i hin,
    ext1 x,
    rw [set.mem_set_of_eq, first_gt_before_le_iff hin x],
    simp_rw set.mem_Union,
    refl, },
  have : {x : α | c < sup_norm_Iic f n x} = ⋃ k ≤ n, {x | τ x = k},
  { ext1 x,
    have : c < sup_norm_Iic f n x ↔ τ x ≤ n,
      from sup_norm_Iic_gt_iff_first_gt_before_le hf_nonneg,
    rw [set.mem_set_of_eq, this],
    simp only [set.mem_Union, set.mem_set_of_eq, exists_prop],
    refine ⟨λ hyp, _, λ hyp, _⟩,
    sorry,
    sorry, },
  rw this,
  calc ennreal.of_real c * μ (⋃ (k : ℕ) (H : k ≤ n), {x : α | τ x = k})
      ≤ ennreal.of_real c * ∑ k in finset.range (n+1), μ {x : α | τ x = k} : begin
      refine ennreal.mul_le_mul le_rfl _,
      refine le_trans (le_of_eq _) (measure_bUnion_finset_le _ _),
      congr' with k x,
      simp only [set.mem_Union, set.mem_set_of_eq, exists_prop, finset.mem_range,
        and.congr_left_iff],
      exact λ _, nat.lt_succ_iff.symm,
    end
  ... = ∑ k in finset.range (n+1), ennreal.of_real c * μ {x : α | τ x = k} : finset.mul_sum
  ... = ∑ k in finset.range (n+1), ennreal.of_real c *
    ∫⁻ x in{x : α | τ x = k}, (λ _, (1 : ℝ≥0∞)) x ∂μ :
      by simp_rw [lintegral_const, measure.restrict_apply_univ, one_mul]
  ... = ∑ k in finset.range (n+1), ennreal.of_real c *
    ∫⁻ x, {x : α | τ x = k}.indicator (λ _, (1 : ℝ≥0∞)) x ∂μ :
      by { congr, ext1 k, rw lintegral_indicator _ (ℱ.le k _ (hτ_stop.measurable_set_eq k)), }
  ... = ∑ k in finset.range (n+1),
    ∫⁻ x, {x : α | τ x = k}.indicator (λ _, ennreal.of_real c) x ∂μ : begin
      congr,
      ext1 k,
      rw ← lintegral_const_mul,
      { congr, ext1 x, by_cases hx : x ∈ {x : α | τ x = k} ; simp [hx], },
      { exact measurable.indicator (by apply measurable_const)
          (ℱ.le k _ (hτ_stop.measurable_set_eq k)), },
    end
  ... ≤ ∑ k in finset.range (n+1),
    ∫⁻ x, {x : α | τ x = k}.indicator (λ x, ennreal.of_real (f k x)) x ∂μ : begin
      refine finset.sum_le_sum (λ k hk, _),
      sorry,
    end
  ... = ∑ k in finset.range (n+1),
    ennreal.of_real ∫ x, {x : α | τ x = k}.indicator (f k) x ∂μ : begin
      congr,
      ext1 k,
      rw of_real_integral_eq_lintegral_of_real,
      sorry,
      sorry,
      sorry,
    end
  ... ≤ ∑ k in finset.range (n+1),
    ennreal.of_real ∫ x, {x : α | τ x = k}.indicator (μ[f n | ℱ k]) x ∂μ : begin
      refine finset.sum_le_sum (λ k hk, ennreal.of_real_le_of_real _),
      refine integral_mono_ae _ _ _,
      { exact (h.integrable _).indicator (ℱ.le _ _ (hτ_stop.measurable_set_eq (k : with_top ℕ))), },
      { exact integrable_condexp.indicator
          (ℱ.le _ _ (hτ_stop.measurable_set_eq (k : with_top ℕ))),},
      rw finset.mem_range at hk,
      have h_le : (k : with_top ℕ) ≤ n, sorry,
      filter_upwards [h.ae_le_condexp h_le] with x hx,
      by_cases hτx : τ x = (k : with_top ℕ),
      { simpa only [hτx, set.indicator_of_mem, set.mem_set_of_eq] using hx, },
      { simp only [hτx, set.indicator_of_not_mem, set.mem_set_of_eq, not_false_iff], },
      sorry,
    end
  ... = ∑ k in finset.range (n+1),
    ennreal.of_real ∫ x, {x : α | τ x = k}.indicator (f n) x ∂μ : begin
      sorry,
      sorry,
      congr,
      ext1 k,
      congr' 1,
      simp_rw integral_indicator (ℱ.le k _ (hτ_stop.measurable_set_eq k)),
      exact set_integral_condexp _ (h.integrable n) (hτ_stop.measurable_set_eq k),
    end
  ... = ennreal.of_real ∑ k in finset.range (n+1), ∫ x, {x : α | τ x = k}.indicator (f n) x ∂μ : sorry
  ... = ennreal.of_real ∫ x, (∑ k in finset.range (n+1), {x : α | τ x = k}.indicator (f n)) x ∂μ : sorry
  ... = ennreal.of_real (∫ x in {x | c < sup_norm_Iic f n x}, f n x ∂μ) : sorry,
end

end probability_theory


example : 0 = 0 := rfl
