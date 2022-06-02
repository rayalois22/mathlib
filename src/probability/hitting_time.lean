/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.notation
import probability.stopping

/-! # Hitting times -/

open_locale probability_theory measure_theory ennreal nnreal filter

open measure_theory topological_space

namespace probability_theory

variables {ι α β : Type*} [complete_lattice ι] {mα : measurable_space α} {μ : measure α}
  {s t : set β} {f : ι → α → β} {n : ι} {x : α}

/-- First time at which the random process `f` belongs to the set `s`. -/
def hitting_time (f : ι → α → β) (s : set β) : α → ι :=
λ x, Inf {i | f i x ∈ s}

@[simp] lemma hitting_time_univ : hitting_time f set.univ = λ _, ⊥ := by simp [hitting_time]

@[simp] lemma hitting_time_empty : hitting_time f (∅ : set β) = λ _, ⊤ := by simp [hitting_time]

lemma hitting_time_inter_ge_sup :
  hitting_time f s ⊔ hitting_time f t ≤ hitting_time f (s ∩ t) :=
begin
  intro x,
  simp only [hitting_time, pi.sup_apply, set.mem_inter_eq, le_Inf_iff, set.mem_set_of_eq,
    sup_le_iff, and_imp],
  exact ⟨λ i hixs hixt, Inf_le hixs, λ i hixs hixt, Inf_le hixt⟩,
end

lemma hitting_time_union_le_inf :
  hitting_time f (s ∪ t) ≤ hitting_time f s ⊓ hitting_time f t :=
begin
  intro x,
  simp only [hitting_time, pi.inf_apply, set.mem_union_eq, le_inf_iff, le_Inf_iff,
    set.mem_set_of_eq],
  exact ⟨λ i hixs, Inf_le (or.inl hixs), λ i hixt, Inf_le (or.inr hixt)⟩,
end

lemma exists_mem_of_hitting_time_lt_top (h : hitting_time f s x ≠ ⊤) : ∃ j, f j x ∈ s :=
begin
  by_contra' h_forall_nmem,
  simpa only [hitting_time, h_forall_nmem, set.set_of_false, Inf_empty, not_top_lt] using h,
end

lemma hitting_time_mem {ι} [complete_linear_order ι] [is_well_order ι (<)]
  {f : ι → α → β} (h : hitting_time f s x ≠ ⊤) :
  f (hitting_time f s x) x ∈ s :=
Inf_mem (exists_mem_of_hitting_time_lt_top h)

lemma hitting_time_le_iff {ι} [complete_linear_order ι] [is_well_order ι (<)]
  {f : ι → α → β} {n : ι} (hn : n ≠ ⊤) :
  hitting_time f s x ≤ n ↔ ∃ j ≤ n, f j x ∈ s :=
⟨λ h, ⟨hitting_time f s x, h, hitting_time_mem (h.trans_lt hn.lt_top).ne⟩,
  λ h, (Inf_le (by exact h.some_spec.some_spec)).trans h.some_spec.some⟩

section nat

variables {𝒢 : filtration (with_top ℕ) mα} {g : (with_top ℕ) → α → β}

instance with_top.encodable {α} [encodable α] : encodable (with_top α) := option.encodable
instance with_bot.encodable {α} [encodable α] : encodable (with_bot α) := option.encodable

instance : is_well_order (with_top ℕ) (<) := ⟨with_top.well_founded_lt nat.lt_wf⟩

lemma is_stopping_time_hitting_time [topological_space β] [metrizable_space β] [measurable_space β]
  [borel_space β]
  (hg : adapted 𝒢 g) (hs : measurable_set s) :
  is_stopping_time 𝒢 (hitting_time g s) :=
begin
  intro i,
  by_cases hi_top : i = ⊤,
  { rw hi_top, simp, },
  simp_rw hitting_time_le_iff hi_top,
  have : {x : α | ∃ j ≤ i, g j x ∈ s} = ⋃ j ≤ i, {x | g j x ∈ s},
  { ext1 x, simp only [set.mem_set_of_eq, set.mem_Union], },
  rw this,
  refine measurable_set.bUnion (set.countable_encodable _) (λ n hn, 𝒢.mono (hn) _ _),
  exact (hg n).measurable hs,
end

end nat

end probability_theory
