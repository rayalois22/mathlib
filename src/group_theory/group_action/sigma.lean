/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import group_theory.group_action.defs

/-!
# Sigma instances for additive and multiplicative actions

This file defines instances for arbitrary sum of additive and multiplicative actions.
-/

variables {ι : Type*} {M N : Type*} {α : ι → Type*}

namespace sigma

section has_scalar
variables [Π i, has_scalar M (α i)] [Π i, has_scalar N (α i)] (a : M) (i : ι) (b : α i)
  (x : Σ i, α i)

@[to_additive sum.has_vadd] instance : has_scalar M (Σ i, α i) := ⟨λ a, sigma.map id $ λ i, (•) a⟩

@[to_additive] lemma smul_def : a • x = x.map id (λ i, (•) a) := rfl
@[simp, to_additive] lemma smul_mk : a • mk i b = ⟨i, a • b⟩ := rfl

instance [has_scalar M N] [Π i, is_scalar_tower M N (α i)] : is_scalar_tower M N (Σ i, α i) :=
⟨λ a b x, by { cases x, rw [smul_mk, smul_mk, smul_mk, smul_assoc] }⟩

@[to_additive] instance [Π i, smul_comm_class M N (α i)] : smul_comm_class M N (Σ i, α i) :=
⟨λ a b x, by { cases x, rw [smul_mk, smul_mk, smul_mk, smul_mk, smul_comm] }⟩

instance [Π i, has_scalar Mᵐᵒᵖ (α i)] [Π i, is_central_scalar M (α i)] :
  is_central_scalar M (Σ i, α i) :=
⟨λ a x, by { cases x, rw [smul_mk, smul_mk, op_smul_eq_smul] }⟩

@[to_additive] instance [has_faithful_smul M (α i)] : has_faithful_smul M (Σ i, α i) :=
⟨λ x y h, eq_of_smul_eq_smul $ λ a : α i, heq_iff_eq.1 (ext_iff.1 $ h $ mk i a).2⟩

end has_scalar

@[to_additive] instance {m : monoid M} [Π i, mul_action M (α i)] : mul_action M (Σ i, α i) :=
{ mul_smul := λ a b x, by { cases x, rw [smul_mk, smul_mk, smul_mk, mul_smul] },
  one_smul := λ x, by { cases x, rw [smul_mk, one_smul] } }

end sigma
