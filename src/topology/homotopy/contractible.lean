/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/

import topology.homotopy.path
import topology.homotopy.equiv

/-!
# Contractible spaces

In this file, we define `contractible_space`, a space that is homotopy equivalent to `unit`.
-/

noncomputable theory


namespace continuous_map

/-- A map is nullhomotopic if it is homotopic to some constant map -/
def nullhomotopic {X Y : Type*} [topological_space X] [topological_space Y] (f : C(X, Y)) : Prop :=
∃ y : Y, homotopic f (continuous_map.const _ y)

end continuous_map

open continuous_map

class contractible_space (X : Type*) [topological_space X] : Prop :=
(hequiv_unit : nonempty (homotopy_equiv X unit))

namespace contractible_space
variables (X : Type*) [topological_space X] [contractible_space X]

@[priority 50]
instance : nonempty X := nonempty.map (λ h, homotopy_equiv.inv_fun h ()) hequiv_unit

lemma id_nullhomotopic : (continuous_map.id X).nullhomotopic :=
begin
  obtain ⟨hv⟩ := @hequiv_unit X _ _,
  use hv.inv_fun (),
  convert hv.left_inv.symm,
  ext, simp, congr,
end

lemma contractible_iff_id_nullhomotopic (Y : Type*) [topological_space Y] :
  contractible_space Y ↔ (continuous_map.id Y).nullhomotopic :=
begin
  split, { introI, apply id_nullhomotopic, },
  rintro ⟨p, h⟩,
  refine_struct { hequiv_unit := ⟨{ to_fun := continuous_map.const _ (),
    inv_fun := continuous_map.const _ p }⟩ },
  { exact h.symm, }, { convert homotopic.refl (continuous_map.id unit), ext, },
end

instance : path_connected_space X :=
begin
  obtain ⟨p, ⟨h⟩⟩ := id_nullhomotopic X,
  have : ∀ x, joined p x := λ x, nonempty.intro (h.eval_at x).symm,
  rw path_connected_space_iff_eq, use p, ext, tauto,
end

end contractible_space
