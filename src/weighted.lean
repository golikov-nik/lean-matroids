import data.fintype.basic
import data.fintype.sort
import matroid
import finset
import base_of
import data.real.basic

variables {α : Type*} [fintype α] [decidable_eq α] {m : matroid α} {A B X : finset α} {w : α → ℝ} {order : list α}

open finset

namespace matroid

instance : decidable_pred m.ind := m.ind_dec

@[simp] def is_min_ind (m : matroid α) (w : α → ℝ) (X A : finset α)
  := m.ind A ∧ A ⊆ X ∧ ∀ B ⊆ X, m.ind B → B.card = A.card → A.sum w ≤ B.sum w

lemma insert_subset_of_mem_of_subset {x : α} : x ∈ X → A ⊆ X → insert x A ⊆ X := begin
  repeat { rw subset_iff }, finish,
end

theorem rado_edmonds :
  is_min_ind m w X A → ¬m.base_of X A →
    ∃ x, x ∉ A ∧ is_min_ind m w X (insert x A) := begin
  rintro ⟨indA, hAX, Amin⟩ A_not_base,
  have h_min_ssuperset : ∃ B ⊆ X, is_min_ind m w X B ∧ B.card = A.card + 1, {
    obtain ⟨B, Bgood, Bmin⟩ := exists_min_image (filter (λ S, m.ind S ∧ S.card = A.card + 1) (powerset X)) (λ S, S.sum w) _, {
      simp only [mem_powerset, mem_filter] at Bgood,
      obtain ⟨hBX, indB, Bcard⟩ := Bgood,
      exact ⟨B, hBX, by finish, Bcard⟩,
    }, {
      rw base_of at A_not_base,
      simp only [exists_prop, not_and, not_not, not_forall] at A_not_base,
      specialize A_not_base hAX indA,
      rcases A_not_base with ⟨x, hxA, hxX, hx⟩,
      use insert x A,
      simp only [mem_powerset, mem_filter],
      refine ⟨_, hx, card_insert_of_not_mem hxA⟩,
      exact insert_subset_of_mem_of_subset hxX hAX,
    }
  },
  obtain ⟨B, hBX, ⟨indB, Bmin⟩, Bcard⟩ := h_min_ssuperset,
  obtain ⟨x, hxB, hxA, hx⟩ := m.ind_exchange _ _ indA indB (by linarith),
  refine ⟨x, hxA, _⟩,
  rw is_min_ind,
  refine ⟨hx, _⟩,
  have h_ins_card := card_insert_of_not_mem hxA,
  have insert_subset_X := insert_subset_of_mem_of_subset (hBX hxB) hAX,
  have hw : (insert x A).sum w = B.sum w, {
    apply le_antisymm, {
      rw sum_insert hxA,
      dsimp only,
      suffices : A.sum w ≤ B.sum w - w x, { linarith },
      have w_diff : B.sum w - w x = (B.erase x).sum w, {
        suffices : B.sum w = (B.erase x).sum w + w x, { linarith },
        nth_rewrite 0 ← insert_erase hxB,
        rw sum_insert (not_mem_erase _ _),
        linarith,
      },
      rw w_diff,
      apply Amin, {
        exact subset.trans (erase_subset _ _) hBX,
      }, {
        exact m.ind_subset _ _ (erase_subset _ _) indB,
      },
      suffices : (B.erase x).card + 1 = A.card + 1, { linarith },
      rw card_erase_of_mem' hxB,
      exact Bcard,
    }, {
      apply Bmin.2, all_goals { finish },
    }
  },
  rw [hw, h_ins_card, ← Bcard],
  exact ⟨insert_subset_X, Bmin.2⟩,
end

open list

def find_base_greedy (m : matroid α) : list α → finset α
| [] := ∅
| (x :: l) := let lBase := find_base_greedy l in 
    if m.ind (insert x lBase) then insert x lBase else lBase

lemma base_of_insert (x : α) :
  m.base_of X A → m.base_of (insert x X) (insert x A) ∨
    m.base_of (insert x X) A ∧ ¬m.ind (insert x A) := begin
  intro Abase,
  by_cases h_ind : (m.ind $ insert x A), {
    left,
    refine ⟨insert_subset_insert _ (base_of_subset Abase), h_ind, _⟩,
    intros y hyA hyX,
    have h_not_ind := Abase.2.2 y (λ h, hyA $ subset_insert x A h),
    rw mem_insert at hyX,
    cases hyX, {
      finish,
    }, {
      refine dep_superset _ (h_not_ind hyX),
      exact insert_subset_insert _ (subset_insert _ _),
    }
  }, {
    right,
    refine ⟨_, h_ind⟩,
    refine ⟨subset.trans (base_of_subset Abase) (subset_insert _ _), base_of_ind Abase, _⟩,
    intros y hyA hyX,
    have h_not_ind := Abase.2.2 y hyA,
    finish,
  }
end

lemma find_base_greedy_finds_base_of_order :
  m.base_of order.to_finset (find_base_greedy m order) := begin
  induction order with hd tl h_order, {
    simp only [to_finset_nil],
    rw [find_base_greedy, ← base_of_refl_iff_ind],
    exact m.ind_empty,
  }, {
    rw [to_finset_cons, find_base_greedy],
    dsimp only,
    have base_of_insert_options := base_of_insert hd h_order,
    by_cases (m.ind $ insert hd $ find_base_greedy m tl), {
      finish,
    }, {
      finish using base_of_ind,
    }
  }
end

theorem find_base_greedy_finds_base :
  (∀ x, x ∈ order ↔ x ∈ X) → m.base_of X (find_base_greedy m order) := begin
  intro mem_order,
  convert find_base_greedy_finds_base_of_order,
  ext,
  rw mem_to_finset,
  exact (mem_order a).symm,
end

theorem find_base_greedy_of_sorted_finds_min :
  (∀ x, x ∈ order ↔ x ∈ X) → order.sorted (λ a b, w a ≥ w b) →
    is_min_ind m w X (find_base_greedy m order) := begin
  intros mem_order order_sorted,
  suffices h_suffix : ∀ (l : list α), l <:+ order → is_min_ind m w X (find_base_greedy m l), {
    apply h_suffix,
    exact suffix_refl order,
  },
  intro l,
  induction l with hd tl hl, {
    rintro -,
    rw [is_min_ind, find_base_greedy],
    finish,
  },
  intro hd_tl_suffix,
  specialize hl (is_suffix.trans (suffix_cons hd tl) hd_tl_suffix),
  rw find_base_greedy,
  dsimp only,
  by_cases (m.ind $ insert hd $ find_base_greedy m tl), {
    rw if_pos h,
    obtain ⟨pref, rfl⟩ := hd_tl_suffix,
    refine ⟨h, _, _⟩, {
      apply insert_subset_of_mem_of_subset, {
        finish,
      },
      exact hl.2.1,
    },
    by_cases h_in : hd ∈ find_base_greedy m tl, {
      rw insert_eq_of_mem h_in,
      exact hl.2.2,
    }, {
      obtain ⟨x, hx, ⟨xMin_ind, xMin_sub, xMin_min⟩⟩ := rado_edmonds hl _, {
        intros B Bsub Bind Bcard,
        rw card_insert_of_not_mem hx at xMin_min,
        rw card_insert_of_not_mem h_in at Bcard,
        specialize xMin_min B Bsub Bind Bcard,
        rw sum_insert hx at xMin_min,
        rw sum_insert h_in,
        suffices : w x ≥ w hd, { linarith },
        rw insert_subset at xMin_sub,
        rcases mem_append.1 ((mem_order x).2 xMin_sub.1) with (hx_pref | hx_hd), {
          obtain ⟨a, b, rfl⟩ := mem_split hx_pref,
          exact (pairwise_append.1 order_sorted).2.2 x hx_pref hd (mem_cons_self _ _),
        }, {
          rw mem_cons_iff at hx_hd,
          have x_eq_hd : x = hd := by {
            suffices : x ∉ tl, { finish },
            by_contradiction,
            exact (find_base_greedy_finds_base_of_order.2.2 x hx $ mem_to_finset.mpr h) xMin_ind,
          },
          subst x_eq_hd,
          linarith,
        }
      }, {
        rw base_of,
        simp only [exists_prop, mem_insert, not_and, mem_to_finset, not_not, not_forall],
        rintro - -,
        refine ⟨hd, h_in, _, h⟩,
        rw ← mem_order hd,
        finish,
      }
    }
  }, {
    rw if_neg h,
    exact hl,
  }
end

noncomputable def find_min_base_greedy (m : matroid α) (w : α → ℝ) (X : finset α) :=
  find_base_greedy m (merge_sort (λ a b, w a ≥ w b) X.1.to_list)

theorem find_min_base_correct :
  m.base_of X (find_min_base_greedy m w X) ∧
    is_min_ind m w X (find_min_base_greedy m w X) := begin
  have mem_order : ∀ (x : α), x ∈ merge_sort (λ (a b : α), w a ≥ w b) X.val.to_list ↔ x ∈ X := by {
    intro x,
    rw [mem_def, ← multiset.mem_to_list, perm.mem_iff $ perm_merge_sort _ _],
  },
  split, {
    exact find_base_greedy_finds_base mem_order,
  }, {
    apply find_base_greedy_of_sorted_finds_min mem_order,
    apply sorted_merge_sort _, {
      refine {total := _},
      intros a b,
      apply le_total,
    }, {
      refine {trans := _},
      finish,
    }
  }
end

end matroid