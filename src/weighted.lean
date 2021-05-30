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

def is_best_ind (m : matroid α) (w : α → ℝ) (X A : finset α)
  := m.ind A ∧ A ⊆ X ∧ ∀ B ⊆ X, m.ind B → B.card = A.card → A.sum w ≤ B.sum w

theorem rado_edmonds :
  is_best_ind m w X A → ¬m.base_of X A →
    ∃ x, x ∉ A ∧ is_best_ind m w X (insert x A) := begin
  rintro ⟨indA, hAX, Abest⟩ A_not_base,
  have h_best_bigger : ∃ B ⊆ X, is_best_ind m w X B ∧ B.card = A.card + 1, {
    obtain ⟨B, Bgood, Bmin⟩ := exists_min_image (filter (λ S, m.ind S ∧ S.card = A.card + 1) (powerset X)) (λ S, S.sum w) _, {
      simp only [mem_powerset, mem_filter] at Bgood,
      obtain ⟨hBX, indB, Bcard⟩ := Bgood,
      refine ⟨B, hBX, _, Bcard⟩,
      rw is_best_ind,
      refine ⟨indB, _⟩,
      simp only [mem_powerset, and_imp, mem_filter] at Bmin,
      refine ⟨hBX, _⟩,
      rw Bcard,
      exact Bmin,
    }, {
      rw base_of at A_not_base,
      simp only [exists_prop, not_and, not_not, not_forall] at A_not_base,
      specialize A_not_base hAX indA,
      rcases A_not_base with ⟨x, hxA, hxX, hx⟩,
      use insert x A,
      simp only [mem_powerset, mem_filter],
      refine ⟨_, hx, _⟩, {
        intros x0 h_x0,
        rw mem_insert at h_x0,
        cases h_x0, {
          subst h_x0, exact hxX,
        }, {
          exact hAX h_x0,
        }
      }, {
        exact card_insert_of_not_mem hxA,
      }
    }
  },
  obtain ⟨B, hBX, ⟨indB, Bbest⟩, Bcard⟩ := h_best_bigger,
  obtain ⟨x, hxB, hxA, hx⟩ := m.ind_exchange _ _ indA indB (by linarith),
  refine ⟨x, hxA, _⟩,
  rw is_best_ind,
  refine ⟨hx, _⟩,
  have h_ins_card := card_insert_of_not_mem hxA,
  have insert_subset_X : insert x A ⊆ X := by begin
    intros x0 h_x0,
    rw mem_insert at h_x0,
    cases h_x0, {
      subst h_x0,
      exact hBX hxB,
    }, {
      exact hAX h_x0,
    }
  end,
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
      apply Abest, {
        exact subset.trans (erase_subset _ _) hBX,
      }, {
        exact m.ind_subset _ _ (erase_subset _ _) indB,
      },
      suffices : (B.erase x).card + 1 = A.card + 1, { linarith },
      rw card_erase_of_mem' hxB,
      exact Bcard,
    }, {
      apply Bbest.2, {
        exact insert_subset_X,
      },
      exact hx,
      rw h_ins_card,
      exact Bcard.symm,
    }
  },
  rw [hw, h_ins_card, ← Bcard],
  exact ⟨insert_subset_X, Bbest.2⟩,
end

def find_base_greedy_rec (m : matroid α) : finset α → list α → finset α
| A [] := A
| A (x :: l) :=
  find_base_greedy_rec (if m.ind (insert x A) then (insert x A) else A) l

def find_base_greedy (m : matroid α) (order : list α)
  : finset α := find_base_greedy_rec m ∅ order

-- theorem find_base_finds_base :
--   (∀ x, x ∈ order ↔ x ∈ X) → m.base_of X (find_base_greedy m order) := begin
--   intro mem_order,

-- end

end matroid