
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  intro hnp,
  have hnnp := hnp hp,
  exact hnnp,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hp,
  by_cases h : P,
  exact h,
  have hboom := hp h,
  exfalso,
  exact hboom,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro hp,
  by_cases h : P,
  exact h,
  have hboom := hp h,
  exfalso,
  exact hboom,
  intro hp,
  intro hnp,
  have hnnp := hnp hp,
  exact hnnp,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hor,
  cases hor with hp hq,
  right,
  exact hp,
  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro handq,
  cases handq with hp hq,
  split,
  exact hq,
  exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hnporq,
  cases hnporq with hnp hq,
  intro hp,
  exfalso,
  have hboom := hnp hp,
  exact hboom,
  intro hp,
  exact hq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hporq,
  cases hporq with hp hq,
  intro hnp,
  have hboom := hnp hp,
  exfalso,
  exact hboom,
  intro hnp,
  exact hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hpinpq,
  intro hnq,
  intro hp,
  apply hnq,
  apply hpinpq,
  exact hp,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  sorry,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  sorry,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  sorry,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro hnp,
  apply hnp,
  apply h,
  intro hp,
  have hboom := hnp hp,
  exfalso,
  exact hboom,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro hporq,
  intro hnpandnq,
  cases hnpandnq with hnp hnq,
  cases hporq with hp hq,
  apply hnp,
  exact hp,
  apply hnq,
  exact hq,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro hpandq,
  cases hpandq with hp hq,
  intro hnpornq,
  cases hnpornq with hnp hnq,
  apply hnp,
  exact hp,
  apply hnq,
  exact hq,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro nhporq,
  split,
  intro hp,
  apply nhporq,
  left,
  exact hp,
  intro hq,
  apply nhporq,
  right,
  exact hq,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro hnpandnq,
  cases hnpandnq with hnp hnq,
  intro hporq,
  cases hporq with hp hq,
  apply hnp,
  exact hp,
  apply hnq,
  exact hq,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro hnqornp,
  intro hpandq,
  cases hpandq with hp hq,
  cases hnqornp with hnq hnp,
  apply hnq,
  exact hq,
  apply hnp,
  exact hp,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro nhporq,
  split,
  intro hp,
  apply nhporq,
  left,
  exact hp,
  intro hq,
  apply nhporq,
  right,
  exact hq,
  intro hnpandnq,
  cases hnpandnq with hnp hnq,
  intro hporq,
  cases hporq with hp hq,
  apply hnp,
  exact hp,
  apply hnq,
  exact hq,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with hp hqorr,
  cases hqorr with hq hr,
  left,
  split,
  exact hp,
  exact hq,
  right,
  split,
  exact hp,
  exact hr,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h with hpandq hpandr,
  cases hpandq with hp hq,
  split,
  exact hp,
  left,
  exact hq,
  cases hpandr with hp hr,
  split,
  exact hp,
  right,
  exact hr,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h with hp hqandr,
  split,
  left,
  exact hp,
  left,
  exact hp,
  cases hqandr with hq hr,
  split,
  right,
  exact hq,
  right,
  exact hr,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with hporq hporr,
  cases hporq with hp hq,
  left,
  exact hp,
  cases hporr with hp hr,
  left,
  exact hp,
  right,
  split,
  exact hq,
  exact hr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h,
  intro hp,
  intro hq,
  apply h,
  split,
  exact hp,
  exact hq,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro h,
  intro hpandq,
  cases hpandq with hp hq,
  apply h,
  exact hp,
  exact hq,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  exact hp,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  exact hq,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro hpandq,
  cases hpandq with hp hq,
  exact hp,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro hpandq,
  cases hpandq with hp hq,
  exact hq,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro hpandp,
  cases hpandp with hp hp,
  exact hp,
  intro hp,
  split,
  exact hp,
  exact hp,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro hporp,
  cases hporp with hp hp,
  exact hp,
  exact hp,
  intro hp,
  left,
  exact hp,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro x,
  intro hp,
  apply h,
  existsi x,
  exact hp,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro e,
  cases e with x hx,
  apply h,
  exact hx,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
