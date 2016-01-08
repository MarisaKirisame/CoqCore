Require Import Program Permutation List Tactic EqDec Classical.

Definition bring_to_front_type { T } (dec : eq_dec T) e (l : list T) : In e l -> 
  { lr : (list T) * (list T) | (fst lr) ++ e :: snd lr = l /\ ~In e (fst lr) }.
  induction l; intros; simpl in *; try tauto.
  destruct (dec e a); subst; [exists (@nil T, l); tauto|].
  assert (In e l) by intuition; clear H; intuition.
  destruct X as [[l' r'] H].
  intuition; simpl in *; subst.
  exists (a::l', r'); simpl in *; intuition.
Defined.

Definition bring_to_front_prop { T } e (l : list T) : In e l -> 
  exists lr : (list T) * (list T), (fst lr) ++ e :: snd lr = l /\ ~In e (fst lr).
  induction l; intros; simpl in *; try tauto.
  destruct (classic (a = e)); subst.
  exists (@nil T, l); tauto.
  assert (In e l) by intuition; clear H; intuition.
  destruct H as [[l' r'] H].
  intuition; simpl in *; subst.
  exists (a::l', r'); simpl in *; intuition.
Qed.