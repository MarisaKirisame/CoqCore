Require Export List FunctionalExtensionality Tactic Program Omega Arith MoreJMeq.
Set Implicit Arguments.

Theorem foldl_distr : forall A (F : A -> A -> A) R l a,
  (forall r l, R (F l r) = F (R l) (R r)) ->
    fold_left (fun l r => F l (R r)) l (R a) = R (fold_left F l a).
  induction l; simpl in *; subst; intuition.
  replace (F (R a0) (R a)) with (R (F a0 a)) by auto; auto.
Qed.

Theorem foldl_map : forall A B C (F : B -> C -> B) (R : A -> _) l a,
  fold_left (fun l r => F l r) (map R l) a = fold_left (fun l r => F l (R r)) l a.
  induction l; simpl in *; trivial.
Qed.

Definition Select := filter.

Definition Remove A := fun F : A -> bool => Select (fun e => negb (F e)).

Theorem remove_Remove T (D : forall l r, { l = r } + { l <> r }) v :
  remove D v = Remove (fun e : T => if D e v then true else false).
  apply functional_extensionality.
  induction x; intros; simpl in *; repeat destruct D; repeat subst;
  simpl; f_equal; intuition.
Qed.

Theorem Select_Remove A (F : A -> bool) : Select F = Remove (fun e => negb (F e)).
  unfold Remove.
  f_equal.
  apply functional_extensionality.
  intros; destruct (F x); trivial.
Qed.

Theorem nodup_Select_Select_nodup T (F : T -> bool) D l : 
  nodup D (Select F l) = Select F (nodup D l).
  induction l; simpl in *; trivial.
  repeat (match_destruct || simpl in *; ii); try rewrite IHl.
  cleanP admit.
  contradict n.
  rewrite IHl in *.
Qed.

Theorem Select_app A l r (f : A -> bool) : Select f (l ++ r) = Select f l ++ Select f r.
  induction l;
  simpl in *;
  try destruct (f a);
  intuition.
  simpl.
  f_equal;
  trivial.
Qed.

Theorem NoDup_In_In_False : forall A l r (e : A), NoDup (l ++ r) -> In e l -> In e r -> False.
  intros.
  induction l;
  simpl in *;
  intuition;
  invcs H;
  intuition.
Qed.

Theorem In_Select_In A l e (f : A -> bool) : In e (Select f l) -> In e l.
  intros.
  induction l;
  simpl in *;
  try destruct f;
  InInvcs.
Qed.

Program Definition nth_strong T (l : list T) nt (P : nt < length l) : 
  { e | Some e = nth_error l nt } :=
  match nth_error l nt with
  | None => ! 
  | Some e => e 
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply nth_error_None in Heq_anonymous.
  omega.
Qed.

Theorem eq_eq_length T (l r : list T) : l = r -> length l = length r.
  intros.
  subst.
  trivial.
Qed.

Theorem nth_error_eq T (l r : list T) : (forall n, nth_error l n = nth_error r n) <-> l = r.
  split.
  revert r.
  induction l;intros.
  destruct r;trivial.
  specialize(H 0);discriminate.
  destruct r.
  specialize(H 0);discriminate.
  assert(a = t) by (specialize(H 0);invcs H;trivial).
  subst.
  f_equal.
  apply IHl.
  intros.
  specialize(H (S n));trivial.
  intros.
  subst.
  trivial.
Qed.

Theorem foldl_extract A (F : A -> A -> A) li Z C :
  (forall a b c, F (F a b) c = F (F a c) b) ->
    fold_left (fun l r => F l r) li (F Z C) =
    F (fold_left (fun l r => F l r) li Z) C.
  revert Z C.
  induction li;
  simpl;
  intros;
  trivial.
  rewrite IHli.
  clear IHli.
  revert Z a C.
  induction li;
  simpl;
  intros.
  apply H.
  rewrite (IHli _ a0 a), (IHli _ C a).
  do 2 f_equal.
  all:auto.
Qed.

Theorem last_app : forall T (e : T) m l, last (l ++ [e]) m = e.
  induction l;
  try destruct l;
  simpl in *;
  trivial.
Qed.

Definition split_tail T (l : list T) : l <> [] -> { r | l = fst r ++ [snd r] }.
  destruct l.
  tauto.
  intros.
  exists (removelast (t :: l),last (t :: l) t).
  rewrite app_removelast_last at 1 by assumption.
  simpl;auto.
Qed.

Theorem cons_app_tail_eq_length_eq : forall T (l : T) r l' r',
  l :: r = l' ++ [r'] -> length r = length l'.
  intros.
  destruct r, l';simpl in *;discriminate||trivial.
  invcs H.
  destruct l';discriminate.
  invcs H.
  destruct l';simpl in *;invcs H2;trivial.
  rewrite app_length, plus_comm;trivial.
Qed.

Definition list_rev_rect_inner : forall (A : Type) (P : list A -> Type),
  P [] -> (forall (a : A) (l : list A), P l -> P (l ++ [a])) -> 
    forall n (l : list A), n = (length l) -> P l.
  induction n;
  intros.
  destruct l;trivial;discriminate.
  destruct l.
  discriminate.
  inversion H.
  destruct (@split_tail _ (a :: l)).
  discriminate.
  destruct x.
  subst.
  simpl in *.
  rewrite e.
  apply X0.
  apply IHn.
  eapply cons_app_tail_eq_length_eq;eauto.
Qed.

Definition list_rev_rect { A : Type } (l : list A) (P : list A -> Type) :
  P [] -> (forall (a : A) (l : list A), P l -> P (l ++ [a])) -> P l.
  intros;eapply list_rev_rect_inner;eauto.
Qed.

Theorem length_eq T (l r : list T) : l = r -> length l = length r.
  intros;subst;trivial.
Qed.

Theorem nth_error_tl T (l : list T) n : nth_error (tl l) n = nth_error l (S n).
  destruct l, n;trivial.
Qed.

Theorem nth_error_hd_error : forall T (l : list T), nth_error l 0 = hd_error l.
  trivial.
Qed.

Theorem nth_error_JMeq (LT RT : Type) (l : list LT) (r : list RT) : LT = RT ->
  ((forall n : nat, nth_error l n ~= nth_error r n) <-> l ~= r).
  intuition;
  repeat subst;
  trivial.
  apply eq_JMeq.
  apply nth_error_eq.
  intros.
  specialize (H0 n).
  apply JMeq_eq in H0;trivial.
Qed.

Program Definition hd_strong T (l : list T) : 0 < length l -> { e | hd_error l = Some e } :=
  fun _ =>
    match l with
    | [] => !
    | e :: _ => e
    end.
Next Obligation.
  simpl in *;omega.
Qed.

Theorem l_hd_strong_tl T (l : list T) P : ` (hd_strong l P) :: tl l = l.
  intros.
  destruct hd_strong, l;simpl in *;invcs e;trivial.
Qed.

Theorem app_cons : forall T (e : T) l, [e] ++ l = e :: l.
  trivial.
Qed.

Theorem foldl_identity A F (l : list A) (E I : A) :
  (forall e, F e I = e) -> (forall e, F I e = e) -> (forall l r, F l r = F r l) -> 
    (forall a b c, F (F a b) c = F (F a c) b) ->
      fold_left F l E = F (fold_left F l I) E.
  destruct l;intros;simpl in *;rewrite H0 in *;trivial.
  rewrite <- foldl_extract.
  f_equal.
  apply H1.
  apply H2.
Qed.