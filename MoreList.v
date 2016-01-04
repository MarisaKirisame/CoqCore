Require Export List FunctionalExtensionality Tactic Program Omega Arith MoreJMeq.
Require Vector.
Set Implicit Arguments.

Create HintDb MoreList.
Hint Extern 1 => f_equal : MoreList.

Theorem foldl_distr A (F : A -> A -> A) R l : forall a,
  (forall r l, R (F l r) = F (R l) (R r)) ->
    fold_left (fun l r => F l (R r)) l (R a) = R (fold_left F l a).
  induction l; simpl in *; subst; intuition.
  replace (F (R a0) (R a)) with (R (F a0 a)) by auto; auto.
Qed.
Hint Resolve foldl_distr : MoreList.

Theorem foldl_map A B C (F : B -> C -> B) (R : A -> _) l : forall a,
  fold_left (fun l r => F l r) (map R l) a = fold_left (fun l r => F l (R r)) l a.
  induction l; simpl in *; trivial.
Qed.
Hint Resolve foldl_map : MoreList.

Definition Select := filter.

Definition Remove A := fun F : A -> bool => Select (fun e => negb (F e)).

Theorem remove_Remove T (D : forall l r, { l = r } + { l <> r }) v :
  remove D v = Remove (fun e : T => if D e v then true else false).
  apply functional_extensionality.
  induction x; intros; simpl in *; repeat destruct D; repeat subst;
  simpl; f_equal; intuition.
Qed.
Hint Resolve remove_Remove : MoreList.

Theorem Select_Remove A (F : A -> bool) : Select F = Remove (fun e => negb (F e)).
  unfold Remove; f_equal.
  extensionality x; intros; destruct (F x); trivial.
Qed.
Hint Resolve Select_Remove : MoreList.

Theorem In_Select_In A l e (f : A -> bool) : In e (Select f l) -> In e l.
  intros; induction l; simpl in *; try destruct f; InInvcs.
Qed.
Hint Resolve In_Select_In : MoreList.

Theorem In_Select_Sat A l e (f : A -> bool) : In e (Select f l) -> f e = true.
  intros; induction l; simpl in *; try match_destruct; InInvcs; subst; auto.
Qed.
Hint Resolve In_Select_Sat : MoreList.

Theorem In_Sat_Select_In A l e (f : A -> bool) : In e l -> f e = true -> In e (Select f l).
  intros; induction l; simpl in *; try match_destruct; InInvcs; congruence.
Qed.
Hint Resolve In_Sat_Select_In : MoreList.

Theorem nodup_Select_Select_nodup T (F : T -> bool) D l : 
  nodup D (Select F l) = Select F (nodup D l).
  induction l; simpl in *; trivial.
  repeat (match_destruct || simpl in *; ii); try rewrite IHl; auto;
  let f := fun x => match x with (_ = in_left) => idtac | (_ = in_right) => idtac end in
    cleanT f; intuition (try congruence).
  eapply In_Sat_Select_In in i; eauto; tauto.
  apply In_Select_In in i; intuition.
Qed.
Hint Resolve nodup_Select_Select_nodup : MoreList.

Theorem Select_app A l r (f : A -> bool) : Select f (l ++ r) = Select f l ++ Select f r.
  induction l; simpl in *; try destruct (f a); simpl; idtac + f_equal; solve [intuition].
Qed.
Hint Resolve Select_app : MoreList.

Theorem NoDup_not_In_l : forall A l r (e : A), NoDup (l ++ r) -> In e r -> ~In e l.
  intros; induction l; simpl in *; ii; invcs H; intuition.
Qed.
Hint Resolve NoDup_not_In_l : MoreList.

Theorem NoDup_not_In_r : forall A l r (e : A), NoDup (l ++ r) -> In e l -> ~In e r.
  intros; induction l; simpl in *; ii; invcs H; intuition.
Qed.
Hint Resolve NoDup_not_In_r : MoreList.

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

Theorem eq_length_eq T (l r : list T) : l = r -> length l = length r.
  intros; subst; trivial.
Qed.
Hint Resolve eq_length_eq : MoreList.

Theorem nth_error_eq_eq T (l r : list T) : (forall n, nth_error l n = nth_error r n) -> l = r.
  intros; generalize dependent r.
  induction l; intros; destruct r; trivial; try (specialize(H 0); discriminate).
  assert(a = t) by (specialize(H 0); invcs H; trivial); subst; f_equal.
  apply IHl; intros; specialize(H (S n)); trivial.
Qed.
Hint Resolve nth_error_eq_eq : MoreList.

Theorem eq_nth_error_eq T (l r : list T) : l = r -> (forall n, nth_error l n = nth_error r n).
  intros; subst; trivial.
Qed.

Theorem foldl_extract A (F : A -> A -> A) li Z C :
  (forall a b c, F (F a b) c = F (F a c) b) ->
    fold_left (fun l r => F l r) li (F Z C) =
    F (fold_left (fun l r => F l r) li Z) C.
  revert Z C.
  induction li; simpl; intros; trivial.
  rewrite IHli by auto; clear IHli.
  revert Z a C; induction li; simpl; intros; auto.
  rewrite (IHli _ a0 a), (IHli _ C a); auto with *.
Qed.
Hint Resolve foldl_extract : MoreList.

Theorem last_app : forall T (e : T) m l, last (l ++ [e]) m = e.
  induction l; try destruct l; simpl in *; trivial.
Qed.
Hint Resolve last_app : MoreList.

Definition split_tail T (l : list T) : l <> [] -> { r | l = fst r ++ [snd r] }.
  destruct l; intros; try tauto.
  exists (removelast (t :: l),last (t :: l) t).
  rewrite app_removelast_last at 1 by assumption; simpl; auto.
Qed.
Hint Resolve split_tail : MoreList.

Theorem cons_app_tail_eq_length_eq T (l : T) r l' r' :
  l :: r = l' ++ [r'] -> length r = length l'.
  intros H.
  destruct r, l'; simpl in *; discriminate || trivial.
  invcs H; destruct l';discriminate.
  invcs H.
  destruct l'; simpl in *; invcs H2; trivial.
  rewrite app_length, plus_comm; trivial.
Qed.
Hint Resolve cons_app_tail_eq_length_eq : MoreList.

Theorem length_eq T (l r : list T) : l = r -> length l = length r.
  intros;subst;trivial.
Qed.
Hint Resolve length_eq : MoreList.

Theorem nth_error_tl T (l : list T) n : nth_error (tl l) n = nth_error l (S n).
  destruct l, n;trivial.
Qed.
Hint Resolve nth_error_tl : MoreList.

Definition nth_error_hd_error : forall T (l : list T), nth_error l 0 = hd_error l := 
  $(trivial)$.
Hint Resolve nth_error_hd_error : MoreList.

Theorem nth_error_JMeq (LT RT : Type) (l : list LT) (r : list RT) : LT = RT ->
  ((forall n : nat, nth_error l n ~= nth_error r n) <-> l ~= r).
  ii; repeat subst; auto with MoreJMeq MoreList.
Qed.
Hint Resolve nth_error_JMeq : MoreList.

Program Definition hd_strong T (l : list T) : 0 < length l -> { e | hd_error l = Some e } :=
  fun _ =>
    match l with
    | [] => !
    | e :: _ => e
    end.
Next Obligation. simpl in *; omega. Qed.

Theorem l_hd_strong_tl T (l : list T) P : ` (hd_strong l P) :: tl l = l.
  destruct hd_strong, l; simpl in *; invcs e; trivial.
Qed.
Hint Resolve l_hd_strong_tl : MoreList.

Definition app_cons T (e : T) l : [e] ++ l = e :: l := $(trivial)$.
Hint Resolve app_cons : MoreList.

Theorem foldl_identity A F (l : list A) (E I : A) :
  (forall e, F e I = e) -> (forall e, F I e = e) -> (forall l r, F l r = F r l) -> 
    (forall a b c, F (F a b) c = F (F a c) b) ->
      fold_left F l E = F (fold_left F l I) E.
  destruct l; intros; simpl in *; rewrite H0 in *; trivial; 
  rewrite <- foldl_extract; auto using f_equal.
Qed.
Hint Resolve foldl_identity : MoreList.

Definition map_eq_app A B (F : A -> B) x l r :
  map F x = l ++ r -> { p | fst p ++ snd p = x /\ map F (fst p) = l /\ map F (snd p) = r }.
  dependent induction x; intros; simpl in *;
  try solve [exists (@nil A, @nil A); destruct l, r; simpl in *; tauto || discriminate].
  destruct l; simpl in *; invcs H; try solve [exists (@nil A, a :: x); simpl in *; ii].
  Apply IHx; destruct H2 as [[]]; simpl in *; ii; subst.
  exists (a :: l0, l1); simpl; ii.
Defined.

Definition map_eq_cons A B (F : A -> B) x l r :
  map F x = l :: r -> { p | fst p :: snd p = x /\ F (fst p) = l /\ map F (snd p) = r }.
  destruct x; intros; simpl in *; invcs H.
  exists (a, x); ii.
Defined.

Definition app_eq_app A (ll lr rl rr : list A) : ll ++ lr = rl ++ rr ->
  { l' | ll = rl ++ l' /\ l' ++ lr = rr } + { r' | rl = ll ++ r' /\ r' ++ rr = lr }.
  dependent induction ll; intros; simpl in *; subst; try solve [right; exists rl; tauto].
  destruct rl; simpl in *; invcs H; try solve [left; exists (a :: ll); ii].
  destruct (IHll _ _ _ H2) as [[? []]|[? []]]; subst;
  left + right; solve [exists x; ii].
Defined.

Fixpoint split_sum L R (l : list (L + R)) : list L * list R :=
  match l with
  | [] => ([],[])
  | inl h :: t => let (l', r') := split_sum t in (h :: l', r')
  | inr h :: t => let (l', r') := split_sum t in (l', h :: r')
  end.

Definition split_sum_In_fst L R (l : list (L + R)) t : 
  In (inl t) l <-> In t (fst (split_sum l)).
  split; induction l; intros; simpl in *; trivial; ii; subst; simpl in *;
  destruct split_sum eqn:?; simpl in *; ii.
  destruct a; simpl in *; ii; subst; ii.
Defined.

Definition split_sum_In_snd L R (l : list (L + R)) t : 
  In (inr t) l <-> In t (snd (split_sum l)).
  split; induction l; intros; simpl in *; trivial; ii; subst; simpl in *;
  destruct split_sum eqn:?; simpl in *; ii.
  destruct a; simpl in *; ii; subst; ii.
Defined.

Definition Exists_dec_cons (A : Type) (P : A -> Prop) (l : list A) :
  (forall x : A, { P x } + { ~P x }) -> {x | P x /\ In x l} + { ~Exists P l }.
  induction l; intuition idtac.
  right; intros; inversion H.
  destruct a0; intuition eauto with *.
  destruct (X a); [intuition eauto with *|].
  right; intros; inversion H; eauto.
Defined.


Ltac ListInvcs := 
  match goal with
  | H : [] = [] |- _ => clear H
  | H : _ :: _ = _ :: _ |- _ => invcs H
  | H : ?L ++ _ = _ :: _ |- _ => destruct L eqn:?; invcs H
  | H : _ :: _ = ?L ++ _ |- _ => destruct L eqn:?; invcs H
  | H : map _ _ = _ ++ _ |- _ => 
      destruct (map_eq_app _ _ _ _ H) as [[] [? []]]; subst_no_fail; clear H
  | H : _ ++ _ = map _ _ |- _ => 
      destruct (map_eq_app _ _ _ _ H) as [[] [? []]]; subst_no_fail; clear H
  | H : map _ _ = _ :: _ |- _ => 
      destruct (map_eq_cons _ _ H) as [[] [? []]]; subst_no_fail; clear H
  | H : map _ _ = [] |- _ => apply map_eq_nil in H
  | H : [] = map _ _ |- _ => apply map_eq_nil in H
  | H : ?LL ++ ?LR = ?RL ++ ?RR |- _ => 
      destruct (app_eq_app LL LR RL RR H) as [[? []]|[? []]]; subst_no_fail; clear H
  end.

Definition VectorCase0Eq T l : l = Vector.nil T.
  apply (Vector.case0 (fun x => x = _)); ii.
Qed.

Definition VectorCaseSEq T n (l : Vector.t T (S n)) :
  exists h t, l = Vector.cons _ h _ t.
  apply (Vector.caseS' l); eauto.
Qed.

Definition VectorToListEq : forall T n (l r : Vector.t T n), 
  Vector.to_list l = Vector.to_list r -> l = r.
  dependent induction n; ii.
  pose proof (VectorCase0Eq l); subst.
  pose proof (VectorCase0Eq r); subst; ii.
  pose proof (VectorCaseSEq l); existsDestruct; subst.
  pose proof (VectorCaseSEq r); existsDestruct; subst.
  unfold Vector.to_list in *; invcs H; f_equal; auto.
Qed.
