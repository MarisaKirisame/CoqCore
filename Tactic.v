Require Export List.
Set Implicit Arguments.

Ltac invcs H := inversion H;clear H;repeat subst.

Ltac invcsSome := repeat match goal with H : Some _ = Some _ |- _ => invcs H end.

Ltac decExists := repeat match goal with H : exists _, _ |- _ => destruct H end.

Ltac ii := intuition idtac.

Ltac InInvcs := 
  repeat(
    simpl in *; ii;
    try match goal with
    | H : In _ (_ ++ _) |- _ => apply in_app_iff in H;destruct H
    | |- In _ (_ ++ _) => apply in_app_iff
    end).

Ltac get_goal := match goal with |- ?x => x end.

Ltac get_match H F := match H with context [match ?n with _ => _ end] => F n end.

Ltac get_matches F := 
  match goal with
  | [ |- ?X ] => get_match X F
  | [ H : ?X |- _ ] => get_match X F
  end.

Ltac match_context_destruct C :=
  let F := (fun x => destruct x eqn:?) in get_match C F.

Ltac match_type_context_destruct T C :=
  let F := (fun x => let x' := type of x in match x' with T => destruct x eqn:? end) in
    get_match C F.

Definition box P NT (N : NT) : Type := P.

Inductive sandbox_closer : Prop := ms : sandbox_closer -> sandbox_closer.

Theorem sandbox_closer_exit : sandbox_closer -> False. induction 1;trivial. Qed.

Arguments box : simpl never.

Ltac make_sandbox T N := 
  let f := fresh in
    evar (f : box T N);
    let g := get_goal in 
      let H := fresh in
        assert(sandbox_closer -> g) as H;[intro|clear H].

Ltac exit_sandbox := 
  exfalso;
  match goal with
  | X : sandbox_closer |- _ => apply sandbox_closer_exit in X;tauto
  end.

Ltac set_result N T := match goal with | _ := ?X : box _ N |- _ => unify X T end.

Ltac get_result N := match goal with | _ := ?X : box _ N |- _ => X end.

Ltac clear_result N := match goal with | H := _ : box _ N |- _ => clear H end.

Ltac match_type_destruct T :=
  let F := (fun x => let x' := type of x in match x' with T => destruct x eqn:? end) in
    get_matches F.

Ltac match_destruct := let F := (fun x => destruct x eqn:?) in get_matches F.

Ltac cleanT T := 
  repeat match goal with
  | H : ?X |- _ => T X; clear H
  end.

Ltac removeone H := match goal with X : H |- _ => clear X end.

Ltac solvable G T := let f := fresh in assert(f : G) by T; clear f.

Ltac cleanTS T := let F := (fun x => let Te := (removeone x; T) in solvable x Te) in cleanT F.

Ltac isProp X := match type of X with Prop => idtac end.

Ltac cleanP T := let F := (fun x => isProp x; T x) in cleanT F.

Ltac cleanPS T := 
  let F := (fun x => let Te := (removeone x; T) in solvable x Te) in cleanP F.

Require Export Classical.
Ltac DestructPremise :=
  match goal with
  | H : forall _ : ?X, ?Y |- _ => 
      match Y with
      | False => fail 1
      | _ => let F := fresh in destruct (classic X) as [F|F];[specialize (H F)|clear H]
      end
  end.
Ltac ext := let f := fresh in extensionality f.
