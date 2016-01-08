Require Export List FunctionalExtensionality.
Set Implicit Arguments.

Ltac invcs H := inversion H; clear H; repeat subst.

Ltac decExists := repeat match goal with H : exists _, _ |- _ => destruct H end.

Ltac ii := intuition idtac.

Ltac InInvcs := 
  repeat(
    simpl in *; ii;
    try match goal with
    | H : In _ (_ ++ _) |- _ => apply in_app_iff in H; destruct H
    | |- In _ (_ ++ _) => apply in_app_iff
    end).

Ltac get_goal := match goal with |- ?x => x end.

Ltac get_match H F := match H with context [match ?n with _ => _ end] => F n end.

Ltac no_inner_match_smart_destruct T :=
  (is_var T; destruct T) ||
  (let F := fresh in destruct T eqn:?F;
  match type of F with ?Term = _ => let F' x := fail 3 in try get_match Term F' end;
  match type of F with ?Term = _ :> {_} + {_} => clear F | _ => idtac end).

Ltac get_matches F := 
  match goal with
  | [ |- ?X ] => get_match X F
  | [ H : ?X |- _ ] => get_match X F
  end.

Ltac match_context_destruct C :=
  let F := no_inner_match_smart_destruct in get_match C F.

Ltac match_type_context_destruct T C :=
  get_match C ltac:(fun x => let x' := type of x in no_inner_match_smart_destruct).

Definition channel P NT (N : NT) : Type := P.

Arguments channel : simpl never.

Inductive sandbox_closer : Prop := ms : sandbox_closer -> sandbox_closer.

Definition sandbox_closer_exit : sandbox_closer -> False := ltac:(induction 1; trivial).

Ltac set_result N T := match goal with | _ := ?X : channel _ N |- _ => unify X T end.

Ltac get_result N := match goal with | _ := ?X : channel _ N |- _ => X end.

Ltac clear_result N := match goal with | H := _ : channel _ N |- _ => clear H end.

Ltac make_sandbox T N := 
  let f := fresh in 
  let g := get_goal in 
  let H := fresh in
    evar (f : channel T N); assert(sandbox_closer -> g) as H; [intro | clear H].

Ltac exit_sandbox := 
  exfalso;
  match goal with
  | X : sandbox_closer |- _ => apply sandbox_closer_exit in X; tauto
  end.

Ltac match_type_destruct T :=
  get_matches ltac:(fun x => match type of x with T => no_inner_match_smart_destruct x end).

Ltac match_destruct := get_matches no_inner_match_smart_destruct.

Ltac cleanT T := 
  repeat match goal with
  | H : ?X |- _ => T X; clear H
  end.

Ltac removeone H := match goal with X : H |- _ => clear X end.

Ltac solvable G T := let f := fresh in assert(f : G) by T; clear f.

Ltac cleanTS T := cleanT ltac:(fun x => solvable x ltac:(removeone x; T)).

Ltac isProp X := match type of X with Prop => idtac end.

Ltac cleanP T := cleanT ltac:(fun x => isProp x; T x).

Ltac cleanPS T := cleanP ltac:(fun x => solvable x ltac:(removeone x; T)).

Require Export Classical.
Ltac DestructPremise :=
  match goal with
  | H : ?T |- _ => 
    match T with
    | _ -> False => fail 1
    | forall A : ?X, ?Y => let F := fresh in
            destruct (classic X) as [F| ]; [ specialize (H F) | clear H ]
    end
  end.

Ltac ext := let f := fresh in extensionality f.

Ltac Apply T := match goal with H : _ |- _ => apply T in H end.
Ltac EApply T := match goal with H : _ |- _ => eapply T in H end.

Ltac existsDestruct :=
  repeat match goal with 
  | H : exists _, _ |- _ => destruct H
  end.

Ltac DestructEPair p :=
  match type of p with
  | (?lT*?rT)%type => 
      let l := fresh in 
      let r := fresh in 
        evar (l : lT); 
        evar (r : rT); 
        unify p (l, r);
        simpl
  end.

Ltac FindDestructEPair :=
  match goal with
  | X : _ |- _ => match X with context [?l] => DestructEPair l end
  | |- ?X => match X with context [?l] => DestructEPair l end
  end.

Ltac rewriteTerm T := 
  match goal with
  | H : T = T |- _ => clear H
  | H : _ = T |- _ => rewrite H in *
  | H : T = _ |- _ => rewrite <- H in *
  end.

Ltac DestructPair := repeat match goal with X : _ * _ |- _ => destruct X end.

Ltac SplitOrGoal := 
  match goal with
  | |- ?l \/ ?r => destruct (classic l); [left; assumption|right]
  end.

Ltac Not H := try (H; fail 1).

Ltac ConstructorInvcs H := 
  simplify_eq H; 
  let H' := fresh in
    intro H';
    Not ltac:(constr_eq ltac:(type of H) ltac:(type of H'));
    clear H.

Ltac FindConstructorInvcs := repeat match goal with H : _ |- _ => ConstructorInvcs H end.