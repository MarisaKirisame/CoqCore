Require Export List ProofIrrelevance Permutation Tactic.
Require Import Program.
Set Implicit Arguments.

Theorem Forall_split T P (a : T) l : Forall P (a::l) <-> P a /\ Forall P l.
  intuition;inversion H;tauto.
Qed.

Definition Forall_map A B (P : A -> Prop) (f : forall a, P a -> B) :
  forall(l : list A), Forall P l -> list B.
  induction l;
  intros.
  exact [].
  apply Forall_split in H.
  destruct H.
  specialize(IHl H0).
  exact ((f _ H)::IHl).
Defined.

Theorem in_Forall_map A B (P : A -> Prop) (f : forall a, P a -> B) l F e p : 
  In e l -> In (f e p) (@Forall_map A B P f l F).
  induction l;
  intros;
  simpl in *.
  tauto.
  destruct Forall_split.
  destruct a0.
  intuition;simpl;subst.
  left.
  f_equal;apply proof_irrelevance.
Qed.

Theorem Forall_ignore_left T P (l r : list T) : Forall P (l ++ r) -> Forall P r.
  induction l.
  trivial.
  simpl.
  inversion 1.
  tauto.
Qed.

Theorem Forall_perm T P (l r : list T) : Permutation l r -> Forall P l -> Forall P r.
  induction 1;
  intros;
  repeat match goal with
  | H : Forall _ (_ :: _) |- _ => invcs H
  | |- Forall _ (_ :: _) => constructor
  end;
  intuition.
Qed.

Theorem Forall_ignore_right T P (l r : list T) : Forall P (l ++ r) -> Forall P l.
  intros.
  assert(Permutation (l ++ r) (r ++ l)) by apply Permutation_app_comm.
  eapply Forall_perm in H0;eauto.
  eapply Forall_ignore_left;eauto.
Qed.

Theorem Forall_app T P (l r : list T) : Forall P (l ++ r) <-> Forall P l /\ Forall P r.
  intuition.
  eapply Forall_ignore_right;eauto.
  eapply Forall_ignore_left;eauto.
  induction l;
  repeat match goal with
  | H : Forall _ (_ :: _) |- _ => invcs H
  | |- Forall _ (_ :: _) => constructor
  end;
  simpl;
  intuition.
Qed.

Ltac ForallInvcs := 
  repeat 
    (try match goal with
    | H : Forall _ (_ :: _) |- _ => invcs H
    | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H;destruct H
    | |- Forall _ (_ :: _) => constructor
    | |- Forall _ (_ ++ _) => apply Forall_app
    end;
    simpl in *;
    intuition).