Require Export List ProofIrrelevance Permutation Tactic.
Require Import Program.
Set Implicit Arguments.

Theorem Forall_split T P (a : T) l : Forall P (a::l) <-> P a /\ Forall P l.
  intuition;inversion H;tauto.
Qed.

Program Fixpoint In_map { A B } (l : list A) (f : forall a, In a l -> B) : list B := 
  match l with
  | [] => []
  | h :: t => f h _ :: In_map t (fun a _ => f a _)
  end.
Solve All Obligations with program_simpl; simpl; tauto.

Program Definition Forall_map A B (P : A -> Prop) (f : forall a, P a -> B) :
  forall (l : list A), Forall P l -> list B := fun l H => In_map l (fun a _ => f a _).
Next Obligation.
  eapply Forall_forall; eauto.
Qed.

Theorem in_In_map' { A B : Type } l e : 
  forall f f' P, f = f' -> In (f e P) (@In_map A B l f').
  induction l; intros; simpl in *; ii.
  inversion P; subst.
  left; f_equal; apply proof_irrelevance.
  right; pose (fun x p => f' x (or_intror p)) as h.
  replace (f' e P) with (h e H0) by (unfold h; f_equal; apply proof_irrelevance); auto.
Qed.

Definition in_In_map A B l e f P : In (f e P) (@In_map A B l f) := 
  @in_In_map' A B l e f f P eq_refl.

Theorem in_Forall_map A B (P : A -> Prop) (f : forall a, P a -> B) l F e p : 
  In e l -> In (f e p) (@Forall_map A B P f l F).
  unfold Forall_map; intros.
  pose (fun e H => f e (proj1 (Forall_forall P l) F e H)) as g.
  replace (f e p) with (g e H) by (unfold g; f_equal; apply proof_irrelevance).
  apply in_In_map'; unfold g; extensionality a; extensionality H0.
  f_equal; apply proof_irrelevance.
Qed.

Theorem Forall_ignore_left T P (l r : list T) : Forall P (l ++ r) -> Forall P r.
  induction l; simpl; trivial.
  inversion 1; tauto.
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
  eapply Forall_perm in H0; eauto.
  eapply Forall_ignore_left; eauto.
Qed.

Theorem Forall_app T P (l r : list T) : Forall P (l ++ r) <-> Forall P l /\ Forall P r.
  intuition.
  eapply Forall_ignore_right; eauto.
  eapply Forall_ignore_left; eauto.
  induction l;
  repeat match goal with
  | H : Forall _ (_ :: _) |- _ => invcs H
  | |- Forall _ (_ :: _) => constructor
  end; 
  simpl; intuition.
Qed.

Ltac ForallInvcs := 
  repeat 
    (try match goal with
    | H : Forall _ (_ :: _) |- _ => invcs H
    | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H; destruct H
    | H : Forall _ [] |- _ => clear H
    | |- Forall _ (_ :: _) => constructor
    | |- Forall _ (_ ++ _) => apply Forall_app
    end;
    simpl in *;
    ii).