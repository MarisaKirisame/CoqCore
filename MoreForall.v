Require Export List ProofIrrelevance Permutation Tactic Classical.
Require Import Program.
Set Implicit Arguments.

Theorem Forall_split T P (a : T) l : Forall P (a::l) <-> P a /\ Forall P l.
  intuition; inversion H; tauto.
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

Definition forallb_Forall (A : Type) (f : A -> bool) (l : list A) :
  forallb f l = true <-> Forall (fun x => f x = true) l.
  induction l; ii; simpl in *; repeat constructor;
  unfold andb in *; repeat match_destruct; try congruence; ii.
  invcs H1; auto.
  invcs H1; congruence.
Qed.

Definition ForallJoin (T : Type) (L R : T -> Prop) l : 
  Forall L l -> Forall R l -> Forall (fun x => L x /\ R x) l.
  intros; induction l; simpl in *; constructor; invcs H; invcs H0; ii.
Qed.

Definition Exists_Forall_neg_classic A (P : A -> Prop) l :
  Exists (fun x => ~ P x) l <-> ~ Forall P l := Exists_Forall_neg _ _ (fun x => classic (P x)).

Definition map_Forall A B (F : A -> B) P l : Forall P (map F l) <-> Forall (P ∘ F) l.
  ii; induction l; simpl in *; constructor; invcs H; ii.
Defined.

Ltac ForallInvcs := 
  match goal with
  (*branch0*)
  | |- Forall _ [] => constructor
  (*branch1*)
  | H : Forall _ (_ :: _) |- _ => invcs H
  | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H; destruct H
  | H : Forall _ [] |- _ => clear H
  | H : forallb _ _ = true |- _ => apply forallb_Forall in H
  | |- forallb _ _ = true => apply forallb_Forall
  | HL : Forall _ _, HR : Forall _ _ |- _ => pose proof (ForallJoin HL HR); clear HL HR
  | H : ~Forall _ _ |- _ => apply Exists_Forall_neg_classic in H
  | |- ~Forall _ _ => apply Exists_Forall_neg_classic
  | H : Forall _ _ -> False |- _ => apply Exists_Forall_neg_classic in H
  | |- Forall _ _ -> False => apply Exists_Forall_neg_classic
  | H : Forall _ (map _ _) |- _ => apply map_Forall in H
  | |- Forall _ (map _ _) => apply map_Forall
  (*branch2*)
  | |- Forall _ (_ :: _) => constructor
  | |- Forall _ (_ ++ _) => apply Forall_app
  end.

Theorem Exists_app T P (l r : list T) : Exists P (l ++ r) <-> Exists P l \/ Exists P r.
  intuition.
  + induction l; invcs H; simpl in *; subst; ii; eauto.
  + induction l; invcs H0; simpl in *; eauto.
  + induction l; invcs H0; simpl in *; eauto.
Qed.

Definition Exists_cons T P l (r : list T) : Exists P (l :: r) <-> P l \/ Exists P r := 
  $(intuition; invcs H; eauto)$.

Definition forallb_Exists (A : Type) (f : A -> bool) (l : list A) :
  forallb f l = false <-> Exists (fun x => f x = false) l.
  split.
  + induction l; intros; simpl in *; try congruence;
    unfold andb in *; repeat match_destruct;
    left + right; solve [ii].
  + induction l; intro H; invcs H; simpl in *; unfold andb; 
    repeat match_destruct; congruence || ii.
Qed.

Definition map_Exists A B (F : A -> B) P l : Exists P (map F l) <-> Exists (P ∘ F) l.
  ii; induction l; simpl in *; invcs H; ii; eauto.
Defined.

Ltac ExistsInvcs := 
  match goal with
  (*branch0*)
  | H : Exists _ [] |- _ => invcs H
  (*branch1*)
  | |- Exists _ [] => exfalso
  | H : forallb _ _ = false |- _ => apply forallb_Exists in H
  | |- forallb _ _ = false => apply forallb_Exists
  | H : ~Exists _ _ |- _ => apply Forall_Exists_neg in H
  | |- ~Exists _ _ => apply Forall_Exists_neg
  | H : Exists _ _ -> False |- _ => apply Forall_Exists_neg in H
  | |- Exists _ _ -> False => apply Forall_Exists_neg
  | H : Forall _ (map _ _) |- _ => apply map_Exists in H
  | |- Forall _ (map _ _) => apply map_Exists
  (*branch2*)
  | |- Exists _ (_ :: _) => apply Exists_cons
  | |- Exists _ (_ ++ _) => apply Exists_app
  | H : Exists _ (_ :: _) |- _ => invcs H
  | H : Exists _ (_ ++ _) |- _ => apply Exists_app in H
  end.