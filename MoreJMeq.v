Require Export JMeq Program.
Set Implicit Arguments.

Create HintDb MoreJMeq.
Hint Extern 1 => progress subst : MoreJMeq.

Definition eq_proj1_sig_eq A (P : A -> Prop) (n m : sig P) : 
  n = m -> ` n = ` m := ltac:(intuition).
Hint Resolve functional_extensionality eq_proj1_sig_eq : MoreJMeq.

Definition proj1_sig_eq_eq A (P : A -> Prop) (n m : sig P) : 
  ` n = ` m -> n = m := ltac:(intros; apply subset_eq; trivial).
Hint Resolve proj1_sig_eq_eq : MoreJMeq.

Definition eq_JMeq T (l r : T) : l = r -> l ~= r := ltac:(auto with MoreJMeq).
Hint Resolve JMeq_eq eq_JMeq : MoreJMeq.

Definition JMeq_extensionality_l A B C (l : A -> C) (r : B -> C) :
  (forall L R, L ~= R -> l L = r R) -> A = B -> l ~= r := ltac:(eauto with MoreJMeq).
Hint Resolve JMeq_extensionality_l : MoreJMeq.

Theorem JMeq_extensionality_r A B C (l : A -> B) (r : A -> C) :
  (forall L R, L = R -> l L ~= r R) -> B = C -> l ~= r.
  intros; subst.
  apply eq_JMeq; apply functional_extensionality.
  intros; erewrite H; eauto.
Qed.
Hint Resolve JMeq_extensionality_r : MoreJMeq.

Theorem JMeq_extensionality A B C D (l : A -> B) (r : C -> D) :
  (forall L R, L ~= R -> l L ~= r R) -> A = C -> B = D -> l ~= r.
  intros; subst.
  apply eq_JMeq; apply functional_extensionality.
  intros; erewrite H; eauto.
Qed.
Hint Resolve JMeq_extensionality : MoreJMeq.

Definition JMeq_type_eq A B (a : A) (b : B) (H : a ~= b) : A = B := ltac:(inversion H;trivial).
Hint Resolve JMeq_type_eq : MoreJMeq.

Definition eq_proj1_JMeq T (A B : T -> Prop) (l : sig A) (r : sig B) :
  A = B -> ` l = ` r -> l ~= r := ltac:(intuition).

Definition JMeq_proj1_eq T (A B : T -> Prop) (l : sig A) (r : sig B) :
  A = B -> l ~= r -> ` l = ` r := ltac:(intuition).

Hint Resolve JMeq_eq JMeq_proj1_eq JMeq_proj1_eq : MoreJMeq.