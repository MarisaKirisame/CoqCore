Require Export JMeq Program.
Set Implicit Arguments.

Create HintDb MoreJMeq.
Hint Extern 1 => progress subst : MoreJMeq.

Definition eq_proj1_sig_eq (A : Type) (P : A -> Prop) (n m : {x : A | P x}) : n = m -> ` n = ` m
  := $(intuition)$.
Hint Resolve functional_extensionality eq_proj1_sig_eq : MoreJMeq.

Definition proj1_sig_eq_eq (A : Type) (P : A -> Prop) (n m : {x : A | P x}) : ` n = ` m -> n = m
  := $(intros; apply subset_eq; trivial)$.
Hint Resolve proj1_sig_eq_eq : MoreJMeq.

Definition eq_JMeq T (l r : T) : l = r -> l ~= r := $(auto with MoreJMeq)$.
Hint Resolve eq_JMeq : MoreJMeq.

Definition JMeq_extensionality_l A B C (l : A -> C) (r : B -> C) :
  (forall L R, L ~= R -> l L = r R) -> A = B -> l ~= r := $(eauto with MoreJMeq)$.
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

Definition JMeq_proj1_eq T (A B : T -> Prop) (l : sig A) (r : sig B) :
  A = B -> ` l = ` r -> l ~= r := $(intuition)$.

Definition eq_JMeq_proj1_eq T (A B : T -> Prop) (l : sig A) (r : sig B) :
  A = B -> l ~= r -> ` l = ` r := $(intuition)$.

Hint Resolve JMeq_proj1_eq eq_JMeq_proj1_eq : MoreJMeq.
