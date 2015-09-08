Require Export JMeq Program.
Set Implicit Arguments.

Create HintDb MoreJMeq discriminated.
Hint Extern 1 => progress subst : MoreJMeq.

Hint Extern 1 => apply subset_eq : MoreJMeq.

Definition eq_JMeq T (l r : T) : l = r -> l ~= r := $(auto with MoreJMeq)$.

Hint Resolve eq_JMeq functional_extensionality : MoreJMeq.

Theorem JMeq_extensionality_l A B C (l : A -> C) (r : B -> C) :
  (forall L R, L ~= R -> l L = r R) -> A = B -> l ~= r.
  intros.
  subst; auto with MoreJMeq.
  (*debug auto 10 with MoreJMeq.*)
Qed.

Theorem JMeq_extensionality_r A B C (l : A -> B) (r : A -> C) :
  (forall L R, L = R -> l L ~= r R) -> B = C -> l ~= r.
  intros; subst.
  apply eq_JMeq; apply functional_extensionality.
  intros; erewrite H; eauto.
Qed.

Theorem JMeq_extensionality A B C D (l : A -> B) (r : C -> D) :
  (forall L R, L ~= R -> l L ~= r R) -> A = C -> B = D -> l ~= r.
  intros; subst.
  apply eq_JMeq; apply functional_extensionality.
  intros; erewrite H; eauto.
Qed.

Definition subset_JMeq T (A B : T -> Prop) (l : sig A) (r : sig B) :
  A = B -> l ~= r <-> ` l = ` r := $(intuition)$.
