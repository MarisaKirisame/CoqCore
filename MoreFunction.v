Fixpoint iterate { T } n F (x : T) :=
  match n with
  | 0 => x
  | S n' => iterate n' F (F x)
  end.
Definition f_iterate T n f : forall x : T, iterate (S n) f x = f (iterate n f x).
  induction n; simpl in *; trivial.
Qed.
