
Parameter (Y : Type).
Axiom Y_eq_dec : forall (x y : Y), {x = y} + {~x = y}.
Parameter (ordre : Y -> Y -> Prop).
Axiom total_ordre : forall (x y : Y), {ordre x y} + {ordre y x}.
Hypothesis ordre_refl : forall y, ordre y y.
Hypothesis ordre_sym : forall x y, ordre x y /\ ordre y x -> x = y.
Hypothesis ordre_trans : forall x y z, ordre x y -> ordre y z -> ordre x z.
(*just some variables names to facilitate the definition of lhs and rhs*)
Variable (x : Y).
Variable (y : Y).
Variable (z : Y).


Inductive est_dans : Y -> list Y -> Prop :=
|construct: forall (x : Y) (l : list Y), est_dans x (cons x l) 
|propag : forall (x y : Y) (l : list Y),  est_dans x l -> est_dans x (cons y l).

Inductive sans_doublon :list Y -> Prop :=
|cas_base_sd: sans_doublon nil
|cas_cons_sd : forall (l : list Y) (x : Y), sans_doublon l -> ~(est_dans x l) -> sans_doublon (cons x l).

Check ordre.

Inductive triee : list Y -> Prop :=
|cas_nil_tri : triee nil
|cas_x_tri : forall (x : Y), triee (cons x nil)
|cas_cons_tri : forall (x y: Y)(l : list Y), triee (x :: l) -> ordre y x  -> triee (cons y (cons x l )).
Require Import QArith.

Fixpoint calcul (phi : Y -> Q) (l  : list Y) : Q := match l with 
|nil => 0%Q
|cons x q => phi x + calcul phi q
end.

Fixpoint inserer (x : Y) (l : list Y) : list Y := 
match l with 
|nil => cons x nil
|cons y q => match (Y_eq_dec x y) with 
             |left _ => l 
             |right _ => match (total_ordre x y) with 
                        |left _ => cons x (cons y q)
                        |right _ => cons y (inserer x q)
                      end
             end
end.

Fixpoint union (l l' : list Y) : list Y :=
match l with 
|nil => l'
|cons y q => union q (inserer y l')
end.

Record ensemble_fini :=
{ensemble :>  list Y ; 
is_a_set : sans_doublon ensemble ; 
is_sorted : triee ensemble }.

Lemma tri_logique : forall (l : list Y) (x y : Y), 
triee (cons x l) -> est_dans y l -> ordre x y.
Proof.
intros.
induction l.
inversion H0. 
destruct (Y_eq_dec y0 a).
inversion H.
rewrite e.
auto.
apply IHl. 
inversion H.
inversion H3.
apply cas_x_tri.
apply cas_cons_tri.
auto.
apply ordre_trans with (y := a).
auto.
auto.
inversion H0.
assert (False).
apply n.
auto.
inversion H2.
auto.
Qed.

Print tri_logique.

Lemma tri_cons_tri : forall (l : list Y) (a : Y), 
triee (cons a l) -> triee l.
Proof.
intros.
induction l.
apply cas_nil_tri.
inversion H.
auto.
Qed.


Lemma tri_not_inside : forall (l : list Y) (a x0: Y) , 
triee (cons a l) -> x0 <> a -> ordre x0 a -> ~(est_dans x0 l).
Proof.
intros.
inversion H.
intro.
inversion H2.
rewrite <- H3 in H.
intro.
assert ({ordre x1 x0} + {ordre x0 x1}).
apply total_ordre.
destruct H7.
apply H0.
apply ordre_sym.
split.
auto.
apply ordre_trans with (y := x1).
auto.
auto.
assert ({x0 = x1}+ {x0 <> x1}).
apply Y_eq_dec.
destruct H7.
apply H0.
apply ordre_sym.
split.
auto.
rewrite e.
auto.
inversion H6.
apply n.
auto.
apply H0.
apply ordre_sym.
split.
auto.
apply ordre_trans with (y := x1).
auto.
apply tri_logique with (l := l0).
auto.
auto.
Qed.

Lemma insertion_preserves_inside : forall (l : list Y) (a x0 :Y), 
est_dans a l -> est_dans a (inserer x0 l).
Proof.
intros.
induction l.
inversion H.
simpl.
destruct (Y_eq_dec x0 a0).
auto.
destruct (total_ordre x0 a0).
apply propag.
auto.
destruct (Y_eq_dec a a0).
rewrite e.
apply construct.
apply propag.
apply IHl.
inversion H.
assert (False).
apply n0.
auto.
inversion H1.
auto.
Qed.

Lemma insertion_alr_min : forall (l : list Y) (a : Y), 
(forall (x : Y), est_dans x l -> ordre a x) -> ~est_dans a l-> (inserer a l = cons a l).
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
destruct (Y_eq_dec a a0).
exfalso.
apply H0.
rewrite e.
apply construct.
destruct (total_ordre a a0).
reflexivity.
exfalso.
apply n.
apply ordre_sym.
split.
apply H.
apply construct.
auto.
Qed.

Lemma insertion_conserves_inside : forall (l : list Y) (a x0 :Y), 
est_dans a (inserer x0 l) /\x0 <> a -> est_dans a l.
Proof.
intros.
induction l.
inversion H.
simpl.
simpl in H0.
inversion H0.
assert (False).
apply H1.
symmetry ; auto.
inversion H3.
auto.
destruct (Y_eq_dec a a0).
rewrite e.
apply construct.
apply propag.
apply IHl.
split.
simpl in H.
destruct (Y_eq_dec x0 a0).
destruct H.
inversion H.
assert (False).
apply n.
auto.
inversion H2.
apply insertion_preserves_inside.
auto.
destruct (total_ordre x0 a0).
destruct H.
inversion H.
assert (False).
apply H0.
symmetry.
auto.
inversion H2.
inversion H3.
assert (False).
apply n.
symmetry.
auto.
inversion H6.
apply insertion_preserves_inside.
auto.
destruct H.
inversion H.
assert (False).
apply n.
symmetry.
auto.
inversion H2.
auto.
destruct H.
auto.
Qed.


Lemma insertion_preserves_doublon : forall (l : list Y)(x0 a : Y),
sans_doublon (cons a l) -> x0 <> a -> ((est_dans a (inserer x0 l)) -> False).
Proof.
intros.
induction l.
simpl in H1.
inversion H1.
apply H0.
apply symmetry.
auto.
inversion H4.
simpl in H1.
destruct (Y_eq_dec x0 a0).
inversion H1.
inversion H.
apply H8.
rewrite H4.
apply construct.
apply IHl.
inversion H.
apply cas_cons_sd.
inversion H8.
auto.
intro. 
apply H9.
auto.
apply insertion_preserves_inside.
auto.
destruct (total_ordre x0 a0).
apply IHl.
inversion H.
inversion H4.
apply cas_cons_sd.
auto.
intro.
apply H5.
apply propag.
auto.
assert (False).
apply IHl.
inversion H.
inversion H4.
apply cas_cons_sd.
auto.
intro.
apply H5.
apply propag.
auto.
apply insertion_preserves_inside.
inversion H1.
assert (False).
apply H0.
auto.
inversion H3.
inversion H4.
inversion H.
assert (False).
apply H12.
rewrite H8.
apply construct.
inversion H13.
auto.
inversion H2.
apply IHl.
inversion H.
inversion H4.
auto.
apply cas_cons_sd.
auto.
intro.
apply H5.
apply propag.
auto.
inversion H1.
inversion H.
assert (False).
apply H8.
rewrite H4.
apply construct.
inversion H9.
auto.
Qed.

Lemma sans_doublon_inserer : forall (l : list Y) (x : Y), 
triee l -> sans_doublon l -> sans_doublon (inserer x l).
Proof.
intros.
induction l.
simpl.
apply cas_cons_sd.
auto.
intro.
inversion H1.
simpl.
destruct (Y_eq_dec x0 a).
exact H0.
destruct (total_ordre x0 a).
apply cas_cons_sd.
exact H0.
apply tri_not_inside with (a := a).
apply cas_cons_tri.
auto.
apply ordre_refl.
auto.
auto.
apply cas_cons_sd.
apply IHl.
inversion H.
apply cas_nil_tri.
auto.
inversion H0.
auto.
assert (est_dans a (inserer x0 l) -> False).
apply insertion_preserves_doublon with (x0 := x0) (a := a) (l := l).
auto.
auto.
auto.
Qed.

Lemma insertion_preserves_tri : forall (l : list Y)(a : Y), 
sans_doublon l -> triee l -> triee (inserer a l).
Proof.
intros.
generalize dependent a.
induction l.
intros.
simpl.
apply cas_x_tri.
intros.
simpl.
destruct (Y_eq_dec a0 a).
auto.
destruct (total_ordre a0 a).
apply cas_cons_tri.
auto.
auto.
assert (triee (inserer a0 l)).
apply IHl.
inversion H.
auto.
inversion H0.
auto.
apply cas_nil_tri.
auto.
destruct l.
simpl.
apply cas_cons_tri.
auto.
auto.
simpl.
simpl in H1.
destruct (Y_eq_dec a0 y0).
auto.
destruct (total_ordre a0 y0).
apply cas_cons_tri.
apply cas_cons_tri.
inversion H0.
auto.
auto.
auto.
apply cas_cons_tri.
auto.
auto.
inversion H0.
auto.
Qed.

Lemma sans_doublon_union : forall (l l' : list Y), 
sans_doublon l -> triee l -> sans_doublon l' -> triee l' -> sans_doublon (union l l').
Proof.
intros.
generalize dependent l'.
induction l.
simpl.
intros.
auto.
intros.
simpl.
apply IHl with (l' := inserer a l').
inversion H.
auto.
induction l'.
inversion H0.
auto.
auto.
apply IHl'.
inversion H1.
auto.
inversion H2.
apply cas_nil_tri.
auto.
apply sans_doublon_inserer.
auto.
auto.
apply insertion_preserves_tri.
auto.
auto.
Qed.

Lemma sorted_union : forall (l l' : list Y), 
sans_doublon l -> triee l -> sans_doublon l' -> triee l' -> triee (union l l').
Proof.
intros.
generalize dependent l'.
induction l.
intros.
simpl.
auto.
intros.
simpl.
apply IHl with (l' := inserer a l').
inversion H.
auto.
inversion H0.
auto.
apply cas_nil_tri.
auto.
apply sans_doublon_inserer.
auto.
auto.
apply insertion_preserves_tri.
auto.
auto.
Qed.

Lemma union_not_null : forall (l l' :list Y), 
l <> nil -> l' <> nil -> union l l' <> nil.
Proof.
intros.
generalize dependent l'.
induction l.
intros.
intro.
simpl in H1.
apply H0.
auto.
intros.
simpl.
destruct l.
simpl.
intro.
destruct l'.
simpl in H1.
inversion H1.
simpl in H1.
destruct(Y_eq_dec a y0).
inversion H1.
destruct (total_ordre a y0).
inversion H1.
inversion H1.
simpl.
apply IHl with (l' := inserer a l').
intro.
inversion H1.
intro.
destruct l'.
simpl in H1.
inversion H1.
simpl in H1.
destruct(Y_eq_dec a y1).
inversion H1.
destruct (total_ordre a y1).
inversion H1.
inversion H1.
Qed.

Lemma est_dedans_bien : forall (l : list Y) (a : Y), 
est_dans a (inserer a l).
Proof.
intros.
induction l.
simpl.
apply construct.
simpl.
destruct (Y_eq_dec a a0).
rewrite e.
apply construct.
destruct (total_ordre a a0).
apply construct.
apply propag.
auto.
Qed.



Lemma transmission_gauche : forall (l l' : list Y) (a : Y), 
est_dans a l -> est_dans a (union l l').
Proof.
intros.
generalize dependent l'.
induction l.
intro.
induction l'.
intros.
inversion H.
simpl in IHl'.
simpl.
apply propag.
auto.
intro.
inversion H.
simpl.
Admitted.


Lemma transmission_droite : forall (l l' : list Y) (a : Y), 
est_dans a l -> est_dans a (union l' l).
Proof.
Admitted.

Lemma est_dans_already : forall (l : list Y) (a a0 : Y), 
a <> a0 -> est_dans a (inserer a0 l) -> est_dans a l.
Proof.
intros.
induction l.
simpl in H0.
inversion H0.
assert (False).
apply H.
auto.
inversion H2.
inversion H3.
simpl in H0.
destruct (Y_eq_dec a0 a1).
apply propag.
apply IHl.
inversion H0.
assert (False).
apply H.
rewrite H3.
apply symmetry.
auto.
inversion H2.
apply insertion_preserves_inside.
auto.
destruct (Y_eq_dec a a1).
rewrite e.
apply construct.
apply propag.
destruct (total_ordre a0 a1).
inversion H0.
assert (False).
apply H.
auto.
inversion H2.
inversion H3.
assert (False).
apply n0.
auto.
inversion H6.
auto.
inversion H0.
assert (False).
apply n0.
auto.
inversion H2.
apply IHl.
auto.
Qed.

Lemma transmission_inverse : forall (l l' : list Y) (a :Y), 
est_dans a (union l l') -> est_dans a l \/ est_dans a l'.
Proof.
intros.
generalize dependent l'.
induction l.
intros.
simpl in H.
right.
auto.
intros.
simpl in H.
assert (est_dans a l \/ est_dans a (inserer a0 l')).
apply IHl.
auto.
destruct H0.
left.
apply propag.
auto.
destruct (Y_eq_dec a a0).
rewrite e.
left.
apply construct.
right.
apply est_dans_already with (a := a) (a0 := a0).
auto.
auto.
Qed.

Lemma transmission_not : forall (l l' : list Y) (a : Y), 
~est_dans a (union l l') -> ~est_dans a l /\ ~est_dans a l'.
Proof.
intros.
induction l.
split.
intro.
inversion H0.
simpl in H.
auto.
split.
intro.
apply H.
apply transmission_gauche.
auto.
intro.
apply H.
simpl.
assert (est_dans a l' -> est_dans a (inserer a0 l')).
apply (insertion_preserves_inside).
apply H1 in H0.
apply transmission_droite.
auto.
Qed.

Definition union_finite (A B : ensemble_fini) : ensemble_fini.
Proof.
split with (union A B).
apply sans_doublon_union.
apply is_a_set.
apply is_sorted.
apply is_a_set.
apply is_sorted.
apply sorted_union.
apply is_a_set.
apply is_sorted.
apply is_a_set.
apply is_sorted.
Defined.

Lemma union_preserves_both : forall (x : Y) (l l' : list Y), 
est_dans x (union l l') -> est_dans x l \/ est_dans x l'.
Proof.
intros. 
generalize dependent l'.
induction l.
intros.
induction l'.
simpl in H.
inversion H.
simpl in H.
simpl in IHl'.
right.
auto.
intros.
simpl in H.
destruct (Y_eq_dec x0 a).
left.
rewrite e.
apply construct.
assert (est_dans x0 l \/ est_dans x0 (inserer a l')).
apply IHl.
auto.
destruct H0.
left.
apply propag.
auto.
right.
apply insertion_conserves_inside with (x0 := a) (a := x0).
split.
auto.
intro.
apply n. 
symmetry.
auto.
Qed.

Lemma est_dans_dec : forall (x: Y) (l : list Y), {est_dans x l} + {~est_dans x l}.
Proof.
intros.
induction l.
right.
intro.
inversion H.
destruct IHl.
left.
apply propag.
auto.
destruct (Y_eq_dec x0 a).
left.
rewrite e.
apply construct.
right.
intro.
inversion H.
apply n0.
auto.
apply n.
auto.
Qed.

Lemma equiv_tri : forall (l : list Y) (x : Y), 
(forall (z : Y), est_dans z l -> ordre x z) -> triee l -> triee (cons x l).
Proof.
intros.
induction l.
apply cas_x_tri.
apply cas_cons_tri.
auto.
apply H.
apply construct.
Qed.


Definition singleton (x : Y) : ensemble_fini.
Proof.
split with (cons x nil).
apply cas_cons_sd.
apply cas_base_sd.
intro.
inversion H.
apply cas_x_tri.
Defined.


