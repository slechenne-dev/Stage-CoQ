Require Import convex_algebra.
Require Import LS.
Require Import universal_algebra_generality.
Require Import QArith.
Require Import Lia.
Require Import ZArith.

Check quotient_relation.
Definition convex_quotient_relation := quotient_relation (convex_signature) (convex_equalities).

Axiom term_cqr_dec : forall (t t' : term), {convex_quotient_relation t t'} + {~convex_quotient_relation t t'}.

Lemma Q'_decidable : forall (q q' : Q'), {q = q'} +{~q = q'}.
Proof.
Admitted.



Fixpoint liste_term (t : term) : list Y := match t with 
|generator x => cons x nil
|node op args => union (liste_term (args Fst)) (liste_term (args Snd))
end.

Lemma list_term_not_nil : forall (t : term), ~liste_term t = nil.
Proof.
induction t.
simpl.
intro ; inversion H.
simpl.
apply union_not_null.
apply H.
apply H.
Qed.


(* la preuve ci dessous est vraie (faite à la main) mais demandera un effort de formalisation en coq*)



Lemma meme_term : forall (t t' : term), 
convex_quotient_relation t t' -> (liste_term t) = (liste_term t').
Proof.
intros.
induction H.
destruct e.
simpl.
destruct (Y_eq_dec (convex_algebra.x) (convex_algebra.x)).
simpl.
reflexivity.
exfalso.
apply n.
reflexivity.
simpl.
destruct (Y_eq_dec convex_algebra.x convex_algebra.y).
exfalso.
assert (~convex_algebra.x = convex_algebra.y).
apply convex_algebra.different.
apply H.
auto.
destruct (total_ordre convex_algebra.x convex_algebra.y).
destruct (Y_eq_dec convex_algebra.y convex_algebra.x).
exfalso.
apply n.
apply symmetry.
auto.
destruct (total_ordre convex_algebra.y convex_algebra.x).
exfalso.
apply n.
apply LS.ordre_sym.
split ; auto; auto.
reflexivity.
destruct (Y_eq_dec convex_algebra.y convex_algebra.x).
exfalso.
apply n.
apply symmetry ; exact e.
destruct (total_ordre convex_algebra.y convex_algebra.x).
reflexivity.
exfalso.
apply n.
apply LS.ordre_sym.
split ;auto ; auto.
simpl.
{ assert (Hnxy := convex_algebra.different).
  assert (Hnyz := convex_algebra.different2).
  assert (Hnzx := convex_algebra.different3).
  assert (ordre1 := convex_algebra.order).
  assert (ordre2 := convex_algebra.order2).
  assert (ordre3 := convex_algebra.order3).
  try (case (Y_eq_dec convex_algebra.x convex_algebra.x));
  try (case (Y_eq_dec convex_algebra.y convex_algebra.x));
  try (case (Y_eq_dec convex_algebra.x convex_algebra.y));
  try (case (Y_eq_dec convex_algebra.y convex_algebra.y));
  try (case (Y_eq_dec convex_algebra.x convex_algebra.z));
  try (case (Y_eq_dec convex_algebra.y convex_algebra.z));
  intros; try contradiction; try apply cas_refl; try apply exfalso; auto.
   }
admit.
reflexivity.
rewrite IHquotient_relation ; reflexivity.
rewrite IHquotient_relation1 .
auto.
simpl.
assert (liste_term (args Fst) = liste_term (args' Fst)).
apply H0.
rewrite H1.
assert (liste_term (args Snd) = liste_term (args' Snd)).
apply H0.
rewrite H2.
reflexivity.
simpl.
admit. 
Admitted.


Lemma is_a_set : forall (t : term), 
sans_doublon (liste_term t) /\ triee (liste_term t).
Proof.
intros.
induction t.
split.
simpl.
apply cas_cons_sd.
apply cas_base_sd.
intro.
inversion H.
simpl.
apply cas_x_tri.
split.
simpl.
apply sans_doublon_union.
apply H.
apply H.
apply H.
apply H.
simpl.
apply sorted_union.
apply H. apply H . apply H . apply H.
Qed.


Lemma simplification_cas_3 : forall (t t' : term) (a : Y) (l : list Y) (p : Q'), 
(cons a l = liste_term t) -> convex_quotient_relation t (plus' p (generator a) t') -> 
~est_dans a (liste_term t') -> l = liste_term t'.
Proof.
intros.
assert (cons a l = liste_term (plus' p (generator a) t')).
rewrite H.
apply meme_term.
auto.
assert (inserer a (liste_term t') = cons a (liste_term t')).
apply insertion_alr_min.
intros.
destruct (Y_eq_dec x a).
rewrite e.
apply LS.ordre_refl.
assert (est_dans x (inserer a (liste_term t'))).
apply insertion_preserves_inside.
auto.
simpl in H2.
rewrite <- H2 in H4.
apply tri_logique with (l := l).
rewrite H.
apply is_a_set.
inversion H4.
exfalso.
apply n ; auto.
auto.
auto.
simpl in H2.
rewrite H3 in H2.
inversion H2. 
auto.
Qed.

(*on demontre des égalités admissibles*)

Definition theta_0 (u : Y) (t : term) := match (Y_eq_dec u convex_algebra.x) with 
|left _ => t
|right _ => generator u
end.


Lemma relation_admissible_idem : forall (t : term) (p : Q'), 
convex_quotient_relation (plus' p t t) t.
Proof.
intros. 
apply cas_trans with 
(T' := application_subst convex_signature convex_equalities 
(plus' p (generator convex_algebra.x) (generator convex_algebra.x)) (fun x => theta_0 x t)).
apply cas_passage_contexte.
intros.
simpl.
destruct n.
simpl.
unfold theta_0.
simpl.
destruct (Y_eq_dec convex_algebra.x convex_algebra.x).
apply cas_refl.
assert (False). apply n.
reflexivity.
inversion H.
unfold theta_0.
destruct (Y_eq_dec convex_algebra.x convex_algebra.x).
apply cas_refl.
assert (False). apply n. reflexivity.
inversion H.
apply cas_trans with 
(T' := application_subst convex_signature convex_equalities (generator convex_algebra.x) (fun x => theta_0 x t)).
apply cas_subst.
assert (lhs_convexe (idempotency p) = (plus' p (generator convex_algebra.x) (generator convex_algebra.x))).
simpl ;  reflexivity.
rewrite <- H.
assert (rhs_convexe (idempotency p) = generator (convex_algebra.x)).
simpl ; reflexivity.
rewrite <- H0.
apply cas_base.
simpl.
unfold theta_0.
destruct (Y_eq_dec convex_algebra.x convex_algebra.x).
apply cas_refl.
assert (False). apply n ; reflexivity.
inversion H.
Qed.

Definition theta_1 (u : Y) (t t' : term) : term := match (Y_eq_dec u convex_algebra.x) with 
          |left _ => t  
          |right _ => match (Y_eq_dec u convex_algebra.y) with 
                      |left _  => t'
                      |right _ => generator u
                      end
          end.

Lemma relation_admissible_comm : forall (t t0 : term) (p : Q'), convex_quotient_relation (plus' p t t0) (plus' (opposite p) t0 t).
Proof.
intros.
apply cas_trans with (application_subst (convex_signature) (convex_equalities) (plus' p (generator (convex_algebra.x)) (generator (convex_algebra.y))) (fun z => if Y_eq_dec convex_algebra.x z then t else t0)).
{ unfold plus'; simpl.
  apply cas_passage_contexte.
  intros n.
  destruct n; simpl.
  - case (Y_eq_dec convex_algebra.x convex_algebra.x) ;  intros ; try contradiction.
    apply cas_refl.
  - assert (Hneqxy := convex_algebra.different).
    case (Y_eq_dec convex_algebra.x convex_algebra.y); intros; try contradiction.
    apply cas_refl. }
apply cas_trans with (application_subst (convex_signature) (convex_equalities) (plus' (opposite p) (generator (convex_algebra.y)) (generator (convex_algebra.x))) (fun z => if Y_eq_dec convex_algebra.x z then t else t0)).
2:{ unfold plus'; simpl.
    apply cas_passage_contexte.
    intros n.
    destruct n; simpl.
    - assert (Hneqxy := convex_algebra.different).
      case (Y_eq_dec convex_algebra.x convex_algebra.y); intros; try contradiction.
      apply cas_refl.
    - case (Y_eq_dec convex_algebra.x convex_algebra.x); intros; try contradiction.
      apply cas_refl. }
apply cas_subst.
apply cas_base with (e := commutativity p).
Qed.

Definition theta_2 (u : Y) (t t' t'' : term) : term := 
match (Y_eq_dec u (convex_algebra.x)) with
|right _ => t
|left _ => match (Y_eq_dec u (convex_algebra.y)) with
          |left _ => t'
          |right _ => match (Y_eq_dec u (convex_algebra.z)) with 
                      |left _ => t''
                      |right _ => generator u
                      end
          end
end.

Axiom quotient_relation_cong_Q : forall p p' t t', rationnel p == rationnel p' ->
  convex_quotient_relation (plus' p t t') (plus' p' t t').  

Lemma relation_admissible_assoc : forall (p q : Q') (t t' t'' : term), 
convex_quotient_relation (plus' q (plus' p t t') t'') (plus' (produit p q) t (plus' (calcul_assoc p q) t' t'')).
Proof.
intros.
apply cas_trans with (application_subst (convex_signature) (convex_equalities) (plus' q (plus' p (generator convex_algebra.x) (generator convex_algebra.y)) (generator convex_algebra.z)) (fun o => if Y_eq_dec convex_algebra.x o then t else if Y_eq_dec convex_algebra.y o then t' else t'')).
{ assert (Hnxy := convex_algebra.different).
  assert (Hnyz := convex_algebra.different2).
  assert (Hnzx := convex_algebra.different3).
  simpl; apply cas_passage_contexte.
  intros n; destruct n; simpl; [ apply cas_passage_contexte; intros n; destruct n; simpl | ];
  try (case (Y_eq_dec convex_algebra.x convex_algebra.x));
  try (case (Y_eq_dec convex_algebra.y convex_algebra.x));
  try (case (Y_eq_dec convex_algebra.x convex_algebra.y));
  try (case (Y_eq_dec convex_algebra.y convex_algebra.y));
  try (case (Y_eq_dec convex_algebra.x convex_algebra.z));
  try (case (Y_eq_dec convex_algebra.y convex_algebra.z));
  intros; try contradiction; try apply cas_refl; exfalso; auto. }
  -
(*
apply cas_trans with 
(application_subst (convex_signature) (convex_equalities) (plus' (produit p q)  (generator convex_algebra.x) (plus' (calcul_assoc p q) (generator convex_algebra.y) (generator convex_algebra.z)))(fun o => if Y_eq_dec convex_algebra.x o then t else if Y_eq_dec convex_algebra.y o then t' else t'')).
{ assert (Hnxy := convex_algebra.different).
  assert (Hnyz := convex_algebra.different2).
  assert (Hnzx := convex_algebra.different3). 
  simpl. apply cas_passage_contexte.
  intros n; destruct n; simpl; [ apply cas_passage_contexte; intros n; destruct n; simpl | ];
  try (case (Y_eq_dec convex_algebra.x convex_algebra.x));
  try (case (Y_eq_dec convex_algebra.y convex_algebra.x));
  try (case (Y_eq_dec convex_algebra.x convex_algebra.y));
  try (case (Y_eq_dec convex_algebra.y convex_algebra.y));
  try (case (Y_eq_dec convex_algebra.x convex_algebra.z));
  try (case (Y_eq_dec convex_algebra.y convex_algebra.z));
  intros; try contradiction; try apply cas_refl; exfalso; auto. }*)
Admitted.

Lemma relation_admissible_congurency : forall (p q: Q') (t t0 : term), 
p == q ->convex_quotient_relation (plus' p t t0) (plus' q t t0).
Proof.
intros.
apply cas_trans with (application_subst (convex_signature) (convex_equalities) (plus' p (generator (convex_algebra.x)) (generator (convex_algebra.y))) (fun z => if Y_eq_dec convex_algebra.x z then t else t0)).
{ unfold plus'; simpl.
  apply cas_passage_contexte.
  intros n.
  destruct n; simpl.
  - case (Y_eq_dec convex_algebra.x convex_algebra.x) ;  intros ; try contradiction.
    apply cas_refl.
  - assert (Hneqxy := convex_algebra.different).
    case (Y_eq_dec convex_algebra.x convex_algebra.y); intros; try contradiction.
    apply cas_refl. }
apply cas_trans with (application_subst (convex_signature) (convex_equalities) (plus' q (generator (convex_algebra.x)) (generator (convex_algebra.y))) (fun z => if Y_eq_dec convex_algebra.x z then t else t0)).
2:{ unfold plus'; simpl.
    apply cas_passage_contexte.
    intros n.
    destruct n; simpl.
    - assert (Hneqxy := convex_algebra.different). 
      case (Y_eq_dec convex_algebra.x convex_algebra.x); intros; try contradiction.
      apply cas_refl.
    - pose proof (convex_algebra.different). case (Y_eq_dec convex_algebra.x convex_algebra.y); intros; try contradiction.
      apply cas_refl. }
apply cas_subst.
apply cas_base with (e := congruency p q H).
Qed.


Definition coefficient_1 (p q : Q') : Q' :=
produit (opposite (calcul_assoc q (opposite p))) (opposite (produit q (opposite p))).

Definition coefficient_2 (p q : Q') : Q' :=
calcul_assoc (opposite (calcul_assoc q (opposite p))) (opposite (produit q (opposite p))).

Lemma relation_admissible_assoc_inv : forall (p q : Q') (t t' t'' : term), 
convex_quotient_relation
(plus' p t (plus' q t' t'')) 
(plus' (coefficient_2 p q) (plus' (coefficient_1 p q) t t') t'').
Proof.
Admitted.

Record couple_utile :=
{terme_g : term; 
poid : Q'}.


Lemma separation_case (x : Y) :  forall (t : term), 
{ ~est_dans x (liste_term t)} 
+ {convex_quotient_relation t (generator x)}
+{ r : couple_utile |  convex_quotient_relation t (plus' (poid r) (generator x) (terme_g r)) /\ ~(est_dans x (liste_term (terme_g r)))} .
Proof.
intros.
induction t.
destruct (Y_eq_dec x x0).
left.
right.
rewrite e. apply cas_refl.
left. left.
intro.
simpl in H.
inversion H.
apply n ; auto.
inversion H2.
destruct o.
pose proof (X Fst).
pose proof (X Snd).
destruct X0.
destruct s.
destruct X1.
destruct s.
left. left.
simpl.
intro.
apply union_preserves_both in H.
destruct H.
apply n ; auto.
apply n0 ; auto.
simpl.
right.
split with {|terme_g := (t Fst) ; poid := opposite q|}.
split.
simpl.
apply cas_trans with (T' :=  (plus' q (t Fst) (generator x))).
unfold plus'.
apply cas_passage_contexte.
intros.
destruct n0.
apply cas_refl.
auto.
apply relation_admissible_comm.
auto.
right.
destruct s.
destruct x0.
destruct a.
simpl in H.
remember poid0 as q1.
remember terme_g0 as x1.
split with {|terme_g :=(plus' (calcul_assoc q1 (opposite q)) x1 (t Fst)) ; poid := (produit q1 (opposite q)) |}.
simpl.
split.
apply cas_trans with (T' := plus' q (t Fst) (plus' q1 (generator x) x1)).
unfold plus'; simpl.
apply cas_passage_contexte.
intros.
destruct n0.
apply cas_refl.
unfold plus' in H.
auto.
apply cas_trans with (T' := plus' (opposite q) (plus' q1 (generator x) x1) (t Fst)).
apply relation_admissible_comm.
apply relation_admissible_assoc.
intro.
simpl in H1.
apply union_preserves_both in H1.
destruct H1.
apply H0.
auto.
apply n.
auto.
destruct X1.
destruct s.
right.
split with {| terme_g := t Snd ; poid := q|}.
simpl.
split.
unfold plus'.
apply cas_passage_contexte.
intros n0.
destruct n0.
auto.
apply cas_refl.
auto.
left. right. 
apply cas_trans with (T' := plus' q (generator x) (generator x)).
apply cas_passage_contexte.
intro n.
destruct n.
auto. auto.
apply relation_admissible_idem.
right.
destruct s.
destruct x0.
remember (terme_g0) as x1.
remember poid0 as q1.
destruct a.
split with {|terme_g := x1; poid := coefficient_2 q q1|}.
simpl in H.
simpl in H0.
simpl.
split.
apply cas_trans with (T' := plus' q (generator x) (plus' q1 (generator x) x1)).
apply cas_passage_contexte.
intros.
destruct n.
auto. auto.
apply cas_trans with 
(T' := plus' (coefficient_2 q q1) (plus' (coefficient_1 q q1) (generator x) (generator x)) x1).
apply relation_admissible_assoc_inv.
apply cas_passage_contexte.
intro n.
destruct n.
apply relation_admissible_idem.
apply cas_refl.
auto.
simpl.
destruct X1.
destruct s.
right.
destruct s0.
destruct a.
destruct x0.
simpl in H.
simpl in H0.
remember terme_g0 as x1.
remember poid0 as q1.
split with {|terme_g := (plus' (calcul_assoc q1 q) x1 (t Snd)) ; poid := produit q1 q|}.
simpl.
split.
apply cas_trans with 
(T' := plus' q (plus' q1 (generator x) x1) (t Snd)).
apply cas_passage_contexte.
intros n0 ; destruct n0.
auto.
apply cas_refl.
apply relation_admissible_assoc.
intro.
simpl in H1.
apply union_preserves_both in H1.
destruct H1.
apply H0. auto.
apply n;auto.
destruct x0.
remember terme_g0 as x1 ; remember poid0 as q1.
simpl in a.
destruct a.
split with {| terme_g := x1 ; poid := opposite (produit (opposite q1) q) |}.
split.
simpl.
apply cas_trans with (T' :=plus' q (plus' q1 (generator x) x1) (generator x)).
apply cas_passage_contexte.
intro n ; destruct n.
auto.
auto.
apply cas_trans with (T' := plus' q (plus' (opposite q1) x1 (generator x) ) (generator x)).
apply cas_passage_contexte.
intro n ; destruct n.
apply relation_admissible_comm.
apply cas_refl.
apply cas_trans with 
(T' := (plus' (produit (opposite q1) q)) x1 (plus' (calcul_assoc (opposite q1) q) (generator x) (generator x))).
apply relation_admissible_assoc.
apply cas_trans with 
(T' := plus' (produit (opposite q1) q) x1 (generator x)).
apply cas_passage_contexte.
intro n ; destruct n.
apply cas_refl.
apply relation_admissible_idem.
apply relation_admissible_comm.
auto.
right.
(*
destruct e.
destruct H.
destruct H.
destruct e0.
destruct H1.
destruct H1.
remember x0 as q1.
remember x2 as q2.
split with (produit (coefficient_2 (coefficient_1 (produit q q1) (opposite (calcul_assoc q q1))) q2) (coefficient_2 (produit q q1) (opposite (calcul_assoc q q1)))).
split with (plus' (calcul_assoc (coefficient_2 (coefficient_1 (produit q q1) (opposite (calcul_assoc q q1))) q2) (coefficient_2 (produit q q1) (opposite (calcul_assoc q q1)))) x1 x3).

*)
Admitted. 


Fixpoint Transformation (t : term) (l : list Y) : term.
Proof.
remember l.
destruct l0.
exact t.
destruct (separation_case y t).
destruct s.
exact t.
exact (generator y).
destruct s.
destruct a.
destruct x.
simpl in H.
simpl in H0.
exact (plus' poid0 (generator y) (Transformation terme_g0 l0)).
Defined.

Print Transformation.



Inductive vraie_forme_normale : term -> Prop :=
|cas_base_vraie : forall (x : Y), vraie_forme_normale (generator x) 
|cas_cons_vraie : forall (x : Y) (p : Q')(t : term),
vraie_forme_normale t -> ~(est_dans x (liste_term t)) 
-> triee (liste_term t) -> (forall y, est_dans y (liste_term t) -> ordre x y)
-> vraie_forme_normale (plus' p (generator x) t).





Lemma respect_rel : forall (t : term), 
convex_quotient_relation t (Transformation t (liste_term t)).
Proof.
intros. 
remember (liste_term t) as liste.
generalize dependent t.
induction liste.
intros.
simpl.
apply cas_refl.
intros.
simpl.
destruct (separation_case a t).
destruct s.
apply cas_refl.
auto.
destruct s.
destruct x.
destruct a0.
simpl in c.
simpl in n.
assert (convex_quotient_relation (terme_g0) (Transformation terme_g0 liste)).
apply IHliste. 
assert (cons a liste = liste_term (plus' poid0 (generator a) terme_g0)).
rewrite Heqliste.
apply meme_term.
auto.
simpl in H.
assert (inserer a (liste_term terme_g0) = cons a (liste_term terme_g0)).
apply insertion_alr_min.
intros.
destruct (Y_eq_dec x a).
rewrite e.
apply LS.ordre_refl.
assert (est_dans x (inserer a (liste_term terme_g0))).
apply insertion_preserves_inside.
auto.
rewrite <- H in H1.
apply tri_logique with (l := liste).
rewrite Heqliste.
apply is_a_set.
inversion H1.
exfalso.
apply n0 ; auto.
auto.
auto.
rewrite H0 in H.
inversion H.
auto.
apply cas_trans with (T' := plus' poid0 (generator a) (terme_g0)).
auto.
apply cas_passage_contexte.
intros.
destruct n0.
apply cas_refl.
auto.
Qed.


Theorem is_Normal : forall (t : term),
vraie_forme_normale (Transformation t (liste_term t)).
Proof.
intros.
remember (liste_term t) as liste.
generalize dependent t.
induction liste.
intros.
exfalso.
apply (list_term_not_nil) with (t := t).
rewrite Heqliste.
reflexivity.
intros.
simpl.
destruct (separation_case a t).
destruct s.
exfalso.
apply n.
rewrite <- Heqliste.
apply construct.
apply cas_base_vraie.
destruct s.
destruct x.
destruct a0.
simpl in c.
simpl in n.
assert (liste = liste_term (terme_g0)).
apply simplification_cas_3 with (t :=t) (a := a) (p := poid0).
auto.
auto.
auto.
apply cas_cons_vraie.
apply IHliste.
auto.
simpl.
rewrite H.
assert (liste_term terme_g0 = liste_term (Transformation terme_g0 (liste_term terme_g0))).
apply meme_term.
apply respect_rel.
rewrite <- H0.
auto.
assert (liste_term terme_g0 = liste_term (Transformation terme_g0 (liste_term terme_g0))).
apply meme_term.
apply respect_rel.
rewrite H.
rewrite <- H0.
rewrite <- H.
apply tri_cons_tri with (a := a).
rewrite Heqliste.
apply is_a_set.
intros.
assert (liste_term terme_g0 = liste_term (Transformation terme_g0 (liste_term terme_g0))).
apply meme_term.
apply respect_rel.
rewrite H in H0.
rewrite <-  H1 in H0.
rewrite <- H in H0.
apply tri_logique with (l := liste).
rewrite Heqliste.
apply is_a_set.
auto.
Qed.


Check Term_algebra_model.
Definition convex_term_algebra := Term_algebra_model (convex_signature) (convex_equalities).

Definition q' (x : Y) : D_fin.
Proof.
split with (fun z => match Y_eq_dec z x with 
                        |left _ => 1%Q
                        |right _ => 0%Q
          end) (singleton x).
intros.
destruct (Y_eq_dec x0 x).
exfalso.
apply H.
rewrite e.
unfold singleton; simpl.
apply construct.
reflexivity.
intros.
destruct (Y_eq_dec x0 x).
split.
unfold Qlt.
simpl.
lia.
unfold Qle ; simpl ; lia.
exfalso.
unfold singleton in H.
simpl in H.
inversion H.
apply n.
auto.
inversion H2.
unfold singleton.
simpl.
destruct (Y_eq_dec x x).
unfold Qeq; simpl; lia.
exfalso.
apply n.
reflexivity.
Defined.

Definition convex_term_algebra_free := is_free_term_algebra (convex_signature)
(convex_equalities).


Definition record_free := free_relative (convex_term_algebra) (D_X) (Y) (fun x => generator x) (q').


Definition lifting_dirac_pack : record_free.
Proof.
unfold record_free.
apply convex_term_algebra_free.
Defined.

Definition lifting_dirac := (f_tilde (convex_term_algebra) (D_X) (Y) (fun x => generator x) (q')) lifting_dirac_pack.
Variable (pi : Q').


Lemma dirac_commutes_def : forall (t t' : term) (p : Q'), 
egalite_extentionnelle
 (lifting_dirac (op convex_term_algebra (plus_p p) (fun x => match x with 
                                                         |Fst => t
                                                         |Snd => t'
                                                       end)))
 (op (D_X) (plus_p p) (fun x => match x with 
                                      |Fst => lifting_dirac t
                                      |Snd => lifting_dirac t'
                        end))
.
Proof.
intros.
apply op_commute with (A := convex_term_algebra) (B := D_X) (h := lifting_dirac) (o := plus_p p)
(args := fun x => match x with 
          |Fst => t
          |Snd => t'
    end).
Qed.

Eval compute in (operation convex_signature).
Check (plus_p pi).

Lemma dirac_commutes : forall (t t' : term) (p : Q'),
(egalite_extentionnelle) (lifting_dirac (node (plus_p p : operation convex_signature) (fun x=> match x with
                                                          |Fst => t
                                                          |Snd => t'
                                                          end)))
                        (plus_p' p (lifting_dirac t) (lifting_dirac t')).
Proof.
intros.
pose proof (dirac_commutes_def t t' p).
simpl in H.
auto.
Qed.

Lemma support_is_support : forall (t : term), 
ensemble (support (lifting_dirac t)) = liste_term t.
Proof.
intros.
induction t.
simpl.
reflexivity.
intros.
simpl.
destruct o.
unfold plus_p'.
simpl.
pose proof H Fst.
pose proof H Snd.
assert (f_tilde_term convex_signature convex_equalities D_X q'= lifting_dirac).
simpl.
reflexivity.
rewrite ? H2.
rewrite H0.
rewrite H1.
reflexivity.
Qed.


Inductive relation_2 : term -> term -> Prop :=
|cas_refl_gen : forall (x : Y), relation_2 (generator x) (generator x)
|cas_sym_gen : forall (t t' : term), relation_2 t t' -> relation_2 t' t
|cas_trans_gen : forall (t t' t'' : term),
relation_2 t t' -> relation_2 t' t'' -> relation_2 t t''
|cas_plus : forall (p p' : Q') (args args' : Binary -> term),  
(forall (x : Binary), relation_2 (args x) (args' x)) -> p == p' -> relation_2 (node (plus_p p : operation convex_signature) args) (node (plus_p p' : operation convex_signature) args').


Lemma injectivity_second_case : forall (t t' : term), 
vraie_forme_normale t ->
vraie_forme_normale t' -> 
~convex_quotient_relation t t'-> 
exists (x : Y), ~lifting_dirac t x == lifting_dirac t' x.
Proof.
intros.
generalize dependent t'.
induction t.
intros.
induction t'.
simpl.
split with x.
intro.
destruct (Y_eq_dec x x).
destruct (Y_eq_dec x x0).
apply H1.
rewrite e0.
apply cas_refl.
inversion H2.
apply n.
reflexivity.
simpl.
destruct o.
remember t as args. 
inversion H0.
simpl.
unfold le_plus_star.
simpl. 
split with x0.
assert (f_tilde_term convex_signature convex_equalities D_X q'= lifting_dirac).
simpl.
reflexivity.
rewrite H9.
assert (lifting_dirac t0 x0 == 0).
apply null_outside.
rewrite support_is_support.
auto.
rewrite H10.
destruct (Y_eq_dec x0 x).
destruct (Y_eq_dec x0 x0).
rewrite Qmult_0_r.
rewrite Qplus_0_r.
rewrite Qmult_1_r.
assert (~q == 1).
Search (_ <_ -> ~_ == _).
apply Qlt_not_eq.
apply lt1.
intro.
apply H11.
rewrite H12. reflexivity.
exfalso.
apply n ; reflexivity.
destruct (Y_eq_dec x0 x0).
rewrite Qmult_0_r.
rewrite Qplus_0_r.
rewrite Qmult_1_r.
apply Qlt_not_eq.
apply gt0.
exfalso ; apply n0;  reflexivity.
remember t as args.
intros.
induction t'.
inversion H.
simpl.
assert (f_tilde_term convex_signature convex_equalities D_X q'= lifting_dirac).
simpl.
reflexivity.
split with x0.
unfold le_plus_star ; simpl.
destruct (Y_eq_dec x0 x0).
assert (lifting_dirac t0 x0 == 0).
apply null_outside.
rewrite support_is_support.
auto. 
destruct (Y_eq_dec x0 x).
rewrite H9.
rewrite H10.
rewrite Qmult_0_r.
rewrite Qplus_0_r.
rewrite Qmult_1_r.
apply Qlt_not_eq.
apply lt1.
rewrite H9.
rewrite H10.
rewrite Qmult_0_r.
rewrite Qplus_0_r.
rewrite Qmult_1_r.
intro.
assert (~0==p).
apply Qlt_not_eq.
apply gt0.
apply H12.
rewrite H11 ; reflexivity.
exfalso ; apply n ; reflexivity.
remember t0 as args'.
destruct o0.
inversion H1.
simpl.
destruct o.
assert ((f_tilde_term convex_signature convex_equalities D_X q'= lifting_dirac)).
simpl ; reflexivity.
rewrite ? H8.
unfold plus_p'. simpl.
unfold le_plus_star ; simpl.
rewrite ? H8.
inversion H.
simpl. 
destruct (Qeq_dec q q0).
destruct (Y_eq_dec x0 x).
rewrite ? H8.
assert (exists (x : Y), ~lifting_dirac t2 x == lifting_dirac t1 x).
assert (args Snd = t2).
rewrite <- H12.
reflexivity.
rewrite <-  H17.
apply H0.
rewrite H17 ; auto.
auto.
intro.
apply H2. 
apply cas_trans with (T' := plus' q0 (args Fst) (args Snd)). 
apply cas_passage_contexte ; intros n ; destruct n ; apply cas_refl ; apply cas_refl.
apply cas_trans with (T' := plus' q (args Fst) (args Snd)).
apply relation_admissible_congurency with (t := args Fst) (t0 := args Snd) (p := q0) (q := q).
symmetry; auto.
apply cas_passage_contexte.
intros n.
destruct n.
rewrite <- H5.
rewrite<-  e.
rewrite <- H12.
apply cas_refl.
rewrite <- H5.
auto.
destruct H17.
split with x1.
destruct (Y_eq_dec x1 x0).
destruct (Y_eq_dec x1 x).
rewrite ? Qmult_1_r.
rewrite ? q1.
rewrite Qplus_inj_l.
rewrite Qmult_inj_l.
auto.
intro.
assert (~0 == 1 - q0).
apply Qlt_not_eq.
apply (gt0 (opposite q0)).
apply H19.
rewrite H18.
reflexivity.
exfalso.
apply n.
rewrite e0.
auto.
destruct (Y_eq_dec x1 x).
exfalso.
apply n.
rewrite e.
auto.
rewrite ? Qmult_0_r.
rewrite ? Qplus_inj_l.
rewrite q1.
rewrite Qmult_inj_l.
auto.
intro.
assert (~0 == 1 - q0).
apply Qlt_not_eq.
apply (gt0 (opposite q0)).
apply H19.
rewrite H18.
reflexivity.
rewrite ? e.
rewrite ?H10.
destruct (total_ordre x x0).
split with x.
destruct (Y_eq_dec x x0).
exfalso.
apply n ; rewrite e ; reflexivity.
destruct (Y_eq_dec x x).
assert (lifting_dirac t1 x == 0).
apply  null_outside.
rewrite support_is_support.
auto.
rewrite H17.
assert (lifting_dirac t2 x == 0).
apply null_outside.
rewrite support_is_support.
intro.
assert (ordre x0 x).
apply H16.
auto.
apply n0.
apply LS.ordre_sym.
split ; auto. auto.
rewrite H18.
rewrite ?Qmult_0_r.
rewrite ?Qplus_0_r.
rewrite Qmult_1_r.
apply Qlt_not_eq.
apply gt0.
exfalso.
apply n1; reflexivity.
split with x0.
destruct (Y_eq_dec x0 x0).
destruct (Y_eq_dec x0 x).
exfalso.
apply n ; auto.
assert (lifting_dirac t2 x0 == 0).
apply null_outside.
rewrite support_is_support.
auto.
assert (lifting_dirac t1 x0 == 0).
apply null_outside.
rewrite support_is_support.
intro.
apply n.
apply LS.ordre_sym.
split.
auto.
apply H9.
auto.
rewrite H17 ; rewrite H18.
rewrite ?Qmult_0_r.
rewrite ?Qplus_0_r.
rewrite Qmult_1_r.
intro.
assert( ~0 == q0).
apply Qlt_not_eq.
apply gt0.
apply H20.
rewrite H19 ; reflexivity.
exfalso.
apply n0.
reflexivity.
destruct (total_ordre x x0).
destruct (Y_eq_dec x0 x).
split with x.
rewrite ?e.
destruct (Y_eq_dec x x).
rewrite ? H10.
assert (lifting_dirac t2 x == 0).
apply null_outside.
rewrite support_is_support.
rewrite <- e.
auto.
assert (lifting_dirac t1 x == 0).
apply null_outside.
rewrite support_is_support.
auto.
rewrite H17.
rewrite H18.
rewrite ?Qmult_0_r.
rewrite ?Qplus_0_r.
rewrite ?Qmult_1_r.
intro.
apply n.
rewrite H19 ; reflexivity. 
exfalso.
apply n0 ; reflexivity.
split with x.
destruct (Y_eq_dec x x).
destruct (Y_eq_dec x x0).
exfalso.
apply  n0 ; auto.
rewrite ?H10.
assert (lifting_dirac t2 x == 0).
apply null_outside.
rewrite support_is_support.
intro.
apply n1.
apply (LS.ordre_sym).
split.
auto.
apply H16.
auto.
assert (lifting_dirac t1 x == 0).
apply null_outside.
rewrite support_is_support.
auto.
rewrite H17 ; rewrite H18.
rewrite ?Qmult_0_r.
rewrite Qmult_1_r.
rewrite ?Qplus_0_r.
apply Qlt_not_eq.
apply gt0.
exfalso.
apply n1 ; reflexivity.
destruct (Y_eq_dec x0 x).
split with x0.
rewrite ?e.
destruct (Y_eq_dec x x).
rewrite ? H10.
assert (lifting_dirac t2 x == 0).
apply null_outside.
rewrite support_is_support.
rewrite <- e.
auto.
assert (lifting_dirac t1 x == 0).
apply null_outside.
rewrite support_is_support.
auto.
rewrite H17.
rewrite H18.
rewrite ?Qmult_0_r.
rewrite ?Qplus_0_r.
rewrite ?Qmult_1_r.
intro.
apply n.
rewrite H19 ; reflexivity.
exfalso.
apply n0 ; reflexivity.
split with x0.
rewrite ?H10. 
destruct (Y_eq_dec x0 x0).
destruct (Y_eq_dec x x0).
exfalso.
apply  n0 ; auto.
assert (lifting_dirac t2 x0 == 0).
apply null_outside.
rewrite support_is_support.
auto.
assert (lifting_dirac t1 x0 == 0).
apply null_outside.
rewrite support_is_support.
intro.
apply n1.
apply (LS.ordre_sym).
split.
apply H9.
auto.
auto.
rewrite H17 ; rewrite H18.
destruct (Y_eq_dec x0 x0).
destruct (Y_eq_dec x0 x).
exfalso.
apply n1.
rewrite <- e1.
reflexivity. 
rewrite ?Qmult_0_r.
rewrite ?Qplus_0_r.
rewrite Qmult_1_r.
intro.
assert (~0 == q0).
apply Qlt_not_eq.
apply gt0.
apply H20.
rewrite H19 ; reflexivity.
exfalso.
apply n2 ;reflexivity.
exfalso.
apply n1 ; reflexivity.
Qed.


Lemma delta_is_injective : forall (t t' : term), 
(~convex_quotient_relation t t') -> ~(egalite_extentionnelle (lifting_dirac t) (lifting_dirac t')).
Proof.
intros.
intro.
assert (~convex_quotient_relation (Transformation t (liste_term t)) (Transformation t' (liste_term t'))).
intro.
apply H.
apply cas_trans with (T' := Transformation t (liste_term t)).
apply respect_rel.
apply cas_trans with (T' := Transformation t' (liste_term t')).
auto.
apply cas_sym ; apply respect_rel.
assert (exists (x : Y), ~lifting_dirac (Transformation t (liste_term t)) x == lifting_dirac (Transformation t' (liste_term t')) x).
apply injectivity_second_case.
apply is_Normal.
apply is_Normal.
auto.
destruct H2.
assert (egalite_extentionnelle (lifting_dirac t) (lifting_dirac (Transformation t (liste_term t)))).
apply (op_respect (convex_term_algebra) (D_X) (lifting_dirac)).
apply respect_rel.
assert (egalite_extentionnelle (lifting_dirac t') (lifting_dirac (Transformation t' (liste_term t')))).
apply (op_respect (convex_term_algebra) (D_X) (lifting_dirac)).
apply respect_rel.
unfold egalite_extentionnelle in H2.
unfold egalite_extentionnelle in H3.
unfold egalite_extentionnelle in H4.
apply H2.
rewrite <- H4.
rewrite <- H3.
apply H0.
Qed.

Definition sortir_distribution (phi : Y -> Q) (l : list Y) : Y -> Q :=
match l with 
|nil => fun x => 0
|cons y nil => phi
|cons y q => (fun z => match (Y_eq_dec z y) with 
              |left _ => 0
              |right _ => (phi z) / (1 - (phi y))
            end)
end.

Lemma correspondance_phi_phi' : forall (phi : D_fin) (a y : Y) (q : list Y),
(ensemble (support phi) = cons a (cons y q)) -> 
(forall (l  : list Y), ~est_dans a l ->
 calcul (sortir_distribution phi (ensemble (support phi))) (l) == (calcul phi l)/(1 - phi a)).
Proof.
intros.
rewrite ?H.
simpl.
destruct (Y_eq_dec a a).
destruct (Y_eq_dec y a).
exfalso.
pose proof (LS.is_a_set (support phi)).
rewrite H in H1.
rewrite e0 in H1.
inversion H1.
apply H5.
apply construct.
induction l.
simpl.
unfold Qdiv.
rewrite  Qmult_0_l.
reflexivity.
simpl.
destruct (Y_eq_dec a0 a).
exfalso.
apply H0.
rewrite e0.
apply construct.
unfold Qdiv.
Search (_*(_ + _)).
rewrite ? Qmult_plus_distr_l.
rewrite IHl.
unfold Qdiv.
reflexivity.
intro.
apply H0.
apply propag ; auto.
exfalso.
apply n.
reflexivity.
Qed.

Definition sortir_1er (l : list Y) : list Y:=
match l with 
|nil => nil
|cons x nil => cons x nil
|cons x q => q
end.

Definition sortir_1er_set (l : ensemble_fini) : ensemble_fini.
Proof.
split with (sortir_1er (ensemble l)).
destruct l.
destruct ensemble.
simpl.
apply cas_base_sd.
simpl.
destruct (ensemble).
apply cas_cons_sd.
apply cas_base_sd.
intro H ; inversion H.
inversion is_a_set0.
auto.
destruct l.
simpl.
destruct ensemble.
simpl ; apply cas_nil_tri.
destruct ensemble.
simpl.
apply cas_x_tri.
simpl.
inversion is_sorted.
auto.
Defined.

Lemma is_not_a_set : forall (phi : D_fin), (ensemble (support phi) <> nil).
Proof.
intros.
intro.
assert (calcul phi (support phi) == 0).
rewrite H.
simpl ; reflexivity.
assert (calcul (phi) (support phi) ==1).
apply distribution.
rewrite H1 in H0.
inversion H0.
Qed.

Lemma more_0 : forall (phi : D_fin) (q : list Y), 
calcul phi q >= 0.
Proof.
induction q.
simpl.
unfold Qle; simpl; lia.
simpl.
rewrite <- Qplus_0_r at 1.
Search (_ + _ <= _ + _ ).
apply Qplus_le_compat.
apply convex_algebra.between0_1.
exact IHq.
Qed.

Lemma is_not_1 : forall (x y : Y) (q : list Y) (phi : D_fin), 
(ensemble (support phi) = cons x (cons y q)) -> (~phi x >= 1).
Proof.
intros.
intro.
assert (calcul phi (support phi) > 1).
rewrite H.
simpl.
apply  Qle_lt_or_eq in H0.
destruct H0.
+
  rewrite <- Qplus_0_r at 1.
  apply Qplus_lt_le_compat .
  auto.
  assert (calcul phi (cons y q) = phi y + calcul phi q).
  simpl ; reflexivity.
  rewrite <- H1.
  apply more_0.
+
  rewrite <- H0.
  rewrite <- Qplus_0_r at 1.
  rewrite Qplus_lt_r with (z := 1) (x := 0) (y :=  (phi y + calcul phi q)).
  rewrite <- Qplus_0_r at 1.
  Search (_ + _ < _ + _ ).
  apply Qplus_lt_le_compat with (x := 0) (y := phi y) (z := 0) (t := calcul phi q).
  apply O_inferior_1.
  rewrite H.
  apply propag.
  apply construct.
  apply more_0.
+
  assert (calcul phi (support phi) == 1).
  apply distribution.
  rewrite H2 in H1.
  inversion H1.
Qed.

Lemma inferior_logic : forall (phi : D_fin) (x : Y) (l : list Y), 
(est_dans x l) -> phi x <= calcul phi l.
Proof.
intros.
induction l.
inversion H.
simpl.
inversion H.
rewrite <- Qplus_0_r at 1.
rewrite Qplus_le_r.
apply more_0. 
Search (_ +_ <= _ + _ ).
rewrite <- Qplus_0_l at 1.
apply Qplus_le_compat.
apply between0_1.
apply IHl.
auto.
Qed.





Definition distribution_tronquée (phi : D_fin) : D_fin.
Proof.
split with (sortir_distribution phi (ensemble (support phi))) (sortir_1er_set (support phi)).
intros. 
remember (support phi) as supportphi.
destruct supportphi.
induction ensemble.
simpl.
reflexivity.
simpl in IHensemble.
simpl.
simpl in H.
destruct (ensemble).
apply (null_outside).
rewrite <- Heqsupportphi.
simpl.
auto.
destruct (Y_eq_dec x a).
reflexivity.
assert (phi x == 0).
apply (null_outside).
rewrite <- Heqsupportphi.
simpl.
intro.
inversion H0.
apply n. auto.
apply H; auto.
rewrite H0.
unfold Qeq.
simpl.
lia.
intros.
split.
remember (support phi) as supportphi.
destruct supportphi.
induction ensemble.
simpl.
exfalso.
simpl in H.
pose proof is_not_a_set phi.
apply H0.
rewrite <- Heqsupportphi.
simpl.
reflexivity.
simpl.
simpl in IHensemble.
destruct (ensemble).
apply O_inferior_1.
rewrite <- Heqsupportphi.
simpl.
simpl in H.
auto.
unfold sortir_1er_set in H.
simpl in H.
destruct (Y_eq_dec x a).
inversion H.
rewrite H2 in e.
exfalso.
clear Heqsupportphi.
rewrite e in is_a_set0.
inversion is_a_set0.
apply H6.
apply construct.
rewrite  e in H2.
inversion is_a_set0.
exfalso.
apply H7.
apply propag.
auto. 
unfold Qdiv.
rewrite <- Qmult_0_l with (x := /(1 - phi a)).
Search (_ * _ < _ * _ ).
rewrite Qmult_lt_r with (z := /(1 - phi a)).
apply O_inferior_1.
rewrite <- Heqsupportphi.
simpl.
apply propag.
auto.
apply Qinv_lt_0_compat.
rewrite <- Qplus_lt_r with (z := phi a).
unfold Qminus.
rewrite Qplus_assoc.
rewrite Qplus_comm with (x := phi a) (y := 1).
rewrite <- Qplus_assoc.
rewrite Qplus_opp_r.
rewrite Qplus_lt_l.
apply Qnot_le_lt.
apply is_not_1 with (x := a) (y := y)(q := l) (phi0 := phi).
rewrite<-  Heqsupportphi.
simpl.
reflexivity.
remember (support phi) as supportphi.
destruct supportphi.
induction ensemble.
simpl in Heqsupportphi.
simpl in H.
inversion H.
simpl in IHensemble.
simpl in H.
destruct (ensemble).
inversion H.
pose proof (between0_1 phi a).
simpl.
apply H1.
inversion H2.
simpl.
destruct (Y_eq_dec x a).
unfold Qle ; simpl; lia.
Search (_ /_ <= _).
apply  Qle_shift_div_r with (a := phi x) (b := (1 - (phi a))) (c := 1).
Search (/_). 
Search (_ + _ < _ + _).
rewrite <- Qplus_lt_l with (x := 0) (y := 1 - phi a) (z := phi a).
Search (_ + _ ).
unfold Qminus.
rewrite Qplus_0_l.
rewrite <- Qplus_assoc.
rewrite Qplus_comm with (x := - phi a) (y := phi a).
rewrite Qplus_opp_r.
rewrite Qplus_0_r.
apply Qnot_le_lt.
apply is_not_1 with (x := a)(y := y)(q := l)(phi0 := phi).
rewrite <- Heqsupportphi.
simpl.
reflexivity.
Search (_ * (_ + _ )).
unfold Qminus.
rewrite Qmult_plus_distr_r with (x := 1).
rewrite ? Qmult_1_l.
rewrite <-  Qplus_le_r with (z := phi a).
rewrite Qplus_assoc.
rewrite Qplus_comm with (x := phi a) (y := 1).
rewrite <- Qplus_assoc.
rewrite Qplus_opp_r.
rewrite Qplus_0_r.
apply Qle_trans with (y := phi a + (phi y + calcul phi l)).
apply Qplus_le_r.
assert (calcul phi (cons y l) = phi y + calcul phi l).
simpl ; reflexivity.
rewrite <-  H0.
apply inferior_logic; auto.
rewrite Qplus_assoc.
apply Qle_trans with (y := phi a + phi y + calcul phi l).
rewrite <- Qplus_0_r at 1.
rewrite Qplus_0_r.
rewrite Qplus_le_r with (z := phi a + phi y).
unfold Qle ; simpl ; lia.
assert (phi a + phi y + calcul phi l == calcul phi (support phi)).
rewrite <- Heqsupportphi.
simpl.
rewrite Qplus_assoc.
reflexivity.
rewrite H0.
apply Qle_lteq.
right.
apply distribution.
remember (support phi) as supportphi.
destruct supportphi.
induction ensemble.
simpl.
assert (calcul phi (support phi) == 0).
rewrite <- Heqsupportphi.
simpl.
reflexivity.
rewrite <- H.
apply distribution.
simpl.
destruct ensemble.
simpl.
assert (phi a + 0 = calcul phi (cons a nil)).
simpl ; reflexivity.
rewrite H.
assert (cons a nil = support phi).
rewrite <- Heqsupportphi.
simpl.
reflexivity.
rewrite H0.
apply distribution.
simpl.
destruct (Y_eq_dec y a).
simpl.
rewrite Qplus_0_l.
inversion is_a_set0.
exfalso.
apply H2.
rewrite e.
apply construct.
pose proof (correspondance_phi_phi' phi a y ensemble).
rewrite <- Heqsupportphi in H.
simpl in H.
assert (forall l : list Y,
    ~ est_dans a l ->
    calcul (fun z : Y => if Y_eq_dec z a then 0 else phi z / (1 - phi a)) l ==
    calcul phi l / (1 - phi a)).
apply H.
reflexivity.
clear H.
pose proof (H0 (cons y ensemble)).
inversion is_a_set0.
apply H in H4.
simpl in H4.
destruct (Y_eq_dec y a).
exfalso.
apply n ; auto.
rewrite H4.
unfold Qdiv.
rewrite <- Qmult_inj_r with (z := 1 - phi a).
rewrite <- Qmult_assoc.
Search (_ * _ == 1).
assert (/(1 - phi a) * (1 - phi a) == 1).
rewrite Qmult_comm.
rewrite Qmult_inv_r.
reflexivity.
intro.
Search ( _ + _ == _ + _ ).
rewrite <- Qplus_inj_r with (z := phi a) in H5.
unfold Qminus in H5.
rewrite <- Qplus_assoc in H5.
Search (_ + _ == 0).
rewrite Qplus_comm in H5.
rewrite Qplus_comm with (x := - phi a) (y := phi a) in H5.
rewrite Qplus_opp_r in H5.
rewrite ?Qplus_0_l in H5.
Search (_ <= _).
pose proof (is_not_1 a y ensemble phi).
assert (~1 <= phi a).
apply H6.
rewrite <- Heqsupportphi.
simpl.
reflexivity.
apply H7.
rewrite H5.
unfold Qle ; simpl; lia.
rewrite H5.
rewrite Qmult_comm.
rewrite ? Qmult_1_l.
rewrite <- Qplus_inj_l with (z := phi a).
unfold Qminus.
rewrite Qplus_comm with (x := 1) (y := - phi a).
rewrite ? Qplus_assoc.
rewrite Qplus_opp_r.
rewrite Qplus_0_l.
assert (calcul phi (cons a (cons y ensemble)) == phi a + phi y + calcul phi ensemble).
simpl.
rewrite Qplus_assoc ; reflexivity.
rewrite <- H6.
assert (cons a (cons y ensemble) = support phi).
rewrite <- Heqsupportphi.
simpl ; reflexivity.
rewrite H7.
apply distribution.
intro.
assert (~1 <= phi a).
pose proof (is_not_1 a y ensemble phi).
apply H6.
rewrite <- Heqsupportphi.
simpl.
reflexivity.
apply H6.
rewrite <- Qplus_inj_r with (z := phi a) in H5.
unfold Qminus in H5.
rewrite <- Qplus_assoc in H5.
Search (_ + _ == 0).
rewrite Qplus_comm in H5.
rewrite Qplus_comm with (x := - phi a) (y := phi a) in H5.
rewrite Qplus_opp_r in H5.
rewrite ?Qplus_0_l in H5.
rewrite H5.
unfold Qle ; simpl; lia.
Defined.

Definition indicatrice (x : Y) : Y -> Q :=
(fun z => match (Y_eq_dec x z) with 
|left _ => 1%Q
|right _ => 0%Q
end).

Definition un_x (x : Y) : D_fin.
Proof.
split with (indicatrice x) (singleton x).
intros.
unfold indicatrice.
destruct (Y_eq_dec x x0).
exfalso.
apply H.
unfold singleton.
simpl.
rewrite e.
apply construct.
reflexivity.
intros.
unfold singleton in H.
simpl in H.
inversion H.
split.
unfold indicatrice.
try (case (Y_eq_dec x x)) ; 
intros ; try contradiction ; try apply reflexivity.
unfold Qlt; simpl; lia.
unfold indicatrice.
try (case (Y_eq_dec x x)) ; 
intros ; try contradiction ; try apply reflexivity.
unfold Qle; simpl; lia.
inversion H2.
simpl.
unfold indicatrice.
try (case (Y_eq_dec x x)) ; 
intros ; try contradiction ; try apply reflexivity.
Qed.

Definition phi_a_record 
(phi : D_fin) (a :Y) (y : Y) (q : list Y) (H : est_dans a (support phi)) (H' : cons a (cons y q) = support phi): Q'.
Proof.
split with (phi a).
apply O_inferior_1.
rewrite <-  H'.
apply construct.
apply Qnot_le_lt.
apply is_not_1 with (x := a)(y := y)(q := q).
auto.
Defined.

Lemma prems : forall (phi : D_fin) (a y : Y) (q : list Y), 
ensemble (support phi) = cons a (cons y q) -> est_dans a (support phi).
Proof.
intros.
rewrite H.
apply construct.
Qed.

Lemma deuz : forall (phi : D_fin) ( a y : Y) (q : list Y), 
ensemble (support phi) = cons a (cons y q) -> ensemble (support (distribution_tronquée phi)) = (cons y q).
Proof.
intros.
unfold distribution_tronquée.
simpl.
rewrite H.
simpl.
reflexivity.
Qed.




Fixpoint term_extrait (phi : D_fin)  (l : list Y) (H : ensemble (support phi) = l): term.
Proof.
generalize dependent phi.
induction l.
+
  intros.
  exfalso.
  assert (calcul phi (support phi) == 0).
  rewrite  H.
  simpl.
  reflexivity.
  pose proof (distribution phi).
  rewrite H1 in H0.
  inversion H0.
+
  intros.
   destruct (l).
   ++
    exact (generator a).
  ++
    pose proof prems phi a y l0.
    assert (ensemble (support phi) = cons a (cons y l0)).
    auto.
    apply H0 in H.
    assert (ensemble (support phi) = cons a (cons y l0)) ; auto.
    pose proof deuz phi a y l0.
    apply H3 in H1.
    clear H0 ; clear H3.
    symmetry in H2.  
    exact (plus' (phi_a_record phi a y l0 H H2) (generator a) (IHl (distribution_tronquée phi) H1)).
Defined.


Lemma is_equa: forall (phi : D_fin), ensemble (support phi) = ensemble (support phi).
Proof.
intros ; reflexivity.
Qed.


Lemma correspondance_bien : forall (phi : D_fin), 
forall x, lifting_dirac (term_extrait phi (ensemble (support phi)) (is_equa phi)) x == phi x.
Proof.
intros.
destruct phi.
destruct support.
induction ensemble.
simpl.
simpl in distribution.
inversion distribution.
simpl.
destruct ensemble.
simpl in distribution.
rewrite Qplus_0_r in distribution.
simpl.
destruct (Y_eq_dec x a).
symmetry.
rewrite e.
auto.
symmetry.
apply null_outside.
intro.
simpl in H.
simpl in IHensemble.
inversion H.
exfalso.
apply n ; auto.
inversion H2.
simpl.

unfold le_plus_star.
unfold phi_a_record.
simpl.
simpl in IHensemble.
destruct (Y_eq_dec x a). 









 