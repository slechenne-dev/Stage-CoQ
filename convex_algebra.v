

(*we now move to convex Algebra*)

Require Import QArith.
Require Import QArith_base.
Require Import Lia.
Require Import LS.
Require Import universal_algebra_generality.
Definition Z := LS.Y.

Check Y.
Check ordre.

(*definition of (0; 1)*) 
Record Q' : Type :=
{rationnel :> Q ; 
gt0 : Qlt 0 rationnel ;
lt1 : Qlt rationnel 1 }.

(*rename this into open_O_1 *)


(*introducing our operations *)
Inductive les_plus_p : Type := 
|plus_p : Q' -> les_plus_p.

(*the arity*)
Inductive Binary : Type := Fst | Snd.

(*introducing the three equalities*)
Inductive names_equalities : Type:=
|idempotency : Q'-> names_equalities
|commutativity : Q' -> names_equalities
|associativity: Q' -> Q' -> names_equalities
|congruency : forall (p p' : Q'), p == p' -> names_equalities.


Check universal_algebra_generality.operation.
Check operation.

(*l'ensemble des variables est représenté par nat, ou i est la variable n°i)*)

Definition convex_signature := {| operation := les_plus_p ; arity := (fun x => Binary)|}.

(*just some variables names to facilitate the definition of lhs and rhs*)
Variable (x : LS.Y).
Variable (y : LS.Y).
Variable (z : LS.Y).
Definition term  := Tree convex_signature Z.
Hypothesis different : x <> y.
Hypothesis different2 : y <> z.
Hypothesis different3 : z <> x.
Hypothesis order : ordre x y.
Hypothesis order2 : ordre y z.
Hypothesis order3 : ordre x z.

Definition plus' (p : Q') (x y : term) :=
@node convex_signature Z (plus_p p) (fun i => match i with 
                                        |Fst => x
                                        |Snd => y end).

Definition lhs_convexe (n : names_equalities) : term := match n with 
|idempotency p => plus' p (generator x) (generator x)  
|commutativity  p => plus' p (generator x) (generator y) 
|associativity p q  => plus' q (plus' p (generator x) (generator y)) (generator z)
|congruency p p' H => plus' p (generator x) (generator y)
end.


(*these are some definitions useful for the rhs equalities*)
Definition opposite (q : Q') : Q'.
split with (1 - q).
Proof.
assert (q < 1).
apply lt1.
apply Qlt_minus_iff in H.
auto.
destruct q as [q gt0 lt1].
simpl.
Search (_ + _ < _).
apply Qplus_lt_l with (- 1).
rewrite Qplus_opp_r.
rewrite Qplus_comm. 
rewrite (Qplus_assoc (-1) 1 (-q)).
rewrite (Qplus_comm (-1) 1).
rewrite Qplus_opp_r.
rewrite <- (Qplus_opp_r q) at 2.
apply Qplus_lt_l.
apply gt0.
Defined.

Print opposite.

Definition produit (p q : Q') : Q'.
Proof.
split with (p * q). 
rewrite <- Qmult_0_r with (x := p).
rewrite Qmult_lt_l.
apply gt0. apply gt0.
apply Qlt_trans with (y := p * 1).
rewrite Qmult_lt_l.
apply lt1. apply gt0.
rewrite Qmult_1_r.
apply lt1.
Defined.


Definition calcul_assoc (p q : Q') : Q'.
Proof.
split with (q * (1 - p) * (1 / (1 - p * q))).
rewrite  <- Qmult_0_l with (x := (1/(1 - p * q))).
apply Qmult_lt_r with (x:= 0) (y := q * (1 -p)).
unfold Qdiv.
rewrite Qmult_1_l.
apply (Qinv_lt_0_compat) with (a := (1 - p * q)).
apply (gt0 (opposite (produit p q))).
apply (gt0 (produit q (opposite p))).
rewrite Qmult_plus_distr_r with (x := q) (y := 1) (z := -p).
rewrite Qmult_1_r.
unfold Qdiv.
rewrite Qmult_1_l.
apply Qlt_shift_div_r with (a := q + q * - p) (b := (1 - p * q)) (c := 1).
apply (gt0 (opposite (produit p q ))).
rewrite Qmult_1_l.
rewrite Qmult_comm.
unfold Qminus.
assert (-(p * q) == -p * q).
unfold Qeq ; simpl. lia.
rewrite H.
apply Qplus_lt_l with (x := q) (y := 1) (z := - p * q).
apply lt1.
Defined.


Definition rhs_convexe (n : names_equalities) : term := match n with 
|idempotency p => generator x
|commutativity  p => plus' (opposite p) (generator y) (generator x)
|associativity p q  => plus' (produit p q) (generator x) (plus' (calcul_assoc p q) (generator y) (generator z)) 
|congruency p q H => plus' q (generator x) (generator y)
end.


(*rendre ça plus joli*) 
Definition convex_equalities: EqSignature convex_signature := 
{|equ := names_equalities ; X := Z ;  lhs := lhs_convexe ; rhs := rhs_convexe |}.

Definition convex_algebra := Algebra convex_signature convex_equalities.

(*so, a convex_algebra is now defined*) 


(*WORK IN PROGRESS*)
(* now we need to define D(X)*)


Definition indicatrice (x : Z) : (Z -> Q) := (fun y => match (LS.Y_eq_dec x y) with
|left _ => 1%Q
|right _ => 0%Q
end).

Definition le_plus_star (p : Q) (phi psi : Z -> Q): Z -> Q := 
fun x =>  p * phi (x) + (1 - p)* psi(x).

Fixpoint calcul (phi : Z -> Q) (l  : list Z) : Q := match l with 
|nil => 0%Q
|cons x q => Qplus (phi x) (calcul phi q)
end.

Record D_fin := 
{ phi :> Z -> Q ; 
  support : LS.ensemble_fini ; 
  null_outside:  forall (x : Z), ~(est_dans x support) -> phi x == 0%Q ; 
  O_inferior_1 : forall (x : Z), est_dans x support -> (Qlt 0 (phi x)) /\ phi x <= 1%Q ; 
  distribution : calcul phi support == 1%Q ;
}.

(*change the type and inferior_1 name*)

Lemma calcul_marche_bien  : forall (phi psi : Z -> Q) (l : list Z) (p : Q),  
calcul (le_plus_star p phi psi) l == p *(calcul phi l) + (1 - p) * (calcul psi l).
Proof.
intros.
induction l.
simpl.
unfold Qeq ; simpl ; lia.
simpl.
rewrite IHl.
unfold le_plus_star.
simpl.
unfold Qeq ; simpl ; lia.
Qed.


Lemma null_calcul_null (phi : Z -> Q) :
(forall x, phi x == 0 ) -> (forall l, calcul phi l == 0).
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
rewrite H.
unfold Qeq; simpl; lia.
Qed. 

Lemma calcul_union_simpl : forall (phi : D_fin) (l : list Z),
calcul phi (union (support phi) l) == calcul phi (support phi).
Proof.
Admitted.


Lemma calcul_union_simpl_2 : forall (phi : D_fin) (l : list Z), 
calcul phi (union  l (support phi)) == calcul phi (support phi).
Proof.
intros.
remember (support phi0).
generalize dependent l.
induction (ensemble e).
intros.
induction l.
simpl.
reflexivity.
intros.
simpl.
Admitted.

Lemma Qmult_le_compat_nonneg: forall x y z t : Q', 0 <= x <= y -> 0 <= z <= t -> x * z <= y * t.
Proof.
intros.
apply Qle_trans with (y := x0 * t).
apply Qmult_le_l with (z := x0).
apply gt0.
apply H0.
apply Qmult_le_r.
apply gt0.
apply H.
Qed.

Lemma useful_but_painful : forall p : Q, p * 1 + (1 - p) * 1 == 1.
Proof.
intros.
rewrite 2 Qmult_1_r .
rewrite (Qplus_comm 1 (-p)).
rewrite (Qplus_assoc p (-p) 1).
rewrite (Qplus_opp_r).
unfold Qeq; simpl; lia.
Qed.

Lemma second_useful : forall x y z : Q, x + y == z <-> x == z - y.
Proof.
intros.
split.
intros.
rewrite <- H.
unfold Qminus.
rewrite  <- Qplus_0_r with (x := x0) at 1.
assert (x0 + y0 +- y0 == x0 +(y0 +- y0)).
symmetry.
apply Qplus_assoc with (x := x0) (y:= y0) (z := - y0).
rewrite H0.
apply Qplus_inj_l with (z := x0) (x := 0) (y := y0 +- y0).
rewrite Qplus_opp_r with (q := y0).
reflexivity.
intro.
apply Qplus_inj_r with (z := -y0).
rewrite <- Qplus_0_r with (x := z0 + - y0).
assert (y0 +- y0 == 0).
apply Qplus_opp_r.
rewrite H.
unfold Qminus.
assert (z0 + - y0 + y0 + - y0  == z0 + - y0 + (y0 + - y0)).
rewrite <- Qplus_assoc with (x := z0 + - y0) (y := y0) (z := -y0).
reflexivity.
rewrite H1.
rewrite Qplus_inj_l with (z := z0 + - y0) (x := y0 +- y0) (y := 0).
rewrite H0.
reflexivity.
Qed. 

Lemma between0_1 : forall (phi : D_fin) (x : Z),
0 <= phi x <= 1.
Proof.
intros.
split.
destruct (LS.est_dans_dec x0 (support phi0)).
apply Qlt_le_weak.
apply O_inferior_1.
auto.
assert (phi0 x0 == 0).
apply null_outside.
auto.
rewrite H.
unfold Qle; simpl; lia.
destruct (LS.est_dans_dec x0 (support phi0)).
apply O_inferior_1.
auto.
assert (phi0 x0 == 0).
apply null_outside.
auto.
rewrite H.
unfold Qle; simpl; lia.
Qed.


(*rewrite better*) 
Definition  plus_p' (p : Q') (phi psi : D_fin) : D_fin.
Proof.
split with (le_plus_star p phi psi) (LS.union_finite (support phi) (support psi)).
intros.
unfold le_plus_star.
unfold union_finite.
assert ((~est_dans x0 (support phi)) /\ (~est_dans x0 (support psi))).
apply LS.transmission_not with (l := support phi) (l' := support psi) (a := x0).
auto.
destruct H0.
assert (phi x0 == 0%Q).
apply null_outside.
auto.
assert (psi x0 == 0).
apply null_outside.
auto.
rewrite H2.
rewrite H3.
assert (p * 0 == 0).
unfold Qeq.
simpl.
lia.
rewrite H4.
unfold Qeq.
simpl.
lia.
intros.
unfold le_plus_star.
simpl.
simpl in H.
assert (0 <= (phi x0) <= 1).
apply between0_1.
assert (0 <= (psi x0) <= 1).
apply between0_1.
split.
rewrite <- Qmult_0_r with (x := p).
rewrite <- Qplus_0_r  with (x := p * 0).
rewrite <- Qmult_0_r with (x := (1 - p)) at 2.
destruct (LS.est_dans_dec x0 (support phi)).
apply Qplus_lt_le_compat with (x := p * 0) (y := p * phi x0) (z := (1 - p) * 0) (t := (1 - p) * psi x0).
apply Qmult_lt_l.
apply gt0.
apply O_inferior_1 ; auto.
apply Qmult_le_l.
apply (gt0 (opposite p)).
apply H1.
assert (phi x0 == 0).
apply null_outside ; auto.
rewrite H2.
rewrite ? Qmult_0_r.
rewrite ? Qplus_0_l.
assert (est_dans x0 (support phi) \/ est_dans x0 (support psi)).
apply LS.union_preserves_both.
auto.
destruct H3.
exfalso.
apply n ; auto. 
rewrite <- Qmult_0_r with (x := (1 - p)).
rewrite Qmult_lt_l.
apply O_inferior_1.
auto.
apply (gt0 (opposite p)).
apply Qle_trans with (y := p * 1 + (1 - p) * 1 ).
apply Qplus_le_compat.
apply Qmult_le_l.
apply gt0.
apply H0.
apply Qmult_le_l.
apply (gt0 (opposite p)).
apply H1.
rewrite useful_but_painful.
unfold Qle; simpl; lia.
rewrite calcul_marche_bien.
rewrite  calcul_union_simpl with (l := support psi).
rewrite calcul_union_simpl_2 with (l := support phi).
rewrite ? distribution.
apply useful_but_painful.
Defined.

Lemma simplify_minus : forall x, 
-x == (-1) * x.
Proof.
intros.
rewrite <- Qmult_inj_l with (z := (-1)) (x := - x0) (y := -1 * x0).
assert (- 1 * - 1 ==1).
unfold Qeq; simpl; lia.
rewrite Qmult_assoc.
rewrite H.
rewrite Qmult_1_l.
destruct x0.
unfold Qmult.
simpl.
destruct (Qnum).
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
intro. 
inversion H.
Qed.

Lemma cancellation : forall (p : Q), 
1 - (1 - p) == p.
Proof.
intros.
unfold Qminus.
rewrite  simplify_minus.
rewrite Qmult_plus_distr_r.
rewrite Qplus_assoc.
rewrite <- ? simplify_minus.
rewrite ? Qplus_opp_r.
rewrite Qplus_0_l.
rewrite Qopp_opp.
reflexivity.
Qed.


Definition D: OpAlgebra (convex_signature) :=
{|carrier := D_fin ; 
op := (fun (o : operation convex_signature) => match o with 
                                                 |plus_p p => (fun args => plus_p' p (args Fst) (args Snd)
                                                  )end)|}.


Definition egalite_extentionnelle (phi psi : D_fin) : Prop :=
forall (x : Z), phi x == psi x.

Check egalite_extentionnelle.

Definition EqD : CongRelation D.
Proof.
split with (egalite_extentionnelle).
intros.
remember x0 as f.
unfold egalite_extentionnelle.
intro.
reflexivity.
intros.
remember x0 as f.
unfold egalite_extentionnelle.
intros.
unfold egalite_extentionnelle in H.
rewrite H.
reflexivity.
intro ; intro.
unfold egalite_extentionnelle.
intros.
remember x0 as f ; remember y0 as g ; remember z0 as h.
rewrite <- H0. apply H.
unfold egalite_extentionnelle.
intros.
simpl.
destruct o.
simpl in H. 
unfold plus_p'.
simpl.
unfold le_plus_star.
rewrite ? H.
reflexivity.
Defined.


Definition D_X : convex_algebra.
Proof.
split with D EqD.
intros.
destruct e.
intros.
simpl.
unfold EqD.
unfold egalite_extentionnelle.
intros.
unfold plus_p'.
simpl.
unfold le_plus_star.
simpl.
rewrite <- (Qmult_1_l (val x x0)) at 3. 
rewrite <-  (useful_but_painful q) at 2 . 
rewrite <-  Qmult_plus_distr_l.
rewrite 2 Qmult_1_r.
reflexivity.
unfold EqD.
unfold egalite_extentionnelle.
intros.
unfold plus_p'.
simpl.
intros.
unfold le_plus_star.
unfold opposite.
rewrite (Qplus_comm (q * val x x0) ((1 - q) * val y x0)).
rewrite Qplus_inj_l.
destruct (Qeq_dec (val x x0) 0).
rewrite q0.
rewrite ? Qmult_0_r.
reflexivity.
rewrite Qmult_inj_r.
rewrite cancellation.
reflexivity.
auto.
unfold EqD.
unfold egalite_extentionnelle.
intros.
unfold plus_p'.
simpl.
intros.
unfold le_plus_star.
simpl.
rewrite ? Qmult_plus_distr_r.
rewrite ? Qmult_assoc.
revert q0.
revert q.
intros q0.
intros q1.
rewrite Qmult_comm with (x := q1) (y := q0).
rewrite <- Qplus_assoc with (x := q0 * q1 * val x x0).
rewrite Qplus_inj_l with (z := q0 * q1 * val x x0) (x := q1 * (1 - q0) * val y x0 + (1 - q1) * val z x0) 
(y := ((1 - q0 * q1) * q1 * (1 - q0) * (1 / (1 - q0 * q1)) * val y x0 +
(1 - q0 * q1) * (1 - q1 * (1 - q0) * (1 / (1 - q0 * q1))) * val z x0)).
rewrite Qmult_comm with (x := 1 - q0 * q1) (y := q1).
unfold Qdiv.
rewrite ? Qmult_1_l.
assert (q1 * (1 - q0) * val y x0 == q1 * (1 - q1 * q0) * (1 - q0) * /(1 - q0 * q1) * val y x0).
destruct (Qeq_dec (val y x0) 0). 
rewrite ? q.
rewrite ? Qmult_0_r.
reflexivity.
rewrite Qmult_inj_r with (z := val y x0).
rewrite <- ? Qmult_assoc .
rewrite Qmult_inj_l with (z := q1).
rewrite Qmult_assoc.
rewrite Qmult_comm with (y := 1 - q0) (x := 1 - q1 * q0).
rewrite <- Qmult_assoc. 
rewrite <-  Qmult_1_r with (n := (1 - q0)) at 1.
rewrite Qmult_inj_l with (z := (1 - q0)).
rewrite Qmult_comm with (x := q0).
rewrite Qmult_inv_r.
reflexivity.
intro.
assert ( ~0 == 1 - q1 * q0).
apply (Qlt_not_eq).
apply (gt0 (opposite (produit q1 q0))).
rewrite H in H0.
apply H0; reflexivity.
intro ; assert(~0 == 1 - q0).  apply Qlt_not_eq.
apply (gt0 (opposite q0)).
rewrite H in H0 ; apply H0 ; reflexivity.
intro ; assert(~0 == q1). apply Qlt_not_eq.
apply gt0.
rewrite H in H0 ; apply H0 ; reflexivity.
auto.
rewrite H.
rewrite Qmult_comm with (x := q1) (y := q0).
rewrite Qplus_inj_l with (z :=  q1 * (1 - q0 * q1) * (1 - q0) * / (1 - q0 * q1) * val y x0) (x := ((1 - q1) * val z x0))
(y := ((1 - q0 * q1) * (1 - q1 * (1 - q0) * / (1 - q0 * q1)) * val z x0)).
destruct (Qeq_dec (val z x0) 0).
rewrite q.
rewrite ? Qmult_0_r.
reflexivity.
rewrite Qmult_inj_r.
unfold Qminus.
rewrite Qmult_plus_distr_r.
rewrite Qmult_plus_distr_r.
rewrite ? Qmult_1_r.
rewrite simplify_minus with (x := ((q1 + q1 * - q0) * / (1 + - (q0 * q1)))).
rewrite Qmult_assoc.
rewrite Qmult_comm with (x := (1 + - (q0 * q1))) (y :=  -1).
rewrite <- Qmult_assoc.
rewrite Qmult_assoc with (n := (1 + - (q0 * q1))) (m :=(q1 + q1 * - q0)) 
(p := / (1 + - (q0 * q1))).
rewrite Qmult_comm with (x := (1 + - (q0 * q1))) (y :=(q1 + q1 * - q0)).
rewrite <- ? Qmult_assoc.
rewrite Qmult_inv_r.
rewrite Qmult_1_r.
rewrite <- Qplus_assoc.
rewrite Qplus_inj_l with (z := 1) .
rewrite 2 simplify_minus.
rewrite <- Qmult_plus_distr_r with (x := -1).
rewrite Qmult_inj_l.
rewrite Qplus_assoc.
rewrite Qplus_comm with (x := q0 * q1).
rewrite <-  Qplus_assoc.
rewrite  <- Qplus_0_r at 1.
rewrite Qplus_inj_l.
rewrite <- Qplus_opp_r with (q := q0 * q1).
rewrite Qplus_inj_l.
rewrite ? simplify_minus.
rewrite ? Qmult_assoc.
rewrite ? Qmult_comm with (x := q1).
rewrite <- ?Qmult_assoc.
rewrite Qmult_inj_l.
rewrite Qmult_comm.
reflexivity.
intro ; inversion H0.
intro ; inversion H0.
intro.
symmetry in H0.
assert (~0 == 1 + - (q0 * q1)).
apply Qlt_not_eq.
apply (gt0 (opposite (produit q0 q1))).
rewrite H0 in H1.
apply H1 ; reflexivity.
auto.
unfold EqD.
simpl.
unfold egalite_extentionnelle.
intros.
simpl.
unfold le_plus_star.
simpl.
rewrite ? q.
reflexivity.
Defined.

