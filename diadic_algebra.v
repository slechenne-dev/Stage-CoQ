
(*we now move to Diadic Algebra*)

Require Import QArith.
Require Import QArith_base.
Require Import Lia.
Require Import LS.
Require Import universal_algebra_generality.
Require Import PArith.BinPos.
Check Y.
Check ordre.
Check Qden.


(*definition of D*) 


Lemma test_1 : forall n m, Pos.mul (Pos.pow 2%positive n) (Pos.pow 2%positive m) = 
Pos.pow  2%positive (Pos.add n m ).
Proof.
intros.
generalize dependent n.
apply Pos.peano_rect.
generalize dependent m.
apply Pos.peano_rect.
simpl.
reflexivity.
intros.
rewrite Pos.pow_succ_r.
rewrite Pos.mul_comm.
rewrite <- Pos.mul_assoc.
rewrite Pos.mul_comm in H.
rewrite H.
rewrite Pos.add_1_l.
rewrite <- Pos.pow_succ_r.
rewrite <- Pos.add_1_l.
reflexivity.
intros.
rewrite Pos.pow_succ_r.
rewrite <- Pos.mul_assoc.
rewrite H.
rewrite <- Pos.pow_succ_r.
rewrite Pos.add_succ_l.
reflexivity.
Qed.

Eval compute in (xO xH).
Fixpoint power_2 (n : nat) : positive := match n with 
|0%nat => xH
|S (p) => xO (power_2 p)
end.

Eval compute in (power_2 2).



Record Dyadic : Type :=
{rationnel :> Q ; 
pow_2 : exists n, Qden rationnel = (power_2 n)}.

Record Dyadic_0_1 : Type :=
{dyadic :> Dyadic ; 
gt0 : Qlt 0 dyadic ;
lt1 : Qle dyadic 1 ;}.



(*introducing our operations *)
Inductive le_plus_rond : Type := 
|plus_rond.

(*the arity*)
Inductive Binary : Type := Fst | Snd.

(*introducing the three equalities*)
Inductive names_equalities : Type:=
|idempotency :  names_equalities
|commutativity : names_equalities
|associativity:  names_equalities.


Check universal_algebra_generality.operation.
Check operation.

(*l'ensemble des variables est représenté par nat, ou i est la variable n°i)*)

Definition dyadic_signature := {| operation := le_plus_rond; arity := (fun x => Binary)|}.

(*just some variables names to facilitate the definition of lhs and rhs*)
Variable (x : Y).
Variable (y : Y).
Variable (z : Y).
Variable (t : Y).

Definition term  := Tree dyadic_signature Y.

Definition plus' (x y : term) :=
@node dyadic_signature Y (plus_rond) (fun i => match i with 
                                        |Fst => x
                                        |Snd => y end).

Definition lhs_dyadic (n : names_equalities) : term := match n with 
|idempotency => plus' (generator x) (generator x)  
|commutativity => plus' (generator x) (generator y) 
|associativity => plus' (plus' (generator x) (generator y)) (plus' (generator z) (generator t))
end.

Definition rhs_dyadic (n : names_equalities) : term := match n with 
|idempotency => generator x
|commutativity => plus' (generator y) (generator x)
|associativity => plus' (plus' (generator x) (generator z)) (plus' (generator y) (generator t))
end.


(*rendre ça plus joli*) 
Definition dyadic_equalities: EqSignature dyadic_signature := 
{|equ := names_equalities ; X := Y ;  lhs := lhs_dyadic ; rhs := rhs_dyadic |}.

Definition dyadic_algebra :Type := Algebra dyadic_signature dyadic_equalities.

Lemma pow_morph : forall (n m: nat), Pos.mul (power_2 n) (power_2 m) = power_2 (n + m).
Proof.
intros.
induction n.
induction m.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Definition plus_dyadic (p q : Dyadic) : Dyadic.
Proof.
split with (p + q).
destruct p ; destruct q.
simpl.
destruct pow_3; destruct pow_4.
rewrite H.
rewrite H0.
split with (Nat.add x0 x1).
rewrite pow_morph.
reflexivity.
Defined.

Definition produit_dyadic (p q : Dyadic) : Dyadic.
Proof.
split with (p * q).
destruct p ; destruct q.
destruct pow_3 ; destruct pow_4.
simpl.
rewrite e ; rewrite e0.
split with (Nat.add x0 x1).
rewrite pow_morph.
reflexivity.
Defined.

Definition un_demi : Dyadic.
Proof.
split with (1/2).
simpl.
split with 1%nat.
simpl.
reflexivity.
Defined.

Definition zero : Dyadic.
Proof.
split with 0.
simpl.
split with 0%nat.
simpl.
reflexivity.
Defined.

Definition un : Dyadic.
Proof.
split with 1.
split with 0%nat.
simpl.
reflexivity.
Defined.


Definition indicatrice (x : Y) : (Y -> Dyadic) := (fun y => match (Y_eq_dec x y) with
|left _ => zero
|right _ => un
end).

Definition plus_rond_star (phi psi : Y -> Dyadic): Y -> Dyadic := 
fun x => plus_dyadic (produit_dyadic un_demi (phi x)) (produit_dyadic un_demi (psi x)). 

Fixpoint calcul (phi : Y -> Dyadic) (l  : list Y) : Dyadic := match l with 
|nil => zero
|cons x q => plus_dyadic (phi x) (calcul phi q)
end.

Record Dy_fin := 
{ phi :> Y -> Dyadic ; 
  support : LS.ensemble_fini ; 
  null_outside:  forall (x : Y), ~(est_dans x support) -> phi x == 0%Q ; 
  O_inferior_1 : forall (x : Y), est_dans x support -> (Qlt 0 (phi x)) /\ phi x <= 1%Q ; 
  distribution : calcul phi support == 1%Q ;
}.

Lemma calcul_marche_bien  : forall (phi psi : Y -> Dyadic) (l : list Y),  
calcul (plus_rond_star phi psi) l ==
plus_dyadic (produit_dyadic un_demi (calcul phi l)) (produit_dyadic un_demi (calcul psi l)).
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
unfold produit_dyadic.
simpl.
rewrite ? Qplus_assoc.
Search (_ * ( _ + _)).
rewrite ? Qmult_plus_distr_r.
Search ( _ + _ == _ + _ ).
rewrite <- ? Qplus_assoc.
rewrite Qplus_inj_l with (z := 1/2 * phi0 a).
rewrite <- ? Qplus_assoc.
rewrite Qplus_comm with (x := 1 / 2 * calcul phi0 l ) (y := (1 / 2 * psi a + 1 / 2 * calcul psi l)).
rewrite <- ? Qplus_assoc.
rewrite Qplus_inj_l.
rewrite Qplus_comm.
reflexivity.
Qed.

Lemma null_calcul_null (phi : Y -> Dyadic) :
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

Lemma calcul_union_simpl : forall (phi : Dy_fin) (l : list Y),
calcul phi (union (support phi) l) == calcul phi (support phi).
Proof.
Admitted.


Lemma calcul_union_simpl_2 : forall (phi : Dy_fin) (l : list Y), 
calcul phi (union  l (support phi)) == calcul phi (support phi).
Proof.
Admitted.

Lemma Qmult_le_compat_nonneg: forall x y z t : Q, 0 <= x <= y -> 0 <= z <= t -> x * z <= y * t.
Proof.
Admitted.

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

Lemma between0_1 : forall (phi : Dy_fin) (x : Y),
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


Definition  plus_rond' (phi psi : Dy_fin) : Dy_fin.
Proof.
split with (plus_rond_star phi psi) (LS.union_finite (support phi) (support psi)).
intros.
unfold plus_rond_star.
unfold union_finite in H.
simpl in H.
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
unfold produit_dyadic.
simpl.
rewrite H2.
rewrite H3.
rewrite ? Qmult_0_r.
rewrite Qplus_0_r.
reflexivity.
intros.
unfold plus_rond_star.
simpl.
simpl in H.
assert (0 <= (phi x0) <= 1).
apply between0_1.
assert (0 <= (psi x0) <= 1).
apply between0_1.
split.
rewrite <- Qmult_0_r with (x := 1/2).
rewrite <- Qplus_0_r  with (x := 1/2 * 0).
rewrite <- Qmult_0_r with (x := 1/2) at 2.
destruct (LS.est_dans_dec x0 (support phi)).
apply Qplus_lt_le_compat with (x := 1/2 * 0) (y := 1/2 * phi x0) (z := 1/2 * 0) (t := 1/2 * psi x0).
apply Qmult_lt_l.
unfold Qgt ; simpl; lia.
apply O_inferior_1 ; auto.
apply Qmult_le_l.
unfold Qgt ; simpl; lia.
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
rewrite <- Qmult_0_r with (x := 1/2).
rewrite Qmult_lt_l.
apply O_inferior_1.
auto.
unfold Qlt; simpl; lia.
apply Qle_trans with (y := 1/2 * 1 + 1/2 * 1 ).
apply Qplus_le_compat.
apply Qmult_le_l.
unfold Qlt ; simpl; lia.
apply H0.
apply Qmult_le_l.
unfold Qlt; simpl;  lia.
apply H1.
rewrite useful_but_painful.
unfold Qle; simpl; lia.
rewrite calcul_marche_bien.
unfold produit_dyadic; simpl.
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


Definition Dy: OpAlgebra (dyadic_signature) :=
{|carrier := Dy_fin ; 
op := (fun (o : operation dyadic_signature) => match o with 
                                                 |plus_rond => (fun args => plus_rond' (args Fst) (args Snd)
                                                  )end)|}.


Definition egalite_extentionnelle (phi psi : Dy_fin) : Prop :=
forall (x : Y), phi x == psi x.

Check egalite_extentionnelle.

Definition EqD : CongRelation Dy.
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
unfold plus_rond'.
simpl.
rewrite ? H.
reflexivity.
Defined.

Definition Dy_X : dyadic_algebra.
Proof.
split with Dy EqD.
intros.
destruct e.
intros.
simpl.
unfold EqD.
unfold egalite_extentionnelle.
intros.
unfold plus_rond'.
simpl.
Search ((_ + _ ) * _).
rewrite <- Qmult_plus_distr_l.
rewrite <-  Qmult_1_l  with (n := val x x0) at 2.
destruct (Qeq_dec (val x x0) 0%Q).
rewrite ? q.
unfold Qeq; simpl; lia.
rewrite Qmult_inj_r with (z := val x x0).
unfold Qeq; simpl; lia.
auto.
unfold EqD.
simpl.
unfold egalite_extentionnelle.
intros.
unfold plus_rond'.
simpl.
rewrite Qplus_comm.
reflexivity.
intros.
unfold EqD.
unfold egalite_extentionnelle.
intros.
unfold plus_rond'.
simpl.
intros.
rewrite ?Qmult_plus_distr_r.
rewrite ?Qmult_assoc.
rewrite <- ?Qplus_assoc.
rewrite Qplus_inj_l.
rewrite Qplus_comm.
rewrite <- ? Qplus_assoc.
rewrite Qplus_inj_l.
rewrite Qplus_comm.
reflexivity.
Defined.
