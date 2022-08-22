(* An initial attempt at universal algebra in Coq.
   Author: Andrej Bauer <Andrej.Bauer@andrej.com>

   If someone knows of a less painful way of doing this, please let me know.

   We would like to define the notion of an algebra with given operations satisfying given
   equations. For example, a group has of three operations (unit, multiplication, inverse)
   and five equations (associativity, unit left, unit right, inverse left, inverse right).
*)

(* We start by defining operation signatures. These describe the operations
   of an algebra.

   The main trick is that the arity of an operation is *not* a number
   but rather a type. For instance, the arity of a binary operation
   is a type with two elements. (And nothing prevents us from having
   an infinite type as arity.)
 *)

(*the following libraries are important to manipualte algebras more easily in our proofs, and allow rewrite tactics*)
Require Import Setoid.
Require Import Morphisms.


(*the signature is a set of operation names with an arity function*)
Record OpSignature :=
  {
    operation : Type ; (* (Names of) operations. *)
    arity : operation -> Type (* Each operation has an arity. *)
  }.

Arguments arity {_} _.

(* We shall consider algebras with given operations, but without equations.
   We call these "operation algebras". *)

Record OpAlgebra (S : OpSignature) :=
  {
    carrier :> Type ;
    op : forall o : operation S, (arity o -> carrier) -> carrier;
    (* no equations *)
  }.


Arguments op {_} _ _ _.

Check op.

(*then we define inductively the type of terms : it takes on argument an OpSignature and a type for the base case (infered_generator) *)

Inductive Tree (S : OpSignature) (X : Type) : Type :=
  | generator : X -> Tree S X
  | node : forall (o : operation S), (arity o -> Tree S X) -> Tree S X.

Arguments generator {_} {_} _.
Arguments node {_} {_} _.

 
(* Now given some operations, described by an operation signature S,
   we can define an equation signature which specifies some equations.       
*)
Record EqSignature (S : OpSignature) :=
  { 
  equ :> Type ; (* (names of) equations *)
  X : Type ;

    (* Next we specify the equations. Note that they are polymorphic in the underlying algebra. *)
  lhs : equ -> Tree S X ; (* left-hand sides *)
  rhs : equ -> Tree S X ; (* right-hand sides *)
  }.

 
Arguments lhs {_} _ _.
Arguments rhs {_} _ _.

(* We define how to interpret trees as elements of A *)
Fixpoint inter {S : OpSignature} {A : OpAlgebra S} {X : Type} (val : X -> A) (t : Tree S X) :=
  match t with
  | generator x => val x
  | node o args => op A o (fun x => inter val (args x))
  end.

(* We define the congruence relation used for the algebras *)
Record CongRelation {S : OpSignature} (A : OpAlgebra S) :=
  {
    cong_rel :> A -> A -> Prop; (* the equality relation *)
    cong_rel_refl : forall x, cong_rel x x;
    cong_rel_sym : forall x y, cong_rel x y -> cong_rel y x;
    cong_rel_trans : forall x y z, cong_rel x y -> cong_rel y z -> cong_rel x z;
    cong_rel_cong : forall (o : operation S) (args1 args2 : arity o -> A), (forall (n : arity o), cong_rel (args1 n) (args2 n)) -> cong_rel (op A o args1) (op A o args2);
}.


(* We can now define what it means to have an algebra for a signature S satisfying
   equations E. *)
Record Algebra (S : OpSignature) (E : EqSignature S) :=
  {
  M :> OpAlgebra S ;
  equal : CongRelation M;
  equations : forall (e : E) (val : X S E -> M), equal (inter val (lhs E e)) (inter val (rhs E e)) 
  }.


(* We define the type of homomorphism between algebras A and B. *)

Record Hom {S : OpSignature} {E : EqSignature S} (A : Algebra S E) (B : Algebra S E)  :=
  { 
    map :> A -> B ; (* The underlying map *)
    (* The underlying map commutes with operations: *)
    op_respect : forall (x y : A), (equal S E A) x y -> (equal S E B) (map x) (map y);  
    op_commute : forall (o : operation S) (args : arity o -> A),
                   (equal S E B) (map (op A o args)) (op B o (fun x => map (args x)))
  }.

Definition isomorphic {S : OpSignature} {E : EqSignature S} (A B : Algebra S E) :=
exists (f: Hom A B) (g : Hom B A), (forall x : A, (equal S E A) (g (f x))  x) /\ (forall x : B, (equal S E B) (f (g x)) x).


(*finally, a useful lemma*)
Lemma equal_setoid {S : OpSignature} {E : EqSignature S} (A : Algebra S E) : Setoid_Theory A (equal S E A).
Proof.
unfold Setoid_Theory.
split.
unfold Reflexive.
apply (cong_rel_refl (M S E A) (equal S E A)).
unfold Symmetric.
apply (cong_rel_sym (M S E A) (equal S E A)).
unfold Transitive.
apply (cong_rel_trans (M S E A) (equal S E A)).
Qed.


Section free_is_unique.
(* in this section we are going to define what is freeness and to proove that 2 free object over the same type are isomorphic*)

(*the commuting property*)


(*we then say that an algebra A is free over (X, q) relatively to an algebra B and a function f iff there is only one f_tilde 
in HOM(A, B) such that it makes the diagramm commute :

           f
       X ----->B
       |      /
       |     /
      q|    /f_tilde
       |   /
       |  /
       | /
       A 

*)

Definition commute {S : OpSignature} {E : EqSignature S} (A B : Algebra S E) (X : Type) (q : X -> A) (f : X -> B) (f_tilde : Hom A B)  :=
forall (x : X), (equal S E B) (((map A B) f_tilde) (q x)) (f x).

Record free_relative {S : OpSignature} {E : EqSignature S} (A B : Algebra S E) (X : Type) (q : X -> A) (f : X -> B) :=
{ f_tilde : Hom A B ; 
  it_commutes : commute A B X q f f_tilde ; 
  uniqueness  : forall (g : Hom A B), commute A B X q f g /\ commute A B X q f f_tilde -> (forall (x  : A), (equal S E B) (f_tilde x) (g x)) }.

(*then, we define free : an Algebra is free over (X, q) if for all algebra B and function f X -> B, we have the relative freeness*)
Definition free {S : OpSignature} {E : EqSignature S} (A: Algebra S E) (X : Type) (q : X -> A) :=
 forall (B : Algebra S E) (f : X -> B), free_relative A B X q f. 


Definition identite {S : OpSignature} {E : EqSignature S} (A : Algebra S E) : Hom A A.
Proof.
split with (fun (x : A) => x).
intros.
auto.
intros.
assert (args = fun x => args x).
auto.
rewrite H.
apply (cong_rel_cong A).
intros n ; apply (cong_rel_refl A).
Defined.

Definition composition {S : OpSignature} {E : EqSignature S} (A B C: Algebra S E) (f : Hom A B) (g : Hom B C) : Hom A C.
Proof.
split with (fun x => g (f x)).
intros.
apply ((op_respect B C) g).
apply ((op_respect A B) f).
auto.
intros. 
apply (cong_rel_trans) with (y := g (op B o (fun x => f (args x)))).
apply ((op_respect B C) g).
apply ((op_commute A B) f).
apply (op_commute).
Defined. 

(*rewrite using specialize tactic*)

Lemma uniqueness_of_free (X : Type) {S : OpSignature} {E : EqSignature S} (A B : Algebra S E) (q : X -> A) (q' : X -> B) :
free A X q -> free B X q' -> isomorphic A B.
intros.
unfold isomorphic.
assert (free_relative A B X q q').
apply X0.
assert (free_relative B A X q' q).
apply X1.
exists ((f_tilde A B X q q') X2).
exists ((f_tilde B A X q' q) X3).
remember ((f_tilde A B X q q') X2) as f_hom.
remember ((f_tilde B A X q' q) X3) as g_hom.
split.
+
intros.
assert (free_relative A A X q q).
apply X0.
assert ((forall (x  : A), (equal S E A) ((f_tilde A A X q q X4) x) (identite A x))).
apply (uniqueness A A X q q X4).
split.
unfold commute.
intros.
simpl.
apply (cong_rel_refl A).
apply (it_commutes A A X q q X4).
assert (forall (x : A), (equal S E A) ((f_tilde A A X q q X4) x) ((((composition A B A) f_hom g_hom)) x)).
apply (uniqueness A A X q q X4).
split.
unfold commute.
intros.
assert (commute A B X q q' f_hom).
rewrite Heqf_hom.
apply ((it_commutes A B X q q') X2).
unfold commute in H0.
assert (commute B A X q' q g_hom).
rewrite Heqg_hom.
apply ((it_commutes B A X q' q) X3).
unfold commute in H1.
assert (forall x0, (equal S E A) (g_hom (f_hom (q x0))) (g_hom (q' x0))).
intros.
apply (op_respect).
auto.
simpl.
apply (cong_rel_trans A) with (y := g_hom (q' x0)).
auto.
auto.
apply (it_commutes).
apply (cong_rel_trans A) with (y := f_tilde A A X q q X4 x).
apply (cong_rel_sym A).
simpl in H0.
auto.
simpl in H.
auto.
+
intros.
assert (free_relative B B X q' q').
apply X1.
assert ((forall (x  : B), (equal S E B) ((f_tilde B B X q' q' X4) x) (identite B x))).
apply (uniqueness B B X q' q' X4).
split.
unfold commute.
intros.
simpl.
apply (cong_rel_refl B).
apply (it_commutes B B X q' q' X4).
assert (forall (x : B), (equal S E B) ((f_tilde B B X q' q' X4) x) ((((composition B A B) g_hom f_hom)) x)).
apply (uniqueness B B X q' q' X4).
split.
unfold commute.
intros.
assert (commute B A X q' q g_hom).
rewrite Heqg_hom.
apply ((it_commutes B A X q' q) X3).
unfold commute in H0.
assert (commute A B X q q' f_hom).
rewrite Heqf_hom.
apply ((it_commutes A B X q q') X2).
unfold commute in H1.
assert (forall x0, (equal S E B) (f_hom (g_hom (q' x0))) (f_hom (q x0))).
intros.
apply (op_respect).
auto.
simpl.
apply (cong_rel_trans B) with (y := f_hom (q x0)).
auto.
auto.
apply (it_commutes).
apply (cong_rel_trans B) with (y := f_tilde B B X q' q' X4 x).
apply (cong_rel_sym B).
simpl in H0.
auto.
simpl in H.
auto.
Qed.
End free_is_unique.


(*this section is about the definition and properties of the term algebra*)
Section TermAlgebra_definition.
(*we contextualise the object in this section : to use the definitions here outside of this section, 
we will need to provie an OpSignature S and an E an EqSignature over S**) 
Context (S : OpSignature).
Context (E : EqSignature S).
Check generator.
Definition infered_generator:= X S E.
Check infered_generator.


(*propagation of the substition in a tree : it is to use the substition rule in a tree*)
Fixpoint application_subst (T : Tree S infered_generator) (theta : infered_generator -> Tree S infered_generator) : Tree S infered_generator :=
match T with
|generator x => theta x
|node o args => node o (fun x => 
 application_subst (args x) (theta))
end.

(*the A |- p = q relation : this will be the equality (i.e the CongRelation here) over the terms
(i.e trees) here, and this will define a setoid, as we will proove it later *)

(*changer le type de cong relation de type to prop*)

Inductive quotient_relation : Tree S infered_generator -> Tree S infered_generator -> Prop :=
|cas_base : forall (e : E), quotient_relation (lhs E e) (rhs E e)
|cas_refl : forall (T : Tree S infered_generator), quotient_relation T T
|cas_sym : forall (T T': Tree S infered_generator), quotient_relation T' T -> quotient_relation T T'
|cas_trans : forall (T T' T'' : Tree S infered_generator), quotient_relation T T' -> quotient_relation T' T'' -> quotient_relation T T''
|cas_passage_contexte : forall (op : operation S) (args args' : arity op -> Tree S infered_generator),
(forall (n : arity op), quotient_relation (args n) (args' n)) -> quotient_relation (node op (fun i => args i)) (node op (fun i => args' i))
|cas_subst : forall (T T' : Tree S infered_generator ) (theta : infered_generator -> Tree S infered_generator), 
quotient_relation T T' -> quotient_relation (application_subst T theta) (application_subst T' theta). 



(*we are going to declare the type of trees with quotient relation as a setoid. We need to provide a proof 
that quotient_relation is indeed an equivalence relation *)
Lemma tree_setoid : Setoid_Theory (Tree S infered_generator ) quotient_relation.
Proof.
unfold Setoid_Theory.
split.
unfold Reflexive.
apply cas_refl.
unfold Symmetric.
intros.
apply cas_sym.
exact H.
unfold Transitive.
intros.
apply cas_trans with (T := x) (T' := y) (T'' := z).
auto. auto.
Qed.

Add Setoid (Tree S infered_generator ) quotient_relation tree_setoid as setoid_term_algebra.

(*then, the term algebra is simply the OpAlgebra with carrier the type of trees and the interpretation of an 
operation is the associated node*)


Definition Term_algebra : OpAlgebra S :=
{|carrier := Tree S infered_generator  ; 
op := (fun (o : operation S) => (fun (args : arity o -> Tree S infered_generator ) => node o args))|}.

(*we then need, in order to build an algebra, to define a CongRelation over the Term_algebra. We are going to use quotient_relation *)

Definition eqtree : CongRelation Term_algebra.
split with (quotient_relation).
apply cas_refl.
intros ;  rewrite H ; apply cas_refl.
intros. rewrite H. exact H0.
intros. apply cas_passage_contexte with (op := o) (args := args1) (args' := args2).
auto.
Defined.

(*We need this lemma, it will maybe be redone in the future, but as for now, I will keep it :
an amelioration would be to define substition directly by using inter, but it makes things less clear thatn defining 
properly substition and then showging that indeed it is the same thing*)

Lemma egalité_utile : forall (T : Tree S infered_generator ) (theta : infered_generator -> Tree S infered_generator ), 
quotient_relation (application_subst T theta) (inter (A := Term_algebra) theta T).
Proof.
intros.
induction T.
simpl ; reflexivity.
simpl.
apply cas_passage_contexte.
exact H.
Qed.

(*now, lets show that the term algebra, with the congrelation eqtree (built over quotient_relation) is 
an algebra of the equationnal theory E*)

Definition Term_algebra_model : Algebra S E.
split with Term_algebra eqtree.
intros.
simpl.
rewrite <- ? egalité_utile.
apply cas_subst.
apply cas_base.
Defined.


(*indeed, the term algebra is a model of what it is supposed to represent*)


(*now let's show that the term algebra is free *)

Context  (A : Algebra S E).
Context (f : infered_generator -> A).

(*To manipulate more easily the definitions, we decalre A equal S E A as a setoid*)
Check cong_rel_refl.


Add Setoid A (equal S E A) (equal_setoid A) as A_is_setoid.


(*what we want is a function q (that does not depend of f) called the free map and 
an unique homomorphism f_tilde that makes this diagramm commute :


                     f  
infered_generator ------> A
       |                 /
       |                /
      q|               /f_tilde
       |              /
       |             /
       |            /
      term_algebra 
                  *)

(*we define q*)
Definition q (x : infered_generator) : Term_algebra := 
generator x.

(*we define now the function that is an homomorphism from term_algebra to A by induction over the terms*)

Fixpoint f_tilde_term (t : Term_algebra) : A := match t with 
|generator x => f x
|node operation args => ((op A) operation) (fun x => f_tilde_term (args x))
end.

Lemma lemme_utile_2 : forall (x : Term_algebra),  (equal S E A) (f_tilde_term x) (inter f x).
Proof.
intros.
induction x.
simpl.
reflexivity.
simpl.
apply (cong_rel_cong A).
intros.
apply H.
Qed.



Lemma is_the_same : forall (T : Term_algebra) (f : infered_generator -> A) (theta : infered_generator -> Tree S infered_generator), 
equal S E A (inter f (application_subst T theta)) (inter (fun x => inter f (theta x)) T).
Proof.
intros.
induction T.
simpl.
reflexivity.
intros.
simpl.
apply (cong_rel_cong).
exact H.
Qed.

Lemma equal_is_equal : forall (x y : Term_algebra)(f : infered_generator -> A), 
quotient_relation x y -> (equal S E A) (inter f x) (inter f y).
Proof.
intros.
generalize dependent f0.
induction H.
intros.
apply (equations S E A) with (e := e) (val := f0).
intros.
apply cong_rel_refl.
intros.
apply cong_rel_sym.
auto.
intros.
apply cong_rel_trans with (y := inter f0 T').
auto.
auto.
intros. 
simpl.
apply (cong_rel_cong).
intros.
auto.
intros.
rewrite 2 is_the_same.
apply IHquotient_relation with (f0 := fun x => inter f0 (theta x)).
Qed.


Definition is_an_homomorphism : Hom (Term_algebra_model) A.
Proof.
exists f_tilde_term.
intros. 
+
rewrite ? lemme_utile_2.
apply equal_is_equal.
auto.
+
intros.
simpl.
apply cong_rel_cong.
intros.
apply reflexivity.
Defined.


Lemma makes_the_diagramm_commute : forall (x : infered_generator ), (equal S E A) (f x) (f_tilde_term (q x)).
Proof.
intros.
simpl.
reflexivity.
Qed.




Lemma unicité : forall (f' g' : Hom Term_algebra_model A), 
(forall (x : infered_generator ), (equal S E A) (f' (generator x)) (g' (generator x)))-> (forall (t : Term_algebra), (equal S E A) (f' t) (g' t)).
Proof.
intros.
induction t.
auto.
assert ((equal S E A) (f' (node o t)) (op A o (fun x => f' (t x)))).
apply (op_commute Term_algebra_model A). 
assert ((equal S E A) (g' (node o t)) (op A o (fun x => g' (t x)))).
apply (op_commute Term_algebra_model A ).
apply (cong_rel_trans A (equal S E  A)) with (x :=  (f' (node o t))) (y := (op A o (fun x : arity o => f' (t x)))) (z := (g' (node o t))).
auto.
apply (cong_rel_trans A (equal S E A)) with (x := (op A o (fun x : arity o => f' (t x)))) (y := (op A o (fun x : arity o => g' (t x)))) (z := (g' (node o t))).
apply (cong_rel_cong A (equal S E A)).
auto.
symmetry.
auto.
Qed.

End TermAlgebra_definition.

Section TermALgebra_is_free.
Context (S : OpSignature).
Context (E : EqSignature S).
Check Term_algebra.
Check f_tilde_term.


Definition is_free_term_algebra : free (Term_algebra_model S E) (X S E) (fun x => generator x).
Proof.
unfold free.
intros.
split with (is_an_homomorphism S E B f).
unfold commute.
intro.
simpl.
apply (cong_rel_sym).
unfold is_an_homomorphism.
apply (cong_rel_refl).
intros.
apply unicité.
intros.
unfold is_an_homomorphism.
simpl.
destruct H.
unfold commute in H.
unfold commute in H0.
apply (cong_rel_trans B) with (y := is_an_homomorphism S E B f (generator x0)).
apply (cong_rel_sym B).
auto.
apply (cong_rel_trans B) with (y := f x0).
auto.
apply (cong_rel_sym B).
auto.
Defined.

End TermALgebra_is_free.

Section iso_caracterisation.
Context (S : OpSignature).
Context (E : EqSignature S).
Context (A B : Algebra S E).

Definition injective (f : Hom A B) : Type := forall (x y : A), (equal S E B) (f x) (f y) -> (equal S E A) x y.

Definition surjective (f : Hom A B) : Type := forall x, {t | f t = x}.



Context (f : Hom A B).
Hypothesis injectf : injective f.
Hypothesis surjectf : surjective f.


Definition f_inv (x : B) :  A.
Proof.
unfold surjective in surjectf.
pose proof surjectf x.
destruct X0.
exact x0.
Defined.

Print f_inv.


Lemma un_sens: forall (x : A), (equal S E A) (f_inv (f x)) x.
Proof.
intros.
unfold surjective in surjectf.
unfold injective in injectf.
unfold f_inv.
destruct (surjectf (f x)) as [x0 H].
apply injectf.
rewrite H.
apply cong_rel_refl.
Qed.

Lemma autre_sens : forall (x : B), (equal S E B) (f (f_inv x)) x.
Proof.
intros.
unfold surjective in surjectf.
unfold injective in injectf.
unfold f_inv.
destruct (surjectf x) as [x0 e].
rewrite e.
apply cong_rel_refl.
Qed.

Lemma respect_rel : forall (x y : B), (equal S E B) x y -> (equal S E A) (f_inv x) (f_inv y).
Proof.
intros.
unfold f_inv.
unfold surjective in surjectf.
destruct (surjectf x) as [x0 e].
destruct (surjectf y) as [x1 e'].
unfold injective in injectf.
apply injectf.
rewrite e.
rewrite e'.
auto.
Qed.

Definition iso_back : Hom B A.
Proof.
split with (f_inv).
intros.
apply respect_rel.
auto.
intros.
apply cong_rel_trans with (y := f_inv (op B o (fun x => f (f_inv (args x))))).
apply respect_rel.
apply cong_rel_cong.
intros.
apply cong_rel_sym.
apply autre_sens with (x := args n).
apply cong_rel_trans with (y := f_inv (f (op A o (fun x => f_inv (args x))))).
apply respect_rel.
apply cong_rel_sym.
apply op_commute.
apply un_sens.
Qed.
