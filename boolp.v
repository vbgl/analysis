(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* -------------------------------------------------------------------- *)



(* Quoting Coq'standard library:
"This file provides classical logic and indefinite description under
the form of Hilbert's epsilon operator":
Axiom constructive_indefinite_description :
  forall (A : Type) (P : A->Prop),
    (exists x, P x) -> { x : A | P x }
In fact it also derives the consequences of this axiom, which include
informative excluded middle, choice, etc.                               *)
Require Import ClassicalEpsilon.

(* We also want functional extensionality *)
Require Import FunctionalExtensionality.

(* We also want propositional extensionality *)
Require Import PropExtensionality PropExtensionalityFacts.


From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation cid := (@constructive_indefinite_description _ _).

(* -------------------------------------------------------------------- *)
(* Functional extensionality *)

Lemma funext {T U : Type} (f g : T -> U) : (f =1 g) -> f = g.
Proof. exact: functional_extensionality. Qed.

(* -------------------------------------------------------------------- *)
(* Propositional extensionality *)

Lemma propeqE (P Q : Prop) : (P = Q) = (P <-> Q).
Proof.
apply: propositional_extensionality; split => [-> // |].
exact: propositional_extensionality.
Qed.

Lemma funeqE {T U : Type} (f g : T -> U) : (f = g) = (f =1 g).
Proof. by rewrite propeqE; split=> [->//|/funext]. Qed.

Lemma funeq2E {T U V : Type} (f g : T -> U -> V) : (f = g) = (f =2 g).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite funeqE.
Qed.

Lemma funeq3E {T U V W : Type} (f g : T -> U -> V -> W) :
  (f = g) = (forall x y z, f x y z = g x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> x y; rewrite funeqE.
Qed.

Lemma predeqE {T} (P Q : T -> Prop) : (P = Q) = (forall x, P x <-> Q x).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite propeqE.
Qed.

Lemma predeq2E {T U} (P Q : T -> U -> Prop) :
   (P = Q) = (forall x y, P x y <-> Q x y).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> ??; rewrite propeqE.
Qed.

Lemma predeq3E {T U V} (P Q : T -> U -> V -> Prop) :
   (P = Q) = (forall x y z, P x y z <-> Q x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq3E=> ???; rewrite propeqE.
Qed.


Lemma trueE : true = True :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma falseE : false = False :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma propT (P : Prop) : P -> P = True.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma propF (P : Prop) : ~ P -> P = False.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma eq_forall T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (forall x, U x) = (forall x, V x).
Proof. by move=> e; rewrite propeqE; split=> ??; rewrite (e,=^~e). Qed.

Lemma eq_exists T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (exists x, U x) = (exists x, V x).
Proof.
by move=> e; rewrite propeqE; split=> - [] x ?; exists x; rewrite (e,=^~e).
Qed.

Lemma reflect_eq (P : Prop) (b : bool) : reflect P b -> P = b.
Proof. by rewrite propeqE; exact: rwP. Qed.

Lemma notb (b : bool) : (~ b) = ~~ b.
Proof. apply: reflect_eq; exact: negP. Qed.

Lemma Prop_irrelevance (P : Prop) (x y : P) : x = y.
Proof. by move: x (x) y => /propT-> [] []. Qed.

Lemma exist_congr T (U : T -> Prop) (s t : T) (p : U s) (q : U t) :
  s = t -> exist U s p = exist U t q.
Proof. by move=> st; case: _ / st in q *; apply/congr1/Prop_irrelevance. Qed.

(* -------------------------------------------------------------------- *)

(* Informative excluded middle *)

Lemma pselect (P : Prop) : {P} + {~P}.
Proof. exact: excluded_middle_informative P. Qed.

Lemma lem (P : Prop): P \/ ~P.
Proof. by case: (pselect P); tauto. Qed.

Definition asbool (P : Prop) :=
  if pselect P then true else false.

(* Notation "[ P 'as' 'bool' ]" := (asbool P) *)
(*   (at level 0, format "[ P  'as'  'bool' ]") : bool_scope. *)
Notation "`[< P >]" := (asbool P) : bool_scope.

Lemma asboolE (P : Prop) : `[< P >] = P :> Prop.
Proof. by rewrite propeqE /asbool; case: pselect; split. Qed.

(* todo: this is rwP of the other *)
Lemma asboolP (P : Prop) : reflect P `[< P >].
Proof. by apply: (equivP idP); rewrite asboolE. Qed.

(* Lemma asboolPn (P : Prop) : reflect (~ P) (~~ `[< P >]). *)
(* Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed. *)

(* Lemma asboolW (P : Prop) : `[< P >] -> P. *)
(* Proof. by case: asboolP. Qed. *)

(* Lemma asboolT (P : Prop) : P -> `[< P >]. *)
(* Proof. by case: asboolP. Qed. *)

(* Lemma asboolF (P : Prop) : ~ P -> `[< P >] = false. *)
(* Proof. by apply/introF/asboolP. Qed. *)

(* Lemma is_true_inj : injective is_true. *)
(* Proof. by move=> [] []; rewrite ?(trueE, falseE) ?propeqE; tauto. Qed. *)

(* Lemma asbool_equiv_eq {P Q : Prop} : (P <-> Q) -> `[< P >] = `[< Q >]. *)
(* Proof. by rewrite -propeqE => ->. Qed. *)

(* Lemma asbool_eq_equiv {P Q : Prop} : `[< P >] = `[< Q >] -> (P <-> Q). *)
(* Proof. *)
(* by move=> eq; split=> /asboolP; rewrite (eq, =^~ eq) => /asboolP. *)
(* Qed. *)

(* -------------------------------------------------------------------- *)
(* Reflection (and boolean equality) lemmas *)

(* Lemma and_asboolP (P Q : Prop) : reflect (P /\ Q) (`[< P >] && `[< Q >]). *)
(* Proof. *)
(* apply: (iffP idP); first by case/andP=> /asboolP hP /asboolP hQ. *)
(* by case=> /asboolP-> /asboolP->. *)
(* Qed. *)

(* Lemma or_asboolP (P Q : Prop) : reflect (P \/ Q) (`[< P >] || `[< Q >]). *)
(* Proof. *)
(* apply: (iffP idP); first by case/orP=> /asboolP; [left | right]. *)
(* by case=> /asboolP-> //=; rewrite orbT. *)
(* Qed. *)

(* Lemma asbool_neg {P : Prop} : `[< ~ P >] = ~~ `[< P >]. *)
(* Proof. by apply/idP/asboolPn=> [/asboolP|/asboolT]. Qed. *)

(* Lemma asbool_or {P Q : Prop} : `[< P \/ Q >] = `[< P >] || `[< Q >]. *)
(* Proof. *)
(* apply/idP/idP; first by move=> /asboolW/or_asboolP. *)
(* move/or_asboolP; exact: asboolT. *)
(* Qed. *)

(* Lemma asbool_and {P Q : Prop} : `[< P /\ Q >] = `[< P >] && `[< Q >]. *)
(* Proof. *)
(* apply/idP/idP; first by move=> /asboolW/and_asboolP. *)
(* move/and_asboolP; exact: asboolT. *)
(* Qed. *)


(* Lemma imply_asboolP {P Q : Prop} : reflect (P -> Q) (`[< P >] ==> `[< Q >]). *)
(* Proof. *)
(* apply: (iffP implyP)=> [PQb /asboolP/PQb/asboolW //|]. *)
(* by move=> PQ /asboolP/PQ/asboolT. *)
(* Qed. *)

(* Lemma asbool_imply {P Q : Prop} : `[< P -> Q >] = `[< P >] ==> `[< Q >]. *)
(* Proof. *)
(* apply/idP/idP; first by move/asboolW=> /imply_asboolP. *)
(* move/imply_asboolP; exact: asboolT. *)
(* Qed. *)


(* Lemma imply_asboolPn (P Q : Prop) : reflect (P /\ ~ Q) (~~ `[< P -> Q >]). *)
(* Proof. *)
(* by rewrite asbool_imply negb_imply -asbool_neg; apply: (iffP idP) => /and_asboolP. *)
(* Qed. *)

(* Lemma forall_asboolP {T : Type} (P : T -> Prop) : *)
(*   reflect (forall x, `[< P x >]) (`[< forall x, P x >]). *)
(* Proof. *)
(* apply: (iffP idP); first by move/asboolP=> Px x; apply/asboolP. *)
(* by move=> Px; apply/asboolP=> x; apply/asboolP. *)
(* Qed. *)

(* Lemma exists_asboolP {T : Type} (P : T -> Prop) : *)
(*   reflect (exists x, `[< P x >]) (`[< exists x, P x >]). *)
(* Proof. *)
(* apply: (iffP idP); first by case/asboolP=> x Px; exists x; apply/asboolP. *)
(* by case=> x bPx; apply/asboolP; exists x; apply/asboolP. *)
(* Qed. *)

(* Section QuantifierCombinators. *)

(* Variables (T : Type) (P : pred T) (PP : T -> Prop). *)
(* Hypothesis viewP : forall x, reflect (PP x) (P x). *)

(* Lemma existsPP : reflect (exists x, PP x) `[< exists x, P x >]. *)
(* Proof. by apply: (iffP (asboolP _)); case=> x hx; exists x; apply/viewP. Qed. *)

(* Lemma forallPP : reflect (forall x, PP x) `[< forall x, P x >]. *)
(* Proof. *)
(* Proof. by apply: (iffP (asboolP _)) => h x; apply/viewP. Qed. *)

(* End QuantifierCombinators. *)

(* -------------------------------------------------------------------- *)
(* Contraposition and friends. *)

Lemma contrap (Q P : Prop) : (Q -> P) -> ~ P -> ~ Q.
Proof.
(* move=> cb /asboolPn nb; apply/asboolPn. *)
(* by apply: contra nb => /asboolP /cb /asboolP. *)
(* Qed. *)
Admitted.


Definition contrapNN := contra.

Lemma contrapL (Q P : Prop) : (Q -> ~ P) -> P -> ~ Q.
Proof.
Admitted.
(*   move=> cb /asboolP hb; apply/asboolPn. *)
(* by apply: contraL hb => /asboolP /cb /asboolPn. *)
(* Qed. *)

Definition contrapTN := contrapL.

Lemma contrapR (Q P : Prop) : (~ Q -> P) -> ~ P -> Q.
Proof. Admitted.
(* move=> cb /asboolPn nb; apply/asboolP. *)
(* by apply: contraR nb => /asboolP /cb /asboolP. *)
(* Qed. *)

Definition contrapNT := contrapR.

Lemma contrapLR (Q P : Prop) : (~ Q -> ~ P) -> P -> Q.
Proof. Admitted.
(* move=> cb /asboolP hb; apply/asboolP. *)
(* by apply: contraLR hb => /asboolP /cb /asboolPn. *)
(* Qed. *)

Definition contrapTT := contrapLR.

Lemma contrapT P : ~ ~ P -> P.
Proof. Admitted.
(* by move/asboolPn=> nnb; apply/asboolP; apply: contraR nnb => /asboolPn /asboolP. *)
(* Qed. *)

(* cf X. Leroy's talk for the historical name *)
Lemma wlog_neg P : (~ P -> P) -> P.
Proof. by move=> ?; case: (pselect P). Qed.

Lemma notT (P : Prop) : P = False -> ~ P. Proof. by move->. Qed.

Lemma notTE (P : Prop) : (~ P) -> P = False.
Proof. by move=> nP; rewrite propeqE; split. Qed.

Lemma notFE (P : Prop) : (~ P) = False -> P.
Proof. move/notT; exact: contrapT. Qed.

Lemma notK : involutive not.
Proof.
move=> P; rewrite propeqE; split; first exact: contrapT.
by move=> ? ?.
Qed.

Lemma not_inj : injective not. Proof. exact: can_inj notK. Qed.

Lemma notLR P Q : (P = ~ Q) -> (~ P) = Q. Proof. exact: canLR notK. Qed.

Lemma notRL P Q : (~ P) = Q -> P = ~ Q. Proof. exact: canRL notK. Qed.

(* -------------------------------------------------------------------- *)
(* De Morgan laws for quantifiers *)

Lemma not_forall {T} (P : T -> Prop) : (~ forall x, P x) = exists y, ~ P y.
Proof.
rewrite propeqE; split; last by case=> x Px allP; apply: Px.
by apply: contrapR=> /contrapR nexP x; apply: nexP => nPx; exists x.
Qed.

Lemma not_forallN  {T} (P : T -> Prop) : (~ forall x, ~ P x) = exists y, P y.
Proof. rewrite not_forall; apply: eq_exists => x; exact: notK. Qed.

Lemma not_exists {T} (P : T -> Prop) : (~ exists x, P x) = forall x, ~ P x.
Proof.
by apply: notLR; rewrite not_forall; apply: eq_exists => x; rewrite notK.
Qed.

Lemma not_existsN {T} (P : T -> Prop) : (~ exists x, ~ P x) = forall x, P x.
Proof. by apply: notLR; rewrite not_forall; apply: eq_exists=> x. Qed.

Lemma not_exists2 {T} (P Q : T -> Prop) :
  (~ exists2 x, P x & Q x) = forall x, P x -> ~ Q x.
Proof. (* too long says py *)
apply: notLR; rewrite not_forall; rewrite propeqE; split; case=> x.
  by move=> Px Qx; exists x; apply: contrapL Qx; apply.
move=> hx; exists x; first exact: contrapR hx.
exact: contrapR hx.
Qed.

Lemma lem_forall U (P : U -> Prop) : (forall u, P u) \/ (exists u, ~ P u).
Proof.
case: (pselect (forall u : U, P u)) => h; first by left.
by right; move: h; rewrite not_forall.
Qed.

Lemma lem_exists U (P : U -> Prop) : (exists u, P u) \/ (forall u, ~ P u).
Proof.
case: (pselect (exists u : U, P u)) => h; first by left.
by right; move: h; rewrite not_exists.
Qed.

(* -------------------------------------------------------------------- *)
(* Misc. *)
(* Lemma existsp_asboolP {T} {P : T -> Prop} : *)
(*   reflect (exists x : T, P x) `[< exists x : T, `[<P x>] >]. *)
(* Proof.  exact: existsPP (fun x => @asboolP (P x)). Qed. *)

(* Lemma forallp_asboolP {T} {P : T -> Prop} : *)
(*   reflect (forall x : T, P x) `[< forall x : T, `[<P x>] >]. *)
(* Proof. exact: forallPP (fun x => @asboolP (P x)). Qed. *)

(* Lemma forallp_asboolPn {T} {P : T -> Prop} : *)
(*   reflect (forall x : T, ~ P x) (~~ `[<exists x : T, `[<P x>]>]). *)
(* Proof. by rewrite -not_exists; apply: (iffP negP); rewrite asboolE. Qed. *)


(* Lemma forallp_asboolPn {T} {P : T -> Prop} : *)
(*   reflect (forall x : T, ~ P x) (~~ `[<exists x : T, P x>]). *)
(* Proof. *)
(* apply: (iffP idP)=> [/asboolPn NP x Px|NP]. *)
(* by apply/NP; exists x. by apply/asboolP=> -[x]; apply/NP. *)
(* Qed. *)

(* Lemma existsp_asboolPn {T} {P : T -> Prop} : *)
(*   reflect (exists x : T, ~ P x) (~~ `[<forall x : T, P x>]). *)
(* Proof. *)
(* apply: (iffP idP); last by case=> x NPx; apply/asboolPn=> /(_ x). *)
(* move/asboolPn=> NP; apply/asboolP/negbNE/asboolPn=> h. *)
(* by apply/NP=> x; apply/asboolP/negbNE/asboolPn=> NPx; apply/h; exists x. *)
(* Qed. *)

(* Lemma asbool_forallNb {T : Type} (P : pred T) : *)
(*   `[< forall x : T, ~~ (P x) >] = ~~ `[< exists x : T, P x >]. *)
(* Proof. *)
(* apply: (asbool_equiv_eqP forallp_asboolPn); *)
(*   by split=> h x; apply/negP/h. *)
(* Qed. *)

(* Lemma asbool_existsNb {T : Type} (P : pred T) : *)
(*   `[< exists x : T, ~~ (P x) >] = ~~ `[< forall x : T, P x >]. *)
(* Proof. *)
(* apply: (asbool_equiv_eqP existsp_asboolPn); *)
(*   by split=> -[x h]; exists x; apply/negP. *)
(* Qed. *)

(* -------------------------------------------------------------------- *)
(* Misc. *)

Lemma not_imply (A B : Prop) : (~ (A -> B)) = (A /\ ~ B).
Proof.
rewrite propeqE; split; last by case=> hA hnB iAB; intuition.
move=> niAB; case: (lem A) => [hA | hnA]; intuition.
Qed.


(* -------------------------------------------------------------------- *)
(* Generic mixins *)


(* Any type can be equipped with an eqType structure. *)
Definition gen_eq (T : Type) (u v : T) := `[< u = v >].
Lemma gen_eqP (T : Type) : Equality.axiom (@gen_eq T).
Proof. by move=> x y; apply: (iffP (asboolP _)). Qed.
Definition gen_eqMixin {T : Type} := EqMixin (@gen_eqP T).

(* Any type can be equipped with a choiceType structure.*)
Lemma gen_choiceMixin {T : Type} : Choice.mixin_of T.
Proof.
pose eps (P : pred T) (n : nat) :=
  if pselect (exists x, P x) isn't left ex then None
  else Some (projT1 (cid ex)).
exists eps => [P n x|P [x Px]|P Q /funext -> //].
  by rewrite /eps; case: pselect => // ex [<- ]; case: cid.
by exists 0; rewrite /eps; case: pselect => // -[]; exists x.
Qed.


Definition dep_arrow_eqType (T : Type) (T' : T -> eqType) :=
  EqType (forall x : T, T' x) gen_eqMixin.
Canonical arrow_eqType (T : Type) (T' : eqType) :=
  EqType (T -> T') gen_eqMixin.
Canonical arrow_choiceType (T : Type) (T' : choiceType) :=
  ChoiceType (T -> T') gen_choiceMixin.

Canonical Prop_eqType := EqType Prop gen_eqMixin.
Canonical Prop_choiceType := ChoiceType Prop gen_choiceMixin.
