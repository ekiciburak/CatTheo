From Cat Require Import Imports.

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Record total2 { T: Type } ( P: T -> Type ): Type := 
  tpair 
  { pr1 : T;
    pr2 : P pr1 
  }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

(* Notation "{ x ; .. ; y ; z }" := (tpair _ x .. (tpair _ y z) ..). *)

Notation "'∑'  x .. y , P" := (total2 (fun x => .. (total2 (fun y => P)) ..))
(at level 200, x binder, y binder, right associativity) : type_scope.

Inductive Id {A: Type}: A -> A -> Type :=
  refl: forall a, Id a a.

Arguments refl {A a} , [A] a.

(* Scheme Id_ind := Induction for Id Sort Type.
Arguments Id_ind [A] P f y y0 i.
Scheme Id_rec := Minimality for Id Sort Type.
Arguments Id_rec [A] P f y y0 i.
Definition Id_rect := Id_ind. *)

Definition transport {A: Type} (P: A -> Type) {a b: A} (p: Id a b): P a -> P b.
Proof. now induction p. Defined.

Definition transportE {A: Type} (P: A -> Type) {a b: A} (p: a = b): P a -> P b.
Proof. now induction p. Defined.

Definition dirprod (A B : Type): Type := ∑ a: A, B.

(* Definition pathsdirprod {A B: Type} {a1 a2: A} {b1 b2: B} (id1: Id a1 a2) (id2: Id b1 b2):
  Id {a1;  b1} {a2; b2}.
Proof. now induction id1, id2. Defined.

Definition inverse {A: Type} {a b: A}: Id a b -> Id b a.
Proof. intro p. now induction p. Defined.

Lemma totalspace_paths_inv: ∏ {A: Type} {P: A -> Type} (w w': (∑ a: A, P a)),
  (∑ p: Id (pr1 w) (pr1 w'), Id (transport P p (pr2 w)) (pr2 w')) -> Id w w'.
Proof. intros A P w w'.
       induction w as (w1, w2); induction w' as (w1', w2'). cbn in *.
       intro q. induction q as (p, q). induction p. cbn in *.
       induction q. easy.
Defined.

Lemma totalspace_paths: ∏ {A: Type} {P: A -> Type} (w w': (∑ a: A, P a)),
  Id w w' -> ∑ p: Id (pr1 w) (pr1 w'), Id (transport P p (pr2 w)) (pr2 w').
Proof. intros A P w w' q. induction q. destruct a. cbn.
       exists (refl pr3). easy.
Defined. *)

Set Universe Polymorphism.

(* Polymorphic Cumulative Class Category: Type :=
 mk_Category 
 {
     obj       : Type;
     arrow     : obj -> obj -> Type;
     identity  : ∏ a, arrow a a;
     comp      : ∏ {a b c}, (arrow b c) -> (arrow a b) -> (arrow a c);
     assoc     : ∏ {a b c d} (h : arrow c d) (g : arrow b c) (f : arrow a b), 
                              Id (comp h (comp g f)) (comp (comp h g) f);
     identity_f: ∏ {a b} (f: arrow a b), Id (comp (@identity b) f) f;
     f_identity: ∏ {a b} (f: arrow a b), Id (comp f (@identity a)) f 
  }.

Notation " g 'o' f " := (@comp _ _ _ _ g f) (at level 40, left associativity).

Class Functor (C D: Category): Type :=
  mk_Functor
  {
    fobj            : @obj C -> @obj D;
    fmap            : forall {a b: @obj C} (f: arrow a b), arrow (fobj a) (fobj b);
    preserve_id     : forall {a: @obj C}, Id (fmap (@identity C a)) ((@identity D (fobj a)));
    preserve_comp   : forall {a b c: @obj C} (g : @arrow C b c) (f: @arrow C a b),
                        Id (fmap (g o f)) ((fmap g) o (fmap f))
  }.
Check Functor.
 *)
Definition iscontr (T: Type): Type := ∑ cntr:T, ∏ t:T, t=cntr.

Fixpoint isofhlevel (n: nat) (X: Type): Type:= 
  match n with
    | O => iscontr X
    | S m => ∏ x : X, ∏ x' : X, (isofhlevel m (Id x x'))
   end.

Definition isaprop := isofhlevel 1.

Definition isaset (X: Type): Type := ∏ x x' : X, isaprop (Id x x').

Open Scope bool_scope.

Require Export SetoidClass.

Class Category: Type :=
 mk_Category 
 {
     obj       : Type;
     arrow     : obj -> obj -> Type;
     identity  : forall a, arrow a a;
     comp      : forall {a b c}, (arrow c b) -> (arrow b a) -> (arrow c a);
     compose_respects x y z : Proper (eq ==> eq ==> eq) (@comp x y z);
     assoc     : forall {a b c d} (f : arrow b a) (g : arrow c b) (h : arrow d c), 
                              comp h (comp g f) = comp (comp h g) f;
     identity_f: forall {a b} (f: arrow b a), comp (@identity b) f = f;
     f_identity: forall {a b} (f: arrow b a), comp f (@identity a) = f 
  }.

Notation " g 'o' f " := (@comp _ _ _ _ g f) (at level 40, left associativity).

(* Coercion obj : Category >-> Sortclass. *)

(* Definition isCartesian {E B: Category} {p: Functor E B} {e' e: @obj E} (phi: arrow e' e) :=
  ∏ (e'': @obj E) (psi: arrow e'' e) (g: arrow (fobj e'') (fobj e')), 
    dirprod (Id ((fmap phi) o g) (fmap psi)) 
            (∑ chi: arrow e'' e', dirprod (Id psi (phi o chi)) 
                                          (∏ chi':  arrow e'' e', Id psi (phi o chi') -> Id chi chi')).

Definition GrothendieckFibration {E B: Category} {a: @obj E} (p: Functor E B) :=
  ∏ (b: @obj E) (g: arrow (fobj a) (fobj b)), 
    ∑ (f: arrow a b), dirprod (Id (fmap f) g) (isCartesian f). *)

(** due to Ahrens et al 2019 *)
Class DisplayedCategory (C: Category): Type :=
  mkDispCat
  {
     Dobj        : ∏ (c: @obj C), Type;
     Darrow      : ∏ {a b} (f: arrow a b) (x: Dobj a) (y: Dobj b), Type;
     Didentity   : ∏ {c} (x: Dobj c), Darrow (identity c) x x;
     Dcomp       : ∏ {a b c} {g: arrow c b} {f: arrow b a} {z: Dobj c} {y: Dobj b} {x: Dobj a},
                     Darrow g z y -> Darrow f y x -> Darrow (g o f) z x;
     Dassoc      : ∏ {a b c d} {h: arrow d c} {g: arrow c b} {f: arrow b a} {t: Dobj d} {z: Dobj c} {y: Dobj b} {x: Dobj a}
                     (fp: Darrow f y x) (gp: Darrow g z y) (hp: Darrow h t z), 
                       (transportE (λ k, (Darrow k _ _)) (assoc f g h) (Dcomp hp (Dcomp gp fp))) = (Dcomp (Dcomp hp gp) fp);
     Didentity_f : ∏ {a b} (f: arrow b a) (x: Dobj a) (y: Dobj b) (fp: Darrow f y x), 
                       (transportE (λ k, (Darrow k _ _)) (identity_f f) (Dcomp (Didentity y) fp)) = fp;
     Df_identity : ∏ {a b} (f: arrow b a) (x: Dobj a) (y: Dobj b) (fp: Darrow f y x), 
                        (transportE (λ k, (Darrow k _ _)) (f_identity f) (Dcomp fp (Didentity x))) = fp;
     Darrowisaset: ∏ {a b} (f: arrow a b) (x: Dobj a) (y: Dobj b), isaset (Darrow f x y)
  }.

(** Sets *)

Definition SetCat: Category.
Proof. unshelve econstructor.
       - exact Set.
       - intros A B. exact (B -> A).
       - simpl. intro A. exact (fun a => a).
       - simpl. intros A B C g f. exact (fun a => g (f a)).
       - repeat intro. now subst. 
       - simpl. intros A B C D f g h.
         reflexivity.
       - simpl. intros A B f. reflexivity.
       - simpl. intros A B f. reflexivity.
Defined.

(** Types *)

Definition TypeCat: Category.
Proof. unshelve econstructor.
       - exact Type.
       - intros A B. exact (B -> A).
       - simpl. intro A. exact (fun a => a).
       - simpl. intros A B C g f. exact (fun a => g (f a)).
       - repeat intro. now subst.
       - simpl. intros A B C D f g h.
         reflexivity.
       - simpl. intros A B f. reflexivity.
       - simpl. intros A B f. reflexivity.
Defined.
























