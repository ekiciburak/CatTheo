From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism Terminal Dual Initial Product CoProduct.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

Set Universe Polymorphism.

(** Exponentials *)

Definition fprod {C : Category} {hp : hasProducts C} {X X' Y Y': @obj C} (f: @arrow C Y X) (g: @arrow C Y' X') := 
  (@prod_f C _ _ _ (@hasp C hp _ _) _ (f o (@pi1 C X X' _ (@hasp C hp X X'))) (g o (@pi2 C X X' _ (@hasp C hp X X')))).

Lemma fprod_distrA: forall (Cat: Category) {hp: hasProducts Cat} {X Y Z X' Y' Z': @obj Cat} 
  (f: @arrow Cat Y X) (g: @arrow Cat Z Y) (f': @arrow Cat Y' X') (g': @arrow Cat Z' Y'),
  fprod g g' o fprod f f' = fprod (g o f) (g' o f').
Proof. intros Cat hp X Y Z X' Y' Z' f g f' g'.
       specialize ((@prod_f_uni Cat Z Z' (@pobj Cat hp Z Z') (@hasp Cat hp Z Z')) (@pobj Cat hp X X') 
                  ((@pi1 Cat Z Z' (@pobj Cat hp Z Z') (@hasp Cat hp Z Z')) o fprod (g o f) (g' o f'))
                  ((@pi2 Cat Z Z' (@pobj Cat hp Z Z') (@hasp Cat hp Z Z')) o fprod (g o f) (g' o f'))
                  (fprod (g o f) (g' o f'))
                  eq_refl
                  eq_refl
                  ); intro H.
       specialize ((@prod_f_uni Cat Z Z' (@pobj Cat hp Z Z') (@hasp Cat hp Z Z')) (@pobj Cat hp X X') 
                  ((@pi1 Cat Z Z' (@pobj Cat hp Z Z') (@hasp Cat hp Z Z')) o (fprod g g' o fprod f f' ))
                  ((@pi2 Cat Z Z' (@pobj Cat hp Z Z') (@hasp Cat hp Z Z')) o (fprod g g' o fprod f f' ))
                  (fprod g g' o fprod f f')
                  eq_refl
                  eq_refl
                  ); intro HH.
       unfold fprod in *. simpl.
       rewrite <- HH.
       rewrite <- H.
       rewrite <- prod_f_c1.
       rewrite <- prod_f_c2.
       rewrite assoc.
       rewrite <- prod_f_c1.
       rewrite assoc.
       rewrite <- prod_f_c2.
       rewrite <- assoc.
       rewrite <- prod_f_c1.
       rewrite <- assoc.
       rewrite <- prod_f_c2.
       rewrite assoc.
       rewrite assoc.
       reflexivity.
Qed.

Lemma fprod_distr: forall (Cat: Category) {hp: hasProducts Cat} {A B C D E F: @obj Cat} 
  (f: @arrow Cat B A) (g: @arrow Cat D C) (h: @arrow Cat A E) (i: @arrow Cat C F),
  fprod f g o fprod h i = fprod (f o h) (g o i).
Proof. intros Cat (p, hasp) A B C D E F f g h i.
       unfold fprod. simpl.
       destruct (hasp A C) as (proj1, proj2, t, tax1, tax2, tuniq). simpl in *.
       destruct (hasp B D) as (proj3, proj4, r, rax1, rax2, runiq). simpl in *.
       destruct (hasp E F) as (proj5, proj6, m, max1, max2, muniq). simpl in *.
       pose proof runiq as rruniq.
       specialize (runiq (p E F) (f o h o proj5) (g o i o proj6)
         (r (p A C) (f o proj1) (g o proj2) o t (p E F) (h o proj5) (i o proj6))
         ).
(*        specialize (rruniq (p E F) (f o h o proj5) (g o i o proj6)
         (r (p E F) (f o h o proj5) (g o i o proj6))
         ). *)
       rewrite runiq.
       + easy.
       + rewrite assoc.
         rewrite <- rax1.
         setoid_rewrite <- assoc at 2.
         rewrite <- tax1.
         rewrite assoc.
         reflexivity.
       + rewrite assoc.
         rewrite <- rax2.
         setoid_rewrite <- assoc at 2.
         rewrite <- tax2.
         rewrite assoc.
         reflexivity.
Qed.


Lemma fprod_id:  forall (Cat: Category) {hp: hasProducts Cat} {A B: @obj Cat},
  fprod (identity A) (identity B) = identity (@pobj Cat hp A B).
Proof. intros Cat (p, hasp) A B.
       unfold fprod. simpl.
       rewrite !identity_f.
       destruct (hasp A B) as (proj1, proj2, t, tax1, tax2, tuniq). simpl in *.
       specialize (tuniq _ proj1 proj2 (identity (p A B))).
       apply tuniq.
       - now rewrite f_identity.
       - now rewrite f_identity.
Qed.

Lemma fprod_id_dist: forall (Cat: Category) {hp: hasProducts Cat} {A B C X: @obj Cat} 
  (f: @arrow Cat B A) (g: @arrow Cat C B),
  @fprod Cat hp _ _ _ _ (g o f) (identity X) = @fprod Cat hp _ _ _ _  g (identity X) o @fprod Cat hp _ _ _ _ f (identity X).
Proof. intros.
       rewrite fprod_distr.
       rewrite f_identity.
       easy.
Qed.

(*
Check fprod f g.
Parameters (C: Category) (A B X X' Y Y' prod: @obj C) (p: Product C A B prod) (f: @arrow C Y X) (g: @arrow C Y' X').
Check @prod_f C A B prod p.
Check @pi1 C A B _ p.
*)

Lemma hasProductsSetCat: hasProducts SetCat.
Proof. unshelve econstructor.
       - intros a b. exact (prod a b).
       - intros. simpl. apply setProd.
Defined.

Lemma hasProductsPreOrderCat: hasProducts PreOrderCat.
Proof. unshelve econstructor.
       - intros a b. exact (preorderProdObj a b).
       - intros. simpl. apply preorderProd.
Defined.

Class Exponential (C: Category) {p: hasProducts C} (X Y exp: @obj C): Type :=
{
  app    : @arrow C Y (@pobj C p exp X);
  cur    : forall (Z: @obj C) (f: @arrow C Y (@pobj C p Z X)), @arrow C exp Z;
  curcomm: forall (Z: @obj C) (f: @arrow C Y (@pobj C p Z X)), app o (fprod (cur Z f) (@identity C X)) = f;
  curuni : forall (Z: @obj C) (f: @arrow C Y (@pobj C p Z X)) (g: @arrow C exp Z), 
    app o (fprod g (@identity C X)) = f -> (cur Z f) = g
}.

Class hasExponentials (C: Category) (hprd: hasProducts C): Type :=
{
   eobj: forall (A B: @obj C), @obj C;
   hase: forall (A B: @obj C), @Exponential C hprd A B (eobj A B)
}.

(* Parameters(C: Category) (hp: hasProducts C) (he: hasExponentials C hp) (x y z w: @obj C) 
  (f: @arrow C z (@pobj C hp y x)) (g: @arrow C w z) .
  Check @cur C hp _ _ (@eobj C hp he x w) (@hase C hp he x w) y (g o f).
  Check @cur C hp _ _ (@eobj C hp he x z) (@hase C hp he x z) y f. *)

Definition fExp {C: Category} {hp: hasProducts C} {he: hasExponentials C hp} {A B: @obj C} (X: @obj C) (f: @arrow C B A):=
  @cur C hp X B (@eobj C hp he X B) (@hase C hp he X B) (@eobj C hp he X A)
       (f o  @app C hp X A (@eobj C hp he X A) (@hase C hp he X A)).

Lemma fExpComp: forall {C: Category} {hp: hasProducts C} {he: hasExponentials C hp} {x y z w: @obj C} 
  (f: @arrow C z (@pobj C hp y x)) (g: @arrow C w z), 
  @cur C hp _ _ (@eobj C hp he x w) (@hase C hp he x w) y (g o f) = 
  fExp x g o @cur C hp _ _ (@eobj C hp he x z) (@hase C hp he x z) y f.
Proof. intros.
       unfold fExp.
       specialize (@fExp C hp he z w x g); intro gx.
       destruct hp as (pobj, hasp).
       destruct he as (eobj, hase).
       simpl in *.
       destruct ( hase x w ).
       destruct ( hase x z ).
       simpl in *.
       pose proof curuni0 as cu0.
       pose proof curuni1 as cu1.
       specialize (cu1 y f).
       specialize (cu0 y (g o f) (cur0 (eobj x z) (g o app1) o cur1 y f)).
       rewrite cu0. reflexivity.
       rewrite fprod_id_dist.
       rewrite assoc.
       rewrite curcomm0.
       rewrite <- assoc.
       rewrite curcomm1. easy.
Qed.

Lemma fExpDistributes: forall {C: Category} {hp: hasProducts C} {he: hasExponentials C hp} {a b c: @obj C} 
                              (X: @obj C) (f: @arrow C b a) (g: @arrow C c b),
                              @fExp C hp he a c X (g o f) = @fExp C hp he b c X g o @fExp C hp he a b X f.
Proof. intros.
       unfold fExp in *.
       specialize (@fExpComp C hp he _ _ _ _ (f o (@app C hp X a (@eobj C hp he X a) (@hase C hp he X a))) g); intro h.
       unfold fExp in *.
       rewrite assoc in h.
       rewrite h.
       easy.
Qed.

(*
Check @cur.
Parameters(C: Category) (hp: hasProducts C) (he: hasExponentials C hp) (x y z: @obj C)  (f: @arrow C z y) .
Check (@app C hp _ _ (@eobj C hp he z x) (@hase C hp he z x)).
Check fprod (identity (@eobj C hp he z x)) f.
Check (@app C hp _ _ (@eobj C hp he z x) (@hase C hp he z x)) o fprod (identity (@eobj C hp he z x)) f.
Check
@cur C hp _ _ (@eobj C hp he y x) (@hase C hp he y x) (@eobj C hp he z x)
((@app C hp _ _ (@eobj C hp he z x) (@hase C hp he z x)) o fprod (identity (@eobj C hp he z x)) f).
Check 
(@app C hp _ _ (@eobj C hp he y' x) (@hase C hp he y' x) o fprod (identity (@eobj C hp he y' x)) f).
Check @cur C hp _ _ (@eobj C hp he y x) (@hase C hp he y x) (@eobj C hp he y' x).

  Check @cur C hp _ _ (@eobj C hp he x w) (@hase C hp he x w) y (g o f).
  Check @cur C hp _ _ (@eobj C hp he x z) (@hase C hp he x z) y f. *)

Definition Expf {C: Category} {hp: hasProducts C} {he: hasExponentials C hp} {y z: @obj C} (x: @obj C) (f: @arrow C z y):=
  @cur C hp _ _ (@eobj C hp he y x) (@hase C hp he y x) (@eobj C hp he z x)
       ((@app C hp _ _ (@eobj C hp he z x) (@hase C hp he z x)) o fprod (identity (@eobj C hp he z x)) f).


(* Parameters(C: Category) (hp: hasProducts C) (he: hasExponentials C hp) (x y z w: @obj C) 
 (f: @arrow C z (@pobj C hp y x)) (g: @arrow C x w).
 Check (Expf z g o (@cur C hp _ _ (@eobj C hp he x z) (@hase C hp he x z) y f)).
 Check (    @cur C hp _ _ (@eobj C hp he w z) (@hase C hp he w z) _ (f o (fprod (identity y) g))). *)

Lemma ExpfComp: forall {C: Category} {hp: hasProducts C} {he: hasExponentials C hp} {x y z w: @obj C}
  (f: @arrow C z (@pobj C hp y x)) (g: @arrow C x w), 
    @cur C hp _ _ (@eobj C hp he w z) (@hase C hp he w z) _ (f o (fprod (identity y) g)) = 
    Expf z g o (@cur C hp _ _ (@eobj C hp he x z) (@hase C hp he x z) y f).
Proof. intros.
       unfold Expf.
       specialize (@fprod_distr C hp); intro h1. 
       specialize (@fprod_distr C hp); intro h2. 
       destruct hp as (pobj, hasp).
       destruct he as (eobj, hase).
       simpl in *.
       destruct ( hase w z ).
       destruct ( hase x z ).
       pose proof curuni0 as cu0.
       pose proof curuni1 as cu1.
       pose proof curcomm1 as ccm1.
       pose proof curcomm0 as ccm0.
       simpl in *.
       unfold fprod. simpl.
       specialize (cu0 y ( (f o prod_f (pobj y w) (identity y o pi1) (g o pi2))) 
       (cur0 (eobj x z) (app1 o prod_f (pobj (eobj x z) w) (identity (eobj x z) o pi1) (g o pi2)) o cur1 y f) ).
       rewrite cu0. reflexivity. simpl in *.
       rewrite fprod_id_dist.
       simpl in *.
       rewrite assoc.
       rewrite curcomm0.
       rewrite !identity_f.
       unfold fprod in h1, h2.
       unfold fprod.
       simpl in h1, h2.
       simpl.
       specialize (h1 _ _ _ _ _ _  (identity (eobj x z)) g (cur1 y f) (identity w)).
       rewrite !identity_f in h1.
       rewrite !identity_f.
       rewrite <- assoc.
       rewrite h1.
       unfold fprod in ccm1, cu1.
       simpl in ccm1, cu1.
       specialize (ccm1 y f).
       setoid_rewrite <- ccm1 at 2.
       specialize (h2 _ _ _ _ _ _  (cur1 y f) (identity x) (identity y) g).
       rewrite !identity_f in h2.
       rewrite !identity_f.
       do 2 rewrite <- assoc.
       rewrite h2.
       rewrite f_identity, identity_f.
       reflexivity.
Qed.

Lemma ExpfDistributes: forall {C: Category} {hp: hasProducts C} {he: hasExponentials C hp} {a b c: @obj C} 
                              (X: @obj C) (f: @arrow C b a) (g: @arrow C c b),
                              Expf X (g o f) = Expf X f o Expf X g.
Proof. intros.
       unfold Expf in *.
       specialize (@ExpfComp C hp he
       b (eobj c X) X a (@app C hp c X (@eobj C hp he c X) (@hase C hp he c X) o fprod (identity (eobj c X)) g) f); intro h.
       unfold Expf in *.
       rewrite <- h.
       specialize (@fprod_distr C hp _ _ _ _ _ _ (identity (eobj c X)) g (identity (eobj c X)) f); intro h2.
       rewrite <- assoc.
       rewrite h2.
       rewrite f_identity. 
       reflexivity.
Qed.

Lemma app_bij: forall (C: Category) (X Y Z: @obj C) (hprd: hasProducts C) (e: hasExponentials C hprd),
  Bijective (@arrow C Y (@pobj C hprd Z X)) (@arrow C (@eobj C hprd e X Y) Z).
Proof. intros C X Y Z hp e.
       destruct hp as (prod, pax).
       destruct e as (exp, expax). simpl in *.
       unfold Bijective.
       specialize (expax X Y).
       destruct expax as (app, cur, comm, uni). simpl in *.
       exists (cur Z).
       unshelve econstructor.
       - unfold injective.
         intros g h H. simpl in *.
         pose proof comm as comm1.
         specialize (comm Z g).
         rewrite <- comm.
         specialize (comm1 Z h).
         rewrite <- comm1. rewrite H. easy.
       - unfold surjective.
         intro g. simpl in *.
         unfold fprod in *. simpl in *.
         exists (app o prod_f (prod Z X) (g o pi1) (identity X o pi2)).
         specialize (uni Z (app o prod_f (prod Z X) (g o pi1) (identity X o pi2)) g).
         rewrite uni; reflexivity.
Qed.

(** here  for a non-example of CCCs *)
(* Lemma unitSetMon_bij: Bijective (@arrow SetCat (list unit) unit) 
                                (@arrow Mon ListMonoid ListMonoid).
Proof. unshelve econstructor.
       - simpl. intros f.
         unshelve econstructor.
         + simpl. intro g. exact (@eta unit tt).
         + simpl. easy.
         + simpl. easy.
       - simpl. unshelve econstructor.
         + unfold injective. intros.
           inversion H.
           f_equal. *)


(** Exponential objects are unique up to (unique) isomorphism *)

Lemma exponentialIso0:
  forall (C: Category) (hp: hasProducts C) 
         (X Y E E': @obj C) 
         (e: @Exponential C hp X Y E), 
          @Isomorphic C E E' -> @Exponential C hp X Y E'.
Proof. intros C hp X Y E E' 
              (app, cur, curcomm, curuniq) 
              (h, (hinv, hax1, hax2)).
       unshelve econstructor.
       - exact (app o fprod hinv (identity X)).
       - intros A f. exact (h o cur A f).
       - simpl. intros A f.
         rewrite <- assoc.
         rewrite fprod_distr.
         rewrite assoc, hax2, f_identity, identity_f.
         specialize (curcomm _ f). 
         rewrite curcomm. easy.
       - intros A f e' H. simpl in *.
         rewrite <- assoc, fprod_distr, f_identity in H.
         specialize (curuniq A f (hinv o e')).
         rewrite curuniq, assoc, hax1, identity_f. easy.
         rewrite H. easy.
Qed.

Lemma ExponentialIso: 
  forall (C: Category) (hp: hasProducts C) 
         (X Y E E': @obj C) 
         (e:  @Exponential C hp X Y E) 
         (e': @Exponential C hp X Y E'), @Isomorphic C E E'.
Proof. intros C hp X Y E E' (app1, cur1, curcomm1, curuniq1) 
              (app2, cur2, curcomm2, curuniq2).
       unshelve econstructor.
       - exact (cur2 E app1).
       - unshelve econstructor.
         + exact (cur1 E' app2).
         + specialize (curcomm1 E' app2).
           specialize (curcomm2 E app1).
           rewrite <- curcomm2 in curcomm1.
           rewrite <- assoc, fprod_distr, f_identity in curcomm1.
           pose proof curuniq2 as curuniq2'.
           specialize (curuniq2 E' app2 (cur2 E app1 o cur1 E' app2)).
           rewrite <- curuniq2.
           specialize (curuniq2' E' app2 (identity E')).
           rewrite curuniq2'. 
           * easy.
           * destruct hp as (pobj, p). simpl in *.
             rewrite fprod_id, f_identity. easy.
           * easy.
         + specialize (curcomm2 E app1).
           specialize (curcomm1 E' app2).
           rewrite <- curcomm1 in curcomm2.
           rewrite <- assoc, fprod_distr, f_identity in curcomm2.
           pose proof curuniq1 as curuniq1'.
           specialize (curuniq1 E app1 (cur1 E' app2 o cur2 E app1)).
           rewrite <- curuniq1.
           specialize (curuniq1' E app1 (identity E)).
           rewrite curuniq1'. 
           * easy.
           * destruct hp as (pobj, p). simpl in *.
             rewrite fprod_id, f_identity. easy.
           * easy.
Qed.

(** terminal in some category *)

Definition ECat (C: Category) (X Y E: @obj C) (hp: hasProducts C) (e: @Exponential C hp X Y E): Category.
Proof. destruct e as (app, cur, comm, uniq).
       destruct hp as (prod, p).
       destruct (p X Y) as (pi1, pi2, h, hax1, hax2, huniq). 
       simpl in *.
       unshelve econstructor.
       - exact { Z: @obj C & @arrow C Y (prod Z X) }.
       - intros (Z, f) (Z', f'). simpl in *.
         exact { g: @arrow C Z Z' & f o (@fprod C (Build_hasProducts C prod p) _ _ _ _ g (identity X)) = f' }.
       - simpl. intros (Z, f).
         exists (identity Z).
         rewrite fprod_id, f_identity. easy.
       - simpl. intros (Z, f) (T, g) (U, i) (V, j) (K, k).
         exists (V o K).
         assert (identity X = identity X o identity X) by now rewrite f_identity.
         rewrite H.
         rewrite <- fprod_distr.
         rewrite assoc. subst. easy.
        - simpl. repeat intro. now subst.
        - simpl. intros (Z, f) (T, g) (U, i) (V, j) (k, Hk) (l, Hl) (m, Hm).
          apply subsetT_eq_compat.
          rewrite assoc. easy.
        - simpl. intros (Z, f) (T, g) (u, Hu).
          apply subsetT_eq_compat.
          rewrite identity_f. easy.
        - simpl. intros (Z, f) (T, g) (u, Hu).
          apply subsetT_eq_compat.
          rewrite f_identity. easy.
Defined.

Definition ECatT (C: Category) (X Y E: @obj C) (hp: hasProducts C) (e: @Exponential C hp X Y E):
  @obj (ECat C X Y E hp e).
Proof. intros.
       destruct e as (app, cur, comm, uniq). cbn.
       destruct hp as (prod, p).
       destruct (p X Y) as (pi1, pi2, h, hax1, hax2, huniq). simpl in *.
       exists E. exact app.
Defined.

Lemma tECat: forall (C: Category) (X Y E: @obj C) (hp: hasProducts C) (e: @Exponential C hp X Y E),
  Terminal (ECat C X Y E hp e) (ECatT C X Y E hp e).
Proof. intros C X Y E (prod, p) (app, cur, comm, uniq).
       unshelve econstructor.
       - simpl in *. intro A.
         destruct (p X Y) as (pi1, pi2, h, hax1, hax2, huniq).
         simpl in *.
         destruct A as (Z, f).
         exists (cur Z f).
         rewrite comm. easy.
       - simpl in *. intros A f g.
         destruct (p X Y) as (pi1, pi2, h, hax1, hax2, huniq).
         simpl in *.
         destruct A as (Z, u).
         destruct f as (f, Hf).
         destruct g as (g, Hg).
         apply subsetT_eq_compat.
         pose proof comm as comm'.
         specialize (comm Z u).
         pose proof uniq as uniq'.
         specialize (uniq Z u f).
         specialize (comm' Z u).
         specialize (uniq' Z u g).
         rewrite <- uniq, <- uniq'. 
         + easy.
         + easy.
         + easy.
Qed.

Class POHI (P: PreOrder) (h: hasPOBM P) (p q: @pos P): Type :=
{
   hi   : @pos P;
   hiapp: @pohrel P (@pobm P hi p (@hpobm P h hi p)) q = true;
   hiob : forall r, @pohrel P r hi = true <-> @pohrel P (@pobm P r p (@hpobm P h r p)) q = true
}.

Class hasPOHI (P: PreOrder) (h: hasPOBM P): Type :=
{
  hhi: forall p q, POHI P h p q
}.

Lemma heyting: forall (P: PreOrder) (p q: @obj (PreOrderDetCat P)) (h1: hasPOBM P) (h2: hasPOHI P h1),
  @Exponential (PreOrderDetCat P) (hasProductsPreOrderDetCat P h1) p q (@hi P h1 p q (@hhi P h1 h2 p q)).
Proof. intros.
       unshelve econstructor.
       - unfold PreOrderICMap.
         destruct P as (P, le, r, t).
         destruct h1 as (h1).
         destruct h2 as (h2).
         compute in *.
         destruct (h2 p q) as (hi, app, cur).
         compute in *.
         destruct (h1 hi p) as (pobj, pi1, pi2, uni).
         simpl in *.
         rewrite app. exact tt.
       - simpl. intros z f.
         destruct P as (P, le, r, t).
         destruct h1 as (h1).
         destruct h2 as (h2).
         compute in *.
         destruct (h2 p q) as (hi, app, cur).
         simpl in *.
         specialize (cur z).
         destruct cur.
         rewrite H0. exact tt.
         destruct (h1 z p). simpl in *.
         case_eq (le pobm q); intros. easy. rewrite H1 in f. easy.
       - intros. apply PreOrderICMapEq.
       - intros. apply PreOrderICMapEq.
Defined.

Lemma hasExponentialsPreOrderDetCat (P: PreOrder) (h1: hasPOBM P) (h2: hasPOHI P h1): 
  hasExponentials (PreOrderDetCat P) (hasProductsPreOrderDetCat P h1).
Proof. unshelve econstructor.
       - simpl in *. intros p q.
         exact (@hi P h1 p q (@hhi P h1 h2 p q)).
       - simpl. intros p q. apply heyting.
Defined.

Lemma setExponential: forall X Y: @obj SetCat, @Exponential SetCat hasProductsSetCat X Y (X -> Y).
Proof. intros X Y.
       unshelve econstructor.
       - simpl. exact (fun (f: (X -> Y) * X) => 
                            match f with 
                              | (f, x) => f x 
                            end).
       - simpl.
         intro A.
         exact (fun (f: A * X -> Y) => fun (a: A) => fun (x: X) => f (a, x)).
       - simpl. intros A f.
         apply functional_extensionality.
         intros (a, x). easy.
       - simpl. intros A f g H.
         rewrite <- H. easy.
Defined.

(* Lemma setExponential: forall A B: @obj SetCat, @Exponential SetCat hasProductsSetCat A B (A -> B).
Proof. intros A B.
       unshelve econstructor.
       - simpl. intros (f, a). exact (f a).
       - simpl. intros Z f z a. exact (f (z, a)).
       - simpl. intros Z f. 
         unfold fprod. simpl.
         apply functional_extensionality.
         intros (z, a). easy.
       - simpl. intros Z f g H.
         rewrite <- H. easy.
Defined.
 *)
Lemma hasExponentialsSetCat: hasExponentials SetCat hasProductsSetCat.
Proof. unshelve econstructor.
       - intros a b. exact (a -> b).
       - simpl. apply setExponential.
Qed.

(* Lemma hasExponentialsPreOrderCat: hasExponentials PreOrderCat hasProductsPreOrderCat.
Proof. unshelve econstructor.
       - intros P1 P2.
         simpl in *.
         destruct P1 as (P1, a1, r1, t1).
         destruct P2 as (P2, a2, r2, t2).
         unshelve econstructor.
         + exact (P1 -> P2).
         + intros f g.
*)


