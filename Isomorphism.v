From Cat Require Import Imports Category Preorder Monoid Poset.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Set Universe Polymorphism.

Lemma funextcontra: ∏ (A B : Type) (f g : A -> B), f = g -> (∏ x : A, f x = g x).
Proof. intros.
       rewrite H.
       reflexivity.
Qed.

(** Injection, Surjection and Bijection *)

Definition injective {X Y: @obj TypeCat} (f: arrow Y X) := forall x x', f x = f x' -> x = x'.

Definition surjective {X Y: @obj TypeCat} (f: X -> Y) := forall y, { x | f x = y }.

Class bijection {X Y: @obj TypeCat} (f: X -> Y) := 
{ 
  finj: injective f;
  fsurj: surjective f
}.

(** Left Canecallable, Right Cancellable *)

Definition leftCancellable {C: Category} {X Y Z: @obj C} (h: arrow Z Y) (f g: arrow Y X) := 
  h o f = h o g -> f = g.

Lemma injlc: forall {X Y Z: @obj TypeCat} (h: arrow Z Y) (f g: arrow Y X),
  injective h -> leftCancellable h f g.
Proof. unfold injective, leftCancellable.
       intros X Y Z h f g i e.
       apply functional_extensionality.
       intro x.
       specialize (i (f x) (g x)).
       apply i.
       simpl in e.
       apply funextcontra with (x := x) in e.
       rewrite e.
       reflexivity.
Qed.

Definition rightCancellable {C: Category}  {X Y Z: @obj C} (h: arrow Y X) (f g: arrow Z Y) := 
  f o h = g o h -> f = g.

Lemma surjrc: forall {X Y Z: @obj TypeCat} (h: arrow Y X) (f g: arrow Z Y),
  surjective h -> rightCancellable h f g.
Proof. unfold surjective, rightCancellable.
       intros X Y Z h f g i e.
       apply functional_extensionality.
       intro y.
       specialize (i y).
       destruct i as (x, i).
       simpl in e.
       apply funextcontra with (x := x) in e.
       rewrite i in e.
       exact e.
Qed.


(** Isomorphism *)

Class Isomorphism (C: Category) {X Y: @obj C} (f: @arrow C Y X) :=
{
  isoinv: @arrow C X Y;
  isoidl: f o isoinv = @identity C Y;
  isoidr: isoinv o f = @identity C X
}.

Lemma IsomorphismEq: forall {C: Category} {X Y: @obj C} (f: arrow Y X) (i j: Isomorphism C f), 
      @isoinv C X Y f i = @isoinv C X Y f j ->   i = j.
Proof. intros C X Y f (finv1, fax11, fax12) (finv2, fax21, fax22) eq.
       simpl in *.
       subst.
       f_equal.
       - now destruct (proof_irrelevance _ fax11 fax21).
       - now destruct (proof_irrelevance _ fax12 fax22).
Qed.

Lemma isolc: forall {C: Category} {X Y Z: @obj C} (h: arrow Z Y) (f g: arrow Y X),
  Isomorphism C h -> leftCancellable h f g.
Proof. unfold injective, leftCancellable.
       intros C X Y Z h f g (hinv, hax1, hax2) e.
       assert (ee: hinv o h o f = hinv o h o g).
       { rewrite <- assoc, e.
         rewrite assoc.
         reflexivity.
       }
       rewrite hax2, !identity_f in ee.
       exact ee.
Qed.

Lemma isorc: forall {C: Category} {X Y Z: @obj C} (h: arrow Y X) (f g: arrow Z Y),
  Isomorphism C h -> rightCancellable h f g.
Proof. unfold injective, rightCancellable.
       intros C X Y Z h f g (hinv, hax1, hax2) e.
       assert (ee: f o h o hinv = g o h o hinv).
       { rewrite e.
         reflexivity.
       }
       rewrite <- assoc, hax1, <- assoc, hax1, !f_identity in ee.
       exact ee.
Qed.

Lemma comp_iso: forall {C: Category} {X Y Z: @obj C} (f: arrow Y X) (g: arrow Z Y),
  Isomorphism C f ->
  Isomorphism C g ->
  Isomorphism C (g o f).
Proof. intros C X Y Z f g (finv, finv_ax1, finv_ax2) (ginv, ginv_ax1, ginv_ax2).
       unshelve econstructor.
       - exact (finv o ginv).
       - rewrite assoc.
         setoid_rewrite <- assoc at 2.
         rewrite finv_ax1, f_identity.
         rewrite ginv_ax1.
         reflexivity.
       - rewrite assoc.
         setoid_rewrite <- assoc at 2.
         rewrite ginv_ax2, f_identity.
         rewrite finv_ax2.
         reflexivity.
Qed.

Lemma comp_iso_r: forall {C: Category} {X Y Z: @obj C} (f: arrow Y X) (g: arrow Z Y),
  Isomorphism C f ->
  Isomorphism C (g o f) ->
  Isomorphism C g.
Proof. intros C X Y Z f g fiso gofiso.
       pose proof fiso as fiso'.
       destruct fiso as (finv, finv_ax1, finv_ax2).
       destruct gofiso as (gofinv, gofinv_ax1, gofinv_ax2).
       unshelve econstructor.
       - exact (f o gofinv).
       - rewrite assoc.
         rewrite gofinv_ax1.
         reflexivity.
       - simpl.
         specialize (@isorc C X Y Y f (f o gofinv o g) (identity Y) fiso'); intro CC.
         unfold rightCancellable in CC.
         apply CC.
         do 2 rewrite <- assoc.
         rewrite gofinv_ax2.
         rewrite f_identity, identity_f.
         reflexivity.
Qed.

Definition Bijective (X Y: Type) := { f: X -> Y & bijection f }.

Definition Isomorphic {C: Category} (X Y: @obj C) := { f: (@arrow C Y X) & Isomorphism C f }.

Lemma bijisol: forall X Y (f: @arrow SetCat Y X), bijection f -> Isomorphism SetCat f.
Proof. intros X Y f (finj, fsurj).
       unfold injective, surjective in *.
       unshelve econstructor.
       - simpl in *.
         intro a.
         specialize (fsurj a).
         exact (proj1_sig fsurj).
       - simpl in *.
         apply functional_extensionality.
         intro y.
         unfold proj1_sig.
         destruct (fsurj y) as (a, a_ax).
         exact a_ax.
       - simpl in *.
         apply functional_extensionality.
         intro a.
         unfold proj1_sig.
         simpl.
         destruct (fsurj (f a)) as (x, x_ax).
         apply finj.
         exact x_ax.
Qed.

Lemma bijisor: forall X Y (f: @arrow SetCat Y X), Isomorphism SetCat f -> bijection f.
Proof. intros X Y f (finv, ax1, ax2). simpl in *.
(*     specialize (@funextcontra _ _ _ _ ax1).
       intro ax1'. simpl in ax1'. *)
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl ax1) as ax1';
       cbv beta in ax1'.
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl ax2) as ax2';
       cbv beta in ax2'.
       unshelve econstructor.
       - unfold injective.
         intros x y H.
         pose proof ax2' as ax2''.
         specialize (ax2' x).
         rewrite H in ax2'.
         rewrite ax2'' in ax2'.
         symmetry.
         exact ax2'.
       - unfold surjective.
         intro y.
         exists (finv y).
         rewrite ax1'.
         reflexivity.
Qed.

Lemma bijisolT: forall X Y (f: @arrow TypeCat Y X), bijection f -> Isomorphism TypeCat f.
Proof. intros X Y f (finj, fsurj).
       unfold injective, surjective in *.
       unshelve econstructor.
       - simpl in *. intro y.
         specialize (fsurj y).
         destruct fsurj as (x, xax).
         exact x.
       - cbn in *.
         apply functional_extensionality.
         intro y.
         destruct (fsurj y) as (x, xax).
         exact xax.
       - simpl in *.
         apply functional_extensionality.
         intro x.
         destruct (fsurj (f x)) as (y, yax).
         apply finj. easy.
Qed.

Lemma bijisorT: forall X Y (f: @arrow TypeCat Y X), Isomorphism TypeCat f -> bijection f.
Proof. intros X Y f (finv, ax1, ax2). simpl in *.
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl ax1) as ax1';
       cbv beta in ax1'.
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl ax2) as ax2';
       cbv beta in ax2'.
       unshelve econstructor.
       - unfold injective.
         intros x y H.
         pose proof ax2' as ax2''.
         specialize (ax2' x).
         rewrite H in ax2'.
         rewrite ax2'' in ax2'. easy.
       - unfold surjective.
         intro y.
         exists (finv y).
         rewrite ax1'. easy.
Qed.

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.

Lemma bijiso: forall X Y (f: @arrow SetCat Y X), iffT (Isomorphism SetCat f) (bijection f).
Proof. intros.
       red. split.
       - intro H. apply bijisor. easy.
       - intro H. apply bijisol. easy.
Qed.

Lemma bijisoT: forall X Y (f: @arrow SetCat Y X), iffT (Isomorphism TypeCat f) (bijection f).
Proof. intros.
       red. split.
       - intro H. apply bijisor. easy.
       - intro H. apply bijisol. easy.
Qed.

Lemma bijlc: forall {X Y Z: @obj TypeCat} (h: arrow Z Y) (f g: arrow Y X),
  bijection h -> leftCancellable h f g.
Proof. unfold injective, leftCancellable.
       intros X Y Z h f g e.
       apply bijisolT in e.
       apply isolc.
       exact e.
Qed.

Lemma bijrc: forall {X Y Z: @obj TypeCat} (h: arrow Y X) (f g: arrow Z Y),
  bijection h -> rightCancellable h f g.
Proof. unfold surjective, rightCancellable.
       intros X Y Z h f g e.
       apply bijisolT in e.
       apply isorc.
       exact e.
Qed.


Lemma MonoidMapIsol: forall (M1 M2: Monoid) (f: MonoidMap M1 M2), 
 bijection (@monmap M1 M2 f) -> Isomorphism Mon f.
Proof. intros (M1, e1, op1, ax1, ax2, ax3) (M2, e2, op2, ax4, ax5, ax6) (f, fax1, fax2) (finj, fsurj).
       simpl in *.
       unfold injective, surjective in *.
       unshelve econstructor.
       - simpl. unshelve econstructor.
         + simpl. intro y.
           exact (proj1_sig (fsurj y)).
         + simpl.
           unfold proj1_sig.
           destruct (fsurj e2) as (x, xax).
           rewrite <- fax1 in xax.
           specialize (finj _ _ xax). 
           exact finj.
         + simpl. intros x y.
           unfold proj1_sig.
           destruct (fsurj (op2 x y)) as (a, aax).
           destruct (fsurj x) as (b, bax).
           destruct (fsurj y) as (c, cax).
           rewrite <- bax, <- cax, <- fax2 in aax.
           specialize (finj _ _ aax). 
           exact finj.
       - apply MonoidMapEq. simpl.
         apply functional_extensionality.
         intro x.
         destruct (fsurj x) as (a, aax).
         simpl.
         easy.
       - apply MonoidMapEq. simpl.
         apply functional_extensionality.
         intro x.
         destruct (fsurj (f x)) as (a, aax).
         specialize (finj _ _ aax).
         easy.
Qed.

Lemma MonoidMapIsor: forall (M1 M2: Monoid) (f: MonoidMap M1 M2), 
 Isomorphism Mon f -> bijection (@monmap M1 M2 f).
Proof. intros (M1, e1, op1, ax1, ax2, ax3) (M2, e2, op2, ax4, ax5, ax6) 
              (f, fax1, fax2) ((finv, finvax1, finvax2), ob1, ob2).
       simpl in *.
       inversion ob1.
       inversion ob2.
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H0) as H0';
       cbv beta in H0'.
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H1) as H1';
       cbv beta in H1'.
       unshelve econstructor.
       - unfold injective.
         intros x y H.
         pose proof H1' as H2.
         specialize (H1' y).
         rewrite <- H, H2 in H1'.
         rewrite H1'.
         reflexivity.
       - unfold surjective.
         intro y.
         exists (finv y).
         rewrite H0'.
         reflexivity.
Qed.

Lemma MonoidMapIso: forall (M1 M2: Monoid) (f: MonoidMap M1 M2), 
  iffT (bijection (@monmap M1 M2 f)) (Isomorphism Mon f).
Proof. intros.
       split.
       - apply MonoidMapIsol.
       - apply MonoidMapIsor.
Qed.

Lemma PoSetdMapIsol: forall (P1 P2: PoSet) (f: PoSetMap P1 P2), 
 surjective (@posmap _ _ (@posetmap P1 P2 f)) *
 (forall x x', (@pohrel (@poset P2)) ((@posmap _ _ (@posetmap P1 P2 f)) x) ((@posmap _ _ (@posetmap P1 P2 f)) x') = true -> 
               (@pohrel (@poset P1) x x' = true)) -> 
 Isomorphism Poset f.
Proof. intros P1 P2 f (H, Hrlctv).
       destruct P1 as ((P1, le1, r1, t1), a1).
       destruct P2 as ((P2, le2, r2, t2), a2).
       destruct f as (f). destruct f as (f, Hf).
       simpl in *.
       unfold surjective in H. 
       unshelve econstructor.
       - simpl. unshelve econstructor.
         + simpl. unshelve econstructor.
           ++ simpl. intro y.
              destruct (H y) as (x, xax).
              exact x.
           ++ simpl. intros x x' Hx.
              destruct (H x) as (a, aax).
              destruct (H x') as (b, bax).
              apply Hrlctv. (** crucial -- additional assumption of 'reflective'ness *)
              rewrite <- aax, <- bax in Hx. easy.
       - apply PoSetMapEq, PreOrderMapEq.
         simpl.
         apply functional_extensionality.
         intro x.
         destruct (H x) as (a, aax).
         easy.
       - apply PoSetMapEq, PreOrderMapEq.
         simpl.
         apply functional_extensionality.
         intro x.
         destruct (H (f x)).
         apply a1. (** the reason why this characterization does not work for Preord *)
         split.
         + apply Hrlctv. rewrite e. apply r2.
         + apply Hrlctv. rewrite e. apply r2.
Qed.

Lemma PoSetdMapIsor: forall (P1 P2: PoSet) (f: PoSetMap P1 P2),
 Isomorphism Poset f ->
 surjective (@posmap _ _ (@posetmap P1 P2 f)) *
 (forall x x', (@pohrel (@poset P2)) ((@posmap _ _ (@posetmap P1 P2 f)) x) ((@posmap _ _ (@posetmap P1 P2 f)) x') = true -> (@pohrel (@poset P1) x x' = true)).
Proof. intros P1 P2 f (finv, fax1, fax2).
       destruct P1 as ((P1, le1, r1, t1), a1).
       destruct P2 as ((P2, le2, r2, t2), a2).
       destruct f as (f). destruct f as (f, Hf).
       simpl in *.
       destruct finv as (finv). destruct finv as (finv, Hfinv).
       simpl in *. 
       inversion fax1.
       inversion fax2.
       clear fax1 fax2.
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H0) as fax1;
       cbv beta in fax1.
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H1) as fax2;
       cbv beta in fax2.
       split.
       - unshelve econstructor.
         + exact (finv y).
         + apply fax1.
       - intros x x' Hfx.
         specialize (Hfinv (f x) (f x')).
         rewrite !fax2 in Hfinv.
         apply Hfinv.
         easy.
Qed.

Lemma PoSetdMapIso: forall (P1 P2: PoSet) (f: PoSetMap P1 P2),
 iffT (Isomorphism Poset f)
 (surjective (@posmap _ _ (@posetmap P1 P2 f)) *
 (forall x x', (@pohrel (@poset P2)) ((@posmap _ _ (@posetmap P1 P2 f)) x) ((@posmap _ _ (@posetmap P1 P2 f)) x') = true -> (@pohrel (@poset P1) x x' = true))).
Proof. intros. split.
       - intros. apply PoSetdMapIsor. easy.
       - intros. apply PoSetdMapIsol. easy.
Qed.
