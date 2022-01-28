From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism Terminal Dual Initial Product CoProduct Exponential CCC IPL.

Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Coq.Strings.Byte.
Require Import Coq.Lists.List.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** STLC *)

Inductive type: Type :=
  | grndty: type
  | uty   : type
  | prodty: type -> type -> type
  | funty : type -> type -> type
  | T     : type -> type.

Fixpoint type_eqb (t1 t2: type): bool :=
  match t1, t2 with
    | grndty, grndty => true
    | uty, uty => true
    | funty a1 a2, funty b1 b2 => type_eqb a1 b1 && type_eqb a2 b2
    | prodty a1 a2, prodty b1 b2 => type_eqb a1 b1 && type_eqb a2 b2
    | T a, T b => type_eqb a b
    | _, _ => false
  end.

Inductive term: Type :=
  | consttrm: type -> nat -> term
  | vartrm  : string -> term
  | utrm    : term
  | pairtrm : term -> term -> term
  | fsttrm  : term -> term
  | sndtrm  : term -> term
  | abstrm  : string -> type -> term -> term
  | apptrm  : term -> term -> term
  (** additional terms of Computational Lambda Calculus (CLC)*)
  | ret     : term -> term
  | do      : string -> term -> term -> term.

Definition con := list (string * type)%type.

Definition extend_con (c: con) (x: string) (t: type) :=
  (x, t) :: c.

Fixpoint lookup {A: Type} (c: list (string * A)) (s: string): option A :=
  match c with
    | nil => None
    | (x, t) :: r => if String.eqb x s then Some t else (lookup r s)
  end.

Fixpoint isdom {A: Type} (c: list (string * A)) (s: string): bool :=
  match c with
    | nil => false
    | (x, t) :: r => if String.eqb x s then true else (isdom r s)
  end.

Inductive typing: list (string * type) -> term -> type -> Prop :=
  | varT1 : forall Gamma (A: type) x, NoDup (map fst Gamma) -> isdom Gamma x = false -> typing ((x, A) :: Gamma) (vartrm x) A
  | varT2 : forall Gamma (A A': type) x x', typing Gamma (vartrm x) A -> isdom Gamma x' = false -> typing ((x', A') :: Gamma) (vartrm x) A
  | constT: forall Gamma (A: type) n, NoDup (map fst Gamma) -> typing Gamma (consttrm A n) A
  | unitT : forall Gamma, NoDup (map fst Gamma) -> typing Gamma utrm uty
  | pairT : forall Gamma (A B: type) s t, typing Gamma s A -> typing Gamma t B -> typing Gamma (pairtrm s t) (prodty A B)
  | fstT  : forall Gamma (A B: type) t, typing Gamma t (prodty A B) -> typing Gamma (fsttrm t) A
  | sndT  : forall Gamma (A B: type) t, typing Gamma t (prodty A B) -> typing Gamma (sndtrm t) B
  | absT  : forall Gamma (A B: type) x t, typing ((x, A) :: Gamma) t B -> typing Gamma (abstrm x A t) (funty A B)
  | appT  : forall Gamma (A B: type) s t, typing Gamma s (funty A B) -> typing Gamma t A -> typing Gamma (apptrm s t) B
  (** additional typing rules for CLC terms *)
  | retT  : forall Gamma (A: type) t, typing Gamma t A -> typing Gamma (ret t) (T A)
  | doT   : forall Gamma (A B: type) x s t, typing Gamma s (T A) -> typing ((x, A) :: Gamma) t (T B) -> typing Gamma (do x s t) (T B).

Example stlc_typing_derivation: forall (A B C: type), 
  typing nil 
         (abstrm "f" (funty A B) (abstrm "g" (funty B C) (abstrm "x" A (apptrm (vartrm "g") (apptrm (vartrm "f") (vartrm "x"))))))
         (funty (funty A B) (funty (funty B C) (funty A C))).
Proof. intros A B C.
       apply absT.
       apply absT.
       apply absT.
       apply appT with (A := B).
       - apply varT2.
         + apply varT1.
          ++ simpl.
             apply NoDup_cons.
             * simpl. easy.
             * apply NoDup_nil.
          ++ simpl. reflexivity.
         + simpl. reflexivity.
       - apply appT with (A := A).
         + apply varT2.
           ++ apply varT2.
              * apply varT1.
                ** simpl. apply NoDup_nil.
                ** simpl. reflexivity.
              * simpl. reflexivity.
           ++ simpl. reflexivity.
         + apply varT1.
           ++ simpl. apply NoDup_cons.
              * simpl. unfold not.
                intros [ H | H].
                ** inversion H.
                ** easy.
              * apply NoDup_cons.
                ** simpl. easy.
                ** apply NoDup_nil.
           ++ simpl. reflexivity.
Qed.

Example CHIPLvsSTLC: forall (phi psi theta: type),
  typing (("y", funty phi psi) :: ("z", funty psi theta) :: nil)
         (abstrm "x" phi (apptrm (vartrm "z") (apptrm (vartrm "y") (vartrm "x"))))
         (funty phi theta).
Proof. intros.
       apply absT.
       apply appT with (A := psi).
       + apply varT2.
         ++ apply varT2.
            * apply varT1.
              ** simpl. apply NoDup_nil.
              ** simpl. reflexivity.
            * simpl. reflexivity.
         ++ simpl. reflexivity.
       + apply appT with (A := phi).
         ++ apply varT2.
            * apply varT1.
              ** simpl. apply NoDup_cons.
                 *** simpl. easy.
                 *** apply NoDup_nil.
              ** simpl. reflexivity.
            * simpl. reflexivity.
         ++ apply varT1.
            * simpl. apply NoDup_cons.
              ** simpl. unfold not. 
                 intros [H | H].
                 *** inversion H.
                 *** easy.
              ** apply NoDup_cons.
                 *** simpl. easy.
                 *** apply NoDup_nil. 
            * simpl. reflexivity.
Qed.

(** add "eval" (or equality) here *)

Fixpoint unique_help (l: list string) (n: string) :=
match l with
  | nil    => nil
  | h :: t => if String.eqb n h then unique_help t n else h :: (unique_help t n)
end.

Fixpoint unique (x: list string) :=
match x with
  | nil    => nil
  | h :: t => h :: (unique_help (unique t) h)
end.

Fixpoint vars (e: term) (l: list string): list string :=
  match e with
    | consttrm A n    => l
    | vartrm s        => s :: l
    | utrm            => l
    | pairtrm e1 e2   => unique (vars e1 l ++ vars e2 l)
    | fsttrm e        => unique (vars e l)
    | sndtrm e        => unique (vars e l)
    | abstrm x t e    => unique (x :: (vars e l))
    | apptrm t r      => unique (vars t l ++ vars r l)
    | ret e           => unique (vars e l)
    | do x s t        => unique (x :: (vars s l ++ vars t l))
  end.

Fixpoint fv_e (e: term) (l: list string): list string :=
  match e with
    | consttrm A n    => l
    | vartrm s        => s :: l
    | utrm            => l
    | pairtrm e1 e2   => unique (fv_e e1 l ++ fv_e e2 l)
    | fsttrm e        => unique (fv_e e l)
    | sndtrm e        => unique (fv_e e l)
    | abstrm x t e    => List.filter (fun a => negb (String.eqb a x)) (fv_e e l)
    | apptrm t r      => unique (fv_e t l ++ fv_e r l)
    | ret e           => unique (fv_e e l)
    | do x s t        => List.filter (fun a => negb (String.eqb a x)) (unique (fv_e s l ++ fv_e t l))
  end.

Definition fv (e: term) := fv_e e nil.

Definition allvars (e: term) := vars e nil.

Fixpoint replace (e: term) (x: string) (s: term): term :=
  match e with
    | vartrm v                   => if String.eqb v x then s else e
    | pairtrm t1 t2              => pairtrm (replace t1 x s) (replace t2 x s)
    | fsttrm t                   => fsttrm (replace t x s)
    | sndtrm t                   => sndtrm (replace t x s)
    | apptrm t1 t2               => apptrm (replace t1 x s) (replace t2 x s)
    | abstrm y A t               => if (Bool.eqb (String.eqb y x) false)
                                    then abstrm y A (replace t x s) 
                                    else abstrm x A (replace t x s) 
    | ret e                      => ret (replace e x s)
    | do y k t                   => if (Bool.eqb (String.eqb y x) false)
                                    then do y (replace k x s) (replace t x s) 
                                    else do x (replace k x s) (replace t x s) 
    | _                          => e
  end.

Definition repbound (e: term) (y: string): term :=
  match e with
    | abstrm x A t => abstrm y A (replace t x (vartrm y)) 
    | do x s t     => do y s (replace t x (vartrm y))
    | _            => e
  end.

Definition InB := 
fix InB (a: string) (l : list string) {struct l} : bool :=
  match l with
  | nil => false
  | b :: m => (String.eqb b a) || InB a m
  end.

Fixpoint alphac (t1 t2: term): bool :=
  match t1, t2 with
    | consttrm A n, consttrm B m   => if Nat.eqb n m && type_eqb A B then true else false
    | vartrm x, vartrm y           => String.eqb x y
    | utrm, utrm                   => true
    | pairtrm s t, pairtrm s' t'   => if alphac s s' && alphac t t' then true else false
    | fsttrm t, fsttrm t'          => alphac t t'
    | sndtrm t, sndtrm t'          => alphac t t'
    | abstrm x A t, abstrm x' B t' => if negb (String.eqb x x') && negb (InB x (fv t')) && type_eqb A B then
                                        let f := replace t' x' (vartrm x) in
                                        alphac t f
                                      else if (String.eqb x x') then
                                        alphac t t'
                                      else false
    | apptrm s t, apptrm s' t'     => if alphac s s' && alphac t t' then true else false
    | ret t, ret t'                => alphac t t'
    | do x s t, do x' s' t'        => if negb (String.eqb x x') && negb (InB x (fv t')) && alphac s s' then
                                        let f := replace t' x' (vartrm x) in
                                        alphac t f
                                      else if (String.eqb x x') && alphac s s' then
                                        alphac t t'
                                      else false
    | _,_                          => false
  end.

(* Compute repbound (abstrm "x" grndty (pairtrm (vartrm "x") (vartrm "y"))) "z".
Compute replace (abstrm "x" grndty (pairtrm (vartrm "x") (vartrm "y"))) "x" (vartrm "z").
Compute alphac (abstrm "x" grndty (pairtrm (vartrm "x") (vartrm "y"))) (abstrm "x" grndty (pairtrm (vartrm "x") (vartrm "y"))).
Compute alphac (abstrm "x" grndty (pairtrm (vartrm "x") (abstrm "y" grndty (vartrm "y")))) 
               (abstrm "z" grndty (pairtrm (vartrm "z") (abstrm "t" grndty (vartrm "t")))).
Compute alphac (abstrm "x" grndty (pairtrm (vartrm "x") (abstrm "y" grndty (vartrm "y")))) 
               (abstrm "z" grndty (pairtrm (vartrm "z") (abstrm "x" grndty (vartrm "x")))).
Compute alphac (apptrm (abstrm "y" grndty (vartrm "y")) (vartrm "x"))
               (apptrm (abstrm "x" grndty (vartrm "x")) (vartrm "x")). *)

Inductive alpha: term -> term -> Prop :=
  | constA: forall (A: type) n, alpha (consttrm A n) (consttrm A n)
  | varA  : forall x, alpha (vartrm x) (vartrm x)
  | unitA : alpha utrm utrm
  | pairA : forall s s' t t', alpha s s' -> alpha t t' -> alpha (pairtrm s t) (pairtrm s' t')
  | fstA  : forall t t', alpha t t' -> alpha (fsttrm t) (fsttrm t')
  | sndA  : forall t t', alpha t t' -> alpha (sndtrm t) (sndtrm t')
  | appA  : forall s s' t t', alpha s s' -> alpha t t' -> alpha (apptrm s t) (apptrm s' t')
  | absA  : forall (A: type) x x' t t' y, alpha (repbound (abstrm x A t) y) (repbound (abstrm x' A t') y) -> 
                                          String.eqb x  y = false  ->
                                          String.eqb x' y = false  ->
                                          ~ List.In y (fv t)  ->
                                          ~ List.In y (fv t') ->
                                          alpha (abstrm x A t) (abstrm x' A t')
  | retA  : forall t t', alpha t t' -> alpha (ret t) (ret t')
  | doA   : forall x s t x' s' t' y, alpha (repbound (do x s t) y) (repbound (do x' s' t') y) -> 
                                     alpha s s' ->
                                     String.eqb x  y = false  ->
                                     String.eqb x' y = false  ->
                                     ~ List.In y (fv s)  ->
                                     ~ List.In y (fv s') ->
                                     ~ List.In y (fv t)  ->
                                     ~ List.In y (fv t') ->
                                     alpha (do x s t) (do x' s' t').

Fixpoint subst (e: term) (x: string) (s: term): term :=
  match e with
    | vartrm v        => if String.eqb v x then s else e
    | pairtrm t1 t2   => pairtrm (subst t1 x s) (subst t2 x s)
    | fsttrm t        => fsttrm (subst t x s)
    | sndtrm t        => sndtrm (subst t x s)
    | apptrm t1 t2    => apptrm (subst t1 x s) (subst t2 x s)
    | abstrm y A t    => if (Bool.eqb (String.eqb y x) false) && negb (InB y (allvars s))
                         then abstrm y A (subst t x s) 
                         else e
    | ret e           => ret (subst e x s)
    | do y k t        => if (Bool.eqb (String.eqb y x) false) && negb (InB y (allvars s))
                         then do y (subst k x s) (subst t x s) 
                         else e
    | _               => e
  end.

Fixpoint substFV (e: term) (x: string) (s: term): term :=
  match e with
    | vartrm v        => if String.eqb v x then s else e
    | pairtrm t1 t2   => pairtrm (substFV t1 x s) (subst t2 x s)
    | fsttrm t        => fsttrm (substFV t x s)
    | sndtrm t        => sndtrm (substFV t x s)
    | apptrm t1 t2    => apptrm (substFV t1 x s) (substFV t2 x s)
    | abstrm y A t    => if (Bool.eqb (String.eqb y x) false) && negb (InB y (fv s))
                         then abstrm y A (substFV t x s) 
                         else e
    | ret e           => ret (substFV e x s)
    | do y k t        => if (Bool.eqb (String.eqb y x) false) && negb (InB y (fv s))
                         then do y (substFV k x s) (substFV t x s) 
                         else e
    | _               => e
  end.

(*
Eval compute in subst   (abstrm "y" grndty (pairtrm (vartrm "y") (vartrm "x"))) "x"  (vartrm "y").
Eval compute in repbound (abstrm "y" grndty (pairtrm (vartrm "y") (vartrm "x"))) "z".
Eval compute in subst   (repbound (abstrm "y" grndty (pairtrm (vartrm "y") (vartrm "x"))) "z") "x"  (vartrm "y").
Eval compute in subst   (abstrm "y" grndty (pairtrm (vartrm "y") (vartrm "x"))) "x" (abstrm "y" grndty (vartrm "y")).
Eval compute in substFV (abstrm "y" A (pairtrm (vartrm "y") (vartrm "x"))) "x" (abstrm "y" A (vartrm "y")). *)

Inductive betaeta: con -> type -> term -> term -> Prop :=
  | absB : forall Gamma (A B: type) x s t, typing ((x, A) :: Gamma) t B ->
                                           typing Gamma s A ->
                                           betaeta Gamma B (abstrm x A t) (subst t x s)
  | absE : forall Gamma (A B: type) x t, typing Gamma t (funty A B) ->
                                         ~List.In x (allvars t) ->
                                         betaeta Gamma (funty A B) t (abstrm x A t)
  | absC : forall Gamma (A B: type) x t t', betaeta ((x, A) :: Gamma) B t t' ->
                                            betaeta Gamma (funty A B) (abstrm x A t) (abstrm x A t') 
  | fstB : forall Gamma (A B: type) s t, typing Gamma s A ->
                                          typing Gamma t B ->
                                          betaeta Gamma A (fsttrm (pairtrm s t)) s
  | sndB : forall Gamma (A B: type) s t, typing Gamma s A ->
                                         typing Gamma t B ->
                                         betaeta Gamma A (sndtrm (pairtrm s t)) t
  | pairE: forall Gamma (A B: type) t, typing Gamma t (prodty A B) ->
                                       betaeta Gamma (prodty A B) t (pairtrm (fsttrm t) (sndtrm t))
  | unitE: forall Gamma t, typing Gamma t uty ->
                           betaeta Gamma uty t utrm
  | appC : forall Gamma (A B: type) s s' t t', betaeta Gamma (funty A B) s s' ->
                                               betaeta Gamma A t t' ->
                                               betaeta Gamma B (apptrm s t) (apptrm s' t')
  | beR  : forall Gamma (A: type) t, typing Gamma t A ->
                                     betaeta Gamma A t t
  | beS  : forall Gamma (A: type) s t, betaeta Gamma A s t ->
                                       betaeta Gamma A t s
  | beT  : forall Gamma (A: type) r s t, betaeta Gamma A r s ->
                                         betaeta Gamma A s t ->
                                         betaeta Gamma A r t
  | dr1  : forall Gamma (A B: type) x s t, typing Gamma s A ->
                                           typing ((x, A) :: Gamma) t (T B) ->
                                           betaeta Gamma (T B) (do x (ret s) t) (subst t x s)
  | dr2  : forall Gamma (A: type) x t, typing Gamma t (T A) ->
                                       betaeta Gamma (T A) t (do x t (ret (vartrm x)))
  | dr3  : forall Gamma (A B C: type) x y s t u, typing Gamma s (T A) ->
                                                 typing ((x, A) :: Gamma) t (T B) ->
                                                 typing ((y, B) :: Gamma) u (T C) ->
                                                 betaeta Gamma (T C) (do y (do x s t) u) (do x s (do y t u)).


Fixpoint recTy (C: isCCC) (l: list type) (M: type -> (@obj (@uc C))): (@obj (@uc C)) := 
  match l with
    | nil     => @tobj (@uc C) (@hasT (@uc C) (@uobs C))
    | x :: xs => @pobj (@uc C) (@hasP (@uc C) (@uobs C)) (M x) (recTy C xs M)
  end.

(* think about well-typed term representation in a CCC *)
(*
Parameters (G: con) (A: type) (x: string) (p1: NoDup (map fst G)) (p2: isdom G x = false).
Check varT1 G A x p1 p2.

 Fixpoint recTm (C: isCCC) 
               (c: con) (A: type) (t: term) 
               (p: typing c t A) 
               (MT: type -> (@obj (@uc C)))
               (MTL: con -> (@obj (@uc C))): (@arrow (@uc C) (MT A) (MTL c)) :=
  match p with
    | varT1 G B x p1 p2  => @pi2 (@uc C) 
                                 (MTL G) 
                                 (MT B) 
                                 (@pobj (@uc C) (@hasP (@uc C) (@uobs C)) (MTL G) (MT B))
                                 (@hasp (@uc C) (@hasP (@uc C) (@uobs C)) (MTL G) (MT B))
  end. *)

Class interpTT (C: isCCC) : Type :=
{
  MT  : type -> (@obj (@uc C));
  int1: { p: (@obj (@uc C)) | MT grndty = p };
  int2: MT uty = @tobj (@uc C) (@hasT (@uc C) (@uobs C));
  int3: forall (A B: type), MT (prodty A B) = @pobj (@uc C) (@hasP (@uc C) (@uobs C)) (MT A) (MT B);
  int4: forall (A B: type), MT (funty A B)  = @eobj (@uc C) (@hasP (@uc C) (@uobs C)) (@hasE (@uc C) (@uobs C)) (MT A) (MT B);
  MTL : con -> (@obj (@uc C));
  int5: forall (c: con), MTL c = recTy C (map snd c) MT;
  MTT : forall (c: con) (A: type) (t: term), typing c t A -> (@arrow (@uc C) (MT A) (MTL c));
(*
  int6: forall (c: con) (A: type) (x: string) (p1: NoDup (map fst c)) (p2: isdom c x = false), 
                   MTT ((x, A) :: c) A (vartrm x) (varT1 c A x p1 p2) = 
                   @pi2
*)
(*
                   @pi2 (@uc C) 
                                 (recTy C (map snd ((x, A) :: c)) MT)
                                 (MT A) 
                                 (@pobj (@uc C) (@hasP (@uc C) (@uobs C)) (recTy C (map snd ((x, A) :: c)) MT) (MT A))
                                 (@hasp (@uc C) (@hasP (@uc C) (@uobs C)) (recTy C (map snd ((x, A) :: c)) MT) (MT A))
*)
}.







