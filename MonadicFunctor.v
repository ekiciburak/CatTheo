From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor 
NaturalTransformation Adjunction ParamKleisliTriple Monad Presheaf Yoneda IndexedCategories 
ComparisonK EilenbergMoore ComparisonEM.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import JMeq.

Set Universe Polymorphism.

Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.
Arguments Compose_Functors {_} {_} {_} _ _.
Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.
Arguments Compose_NaturalTransformations {_ _ _ _ _ } _ _.
Arguments Compose_NaturalTransformations_H {_ _ _ _ _ } _ _.

Arguments eta {_ _} _.
Arguments mu  {_ _} _.

Arguments unit {_ _ _ _} _.
Arguments counit {_ _ _ _} _.


Definition MonadicFucntor (C D: Category) (U: Functor D C) :=
 { F: Functor C D & 
   { A: Adjunction F U & 
       let M   := adj_mon F U A in
       let EMC := EilenbergMooreCategory M in
       let K   := KT F U A in
       CatEquivalenceA D EMC K
   } 
 }.
