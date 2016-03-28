Require Import List.
Import ListNotations.
Require Import Omega.


(* Role of a subtree w.r.t. its parent node: whether
   it its unique descendant (U), right (R) or left (L)
*)
Inductive Role := U | R | L.

(* A path from the root of the tree to a given node
   is represented as a list of "turns" (roles)
*)
Definition Path := list Role.

(* A term tree is a tree with each node indexed by
   a path and number of enclosing lambdas
*)
Inductive TermT (P : Path) (l : nat) := 
  Lam  : TermT (P++[U]) (S l) -> TermT P l
| App  : TermT (P++[L]) l -> TermT (P++[R]) l -> TermT P l
| BVar : forall (n : nat), n < l -> TermT P l
| FVar : nat -> TermT P l.

(* A term is a tree with the root indexed by empty
   path and zero number of enclosed lambdas
*)
Definition Term := TermT [] 0.

(* Some test cases *)
Definition IdT  : Term.
  refine (Lam [] 0 (BVar [U] 1 0 _)). 
  omega.
Defined.

Definition AppT : Term. 
  refine (
    Lam [] 0 (
      Lam [U] 1 (
        App [U; U] 2 
          (BVar [U;U;L] 2 1 _) 
          (BVar [U;U;R] 2 0 _)
      )
    )
  ).
  omega. omega.
Defined.

(* Auxilliary lemma *)
Lemma cons_to_app : forall (A : Set) (a : A) (l : list A), a::l = [a] ++ l.
Proof.
  intros A a l. reflexivity.
Qed.

(* Subterm: subterm t p returns a subterm of t, indexed by 
   (relative) path p; if the term does not exists, returns None
*)
Definition subterm : 
  forall {P : Path} {l : nat} (P' : Path), 
  TermT P l -> option { l' : nat & TermT (P ++ P') l'}.
  refine (
    fix subterm' {P : Path} {l : nat} (P' : Path) {struct P'} : TermT P l -> option { l' : nat & TermT (P ++ P') l'} := fun T =>
      match P' return option { l' : nat & TermT (P ++ P') l'} with
      | []   => Some _
      | x::p =>           
          match x return option { l' : nat & TermT (P ++ x::p) l'} with
          | U => match T return option { l' : nat & TermT (P ++ U::p) l'} with
                 | Lam t => _
                 | _     => None
                 end 
          | L => match T return option { l' : nat & TermT (P ++ L::p) l'} with
                 | App t _ => _
                 | _       => None
                 end 
          | R => match T return option { l' : nat & TermT (P ++ R::p) l'} with
                 | App _ t => _
                 | _       => None
                 end 
        end  
      end). 
  rewrite app_nil_r. exists l. exact T.  
  apply (subterm' (P++[U]) (S l) p) in t. rewrite cons_to_app. rewrite app_assoc. assumption.
  apply (subterm' (P++[R])  l    p) in t. rewrite cons_to_app. rewrite app_assoc. assumption.  
  apply (subterm' (P++[L])  l    p) in t. rewrite cons_to_app. rewrite app_assoc. assumption.
Defined.

Notation "A [ p ]" := (subterm p A) (at level 0).
