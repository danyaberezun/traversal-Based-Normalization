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
   path
*)
Definition Term := TermT [] 0.

(* Some test cases *)
Definition IdT  : Term.
  refine (Lam [] 0 (BVar [U] 1 0 _)). 
  omega.
Defined.

Definition AppT : Term. 
  refine (Lam [] 0 (Lam [U] 1 (App [U; U] 2 (BVar [U;U;L] 2 1 _) (BVar [U;U;R] 2 0 _)))).
  omega. omega.
Defined.

Lemma cons_to_app : forall (A : Set) (a : A) (l : list A), a::l = [a] ++ l.
Proof.
  intros A a l. reflexivity.
Qed.

Definition subterm : forall (P P' : Path) (l : nat), TermT P l -> option (TermT (P ++ P') l').
  refine (
    fix subterm' (P P' : Path) 
                 (l : nat ) {struct P'} : TermT P l -> exists l', option (TermT (P ++ P') l') := fun T =>
      match P' return exists l', option (TermT (P ++ P') l') with
      | []   => Some _
      | x::p =>           
          match x return exists l', option (TermT (P ++ x::p) l') with
          | U => match T return exists l', option (TermT (P ++ U::p) l') with
                 | Lam t => _
                 | _     => None
                 end 
          | L => match T return exists l', option (TermT (P ++ L::p) l') with
                 | App t _ => _
                 | _       => None
                 end 
          | R => match T return exists l', option (TermT (P ++ R::p) l') with
                 | App _ t => _
                 | _       => None
                 end 
        end  
      end). 
  rewrite app_nil_r. exact T.
  intros.
    apply (subterm' (P++[U]) p) in t. rewrite cons_to_app. rewrite app_assoc. assumption.
    apply (subterm' (P++[R]) p) in t. rewrite cons_to_app. rewrite app_assoc. assumption.  
    apply (subterm' (P++[L]) p) in t. rewrite cons_to_app. rewrite app_assoc. assumption.
Defined.

Definition subpath (A B : Path) : Prop := 
  exists (A' : Path), A' ++ A = B /\ length A' > 0.
