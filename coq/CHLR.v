Require Import List.
Import ListNotations.

(* Role of a subtree w.r.t. its parent node: whether
   it its unique descendant (U), right (R) or left (L)
*)
Inductive Role := U | R | L.

(* A path from the root of the tree to a given node
   is represented as a list of "turns" (roles)
*)
Definition Path := list Role.

(* A term tree is a tree with each node indexed by
   a path
*)
Inductive TermT (P : Path) := 
  Lam  : TermT (P++[U]) -> TermT P
| App  : TermT (P++[L]) -> TermT (P++[R]) -> TermT P
| BVar : Path -> TermT P
| FVar : nat  -> TermT P.

(* A term is a tree with the root indexed by empty
   path
*)
Definition Term := TermT [].

(* Some test cases *)
Definition IdT  : Term := Lam [] (BVar [U] []).
Definition AppT : Term := Lam [] (Lam [U] (App [U; U] (BVar [U;U;L] []) (BVar [U;U;R] [U]))).

Lemma cons_to_app : forall (A : Set) (a : A) (l : list A), a::l = [a] ++ l.
Proof.
  intros A a l. reflexivity.
Qed.

Definition subterm : forall (P P' : Path), TermT P -> option (TermT (P ++ P')).
  refine (
    fix subterm' (P P' : Path) {struct P'} : TermT P -> option (TermT (P ++ P')) := fun T =>
      match P' return option (TermT (P ++ P')) with
      | []   => Some _
      | x::p =>           
          match x return option (TermT (P ++ x::p)) with
          | U => match T return option (TermT (P ++ U::p)) with
                 | Lam t => _
                 | _     => None
                 end 
          | L => match T return option (TermT (P ++ L::p)) with
                 | App t _ => _
                 | _       => None
                 end 
          | R => match T return option (TermT (P ++ R::p)) with
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
