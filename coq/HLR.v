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
Inductive Term := 
  Lam  : Path -> nat -> Term -> Term
| App  : Path -> nat -> Term -> Term -> Term
| BVar : Path -> nat -> nat -> Term
| FVar : Path -> nat -> Term.

(* Some test cases *)
Definition IdT : Term.
  refine (Lam  [] 0 (BVar [U] 0 1)).
Defined.

Definition AppT : Term. 
  refine (
    Lam [] 0 (
      Lam [U] 1 (
        App [U; U] 2 
          (BVar [U;U;L] 2 1) 
          (BVar [U;U;R] 2 0)
      )
    )
  ).
Defined.

(* Auxilliary lemma *)
Lemma cons_to_app : forall (A : Set) (a : A) (l : list A), a::l = [a] ++ l.
Proof. auto. Qed.

Definition getpath : Term -> Path.
  refine (
      fun T =>
        match T with
          | Lam  p _ _   => p
          | App  p _ _ _ => p
          | BVar p _ _   => p
          | FVar p _     => p
        end
    ).
Defined.

Definition getlamnum : Term -> nat.
  refine (
      fun T =>
        match T with
          | Lam  _ l _   => l
          | App  _ l _ _ => l
          | BVar _ l _   => l
          | FVar _ l     => l
        end
    ).
Defined.

(*
Term -- an argument subterm
Path -- new path to the root
nat -- new root lambda bumber
nat -- old root lanbda number
 *)
Definition fixpaths :
  Term -> Path -> nat -> nat -> Term.
  refine(
      fix fixpaths' (T : Term) (P : Path) (l : nat) (li : nat) : Term :=
        match T with
          | Lam  _ _  t     => Lam P l (fixpaths' t (P++[U]) (l + 1) li)
          | App  _ _  t1 t2 =>
            App  P l (fixpaths' t1 (P++[L]) l li) (fixpaths' t2 (P++[R]) l li)
          | BVar _ l' i     =>
            let i' := if (le_lt_dec i li) then i else l - l' + i
            in BVar P l i'
          | FVar _ _        => FVar P l
        end
    ).
Defined.

Definition example :Term.
  refine( Lam [U;R] 1 (
                App [U;R;U] 2 
                    (BVar [U;R;U;L] 2 2) 
                    (BVar [U;R;U;R] 2 1))).
Defined.

Eval compute in
    fixpaths
      example
      [U;L;L;U]
      2
      1.
(* Has to return
Lam [U; L; L; U] 2
    (App [U; L; L; U; U] 3 (BVar [U; L; L; U; U; L] 3 3)
         (BVar [U; L; L; U; U; R] 3 1))
 *)

(* Subterm: subterm t p returns a subterm of t, indexed by 
   (relative) path p; if the term does not exists, returns None
*)
Definition subterm : 
  Term -> Path -> option Term.
  refine (
      fun t0 P =>
        let fix subterm' (T : Term) (P : Path)
            : option Term :=
            match P with
              | []    => Some T
              | x::xs =>
                match x with
                  | U => match T with
                           | Lam p l t => subterm' t xs
                           | _ => None
                         end
                  | R => match T with
                           | App p l t1 t2 => subterm' t2 xs
                           | _ => None
                         end
                  | L => match T with
                           | App p l t1 t2 => subterm' t1 xs
                           | _ => None
                         end
                end
            end
        in subterm' t0 P
    ).
Defined.

Notation "A [ p ]" := (subterm A p) (at level 0).

Eval compute in example [ [U;U] ].
Eval compute in example [[U]].

Definition exampleC : Term.
  refine (
      Lam ([]) 0
          (App ([U]) 1
               (App ([U;L]) 1
                    (Lam ([U;L;L]) 1
                         (BVar ([U;L;L;U]) 2 1))
                    (Lam ([U;L;R]) 1
                         (BVar ([U;L;R;U]) 2 1))
               )
               (Lam ([U;R]) 1 (
                      App ([U;R;U]) 2 
                          (BVar ([U;R;U;L]) 2 2) 
                          (BVar ([U;R;U;R]) 2 1)))
               )
    ).
Defined.

Eval compute in subterm exampleC ([U;R]).
Eval compute in subterm exampleC ([U;L;L;U]).

Definition substsubterm : 
  Term -> Path -> Path -> option Term.
  refine (
      fun t p1 p2 =>
        let fix substsubterm' (T1 T2 : Term) (p2 p2' : Path) (n1 n2 : nat) : option Term :=
            match p2 with
              | []    =>
                match T1 with
                  | BVar _ _ _ => Some (fixpaths T2 p2' n1 n2)
                  | _          => None
                end
              | x::xs =>
                match x with
                  | U => match T1 with
                           | Lam p l t =>
                             let t' := substsubterm' t T2 xs p2' n1 n2
                             in match t' with
                                  | None    => None
                                  | Some t' => Some (Lam p l t')
                                end
                           | _ => None
                         end
                  | R => match T1 with
                           | App p l t1 t2 =>
                             let t2' := substsubterm' t2 T2 xs p2' n1 n2
                             in match t2' with
                                  | None     => None
                                  | Some t2' => Some (App p l t1 t2')
                                end
                           | _ => None
                         end
                  | L => match T1 with
                           | App p l t1 t2 =>
                             let t1' := substsubterm' t1 T2 xs p2' n1 n2
                             in match t1' with
                                  | None     => None
                                  | Some t1' => Some (App p l t1' t2)
                                end
                           | _ => None
                         end
                end
            end
        in let t' := t [p1]
           in let t'' := t [p2]
              in match t'' with
                   | None     => None
                   | Some t'' => 
                     match t' with
                       | None    => None
                       | Some t' => substsubterm' t t'' p1 p1 (getlamnum t') (getlamnum t'')
                     end
                 end
    ).
Defined.

Eval compute in substsubterm exampleC ([U;L;L;U]) ([U;R]).
(* Has to be equal to
Some
(Lam [] 0
     (App [U] 1
          (App [U; L] 1
               (Lam [U; L; L] 1
                    (Lam [U; L; L; U] 2
                         (App [U; L; L; U; U] 3 (BVar [U; L; L; U; U; L] 3 3)
                              (BVar [U; L; L; U; U; R] 3 1))))
               (Lam [U; L; R] 1 (BVar [U; L; R; U] 2 1)))
          (Lam [U; R] 1
               (App [U; R; U] 2 (BVar [U; R; U; L] 2 2)
                    (BVar [U; R; U; R] 2 1)))))
*)
Eval compute in substsubterm exampleC ([U;L;L]) ([U;R]).
Eval compute in substsubterm exampleC ([U;L;L;R]) ([U;R]).
Eval compute in substsubterm exampleC ([U;L;L;U]) ([U;R;R]).
(* None (for all 3 cases) *)


(** 
===========================================
Transition System for Head Linear Reduction
 ===========================================
*)

(* Context Gamma *)
Inductive Gamma : Type :=
 | EmptyGamma : Gamma
 | ConsGamma  : nat -> Path -> Gamma -> Gamma -> Gamma.

(* Incompelete Application List Delta *)
Inductive Delta : Type :=
| EmptyDelta : Delta
| ConsDelta  : Path -> Gamma -> Delta.

(* Term P l --- is an input term with indexed path *)
(* Gamma    --- is a current condext *)
(* Delta    --- is a current list of incomplete applications *)
Inductive HLRState :=
  HLRStateC : Term -> Path -> nat -> Gamma -> Delta -> HLRState.

Definition hlrStep :
  HLRState -> HLRState.
  refine (
      fun s =>
        match s with
          | HLRStateC t P l G D =>
            match t [P] with
              | Some e => HLRStateC t P l G D
              | None => s
            end

              
            (* match subterm P t with *)
            (*   | Some e => *)
            (*     match e with *)
            (*       | existT l1 t1 => *)
            (*         match t1 with *)
            (*           | App t1 t2 => HLRStateC t (P ++ [L]) G D *)
            (*           | _ => HLRStateC t ([U]) G D *)
            (*         end *)
            (*     end *)
            (*   | None => HLRStateC t ([]) G D *)
            (* end *)
            

            
        end).
Defined.
