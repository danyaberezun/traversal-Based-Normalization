Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Bool.

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

Definition AppT' : Term. 
  refine (
      Lam [] 0 (
            Lam [U] 1 (
                  App [U; U] 2 
                      (BVar [U;U;L] 2 0 _) 
                      (BVar [U;U;R] 2 0 _)
                )
          )
    ).
  omega. omega.
Defined.

Eval compute in AppT'.
Eval compute in AppT.

(* Auxilliary lemma *)
Lemma cons_to_app : forall (A : Set) (a : A) (l : list A), a::l = [a] ++ l.
Proof. auto. Qed.


(* Subterm: subterm t p returns a subterm of t, indexed by 
   (relative) path p; if the term does not exists, returns None
*)
Definition subterm : 
  forall {P : Path} {l : nat} (P' : Path),
  TermT P l -> option { l' : nat & TermT (P ++ P') l'}.
  refine (
      fix subterm' {P : Path} {l : nat} (P' : Path) {struct P'}
      : TermT P l -> option { l' : nat & TermT (P ++ P') l'} :=
        fun T =>
      match P' return option { l' : nat & TermT (P ++ P') l'} with
      | []   => Some _
      | x::p =>
          match x return option { l' : nat & TermT (P ++ x::p) l'} with
          | U => match T return option { l' : nat & TermT (P ++ U::p) l'} with
                 | Lam _ _ t => _
                 | _     => None
                 end
          | L => match T return option { l' : nat & TermT (P ++ L::p) l'} with
                 | App _ _ t _ => _
                 | _       => None
                 end
          | R => match T return option { l' : nat & TermT (P ++ R::p) l'} with
                 | App _ _ _ t => _
                 | _       => None
                 end
        end
  end).
  exists l. rewrite app_nil_r. apply T.
  apply (subterm' (P++[U]) (S l) p) in t. rewrite <- app_assoc in t. assumption.
  apply (subterm' (P++[R])  l    p) in t; rewrite <- app_assoc in t; assumption.
  apply (subterm' (P++[L])  l    p) in t; rewrite <- app_assoc in t; assumption.
Defined.

Notation "A [| p |]" := (subterm p A) (at level 0).

Print subterm.
Check subterm.
Eval compute in (AppT) [| [U;U] |].
Eval compute in (AppT) [|[]|].
Eval compute in ((AppT) [|[]|] : option {l' : nat & TermT [] l'}).
Eval cbv in (((AppT) [|[]|] : option {l' : nat & TermT [] l'})).

Require Import Coq.Program.Equality.

Theorem AppTEq :
  ((AppT) [|[]|] : option {l' : nat & TermT ([]) l'}) =
  Some (existT (fun x => TermT [] x) 0 AppT).
Proof. simpl_eq; auto. Qed.

Theorem PE :
  option {l' : nat & TermT ([] ++ []) l'} = option {l' : nat & TermT ([]) l'}.
Proof. reflexivity. Qed.

Theorem TEq:
  forall T : Term,
    (T [|[]|] : option {l' : nat & TermT [] l'}) =
    Some (existT (fun x => TermT [] x) 0 T).
Proof. simpl_eq; auto. Qed.

Definition laminPath :
  Path -> nat.
  refine(fix laminPath' (p : Path) : nat :=
           match p with
             | [] => 0
             | U :: ps => 1 + laminPath' ps
             | _ :: ps => laminPath' ps
           end
        ).
Defined.

Definition fixpath :
  forall {P : Path} {l : nat} (P' : Path) (l' : nat),
    TermT P l -> l' >= l ->TermT P' l'.
  refine(
      fun P l P' l' t EQ =>
        let fix fixpath' {P : Path} {l : nat} (t : TermT P l) (l' : nat) (P' : Path) (pr : l' >= l)
            : TermT P' l' :=
            match t with
              | Lam _ _ t     => Lam P' l' (fixpath' t (S l') (P' ++ [U]) _)
              | App _ _ t1 t2 => App P' l' (fixpath' t1 l' (P' ++ [L]) pr) (fixpath' t1 l' (P' ++ [R]) _)
              | BVar _ _ n eq => BVar P' l' n _
              | FVar _ _ n    => FVar P' l' n
            end
        in fixpath' t l' P' EQ
    ).
  omega.
  omega.
  omega.
Defined.

Definition lamFromPath :
  Path -> nat.
  refine (fix lamFromPath' (P : Path) : nat :=
            match P with
              | [] => 0
              | x :: xs => let l := (lamFromPath' xs)
                           in match x with
                                | U => S l
                                | _ => l
                              end
            end
         ).
Defined.

Definition eqq : Role -> Role -> bool.
  refine (
      fun r1 r2 => match r1 with
                     | U => match r2 with
                              | U => true
                              | _ => false
                            end
                     | L => match r2 with
                              | L => true
                              | _ => false
                            end
                     | R => match r2 with
                              | R => true
                              | _ => false
                            end
                   end
    ).
Defined.

Definition substsubterm1 :
  forall {p p1 : Path} {l l1 : nat}
                           (p1' : Path)
                           (t : TermT p l)
                           (T : TermT p1 l1)
                           (eq : l >= l1),
            option (TermT p l).
  refine(
      fix substsubterm' {p p1: Path} {l l1 : nat}
                           (p1' : Path)
                           (t : TermT p l)
                           (T : TermT p1 l1)
                           (eq : l >= l1)
            : option (TermT p l) :=
            match p1' with
              | [] => Some (fixpath p l T _)
              | x :: xs => match x with
                             | U => match t with
                                      | Lam _ _ t => match substsubterm' xs t T _ with
                                                       | None => None
                                                       | Some t => Some (Lam p l t)
                                                     end
                                      | _ => None
                                    end
                             | L => match t with
                                      | App _ _ t1 t2 => match substsubterm' xs t1 T _ with
                                                       | None => None
                                                       | Some t1 => Some (App p l t1 t2)
                                                         end
                                      | _ => None
                                    end
                             | R => match t with
                                      | App _ _ t1 t2 => match substsubterm' xs t2 T _ with
                                                       | None => None
                                                       | Some t2 => Some (App p l t1 t2)
                                                         end
                                      | _ => None
                                    end
                           end
            end
    ).
  omega.
  omega.
  omega.
  omega.
Defined.

Definition substsubterm :
  forall {P : Path} {l : nat} (p1 p2 : Path),
  TermT P l -> option (TermT P l).
  refine(
      fun P l p1 p2 t =>
        let fix substsubterm' {p : Path} {l : nat}
                (p1' p2' : Path)
                (t : TermT p l)
            : option (TermT p l) :=
            match p2' with
              | [] => None
              | [R] => match p1' with
                         | L :: ys => match t with
                                        | App _ _ t1 t2 => match substsubterm1 ys t1 t2 _ with
                                                             | None => None
                                                             | Some t1 => Some (App p l t1 t2)
                                                           end
                                        | _ => None
                                      end
                         | _ => None
                       end
              | [L] => None
              | [U] => None
              | x :: xs => match p1' with
                             | [] => None
                             | y :: ys => match eqq x y with
                                            | true => match x with
                                                 | U => match t with
                                                          | Lam _ _ t' => match (substsubterm' xs ys t') with
                                                                            | None => None
                                                                            | Some t' => Some (Lam p l t')
                                                                          end
                                                          | _ => None
                                                        end
                                                 | L =>  match t with
                                                          | App _ _ t' t'' => match (substsubterm' xs ys t') with
                                                                                | None => None
                                                                                | Some t' => Some (App p l t' t'')
                                                                              end
                                                          | _ => None
                                                        end
                                                 | R =>  match t with
                                                           | App _ _ t' t'' => match (substsubterm' xs ys t'') with
                                                                                 | None => None
                                                                                 | Some t'' => Some (App p l t' t'')
                                                                               end
                                                          | _ => None
                                                         end
                                                         end
                                            | false => None
                                          end
                           end
            end
        in substsubterm' p1 p2 t
    ).
  auto.   
Defined.

Eval compute in AppT.
Eval compute in substsubterm [U;U;L] [U;U;R] AppT.

Definition TermTEquality :
  forall {P : Path} {l : nat},
    TermT P l -> TermT P l -> bool.
  refine(
      fix eq {P : Path} {l : nat}
          (t1 t2 : TermT P l)
      : bool :=
        match t1 with
          | Lam _ _ t1 => match t2 with
                            | Lam _ _ t2 => eq t1 t2
                            | _ => false
                          end
          | App  _ _ t1' t1'' => match t2 with
                            | App _ _ t2' t2'' => eq t1' t2' && eq t1'' t2''
                            | _ => false
                          end
          | BVar _ _ n _ => match t2 with
                            | BVar _ _ m _ => beq_nat m n
                            | _ => false
                          end
          | FVar _ _ n => match t2 with
                            | FVar _ _ m => beq_nat m n
                            | _ => false
                          end
        end
    ).
Defined.

Definition OptionTermTEquality :
  forall {P : Path} {l : nat},
    option (TermT P l) -> option (TermT P l) -> bool.
  refine(
      fix eq  {P : Path} {l : nat}
          (t1 t2 : option (TermT P l))
      : bool :=
        match t1 with
          | None => match t2 with
                      | None => true
                      | _ => false
                    end
          | Some t1 => match t2 with
                      | None => false
                      | Some t2 => TermTEquality t1 t2
                    end
        end
    ).
Defined.

Eval cbv in  OptionTermTEquality (substsubterm [U;U;L] [U;U;R] AppT) (Some AppT').
Eval compute in AppT'. Eval compute in AppT.

Theorem substExample :
  OptionTermTEquality (substsubterm ([U;U;L]) ([U;U;R]) AppT) (Some AppT') = true.
Proof.
  unfold substsubterm; unfold substsubterm1; unfold fixpath; unfold eqq;  simpl_eq; auto.
Qed.

(* Theorem substExample' : *)
(*   substsubterm ([U;U;L]) ([U;U;R]) AppT = Some (AppT'). *)
(* Proof. *)
(*   unfold substsubterm; unfold substsubterm1; unfold fixpath; unfold eqq.  simpl_eq. *)
(*   (* How to unfold AppT'  *) *)
(*   Admitted. *)
(* Qed. *)


