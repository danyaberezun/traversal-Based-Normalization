Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Bool.
Require Import Coq.Program.Equality.
Set Asymmetric Patterns.

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
    ); omega.
Defined.

Definition exampleC : Term. 
  refine (
      Lam [] 0
          (App [U] 1
               (Lam [U;L] 1
                    (App [U;L;U] 2
                         (BVar [U;L;U;L] 2 0 _)
                         (Lam [U;L;U;R] 2 (BVar [U;L;U;R;U] 3 0 _))
                    )
               )
               (Lam [U;R] 1
                    (App [U;R;U] 2
                         (BVar [U;R;U;L] 2 1 _)
                         (BVar [U;R;U;R] 2 0 _)
                    )
               )
          )
    ); omega.
Defined.

Eval compute in AppT.
Eval compute in AppT'.
Eval compute in exampleC.

(* Auxilliary lemma *)
Lemma cons_to_app : forall (A : Set) (a : A) (l : list A), a::l = [a] ++ l.
Proof. auto. Qed.

(* Subterm: subterm t p returns a subterm of t, indexed by 
   (relative) path p; if the term does not exists, returns None
*)
(* Definition subterm :  *)
(*   forall {P : Path} {l : nat} (P' : Path), *)
(*   TermT P l -> option { l' : nat & TermT (P ++ P') l'}. *)
(*   refine ( *)
(*       fix subterm' {P : Path} {l : nat} (P' : Path) {struct P'} *)
(*       : TermT P l -> option { l' : nat & TermT (P ++ P') l'} := *)
(*         fun T => *)
(*       match P' return option { l' : nat & TermT (P ++ P') l'} with *)
(*       | []   => Some _ *)
(*       | x::p => *)
(*           match x return option { l' : nat & TermT (P ++ x::p) l'} with *)
(*           | U => match T return option { l' : nat & TermT (P ++ U::p) l'} with *)
(*                  | Lam t => _ *)
(*                  | _     => None *)
(*                  end *)
(*           | L => match T return option { l' : nat & TermT (P ++ L::p) l'} with *)
(*                  | App t _ => _ *)
(*                  | _       => None *)
(*                  end *)
(*           | R => match T return option { l' : nat & TermT (P ++ R::p) l'} with *)
(*                  | App _ t => _ *)
(*                  | _       => None *)
(*                  end *)
(*         end *)
(*   end). *)
(*   exists l; rewrite app_nil_r; apply T. *)
(*   apply (subterm' (P++[U]) (S l) p) in t. rewrite <- app_assoc in t. assumption. *)
(*   apply (subterm' (P++[R])  l    p) in t; rewrite <- app_assoc in t; assumption. *)
(*   apply (subterm' (P++[L])  l    p) in t; rewrite <- app_assoc in t; assumption. *)
(* Defined. *)

Definition subterm : 
  forall {P P2 : Path} {l : nat} (P' : Path),
    TermT P l -> P2 = P ++ P' -> option { l' : nat & TermT P2 l'}.
  refine (
      fix subterm' {P P2 : Path} {l : nat} (P' : Path) {struct P'}
      : TermT P l -> P2 = P ++ P'  -> option { l' : nat & TermT P2 l'} :=
        fun T EQ => _
    ).
  induction P'.
  apply Some; exists l; rewrite app_nil_r in EQ; rewrite EQ; assumption.
  destruct a.
  - destruct T.
    apply (subterm' (P++[U]) P2 (S l) P') in T; [auto | rewrite <- app_assoc];  assumption.
    apply None.
    apply None.
    apply None.
  - destruct T.
    apply None.
    apply (subterm' (P++[R]) P2 l P') in T2; [auto | rewrite <- app_assoc];  assumption.
    apply None.
    apply None.
  - destruct T.
    apply None.
    apply (subterm' (P++[L]) P2 l P') in T1; [auto | rewrite <- app_assoc];  assumption.
    apply None.
    apply None.
Defined.

Notation "A [| p |] l1" := (subterm p A l1) (at level 0).

Lemma l1 : [U;U] = [U;U] ++ []. auto. Qed.
Eval compute in AppT [| [U;U] |] l1.

(* fixpath : by a given P' : Path, l' : nat, and t : TermT P l 
  returns a TermT P' l' that is a same "term" with a new
  path and lambda counter.
  This function will be user futher in linear substitution
*)
Definition fixpath :
  forall {P : Path} {l : nat} (P' : Path) (l' ll: nat),
    TermT P l -> l' >= l ->TermT P' l'.
  refine(
      fun P l P' l' ll t EQ =>
        let fix fixpath' {P : Path} {l : nat} (t : TermT P l) (l' : nat) (P' : Path) (pr : l' >= l) (ll : nat)
            : TermT P' l' :=
            match t with
              | Lam t        => Lam P' l' (fixpath' t (S l') (P' ++ [U]) _ ll)
              | App t1 t2 => App P' l' (fixpath' t1 l' (P' ++ [L]) pr ll ) (fixpath' t2 l' (P' ++ [R]) _ ll)
              | BVar n eq => match n <? ll with
                               | true => BVar P' l' 0 _
                               | false => BVar P' l' (l' - l + n) _
                             end
              | FVar n    => FVar P' l' n
            end
        in fixpath' t l' P' EQ ll
    ); omega.
Defined.

(* lamInPath : is an auxiliary function that returns a number of
  lambda nodes in a given path
*)
Fixpoint lamInPath (P : Path) : nat :=
  match P with
    | [] => 0
    | x :: xs => let l := (lamInPath xs)
                 in match x with
                      | U => S l
                      | _ => l
                    end
  end.

(* An equality function for Role *)
Definition eqq (r1 r2 : Role) : bool :=
  match r1 with
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
  end.

(* An auxiliary funciton for linearSubstitution function *)
Definition linearSubstitution1 :
  forall {p p1 : Path} {l l1 : nat}
                           (p1' : Path)
                           (t : TermT p l)
                           (T : TermT p1 l1)
                           (eq : l >= l1)
                           (ll : nat),
            option (TermT p l).
  refine(
      fix linearSubstitution' {p p1: Path} {l l1 : nat}
          (p1' : Path)
          (t : TermT p l)
          (T : TermT p1 l1)
          (eq : l >= l1)
          (ll : nat)
      : option (TermT p l) :=
        match p1' with
          | [] => match t with
                    (* check : we replace BVar *)
                    (* check : we substitudes the correct variable : i.e. ll == i+1 *)
                    | BVar i _ => if beq_nat ll (i+1)
                                  then Some (fixpath p l ll T _)
                                  else None
                    (* | BVar i _ => Some (fixpath p l ll T _) *)
                    | _ => None
                  end
          | x :: xs => match x with
                         | U => match t with
                                  | Lam t => match linearSubstitution' xs t T _ ll with
                                               | None => None
                                               | Some t => Some (Lam p l t)
                                             end
                                  | _ => None
                                end
                         | L => match t with
                                  | App t1 t2 => match linearSubstitution' xs t1 T _ ll with
                                                   | None => None
                                                   | Some t1 => Some (App p l t1 t2) 
                                                 end
                                  | _ => None
                                end
                         | R => match t with
                                  | App t1 t2 => match linearSubstitution' xs t2 T _ ll with
                                                   | None => None
                                                   | Some t2 => Some (App p l t1 t2)
                                                 end
                                  | _ => None
                                end
                       end
        end
    ); omega.
Defined.

(* linearSubstitution : is a function that performs a linear substitution.
  p1 is path to the BVar to be replaced by the subtree indexed by the path p2
 *)
Definition linearSubstitution :
  forall {P : Path} {l : nat} (p1 p2 : Path),
  TermT P l -> option (TermT P l).
  refine(
      fun P l p1 p2 t =>
        let fix linearSubstitution' {p : Path} {l : nat}
                (p1' p2' : Path)
                (t : TermT p l)
            : option (TermT p l) :=
            match p2' with
              | [] => None
              | [R] => match p1' with
                         | L :: ys => match t with
                                        | App t1 t2 => match linearSubstitution1 ys t1 t2 _ l with
                                                         | None => None
                                                         | Some t1 => Some (App p l t1 t2)
                                                       end
                                        | _ => None
                                      end
                         | _ => None
                       end
              | [_] => None
              | x :: xs =>
                match p1' with
                  | [] => None
                  | y :: ys => match eqq x y with
                                 | true => match x with
                                             | U => match t with
                                                      | Lam t' => match linearSubstitution' ys xs t' with
                                                                    | None => None
                                                                    | Some t' => Some (Lam p l t')
                                                                  end
                                                      | _ => None
                                                    end
                                             | L =>  match t with
                                                       | App t' t'' => match linearSubstitution' ys xs t' with
                                                                         | None => None
                                                                         | Some t' => Some (App p l t' t'')
                                                                       end
                                                       | _ => None
                                                     end
                                             | R =>  match t with
                                                       | App t' t'' => match linearSubstitution' ys xs t'' with
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
        in linearSubstitution' p1 p2 t
    ); auto.   
Defined.

Notation "T [| p1 --> p2 |]" := (linearSubstitution p1 p2 T) (at level 0).

(* An equality function for TermT *)
Fixpoint TermTEquality {P : Path} {l : nat} (t1 t2 : TermT P l) : bool :=
  match t1 with
    | Lam t1 => match t2 with
                  | Lam t2 =>  TermTEquality t1 t2
                  | _ => false
                end
    | App t1' t1'' => match t2 with
                        | App t2' t2'' => TermTEquality t1' t2' && TermTEquality t1'' t2''
                        | _ => false
                      end
    | BVar n _ => match t2 with
                    | BVar m _ => beq_nat m n
                    | _ => false
                  end
    | FVar n => match t2 with
                  | FVar m => beq_nat m n
                  | _ => false
                end
  end.

(* An equality function for option TermT *)
Definition OptionTermTEquality {P : Path} {l : nat} (t1 t2 : option (TermT P l)) : bool :=
  match t1 with
    | None => match t2 with
                | None => true
                | _ => false
              end
    | Some t1 => match t2 with
                   | None => false
                   | Some t2 => TermTEquality t1 t2
                 end
  end.

Example otpe : OptionTermTEquality (AppT [| [U;U;L] --> [U;U;R] |]) (Some AppT') = true. auto. Qed.

Definition exampleC' : Term.
  refine(
      Lam [] 0
          (App [U] 1
               (Lam [U;L] 1
                    (App [U;L;U] 2
                         (Lam [U;L;U;L] 2
                              (App [U;L;U;L;U] 3
                                   (BVar [U;L;U;L;U;L] 3 2 _)
                                   (BVar [U;L;U;L;U;R] 3 0 _)))
                         (Lam [U;L;U;R] 2 (BVar [U;L;U;R;U] 3 0 _))))
               (Lam [U;R] 1
                    (App [U;R;U] 2
                         (BVar [U;R;U;L] 2 1 _)
                         (BVar [U;R;U;R] 2 0 _))))
    ); omega.
Defined.

Example exampleCULLUandUR :
  OptionTermTEquality (exampleC [| [U;L;U;L] --> [U;R] |]) (Some exampleC') = true.
repeat simpl_eq; auto. Qed.

Example exampleCULLUandULUR :
  exampleC [| [U;L;U;L] --> [U;L;U;R] |] = None.
repeat simpl_eq; auto. Qed.

Example exampleCULLandUR :
   exampleC [| [U;L;L;U] --> [U;R;R] |] = None.
simpl_eq; auto. Qed.


(**
===========================================
  Transition System for Head Linear Reduction
 ===========================================
**)

(* Context Gamma *)
Inductive Gamma : Type :=
| EmptyGamma : Gamma
(* index (variable) -> argument term -> argument context -> rest of the list *)
| ConsGamma  : nat -> Path -> Gamma -> Gamma -> Gamma.

(* Incompelete Application List Delta *)
Inductive Delta : Type :=
| EmptyDelta : Delta
| ConsDelta  : Path -> Gamma -> Delta -> Delta.

(* Term P l --- is an input term with indexed path *)
(* Gamma    --- is a current condext *)
(* Delta    --- is a current list of incomplete applications *)
(* Inductive HLRState := *)
(* | HLRStateC : Term -> Path -> nat -> Gamma -> Delta -> HLRState *)
(* | HLRStuck  : HLRState -> HLRState. *)


TODO: fix all with respect to the new definition of subterm

Definition ValidPathLam {P : Path} {l : nat} (t : TermT P l) (p : Path) (l1 : nat)  :=
  exists t' : TermT (P ++ p) l1,
    Some (existT (fun x => TermT (P ++ p) x) l1 t') = t [|p|] 
.

Check ValidPathLam.


(* match t[|p|] with *)
  (*   | None => False *)
  (*   | Some (existT l' T') => l1 = l' *)
  (* end. *)

Inductive HLRState :=
| HLRStateC :
    forall (t : Term) (p : Path) (l : nat), ValidPathLam t p l
                                  -> Gamma -> Delta -> HLRState
| HLRStuck  : HLRState -> HLRState.

Definition containsGamma : Gamma -> nat -> option (prod Path Gamma).
  refine (
      fix containsDelta' (G : Gamma) (N : nat): option (prod Path Gamma) :=
        match G with
          | EmptyGamma => None
          | ConsGamma i p g Gs =>
            if (beq_nat i N)
            then Some (pair p g)
            else containsDelta' Gs N
        end
    ).
Defined.

Definition getpath : forall {P : Path} {l : nat}, TermT P l -> Path := fun P _ _  => P.

Definition getlamnum : forall {P : Path} {l : nat}, TermT P l -> nat := fun _ l _  => l.

Definition isLam {P : Path} {l : nat} (t : TermT P l)  :=
  exists t' : TermT (P ++ [U]) (S l), t = Lam P l t'.

Lemma ListTypes :
  forall (P p1 p2 : Path) (l : nat), TermT ((P ++ p1) ++ p2) l = TermT (P ++ p1 ++ p2) l.
Proof. intros; rewrite app_assoc; reflexivity. Qed.



Lemma subtermAss :
  forall {P : Path} {l : nat} (t : TermT P l) (p1 p2 : Path) (l1 l2: nat),
    (exists (t1 : TermT (P ++ p1) l1) (t2 : TermT ((P ++ p1) ++ p2) l2),
       Some (existT (fun x : nat => TermT (P ++ p1) x) l1 t1) = (t) [|p1|] /\ Some (existT (fun x : nat => TermT ((P ++ p1) ++ p2) x) l2 t2) = (t1) [|p2|])
    -> (exists t3 : TermT (P ++ p1 ++ p2) l2,
       Some (existT (fun x : nat => TermT (P ++ p1 ++ p2) x) l2 t3) = (t) [|p1 ++ p2|]).
Proof.
intros. inversion H as [t1 [t2 [H1 H2]]].

induction p2.
- assert (E : TermT (P ++ p1 ++ []) l2) by (rewrite app_assoc; assumption).
  exists E. 


  rewrite app_nil_r.
   rewrite <- app_nil_r.


clear H2.
rewrite <- app_assoc in t2.
exists t2.  



Qed.
  
Theorem ValidPathLamU :
  forall {P : Path} {l : nat} (t : TermT P l) (p : Path) (l1 : nat),
  (exists (t' : TermT (P ++ p) l1),
    Some (existT (fun x => TermT (P ++ p) x) l1 t') = t [| p |] /\ isLam t' )->
    exists (t'' : TermT (P ++ p ++ [U]) (S l1)),
      Some (existT (fun x => TermT (P ++ p ++ [U]) x) (S l1) t'') = t [| p ++ [U] |].
Proof.
  intros P l t p l1 H; inversion H as [t' [H1 H2]].
  unfold isLam in H2; inversion H2 as [T H3].
  assert (E : P ++ p ++ [U] = (P ++ p) ++ [U]) by (rewrite app_assoc; reflexivity).

  clear H3.
  rewrite <- E in T.
  exists T.
  

  
  rewrite <- ListTypes.
  ?????
  rewrite <- E in T.
  exists T.
  rewrite <- app_assoc.
  
Qed.
  
Definition hlrStep :
  HLRState -> HLRState.
  refine (
      fun s =>
        match s with
          | HLRStateC T P E L1 G D =>
            match T [| P |] with
                 | Some (existT l T') => match T' with
                                           | Lam  t =>
                                             match D with
                                               (* [Lam-Non-Elim] *)
                                               | EmptyDelta => HLRStateC T (P ++ [U]) (E + 1) _ G D
                                               (* [Lam-Elim] *)
                                               | ConsDelta px gx Ds =>
                                                 HLRStateC T (P ++ [U]) (l+1) _ (ConsGamma (getlamnum T') px gx G) Ds
                                             end
                                | App  t1 t2 => HLRStateC T (P ++ [L]) l _ G (ConsDelta (P ++ [R]) G D)
                                | BVar i _  =>
                                  (* check that i+1 <= l; otherwise do nothing *)
                                  (* TODO unnecessary: l > i by the definition*)
                                  if i <? l
                                  then match containsGamma G (l - i -1) with
                                         (* match containsGamma G index (l - i -1) with *)
                                         | None => HLRStuck s
                                         | Some (pair p g) =>
                                           match T [| P -->  p |] with
                                             | None => HLRStuck s
                                             (* BVar *)
                                             | Some T => HLRStateC T P l _ g D
                                           end
                                       end
                                  else HLRStuck s
                                | FVar _  => HLRStuck s
                              end
                 | None => HLRStuck s
               end
          | HLRStuck _ => s
        end).
  
  

Defined.

Definition exampleCInit : HLRState := HLRStateC exampleC ([]) 0 EmptyGamma EmptyDelta.

Fixpoint pathEq (xs ys : Path) : bool :=
  match xs with
    | [] => match ys with
              | [] => true
              | _ => false
            end
    | x :: xs => match ys with
                   | y :: ys => eqq x y && pathEq xs ys
                   | [] => false
                 end
  end.

Fixpoint gammaEq (g1 g2 : Gamma) : bool :=
  match g1 with
    | EmptyGamma => match g2 with
                      | EmptyGamma => true
                      | _ => false
                    end
    | ConsGamma l1 p1 g11 g12 => match g1 with
                                   | ConsGamma l2 p2  g21 g22 =>
                                     beq_nat l1 l2 && pathEq p1 p2 && gammaEq g11 g21 && gammaEq g12 g22
                                   | _ => false
                                 end
  end.

Fixpoint deltaEq (d1 d2 : Delta) : bool :=
  match d1 with
    | EmptyDelta => match d2 with
                      | EmptyDelta => true
                      | _ => false
                    end
    | ConsDelta p1 g1 d1 => match d2 with
                                   | ConsDelta p2 g2 d2 =>
                                     pathEq p1 p2 && gammaEq g1 g2 && deltaEq d1 d2
                                   | _ => false
                                 end
  end.

Fixpoint  hlrStateEq (s1 s2 : HLRState) : bool :=
  match s1 with
    | HLRStuck s1 => match s2 with
                       | HLRStuck s2 => hlrStateEq s1 s2
                       | _ => false
                     end
    | HLRStateC T1 P1 L1 G1 D1 => match s2 with
                                    | HLRStateC T2 P2 L2 G2 D2 =>
                                      TermTEquality T1 T2 && pathEq P1 P2 && beq_nat L1 L2 &&
                                             gammaEq G1 G2 && deltaEq D1 D2
                                    | _ => false
                                  end
  end.

Example exampleCIntS1 :
  hlrStateEq (hlrStep exampleCInit) (HLRStateC exampleC [U] 1 EmptyGamma EmptyDelta) = true.
simpl_eq; auto. Qed.

Example exampleCIntS2 :
  hlrStateEq (hlrStep (hlrStep exampleCInit))
             (HLRStateC exampleC [U; L] 1 EmptyGamma
                        (ConsDelta [U; R] EmptyGamma EmptyDelta)) = true.
repeat simpl_eq; auto. Qed.

Example exampleCIntS3 :
  hlrStateEq (hlrStep (hlrStep (hlrStep exampleCInit)))
             (HLRStateC exampleC [U; L; U] 2
                        (ConsGamma 1 [U; R] EmptyGamma EmptyGamma)
                        EmptyDelta)
  = true.
repeat simpl_eq; auto. Qed.

Example exampleCIntS4 :
  hlrStateEq (hlrStep (hlrStep (hlrStep (hlrStep exampleCInit))))
             (HLRStateC exampleC [U; L; U;L] 2
                        (ConsGamma 1 [U; R] EmptyGamma EmptyGamma)
                        (ConsDelta [U;L;U;R] (ConsGamma 1 [U; R] EmptyGamma EmptyGamma) EmptyDelta))
  = true.
repeat simpl_eq; auto. Qed.

(* Example exampleCIntS5 : *)
(*   hlrStateEq (hlrStep (hlrStep (hlrStep (hlrStep (hlrStep exampleCInit))))) *)
(*              (HLRStateC *)
(*                 (Lam [] 0 *)
(*                      (App [U] 1 *)
(*                           (Lam [U; L] 1 *)
(*                                (App [U; L;U] 2 *)
(*                                     (Lam [U; L; U; L] 2 *)
(*                                          (App [U; L; U; L; U] 3 *)
(*                                               (BVar [U; L; U; L; U; L] 3 2 *)
(*                                                     (Decidable.dec_not_not (3 <= 3) (dec_lt 2 3) *)
(*                                                                            (fun H : 3 <= 3 -> False => Zge_left 2 3 (proj1 (Nat2Z.inj_ge 2 3) (not_lt 2 3 H)) *)
(*                                                                                                                 eq_refl))) *)
(*                                               (BVar [U; L; U; L; U; R] 3 0 *)
(*                                                     (Decidable.dec_not_not (1 <= 3) (dec_lt 0 3) *)
(*                                                                            (fun H : 1 <= 3 -> False => Zge_left 0 3 (proj1 (Nat2Z.inj_ge 0 3) (not_lt 0 3 H)) *)
(*                                                                                                                 eq_refl))))) *)
(*                                     (Lam [U; L; U; R] 2 *)
(*                                          (BVar [U; L; U; R; U] 3 0 *)
(*                                                (Decidable.dec_not_not (1 <= 3) (dec_lt 0 3) *)
(*                                                                       (fun H : 1 <= 3 -> False => Zge_left 0 3 (proj1 (Nat2Z.inj_ge 0 3) (not_lt 0 3 H)) *)
(*                                                                                                            eq_refl)))))) *)
(*                           (Lam [U; R] 1 *)
(*                                (App [U; R; U] 2 *)
(*                                     (BVar [U; R; U; L] 2 1 *)
(*                                           (Decidable.dec_not_not (2 <= 2) (dec_lt 1 2) *)
(*                                                                  (fun H : 2 <= 2 -> False => Zge_left 1 2 (proj1 (Nat2Z.inj_ge 1 2) (not_lt 1 2 H)) eq_refl))) *)
(*                                     (BVar [U; R; U; R] 2 0 *)
(*                                           (Decidable.dec_not_not (1 <= 2) (dec_lt 0 2) *)
(*                                                                  (fun H : 1 <= 2 -> False => Zge_left 0 2 (proj1 (Nat2Z.inj_ge 0 2) (not_lt 0 2 H)) eq_refl))))))) *)
(*                 [U; L; U; L] *)
(*                 2 *)
(*                 EmptyGamma *)
(*                 (ConsDelta [U;L;U;R] (ConsGamma 1 [U; R] EmptyGamma EmptyGamma) EmptyDelta)) *)
(*   = true. *)
(* repeat simpl_eq; auto. Qed. *)

(**
=====================
  General substitution
=====================
**)

(* function substitution' is an auxiliary function that is used in function substitution  *)
Definition substitution' : forall {P P' : Path} {l l' : nat} (P1 : Path) (l1 : nat),
                         nat -> TermT P  l -> TermT P' l' ->
                         l > 0 -> l1 >= l' -> S l1 = l -> TermT P1 l1.
  refine (
      fix st' {P P' : Path} {l l' : nat} (P1 : Path) (l1 ll : nat) (t : TermT P  l ) (T : TermT P' l')
          (EQ0 : l > 0) (EQ1 : l1 >= l') (EQ2 : S l1 = l) : TermT P1 l1 :=
        match t with
          | Lam t => Lam P1 l1 (st' (P1 ++ [U]) (S l1) ll t T _ _ _)
          | App t1 t2 => App P1 l1(st'  (P1 ++ [L]) l1 ll t1 T _ _ _) (st' (P1 ++ [R]) l1 ll t2 T _ _ _)
          | FVar n => FVar P1 l1 n
          | BVar n _ => _
        end
    ); try omega.
  remember (lt_eq_lt_dec (l - ll - 1) n) as b eqn:E; destruct b as [[b1 | b2] | b3].
  - destruct l1.
    apply FVar;  apply n.
    apply (BVar P1 (S l1) (n-1)); omega.
  - apply (fixpath P1 l1 l' T EQ1).
  - apply (BVar P1 l1 n).
    assert (QQ : n <= l1 -1) by omega.
    assert (QW : forall p : nat, p + 1 - 1 = p) by  (intros; omega).
    omega.
Defined.

(* function substitution performs a general substitution.
   arguments: term and a path to the redex (to the argument of the redex)
 *)
Definition substitution : Term -> Path -> option Term.
  refine(
      let fix st {P : Path} {l : nat} (t : TermT P l) (p : Path) : option (TermT P l) :=
          match p with
            | [R] => match t with
                       | App (Lam t) T => Some (substitution' P l l t T _ _ _)
                       | _ => None
                     end
            | U :: p => match t with
                          | Lam t => match st t p with
                                       | Some t => Some (Lam P l t)
                                       | None => None
                                     end
                          | _ => None
                        end
            | L :: p => match t with
                          | App t t' => match st t p with
                                          | Some t => Some (App P l t t')
                                          | None => None
                                        end
                          | _ => None
                        end
            | R :: p => match t with
                          | App t' t => match st t p with
                                          | Some t => Some (App P l t' t)
                                          | None => None
                                        end
                          | _ => None
                        end
            | [] => None
          end
      in fun t p => st t p
    ); try omega.
Defined.

(* args:
  - term (куда подставляем)
  - argument (что подставляем)
  - index (???)
*)
Definition general_substitution : forall {P P1 : Path} {l l1 : nat},
                                    TermT P l -> TermT P1 l1 -> nat -> l >= l1 -> TermT P l.
  refine(
      fix st {P P1 : Path} {l l1 : nat} (t : TermT P l) (T : TermT P1 l1) (i : nat) (EQ : l >= l1) : TermT P l :=
          match t with
            | Lam t => Lam P l (st t T i _)
            | App t1 t2 => App P l (st t1 T i _) (st t2 T i _)
            | BVar n _ => if beq_nat (l - n - 1) i
                          then fixpath P l l T _
                          else t
            | FVar _ => t
          end
    ); try omega.
Defined.

(* Examples *)
Definition substex : Term. 
  refine (
      Lam [] 0 (BVar [U] 1 0 _)
    ); omega.
Defined.
Definition substex1 : TermT [U;R] 1. 
  refine (
      Lam [U;R] 1
          (App [U;R;U] 2
               (BVar [U;R;U;L] 2 1 _)
               (BVar [U;R;U;R] 2 0 _))
    ); omega.
Defined.
Definition substex2 : Term.
  refine (
      Lam [] 0
          (Lam [U] 1
               (App [U;U] 2
                    (BVar [U;U;L] 2 1 _)
                    (BVar [U;U;R] 2 0 _)
               )
          )
    ); omega.
Defined.
Example gs1 :
  TermTEquality (general_substitution substex substex1)
                (substex2)
                = true.








Notation "A {| p |}" := (substitution A p) (at level 0).

(* Examples *)
Definition substex : Term. 
  refine (
      Lam [] 0
          (App [U] 1
               (Lam [U;L] 1
                    (BVar [U;L;U] 2 0 _))
               (Lam [U;R] 1
                    (App [U;R;U] 2
                         (BVar [U;R;U;L] 2 1 _)
                         (BVar [U;R;U;R] 2 0 _))))
    ); omega.
Defined.Definition substex' : Term. 
  refine (
      Lam [] 0
          (Lam [U] 1
               (App [U;U] 2
                    (BVar [U;U;L] 2 1 _)
                    (BVar [U;U;R] 2 0 _)))
    ); omega.
Defined.
Definition substex1 : Term. 
  refine (
      Lam [] 0
          (App [U] 1
               (Lam [U;L] 1
                    (App [U;L;U] 2
                         (BVar [U;L;U;L] 2 0 _)
                         (BVar [U;L;U;R] 2 0 _)))
               (Lam [U;R] 1
                    (App [U;R;U] 2
                         (BVar [U;R;U;L] 2 1 _)
                         (BVar [U;R;U;R] 2 0 _))))
    ); omega.
Defined.
Definition substex1' : Term. 
  refine (
      Lam [] 0
          (App [U] 1
               (Lam [U;L] 1
                    (App [U;L;U] 2
                         (BVar [U;L;U;L] 2 1 _)
                         (BVar [U;L;U;R] 2 0 _)))
               (Lam [U;R] 1
                    (App [U;R;U] 2
                         (BVar [U;R;U;L] 2 1 _)
                         (BVar [U;R;U;R] 2 0 _)))
          )
    ); omega.
Defined.
Example ss' : 
    OptionTermTEquality
      (substex {| [U;R] |})
      (Some substex') = true. auto. Qed.
Example ss1' : 
    OptionTermTEquality
      (substex1 {| [U;R] |})
      (Some substex1') = true. auto. Qed.

(* Auxiliary functions that computes "size" of the HLR stateSize
    and thus, enforces termination of expansion function 
*)
Fixpoint gammaSize (g : Gamma) : nat :=
  match g with
    | EmptyGamma => 0
    | ConsGamma _ _ _ gs => 1 + gammaSize gs
  end.

Fixpoint deltaSize (d : Delta) : nat :=
  match d with
    | EmptyDelta => 1
    | ConsDelta _ g' ds => gammaSize g' +  deltaSize ds
  end.

Fixpoint stateSize (s : HLRState) : nat :=
  match s with
    | HLRStuck s => stateSize s
    | HLRStateC _ _ _ g d => gammaSize g +  deltaSize d
  end.

(* An expansion function *)
Definition expansion (s : HLRState)  : option Term :=
  let fix expansion' (ll : nat) (s : HLRState) {struct ll}  : option Term :=
      match ll, s with 0%nat, _ => None
                    | S _, HLRStuck s => None (* TODO : expansion s *)
                    | S ll, HLRStateC t p l g d =>
                      match g with
                        | EmptyGamma =>
                          match d with
                            | EmptyDelta => Some t
                            | ConsDelta p' g' ds => None (* expansion' ll (HLRStateC t p l g' ds) *)
                          end
                        | ConsGamma l' p' g' gs =>
                          (*TODO: incorrect! here have to be:
                           1) real substitution (not linear)
                           2) with throughing out the xcanseled nodes *)
                        (* match t [| p --> p' |] with *)
                          match t {| p' |} with
                            | Some t => ???
                            (* expansion' ll (HLRStateC t p l gs d) *)
                            | None => None
                          end
                      end
      end
  in expansion' (stateSize s) s.

Example est1 :
  OptionTermTEquality (expansion (hlrStep exampleCInit))
                      (Some exampleC) = true.
simpl_eq; auto. Qed.
(**)
Definition exampleC2 : Term. 
  refine (
      Lam [] 0
          (App [U] 1
               (Lam [U;L] 1
                    (App [U;L;U] 2
                         (BVar [U;L;U;L] 2 1 _)
                         (BVar [U;L;U;R] 2 0 _)
                    )
               )
               (Lam [U;R] 1
                    (BVar [U;R;U] 2 0 _))
          )
    ); omega.
Defined.

Example est2 :
  OptionTermTEquality (expansion (hlrStep (hlrStep exampleCInit)))
                      (Some exampleC2) = true.
repeat simpl_eq; auto. Qed.

Example exampleCIntS2 :
  hlrStateEq (hlrStep (hlrStep exampleCInit))
             (HLRStateC exampleC [U; L] 1 EmptyGamma
                        (ConsDelta [U; R] EmptyGamma EmptyDelta)) = true.
repeat simpl_eq; auto. Qed.

Example exampleCIntS3 :
  hlrStateEq (hlrStep (hlrStep (hlrStep exampleCInit)))
             (HLRStateC exampleC [U; L; U] 2
                        (ConsGamma 1 [U; R] EmptyGamma EmptyGamma)
                        EmptyDelta)
  = true.
repeat simpl_eq; auto. Qed.

Definition exampleC : Term. 
  refine (
      Lam [] 0
          (App [U] 1
               (Lam [U;L] 1
                    (App [U;L;U] 2
                         (BVar [U;L;U;L] 2 0 _)
                         (Lam [U;L;U;R] 2 (BVar [U;L;U;R;U] 3 0 _))
                    )
               )
               (Lam [U;R] 1
                    (App [U;R;U] 2
                         (BVar [U;R;U;L] 2 1 _)
                         (BVar [U;R;U;R] 2 0 _)
                    )
               )
          )
    ); omega.
Defined.


(**==============
        Head Redex
     ==============
 **)
Definition headRedex : Term -> option Path.
  refine(
      let fix hr {P : Path} {l : nat} (T : TermT P l) : option Path :=
          match T with
            | App t _ => match t with
                             | Lam _ => Some P
                             | App _ _ => hr t
                             | _ => None
                           end
            | Lam t => hr t
            | _ => None
          end
      in fun t => hr t
    ). Defined.

Example hreC : headRedex exampleC = Some [U]. auto. Qed.

Example exampleCIntS4 :
  hlrStateEq (hlrStep (hlrStep (hlrStep (hlrStep exampleCInit))))
             (HLRStateC exampleC [U; L; U;L] 2
                        (ConsGamma 1 [U; R] EmptyGamma EmptyGamma)
                        (ConsDelta [U;L;U;R] (ConsGamma 1 [U; R] EmptyGamma EmptyGamma) EmptyDelta))
  = true.
repeat simpl_eq; auto. Qed.

Example exampleCIntS5 :
  hlrStateEq (hlrStep (hlrStep (hlrStep (hlrStep (hlrStep exampleCInit)))))
             (HLRStateC
                (Lam [] 0
                     (App [U] 1
                          (Lam [U; L] 1
                               (App [U; L;U] 2
                                    (Lam [U; L; U; L] 2
                                         (App [U; L; U; L; U] 3
                                              (BVar [U; L; U; L; U; L] 3 2
                                                    (Decidable.dec_not_not (3 <= 3) (dec_lt 2 3)
                                                                           (fun H : 3 <= 3 -> False => Zge_left 2 3 (proj1 (Nat2Z.inj_ge 2 3) (not_lt 2 3 H))
                                                                                                                eq_refl)))
                                              (BVar [U; L; U; L; U; R] 3 0
                                                    (Decidable.dec_not_not (1 <= 3) (dec_lt 0 3)
                                                                           (fun H : 1 <= 3 -> False => Zge_left 0 3 (proj1 (Nat2Z.inj_ge 0 3) (not_lt 0 3 H))
                                                                                                                eq_refl)))))
                                    (Lam [U; L; U; R] 2
                                         (BVar [U; L; U; R; U] 3 0
                                               (Decidable.dec_not_not (1 <= 3) (dec_lt 0 3)
                                                                      (fun H : 1 <= 3 -> False => Zge_left 0 3 (proj1 (Nat2Z.inj_ge 0 3) (not_lt 0 3 H))
                                                                                                           eq_refl))))))
                          (Lam [U; R] 1
                               (App [U; R; U] 2
                                    (BVar [U; R; U; L] 2 1
                                          (Decidable.dec_not_not (2 <= 2) (dec_lt 1 2)
                                                                 (fun H : 2 <= 2 -> False => Zge_left 1 2 (proj1 (Nat2Z.inj_ge 1 2) (not_lt 1 2 H)) eq_refl)))
                                    (BVar [U; R; U; R] 2 0
                                          (Decidable.dec_not_not (1 <= 2) (dec_lt 0 2)
                                                                 (fun H : 1 <= 2 -> False => Zge_left 0 2 (proj1 (Nat2Z.inj_ge 0 2) (not_lt 0 2 H)) eq_refl)))))))
                [U; L; U; L]
                2
                EmptyGamma
                (ConsDelta [U;L;U;R] (ConsGamma 1 [U; R] EmptyGamma EmptyGamma) EmptyDelta))
  = true.
repeat simpl_eq; auto. Qed.
