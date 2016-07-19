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
  exists l; rewrite app_nil_r; apply T.
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
Inductive HLRState :=
| HLRStateC : Term -> Path -> nat -> Gamma -> Delta -> HLRState
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

Definition hlrStep :
  HLRState -> HLRState.
  refine (
      fun s =>
        match s with
          | HLRStateC T P L1 G D =>
            match T [| P |] with
                 | Some (existT l T') => match T' with
                                           | Lam  t =>
                                             match D with
                                               (* [Lam-Non-Elim] *)
                                               | EmptyDelta => HLRStateC T (getpath t) (l + 1) G D
                                               (* [Lam-Elim] *)
                                               | ConsDelta px gx Ds =>
                                                 HLRStateC T (getpath t) (l+1) (ConsGamma (getlamnum T') px gx G) Ds
                                             end
                                | App  t1 t2 => HLRStateC T (getpath t1) l G (ConsDelta (getpath t2) G D)
                                | BVar i _  =>
                                (* match containsGamma G index (l - i -1) with *)
                                  match containsGamma G (l - i -1) with
                                                 | None => HLRStuck s
                                                 | Some (pair p g) =>
                                                   match T [| P -->  p |] with
                                                     | None => HLRStuck s
                                                     (* BVar *)
                                                     | Some T => HLRStateC T P l g D
                                                   end
                                               end
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

(* FAIL: it have to except not a Path but a variable!!!!!!! *)
(* A path is a path to the redex (i.e. from the root to the argument node of the redex *)
(* Definition substitution' : forall {P P' : Path} {l l' : nat}, TermT P l -> TermT P' l' -> *)
(*                                                               l >= l' -> TermT P l. *)
(*   refine( *)
(*       fix st' {P P' : Path} {l l' : nat} (t : TermT P l) (t' : TermT P' l') (eq : l >= l') : TermT P l := *)
(*         match t with *)
(*           | Lam t => Lam P l (st' t t' _) *)
(*           | App t1 t2 => App P l (st' t1 t' _) (st' t2 t' _) *)
(*           | BVar n _ => if beq_nat n (l' + 1) *)
(*                         then fixpath P l l' t' _ *)
(*                         else BVar P l n _ *)
(*           | FVar _ => t *)
(*         end *)
(*     ); omega. *)
(* Defined. *)

(* destruct (classic (a = b)) *)
(* Definition fixpath11 : forall {P P' : Path} {l l' : nat}, *)
(*            nat -> TermT P  l -> TermT P' l' -> l >= l' -> TermT P l. *)
(*   refine ( *)
(*       fix fixpath1 {P P' : Path} {l l' : nat} *)
(*           (ll : nat) *)
(*           (t : TermT P  l ) *)
(*           (T : TermT P' l') *)
(*           (EQ : l >= l') : TermT P l := *)
(*         match t with *)
(*           | Lam t => Lam P l (fixpath1 ll t T _) *)
(*           | App t1 t2 => App P l (fixpath1 ll t1 T _) (fixpath1 ll t2 T _) *)
(*           | FVar _ => t (* TODO CHECK *) *)
(*           | BVar n _ => *)
(*             let ll := l + 1 - ll *)
(*             in if beq_nat ll n *)
(*                then fixpath P l l' T _ *)
(*                else if ll <? n *)
(*                     then BVar P l (n - 1) _ *)
(*                     else BVar P l n _ *)
(*         end *)
(*     ); omega. *)
(* Defined. *)

Require Import Logic.Classical_Prop.
Require Import Decidable.
Require Import Arith.EqNat.

Definition Decide P := P \/ ~P.

Theorem decide_eq_nat: forall x y: nat, Decide (x = y).
Proof.
  intros x y. remember (beq_nat x y) as b eqn:E. destruct b.
    left. apply beq_nat_eq. assumption.
    right. apply beq_nat_false. symmetry. assumption. Qed.

Definition fixpath11 : forall {P P' : Path} {l l' : nat} (P1 : Path) (l1 : nat),
                         nat -> TermT P  l -> TermT P' l' ->
                         l > 0 -> l1 >= l' -> S l1 = l -> TermT P1 l1.
  refine (
      fix fixpath1 {P P' : Path} {l l' : nat}
          (P1 : Path)
          (l1 ll : nat)
          (t : TermT P  l )
          (T : TermT P' l')
          (EQ0 : l > 0) (EQ1 : l1 >= l') (EQ2 : S l1 = l) : TermT P1 l1 :=
        match t with
          | Lam t => Lam P1 l1 (fixpath1 (P1 ++ [U]) (S l1) ll t T _ _ _)
          | App t1 t2 => App P1 l1(fixpath1  (P1 ++ [L]) l1 ll t1 T _ _ _) (fixpath1 (P1 ++ [R]) l1 ll t2 T _ _ _)
          | FVar n => FVar P1 l1 n (* TODO CHECK *)
          | BVar n _ => _
            (* let ll := l - 1 - ll *)
            (* in if beq_nat ll n *)
            (*    then _ (*fixpath P1 l1 l' T _*) *)
            (*    else if ll <? n *)
            (*         then _ (* if 0 <? l1 *) *)
            (*              (* then BVar P1 l1 (n - 1) _ *) *)
            (*              (* else FVar P1 l1 n *) *)
            (*         else _ (*BVar P1 l1 n _*) *)
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

Definition substitution : Term -> Path -> option Term.
  refine(
      let fix st {P : Path} {l : nat} (t : TermT P l) (p : Path) : option (TermT P l) :=
          match p with
            | [R] => match t with
                       (* | App t T =>
                        Some (fixpath P l l (substitution' t T _) _) *)
                       | App (Lam t) T => Some (
                                              fixpath11 P l l t T _ _ _
                                            )
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

Definition substex : Term. 
  refine (
      (* Lam [] 0 *)
      (*     (App [U] 1 *)
      (*          (Lam [U;L] 1 *)
      (*               (App [U;L;U] 2 *)
      (*                    (BVar [U;L;U;L] 2 1 _) *)
      (*                    (BVar [U;L;U;R] 2 1 _) *)
      (*               ) *)
      (*          ) *)
      (*          (Lam [U;R] 1 *)
      (*               (App [U;R;U] 2 *)
      (*                    (BVar [U;R;U;L] 2 1 _) *)
      (*                    (BVar [U;R;U;R] 2 0 _) *)
      (*               ) *)
      (*          ) *)
      (*     ) *)

      Lam [] 0
          (App [U] 1
               (Lam [U;L] 1
                    (BVar [U;L;U] 2 0 _)
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

Definition substex' : Term. 
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

Eval compute in
    OptionTermTEquality
      (substitution substex [U;R])
      (Some substex')
.
  


(*
  An expansion function.
 *)
(* TODO : we have to exclude nodes from the term in some way *)
Definition expansion (s : HLRState)  : option Term :=
  let fix expansion' (ll : nat) (s : HLRState) {struct ll}  : option Term :=
      match ll, s with 0%nat, _ => None
                    | S _, HLRStuck s => None (* expansion s *)
                    | S ll, HLRStateC t p l g d =>
                      match g with
                        | EmptyGamma =>
                          match d with
                            | EmptyDelta => Some t
                            | ConsDelta p' g' ds => expansion' ll (HLRStateC t p l g' ds)
                          end
                        | ConsGamma l' p' g' gs =>
                          (*TODO: incorrect! here have to be:
                           1) real substitution (not linear)
                           2) with throughing out the xcanseled nodes *)
                          match t [| p --> p' |] with
                                                     | Some t => expansion' ll (HLRStateC t p l gs d)
                                                     | None => None
                                                   end
                      end
      end
  in expansion' (stateSize s) s.

Example est :
  OptionTermTEquality (expansion (hlrStep exampleCInit))
                      (Some exampleC) = true.
simpl_eq; auto. Qed.


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

