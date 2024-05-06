Require Import List.
Import ListNotations. 
Require Import Lia.
Require Import Nat.
Import Arith.

(*
---- IN ----
in_eq: forall [A : Type] (a : A) (l : list A), In a (a :: l)
in_cons: forall [A : Type] (a b : A) (l : list A), In b l -> In b (a :: l)
---- FORALL -----
Forall_nil:
  forall [A : Type] (P : A -> Prop),
  Forall P Datatypes.nil

Forall_cons:
  forall [A : Type] [P : A -> Prop] 
    (x : A) [l : list A],
  P x -> Forall P l -> Forall P (x :: l)
 *)
Definition lst :=[1000;2;3;5;4000;0].        

(*Function to find max element from a list*)
Fixpoint find_max (x: nat) (l : list nat): {n : nat | In n (x::l) /\ Forall (fun y => y <= n) (x::l) }.
  refine (match l as L return {n : nat | In n (x::L) /\ Forall (fun y => y <= n) (x::L)  } with
          | v::vs => match le_dec x v with
                    | left _   => match find_max v vs with
                                 | exist _ m pf => exist _ m _
                                 end
                                   
                    | right _  => match (find_max x vs) with
                                 | exist _ m pf => exist _ m _
                                 end
                    end
                      
          | nil => exist _ x (conj (in_eq x nil) (Forall_cons x (Nat.le_refl x) (Forall_nil _) )) 
          end). 
- split. destruct pf.  
  + apply in_cons. assumption.
  + apply Forall_cons. destruct pf. apply Forall_inv in H0. exact( Nat.le_trans _ _ _  l0 H0). destruct pf. assumption. 
    
- destruct pf. split. 
  + simpl. simple apply in_inv in H. destruct  H.
    ++ left . assumption.
    ++ right. right. assumption.
  + apply Forall_cons. apply Forall_inv in H0.
    ++ assumption.
    ++ apply Forall_cons. apply Forall_inv in H0. simple apply not_le in n.
       apply not_gt.
       Search ( _ -> ~ _ > _  ) .
       apply gt_asym.
       
       Search ( _ -> _ -> _ > _).
       exact (le_gt_trans _ _ _ H0  n).
       simple apply Forall_inv_tail in H0. assumption.
Show Proof.        
Defined.
Compute (proj1_sig (find_max 3 nil) ).

Print  List.remove'. 

(*Function to find min element from a list*)
Fixpoint find_min (x: nat) (l : list nat): {n : nat | In n (x::l) /\ Forall (fun y => n <= y) (x::l) }.
  refine (match l as L return {n : nat | In n (x::L) /\ Forall (fun y => n <= y) (x::L)  } with
          | v::vs => match le_dec x v with
                    | left _   => match find_min x vs with
                                 | exist _ m pf => exist _ m _
                                 end
                                   
                    | right _  => match (find_min v vs) with
                                 | exist _ m pf => exist _ m _
                                 end
                    end
                      
          | nil => exist _ x _ 
          end).
  - split.
    + apply in_eq.
    + apply Forall_cons.
      ++ trivial. 
      ++ apply Forall_nil.
  - destruct pf. split .
    +  simpl. simple apply in_inv in H. destruct H.
       ++ left. trivial.
       ++ right. right. trivial. 
    +  apply Forall_cons. simple apply Forall_inv in H0.
      ++ trivial.
      ++  apply Forall_cons.
         +++ simple apply Forall_inv in H0. apply (Nat.le_trans _ _ _ H0 l0).
         +++ simple apply Forall_inv_tail in H0. trivial. 
  - destruct pf. split.
    + apply in_cons. trivial.
    + apply Forall_cons. simple apply Forall_inv in H0.
      ++ lia.
      ++ trivial .
Defined.

Compute (proj1_sig (find_min 3 nil)).

Fixpoint find_index_from_in  {a : nat} {l : list nat} (in_pf : In a l) {struct l} : nat .
 refine( (match l as L return l=L -> nat with
         | nil => fun Hyp => _  
          | x::xs =>fun  Hyp => match (Nat.eq_dec a x) with
                           | left _ => 0 
                           | right _ => S ( find_index_from_in a xs _ )
                           end 
         end) (eq_refl l)
       ).
 - rewrite Hyp in in_pf. apply  in_nil in in_pf. contradiction. 
 - rewrite Hyp in in_pf. simple apply in_inv in in_pf. 
   ++ destruct in_pf. 
      +++ Search ( _ = _ -> _ = _ ). apply eq_sym in H. contradiction . 
      +++ trivial. 
Defined.

Compute (find_index_from_in  (proj1 (proj2_sig (find_max 3 lst)))).
