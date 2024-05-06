Require Import Vectors.Vector.
Import VectorNotations.
Require Import Coq.Arith.Arith.
Require Import List.
Definition vector := Vector.t.
Require Import BinNat.
Require Import ZArith.
Require Import Wellfounded.
Require Import ssreflect.
Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.


(*tree*)
Inductive mytree (n: nat) : Type :=
| mymax_index m : m <= n -> mytree n
| mycomp m1 m2 : m1 <= n -> m2 <=n -> mytree n -> mytree n -> mytree n.                                        
                                       

Check mymax_index.

Check mycomp.

Program Definition x:= mymax_index 0 1 _.

Program Definition y:= mymax_index 1 1 _.

Program Definition z := mycomp 2 1 2 _ _ (mymax_index 2 1 _) (mymax_index 2 2 _). 


Definition create_sig {n: nat} (x : nat)  (pfxlen : x <= n) : {m | m <= n}.
exact (exist _ x pfxlen). 
Defined.

Fixpoint index_list_pf (n m : nat) (pfm : m <=n) : list {i | i <= n}.
refine(
  match m as M return (m=M) ->  list {i | i <= n}  with
  | 0 => fun Hyp => nil
  | S k => fun Hyp =>  (cons (create_sig k _) nil) ++ (index_list_pf n k _)
  end (eq_refl m)).
  all: (
  rewrite Hyp in pfm;
  apply le_Sn_le in pfm;
  trivial).
Defined.

Compute (index_list_pf 9 9 _ ).



Definition pf_n_le_n (n : nat) : n <= n.
exact (le_refl n).
Defined.

Definition pf_index_list (n: nat):=  index_list_pf n n (pf_n_le_n n).

(* Every element of 0 to n-1 is in `pf_index_list`.
*)

Check pf_index_list.
Compute pf_index_list 3.




Fixpoint tree_gen_list {n : nat} (x: nat) (pfxlen : x <= n) (l : list {i | i <=n }) : mytree n :=
  match l with
  | nil => mymax_index n x pfxlen  
  | cons y l' => mycomp n x (proj1_sig y) pfxlen (proj2_sig y) (tree_gen_list x pfxlen l') (tree_gen_list (proj1_sig y) (proj2_sig y) l')
 end.                       

(* For any input, for every element of (pfxlen::l) its proj2_sig is in `all_leaves` of `tree_gen_list`. 
*)

Definition tree_gen (n: nat):= tree_gen_list n (pf_n_le_n n) (pf_index_list n).

(* `tree_gen n` will have every element of 0 to n in its `all_leaves`. 
*)


Compute (tree_gen 3).



Fixpoint all_leaves  {n: nat} (t : mytree n) : list nat:=
  match t with
  | mymax_index _ i _ => cons i nil
  | mycomp _ _ _ _ _ t1 t2 =>  (all_leaves t1) ++ (all_leaves t2)
  end.                                


Compute all_leaves (tree_gen 3).


Definition tree_for_list (l : list nat) := tree_gen ((length l)-1).

Compute all_leaves (tree_for_list (10::20::30::40::nil)).


Definition TorF (P : Prop ): Set:= {P} + {~P}.
Search ( _ <= _ -> _ < _).
(*
Lemma le_n_lSn : forall {i n} ,  (i <= n) -> (i < (S n)) := le_lt_n_Sm i n.
lia.
Qed.*)

Definition le_n_lSn  {i n} (pf : i <= n) :  (i < (S n)) := le_lt_n_Sm i n pf.


Fixpoint eval_tree_v {n} {f : nat ->nat -> Prop } (v:vector nat (S n)) (t: mytree n) (compf : forall a b :nat, TorF (f a b)) : {m | m <= n} :=
  match t with
  | mycomp _ i1 i2 p1 p2 t1 t2 => let v1 := Vector.nth_order v (le_n_lSn  p1) in
                             let v2 := Vector.nth_order v (le_n_lSn  p2) in
                             match compf v1 v2 with
                             | left _ => eval_tree_v v t2 compf
                             | right _ => eval_tree_v v t1 compf
                             end
  | mymax_index _ i p => create_sig i p
  end.

Check length.

Fixpoint eval_tree_lst {n} {f : nat -> nat -> Prop} (v : list nat) (t : mytree n) (compf : forall a b: nat, TorF (f a b)) : {m | m <= n} :=
  match t with
  | mycomp _ i1 i2 p1 p2 t1 t2 => let v1 := nth i1 v 0 in
                                 let v2 := nth i2 v 0 in
                                 match compf v1 v2 with
                                 | left _ => eval_tree_lst v t2 compf
                                 | right _ => eval_tree_lst v t1 compf
                                 end
  | mymax_index _ i p => create_sig i p
  end.


Fixpoint eval_tree_lst_max {n} (v : list nat) (t : mytree n) : {m | m <= n} :=
  match t with
  | mycomp _ i1 i2 p1 p2 t1 t2 => let v1 := nth i1 v 0 in
                                 let v2 := nth i2 v 0 in
                                 match le_dec v1 v2 with
                                 | left _ => eval_tree_lst_max v t2 
                                 | right _ => eval_tree_lst_max v t1 
                                 end
  | mymax_index _ i p => create_sig i p
  end.

Check tl.
Check hd.
Check nth.

Fixpoint eval_max {n} (x: nat) (pfxlen : x <= n) (l : list {i | i <=n }) (v : list nat) :=
  match l with
  | nil => create_sig x pfxlen
  | pfylen :: l' => let y := proj1_sig pfylen in
                  match le_dec (nth x v 0) (nth y v 0) with
                  | left _ => eval_max y (proj2_sig pfylen) l' v
                  | right _ => eval_max x pfxlen l' v
                  end
  end.

Search (In).

Definition eval_max_val {n} (x: nat) (pfxlen : x <= n) (l : list {i | i <=n }) (v : list nat): nat :=
  let index := eval_max x pfxlen l v in
  nth (proj1_sig index) v 0 .

                    

   

Definition len {n} (v: vector nat n) := n.
Definition v :=[1000;2;3;5;4000;0].

Definition lst := cons 1000 (cons 2 (cons 3 (cons 5 (cons 4000 (cons 0 nil))))).

Definition compute_max_index {n} (v: vector nat (S n)): {m : nat | m <= n} := eval_tree_v v (tree_gen n) le_dec.

Print compute_max_index.

Definition compute_max_index_lst {n} (v : list nat) (goodList : length v = S n) := eval_tree_lst v (tree_gen n) le_dec.
                                                 

Check compute_max_index.

Definition compute_max {n} (v : vector nat (S n)) := let pfi := proj2_sig (compute_max_index v) in
                                                   Vector.nth_order v (le_n_lSn pfi).

Definition compute_max_lst {n} (v: list nat) (goodList : length v = S n) :=
  let i := proj1_sig (compute_max_index_lst v goodList) in
  nth i v 0.
                                            

Compute (compute_max_index v ).
Compute (@compute_max_index_lst 5 lst _ ).

Fixpoint simple_max_find (x: nat) (l: list nat) : nat := 
  match l with
  | nil => x
  | v :: vs => match le_dec x v with
             | left _ => simple_max_find v vs
             | right _ => simple_max_find x vs
             end
  end.

Compute (simple_max_find 3 nil).


Lemma computes_max {n} (x: nat) (pfxlen : x <= n) (l : list {m | m <= n}) (v : list nat) (pflenght : length v = S n) :
  Forall (fun index => nth (proj1_sig index) v 0 <=  (eval_max_val x (pfxlen) l v) ) (l++(cons (create_sig x pfxlen) nil)). 
  induction l.
  -  simpl. unfold eval_max_val. simpl. apply Forall_cons.
    + simpl. trivial.
    + apply Forall_nil.      
  - 
    apply Forall_cons.
    +  simpl.  unfold eval_max_val. unfold eval_max. destruct le_dec.
       ++ 
                  
