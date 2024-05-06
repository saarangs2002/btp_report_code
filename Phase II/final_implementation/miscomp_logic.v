Require Import BTProject.min_max.
Require Import BTProject.library.
Require Import List.
Import ListNotations. 
Require Import Lia.
Require Import Nat.
Import Arith.
Require Import Coq.Logic.Eqdep_dec.


Definition delta : nat := 1.
Definition thresh := 2*delta.

Definition isMiscomparing (x y: nat) := lt_dec thresh (adiff x y).

Fixpoint  miscomparison_count (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0 
  | v::vs => match isMiscomparing v x with
           | left _ => S ( miscomparison_count x vs)
           | right _ => miscomparison_count x vs
           end
  end.

Check le_dec. 

Definition minindx_or_maxindx (x : nat) (l : list nat) (index : nat) : Prop :=
  ((index = find_index_from_in (proj1 ( proj2_sig (find_min x l)))) /\
     (1 < length (filter (fun y => thresh <? y - proj1_sig (find_min x l)) (x::l)))) \/ 
    ((index = find_index_from_in (proj1 ( proj2_sig (find_max x l)))) /\
    (1 < length (filter (fun y => thresh <?  proj1_sig (find_max x l) - y ) (x::l)))).

Definition faultySensor (x : nat) (l : list nat) : option {n : nat | minindx_or_maxindx x l n} .
 refine( let MIN := find_min x l in
  let MAX := find_max x l in
  match MIN as mIN return MIN=mIN -> option {n : nat | minindx_or_maxindx x l n} with 
  | exist _ min_val pfmin => fun Hyp =>
      let miscomp_from_min := filter (fun y => thresh <?  y -  min_val) (x::l) in
      match lt_dec 1 (length (miscomp_from_min)) with
      | left _ => Some (exist _ (find_index_from_in (proj1 pfmin)) _ ) 
      | right _ => match MAX as mAX return MAX=mAX -> option {n : nat | minindx_or_maxindx x l n} with
                  | exist _ max_val pfmax => fun Hyp_max => 
                                              let  miscomp_from_max := filter (fun y => thresh <?  max_val-y ) (x::l) in
                    match lt_dec 1 (length ( miscomp_from_max )) with
                    | left _ => Some (exist _ (find_index_from_in (proj1 pfmax)) _ )
                    | right _ => None
                    end
                  end (eq_refl MAX)
      end
  end (eq_refl MIN)).
 - left. split.
   + replace (find_min x l) with MIN. rewrite -> Hyp.  unfold proj2_sig.  trivial. 
     trivial.
   +  replace (find_min x l) with MIN. rewrite -> Hyp. unfold proj1_sig. trivial. trivial.      
 - right. split.
   + replace (find_max x l) with MAX. rewrite -> Hyp_max. unfold proj2_sig. trivial.
     trivial.
   +  replace (find_max x l) with MAX. rewrite -> Hyp_max. unfold proj1_sig. trivial. trivial. 
Defined. 

Search filter. 

Definition thresh_filter (x c: nat) (l : list nat) := filter (fun y => thresh <? adiff y c) (x::l).  
 
Compute (faultySensor 2 [2;2;3;2]).                     
                      
Compute (faultySensor 4 [4;2;6;2]).                      

Compute (faultySensor 4 [7]).
Compute (faultySensor 0 [4;3;4;3]).



Hypothesis ground_truth : nat. 
Hypothesis x : nat.
Hypothesis l : list nat. 

Definition MIN := find_min x l.
Definition MAX := find_max x l.

Definition min_val : nat := proj1_sig (MIN).
Definition max_val : nat := proj1_sig (MAX).

Definition min_in  := proj1 (proj2_sig MIN).
Definition max_in  := proj1 (proj2_sig MAX).

(* Single fault assumption *)
Hypothesis single_fault : length (filter (fun y => delta <? adiff ground_truth y) (x::l) ) <= 1.




Lemma max_ge_min : min_val <= max_val. 
  unfold min_val. unfold max_val.
  unfold MIN, MAX.
  induction l. 
  - simpl. trivial. 
  - destruct (find_min x l0) as [min_val min_proof].
    destruct (find_min x (a::l0)) .
    destruct (find_max x (a::l0)).
    simpl.

    destruct a0 as [Hin0 Hforall0].
    destruct a1 as [Hin1 Hforall1].

    apply Forall_inv in Hforall0.
    apply Forall_inv in Hforall1.
    apply (Nat.le_trans _ _  _ Hforall0 Hforall1).   
Qed.  

Lemma min_max_diff (z y : nat) : In y (x::l) -> In z (x::l) -> y - z <= max_val - min_val.
  intros. 
  unfold max_val. unfold min_val. 
  unfold MAX. unfold MIN. 
  destruct (find_max x l). destruct (find_min x l). simpl. 
  unfold adiff.
  destruct a. destruct a0.  
  Search ( Forall _ ).
  rewrite -> Forall_forall in H2.
  rewrite -> Forall_forall in H4.
  
  apply H2 in H as H5.
  apply H4 in H as H6.

  apply H2 in H0 as H7.
  apply H4 in H0 as H8.

  Search (_ -> _-_ <= _-_ ).
  lia. 
  Show Proof. 
Qed.


Check nth.
Check proj1_sig.
Check proj2_sig.

Check Nat.ltb_lt. 

Search ( _ <? _ = _  <-> ~ _ < _ ). 

Lemma filter_to_forall_min {x} {l} : Forall (fun y  => thresh < y - x) (filter (fun y => thresh <? y - x ) l ). 
intros. 
Search filter. 
induction l. 
- simpl filter .
  apply Forall_nil. 
- simpl filter. 
  destruct (lt_dec thresh (a - x)). 
  + apply Nat.ltb_lt in l1 as H1. 
    rewrite ->  H1. apply Forall_cons. trivial. trivial. 
  + Search ( _ < _ <-> _ <? _ = _ ).  apply Nat.ltb_nlt in n as H2. rewrite -> H2. trivial. 
Defined.     

Lemma filter_to_forall_max {x} {l} : Forall (fun y  => thresh < x - y) (filter (fun y => thresh <? x - y ) l ). 
intros. 
Search filter. 
induction l.
- simpl filter .
  apply Forall_nil. 
- simpl filter. 
  destruct (lt_dec thresh (x - a)). 
  + apply Nat.ltb_lt in l1 as H1. 
    rewrite ->  H1. apply Forall_cons. trivial. trivial. 
  + Search ( _ < _ <-> _ <? _ = _ ).  apply Nat.ltb_nlt in n as H2. rewrite -> H2. trivial. 
Defined.

Check filter_to_forall_min.


Lemma helperLemma_min {r v d y} (prp : adiff r v <= d)  :  2 * d < y - v ->  adiff r y > d .
  intros. 
  unfold adiff.
  unfold adiff in prp.
  
  destruct (lt_dec r v). 
  - destruct (lt_dec r y).
    +
      apply Nat.ltb_lt in l0 as H1.
      apply Nat.ltb_lt in l1 as H2.
      rewrite -> H1 in prp.
      rewrite -> H2.  lia.
    + apply Nat.ltb_lt in l0 as H1.
      apply Nat.ltb_nlt in n as H2.
      rewrite -> H1 in prp.
      rewrite -> H2.  lia.
  - destruct (lt_dec r y).
    + apply Nat.ltb_nlt in n as H1.
      apply Nat.ltb_lt in l0 as H2.
      rewrite -> H1 in prp.
      rewrite -> H2.  lia.
    + apply Nat.ltb_nlt in n as H1.
      apply Nat.ltb_nlt in n0 as H2.
      rewrite -> H1 in prp.
      rewrite -> H2.  lia.
Qed.

Lemma helperLemma_max {r v d y} (prp : adiff r v <= d)  :  2 * d < v - y ->  adiff r y > d .
  intros. 
  unfold adiff.
  unfold adiff in prp.
  
  destruct (lt_dec r v). 
  - destruct (lt_dec r y).
    +
      apply Nat.ltb_lt in l0 as H1.
      apply Nat.ltb_lt in l1 as H2.
      rewrite -> H1 in prp.
      rewrite -> H2.  lia.
    + apply Nat.ltb_lt in l0 as H1.
      apply Nat.ltb_nlt in n as H2.
      rewrite -> H1 in prp.
      rewrite -> H2.  lia. 
  - destruct (lt_dec r y).
    + apply Nat.ltb_nlt in n as H1.
      apply Nat.ltb_lt in l0 as H2.
      rewrite -> H1 in prp.
      rewrite -> H2.  lia.
    + apply Nat.ltb_nlt in n as H1.
      apply Nat.ltb_nlt in n0 as H2.
      rewrite -> H1 in prp.
      rewrite -> H2.  lia.
Qed.



Lemma more_than_delta_away_min {r} {mis} {pfMin} : (faultySensor x l = Some (mis) ) -> (proj2_sig (mis) = or_introl (pfMin) )  -> (adiff r (proj1_sig (find_min x l))) <= delta -> Forall (fun y => adiff r y > delta) (filter (fun y => thresh <? y - proj1_sig (find_min x l)) (x::l)).
  intros.
  destruct pfMin.
  simpl in  H0.
   
  remember (filter (fun y : nat => thresh <? y - proj1_sig (find_min x l)) (x :: l)) as fil_lst.
  unfold thresh in Heqfil_lst.

  apply (@Forall_impl nat (fun y => thresh < y - proj1_sig (find_min x l) ) ( fun y => adiff r y > delta ) ) .
  unfold thresh. intro. apply (@helperLemma_min r (proj1_sig (find_min x l)) delta a H1 ). 
  rewrite -> Heqfil_lst.
  apply ( @filter_to_forall_min (proj1_sig (find_min x l)) (x::l)).
Qed.   

Lemma more_than_delta_away_max {r} {mis} {pfMax} : (faultySensor x l = Some (mis)) -> (proj2_sig (mis) = or_intror (pfMax))  -> (adiff r (proj1_sig (find_max x l))) <= delta -> Forall (fun y => adiff r y > delta) (filter (fun y => thresh <? proj1_sig (find_max x l) - y) (x::l)).
  intros. 
  destruct pfMax.
  simpl in H0. 
  remember (filter (fun y : nat => thresh <? proj1_sig (find_max x l) - y ) (x :: l)) as fil_lst.
  unfold thresh in Heqfil_lst. 
  apply (@Forall_impl nat (fun y => thresh < proj1_sig (find_max x l) - y) ( fun y => adiff r y > delta ) ) .
  unfold thresh. intro. apply (@helperLemma_max r (proj1_sig (find_max x l)) delta a H1 ).
  rewrite -> Heqfil_lst.
  apply ( @filter_to_forall_max (proj1_sig (find_max x l)) (x::l)).
Qed.

(*Proof by contradiction, consider 'r' as ground truth, if faultySensor is `Some v` then filter has length > 1. Then by previous two lemmas atleast 2 values deviates from ground truth contradicting our assumption 'single_fault'. *)

Lemma find_index_and_nth {a l} (index : In a l) : nth (find_index_from_in index) l 0  = a.
induction l. 
contradiction. 
simpl. destruct (Nat.eq_dec). 
auto.
destruct (in_inv index).  auto. 
apply (IHl i). 
Defined.
 

Lemma nth_find_min {x l} : (nth (find_index_from_in (proj1 (proj2_sig (find_min x l)))) (x :: l) 0) = proj1_sig (find_min x l).
  remember (find_min x l).
  remember (proj2_sig s). 
  remember (proj1 a).
  rewrite (find_index_and_nth _ ). trivial. 
Defined. 

Lemma lt_gt {a b}: a < b <-> b > a.
 
lia. 
Defined.

Lemma nth_find_max {x l} : (nth (find_index_from_in (proj1 (proj2_sig (find_max x l)))) (x :: l) 0) = proj1_sig (find_max x l).
  remember (find_max x l).
  remember (proj2_sig s). 
  remember (proj1 a).
  rewrite (find_index_and_nth _ ). trivial. 
Defined. 


Lemma Forall_to_filter {x  z lst}: Forall (fun y => adiff x y > z) lst -> filter (fun y => z <? adiff x y) lst = lst. 
intros. 
induction lst. 
simpl. trivial. 

simpl.
apply Forall_inv in H as H1.
apply lt_gt in H1. 
apply Nat.ltb_lt in H1 as hb. 
rewrite hb. 
apply Forall_inv_tail in H as Htl.  
rewrite (IHlst Htl).
trivial.  
Defined.  

Lemma filter_length {A } {f : A -> bool} {lst : list A}:  length (filter f lst) <= (length lst).
induction lst. 
simpl. 
trivial. 

simpl. 
destruct (f a). 
simpl. apply le_n_S.  trivial.
apply le_S. 
trivial. 
Defined.

Lemma filter_filter {A} {f g : A -> bool} {lst : list A}:  filter f (filter g lst) = filter g (filter f lst). 
induction lst . 
- simpl. trivial.
- simpl.   destruct (g a) eqn:gv. destruct (f a) eqn:hv. simpl. rewrite gv, hv.  rewrite IHlst. trivial. 
simpl.   rewrite hv. trivial. 
destruct (f a) eqn:fv.  simpl. rewrite gv. trivial. trivial. 
Qed. 



Lemma faulty_sensor_deviates_gt_delta {mis} : faultySensor x l = Some (mis) -> adiff  ground_truth ( nth (proj1_sig mis) (x::l) 0)  > delta. 
  intros.
  
  remember (proj1_sig mis).   
  remember (proj2_sig mis).
  remember  (nth (proj1_sig mis) (x::l) 0).

  destruct m.
  - 
    apply not_le.
    unfold not.
    intros.
    assert (Forall (fun y => adiff ground_truth y > delta) (filter (fun y => thresh <? y - proj1_sig (find_min x l)) (x::l)) ).
    apply  (@more_than_delta_away_min ground_truth mis a H ).
    auto.
    destruct a. rewrite -> Heqn in H0. rewrite e in H0.  rewrite nth_find_min in H0. 
    trivial. 
    destruct a. simpl in Heqm.
    remember (filter (fun y : nat => delta <? adiff ground_truth y)
            (x :: l)).
    remember single_fault.
    remember (filter
            (fun y : nat =>
             thresh <? y - proj1_sig (find_min x l)) 
            (x :: l)) .
    
    apply Forall_to_filter in H1 as Hfil.
    remember (filter (fun y : nat => delta <? adiff ground_truth y) l3).
    rewrite Heql3 in Heql4.
    rewrite filter_filter in Heql4.
    
    rewrite <- Heql1 in Heql4.
    assert (length (filter (fun y : nat => thresh <? y - proj1_sig (find_min x l)) l1) <=
       length l1). 
    apply filter_length. 

    rewrite Heql1 in H2.
    assert ( length
         (filter (fun y : nat => thresh <? y - proj1_sig (find_min x l))
            (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l))) <= 1).
    apply (   @Nat.le_trans _ (length (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l)) ) _ )  . trivial . trivial.

    rewrite <-  Heql1 in H3. 
    rewrite <- Heql4 in H3.
    rewrite Hfil in H3.
    apply le_not_lt in H3 as conl0.
    contradiction conl0. 
  - apply not_le. 
    unfold not.
    intro. 
    assert (Forall (fun y => adiff ground_truth y > delta) (filter (fun y => thresh <? proj1_sig (find_max x l) - y ) (x::l)) ).
    apply  (@more_than_delta_away_max ground_truth mis a H ).
    auto. destruct a. rewrite -> Heqn in H0. rewrite e in H0. rewrite nth_find_max in H0. 
    trivial.
    destruct a. simpl in Heqm.
    remember (filter (fun y : nat => delta <? adiff ground_truth y)
            (x :: l)).
    remember single_fault.
    remember (filter
            (fun y : nat =>
             thresh <? proj1_sig (find_max x l) - y ) 
            (x :: l)) .
    apply Forall_to_filter in H1 as Hfil.
    remember (filter (fun y : nat => delta <? adiff ground_truth y) l3).
    rewrite Heql3 in Heql4.
    rewrite filter_filter in Heql4.
    
    rewrite <- Heql1 in Heql4. 
    assert (length (filter (fun y : nat => thresh <? proj1_sig (find_max x l) - y) l1) <=
       length l1). 
    apply filter_length.
    rewrite Heql1 in H2.
    assert ( length
         (filter (fun y : nat => thresh <? proj1_sig (find_max x l) - y )
            (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l))) <= 1).
    apply (   @Nat.le_trans _ (length (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l)) ) _ )  .  trivial . trivial.

    rewrite <-  Heql1 in H3. 
    rewrite <- Heql4 in H3.
    rewrite Hfil in H3.
    apply le_not_lt in H3 as conl0.
    contradiction conl0. 
Defined. 

Lemma ge_le {a b} : a >= b <-> b <= a. 
lia. 
Defined.
Lemma two_diff_val {A}{a b} {l : list A}: In a l -> In b l -> a <> b -> length l >= 2.
  intros.
  induction l. 
  simpl.
  -  
  contradiction. 
  - induction l0. 
    simpl. 
    +  Search In.  Check in_inv.  apply in_inv in H. destruct H.
       ++ apply in_inv in H0. destruct H0. rewrite  H in H0. contradiction. 
          contradiction.
       ++ contradiction. 
    + simpl. rewrite ge_le. apply le_n_S. apply le_n_S. Search ( 0 <= _ ). apply (Nat.le_0_l).
Defined. 



Lemma no_other_sensor_is_faulty {v}{mis}{in_pf : In v (x::l) } : (faultySensor x l = Some (mis)) -> (nth (proj1_sig(mis)) (x::l) 0) <> v -> adiff ground_truth v  <= delta. 
          
  
intros. 
remember single_fault. 
apply faulty_sensor_deviates_gt_delta in H as mis_deviates. 
remember (nth (proj1_sig mis) 
            (x :: l) 0) as fault_val.
Search (~ _ -> _ <= _ ). apply not_gt. unfold not. intro. 
remember (proj1_sig mis) .
remember (proj2_sig mis). 
remember (proj2_sig (find_min x l)). 
remember (proj2_sig (find_max x l)) as max_proj.
destruct a. 
destruct m.
 - destruct a.
 rewrite Heqn in Heqfault_val. 
 rewrite e in Heqfault_val.  
rewrite nth_find_min in Heqfault_val. 
 
assert (In fault_val (x::l)). 
rewrite Heqfault_val. 
trivial.

assert (In fault_val (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l))).
apply filter_In. split. 
trivial. apply Nat.ltb_lt. apply lt_gt. 
trivial.  
assert (In v (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l))).
apply filter_In. split.  
trivial.  apply Nat.ltb_lt. apply lt_gt. trivial .
assert (length (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l)) >= 2).
apply (two_diff_val H3 H4 H0 ). 
Search (_ < _  ->  _ <= _   ).
lia. 
 - destruct a.
   destruct max_proj. 
   rewrite Heqn in Heqfault_val.  
   rewrite e in Heqfault_val.  
   rewrite nth_find_max in Heqfault_val.
   assert (In fault_val (x::l)). 
   rewrite Heqfault_val. 
   trivial.
   assert (In fault_val (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l))).
   apply filter_In. split. 
trivial. apply Nat.ltb_lt. apply lt_gt. 
trivial.  
assert (In v (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l))).
apply filter_In. split.  
trivial.  apply Nat.ltb_lt. apply lt_gt. trivial .
assert (length (filter (fun y : nat => delta <? adiff ground_truth y) (x :: l)) >= 2).
apply (two_diff_val H3 H4 H0 ).
lia. 
Defined.

Lemma finds_value_deviate_3delta {v} {mis} (pf_in : (In v (x::l))) : adiff ground_truth v  > 3*delta -> (faultySensor x l = Some (mis)) /\ (nth (proj1_sig(mis)) (x::l) 0) = v. 


  

(*
  P1. The faultySensor returns either of (Some min) (Some max) or None. 
  -> If the faultySensor returns Some v, then 
                                      P2. length (filter () (x::l)) > 1.
                                      R1. Deviation of v from, ground thruth is more than delta.
                                      R2. Using single_fault prove that no other sensors are faulty.
  R3. If there is a sensor that deviates more than 3*delta from ground truth, then `faultySensor` returns Some v
  (If faultySensor returns None, there is no sensor that deviates more than 3*delta from ground truth.)
 
*)


(*
Require Extraction.

Extraction Language Haskell.

Extraction "/home/saarang/Semester 7/BTP/code/v2/voter_new.hs" faultySensor.
*)

