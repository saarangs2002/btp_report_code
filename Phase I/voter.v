Require Import Nat.
Require Import Bool.
Require Import Coq.Lists.List.

Definition thresh : nat := 2.

(* Absolute difference function *)
Definition adiff (n m : nat) : nat :=
  match  n <? m with
  | true => m - n
  | false => n - m
  end.

Print option.

Inductive OPTION  : Type := 
  | Some  : nat -> OPTION
  | None  : nat -> OPTION .

Check Some.

Definition mis_comp_h (X1 X2: OPTION ) : bool := 
match X1,X2 with
| Some x1 , Some x2 => (thresh <? (adiff x1 x2))
| None x1, _ => true
| _,_ => false 
end.

Definition mis_comp (X1 X2 X3: OPTION) : bool := andb (mis_comp_h X1 X2) (mis_comp_h X1 X3).


Compute (mis_comp (Some 5) (Some 11) (Some 10)).


Definition voter_helper (iX1 iX2 iX3: OPTION*nat ) : OPTION*nat := 
  let X1 := fst iX1 in
  let X2 := fst iX2 in
  let X3 := fst iX3 in
  let s1 := snd iX1 in
  let s2 := snd iX2 in
  let s3 := snd iX3 in

  match X1,X2,X3 with 
  | Some x1, Some x2, Some x3 => match mis_comp X1 X2 X3 with
                                 | false => (X1,s1)
                                 | true => match mis_comp_h X2 X3 with
                                           | false =>	(X2,s2) 
                                           | true => (None x1, s1) end
                                 end
  | Some x1, Some x2, None x3 => match mis_comp_h X1 X2 with 
                                 | false => (X1,s1)
                                 | true => (None x1, s1) end

  | Some x1, None x2, Some x3 => match mis_comp_h X1 X3 with 
                                 | false => (X1,s1)
                                 | true => (None x1, s1) end

  | None x1, Some x2, Some x3 => match mis_comp_h X2 X3 with 
                                 | false => (X2,s2)
                                 | true => (None x2, s2) end

  | Some x1, None x2, None x3 => (X1,s1)

  | None x1, Some x2, None x3 => (X2,s2)

  | None x1, None x2, Some x3 => (X3,s3)

  | None x1, None x2, None x3 => (None x1, s1)

  end.

Definition voter (X1 X2 X3: OPTION) (S : nat) : OPTION*nat :=
match S with 
| 1 => voter_helper (X1,1) (X2,2) (X3,3)
| 2 => voter_helper (X2,2) (X1,1) (X3,3)
| 3 => voter_helper (X3,3) (X1,1) (X2,2)
| _ => (None(0),0)
end.

Compute (voter (None 5) (None 11) (None 11) 1).


Definition my_list := 1 :: 2 :: 5 :: nil.

Fixpoint OBC (input_list : list (OPTION*OPTION*OPTION) ) (current_sensor: nat ) (cycles : nat) : nat  := 
match cycles with
            | O => current_sensor
            | S n => match input_list with
                     | nil => current_sensor
                     | x :: xs => match x with 
                                  | (x1,x2,x3) => let next_sensor := snd (voter x1 x2 x3 current_sensor) in
                                                  OBC xs next_sensor n 
                                  end
                     end	
end.

