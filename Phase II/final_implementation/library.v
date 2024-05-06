Require Import Nat.
Require Import Bool.
Require Import Vector.
Import VectorNotations.

Definition MCthresh : nat := 2.
(* change the name of thresh to MCThresh*)

(* Absolute difference function *)
Definition adiff (n m : nat) : nat :=
  match  n <? m with
  | true => m - n
  | false => n - m
  end.

Print option.

Inductive SIGNAL  : Type := 
  | good  : nat -> SIGNAL
  | bad  : nat -> SIGNAL .

Check Some.

Inductive sensorId :=
| first : sensorId
| second : sensorId
| third : sensorId.

Inductive axis := 
| x_ax : axis
| y_ax : axis
| z_ax : axis.


(*Map3 for vectors*)
Definition vector := Vector.t.

Definition f1 {A B} (a: A) (b: B): (A*B) := (a,b).
Definition f2 {A B C} (t: A*B) (c: C): (A*B*C) := match t with
                                        | (a,b) => (a,b,c)
                                        end.

Definition f3 {A B C D} (f:  A -> B -> C -> D): (A*B*C) -> D  := fun (v:A*B*C) => match v with
                                                                           | (a,b,c) => f a b c
                                                                                         end.
Definition map3 {A B C D n} (f : A -> B -> C -> D) (v1 : vector A n) (v2: vector B n) (v3 : vector C n): vector D n :=map (f3 f) (map2 f2 (map2 f1 v1 v2) v3).
