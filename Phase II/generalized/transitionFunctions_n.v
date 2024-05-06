Require Import MyProject.test_inputs.
Require Import MyProject.state_n.
Require Import MyProject.OBC.
Require Import MyProject.library.
Require Import Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import Vector.
Import VectorNotations.

Check SIGNAL.

Check voter.

(* Health and Miscomparison Incrementer*)
Definition CumulativeIncrement (count : nat) (status : bool): nat  :=
  match status with
  | true => 0
  | false => count + 1
  end.

(* Isolation *)
Definition AssignIsolation (status : bool) (count : nat) : bool :=
  match status with
  | true => true
  | false => 4 <? count  
  end .

Compute (AssignIsolation false 4).
Compute (AssignIsolation false 5).
Compute (AssignIsolation false 6).

Definition nat2sid (sid : nat) : sensorId := match sid with
                                    | 1 => first
                                    | 2 => second
                                    | 3 => third
                                    | _ => first 
                                    end.

Definition sid2nat (sid : sensorId) : nat := match sid with
                                           | first => 1
                                           | second => 2
                                           | third => 3
                                           end.

(* Sensor Management  *)
Definition ManageCurSensorAx {ax : axis} (curS : currSensor ax) (v1 v2 v3 : SIGNAL): currSensor ax :=
  match curS with
  | SID axs sid =>SID axs ( sid2nat(snd (voter v1 v2 v3 (nat2sid sid))))
  end.

(* Isolation Management *)
Definition SingleSensorIsolationHelper (iso : bool) (cumm : nat) (miscomp : nat) : bool :=
  orb (AssignIsolation iso  cumm ) (AssignIsolation iso miscomp).

Print t.

Compute  (cons _  4 _ [1]).

Definition hd {n : nat} {t} (v : vector t (S n)) : t :=
  match v with
  | cons _ x _ xs => x
  end.

(*Definition map3Helper {A B C D} (a: A) (b: B) (f: A -> B -> C -> D): C -> D := fun (c: C) => f a b c.*)
Definition SensorIsolationHelper {n : nat} ( iso  : vector bool n) ( cumm : vector nat n) ( miscomp : vector nat n) : vector bool n := map3 SingleSensorIsolationHelper iso cumm miscomp.
  

Definition vec3_2_booltup (vec : vector bool 3) : (bool*bool*bool) :=
  match vec with
  | [b1; b2; b3] => (b1, b2 , b3)
  | _  => (false, false, false)
  end.

Definition vec3_2_nattup (vec : vector nat 3) : (nat*nat*nat) :=
  match vec with
  | [b1; b2; b3] => (b1, b2 , b3)
  | _  => (0, 0, 0)
  end.

Compute (vec3_2_nattup  [1;2;3]).
Definition SingleAxisSensorIsolations {ax : axis} {n} (misComp :@MiscomparisonCount n ax) ( cummHealth : @SensorCumulativeHealthFailure n ax ) ( isos : @IsolatedSensors n ax ) : @IsolatedSensors n ax :=
  match misComp, cummHealth, isos  with
  | (misCount _  mcs), (SenHFcount _ chs), (iso _ iss) => iso ax (SensorIsolationHelper (iss) chs mcs)
  end .


Definition SensorIsoation {n} ( miscompCount  : @AllMiscomparisonCount n ) ( cummHealth :@AllSensorCumulativeHealthFailure n) (isos : @AllIsolatedSensors n) : AllIsolatedSensors :=
  match miscompCount, cummHealth, isos with
  | (AllmisCount (xmc, ymc, zmc) ),(allSenHFcount (xh,yh,zh)),(alliso (xiso,yiso,ziso) ) => alliso (
                                                                                          SingleAxisSensorIsolations xmc xh xiso,
                                                                                          SingleAxisSensorIsolations ymc yh yiso,
                                                                                          SingleAxisSensorIsolations zmc zh ziso)
  end.
(* Function checks if all the values in vector is true
 *)
Arguments nil {A}.
Arguments cons {A} h {n} x.

Fixpoint isAllTrue {n} (v : vector bool n) :bool := match v with
                                            | nil   => true
                                            | cons x xs => andb x (isAllTrue xs)
                                            end.


(* Switch Flags *)
Definition ManageOBCSwitchFlag {n} (commIso : @CommIsolated n) (obcSwitch : OBCFlag) : OBCFlag:=
  match obcSwitch with
  | raised => raised
  | notRaised => match commIso with
                |CommIso v => match isAllTrue v with
                             | true => raised
                             | false => notRaised
                             end
                 end
  end .

(*This function takes 3 values and tells which of it is having miscomparison if any
This might not be the final Function to find the miscomparison in the sensor values
But for the demonstration purpose this function suffice
*)
Definition FlagMisComparison  (v1 v2 v3 :nat): option sensorId  :=
  let ms1 := mis_comp v1 v2 v3 in
  let ms2 := mis_comp v2 v1 v3 in
  let ms3 := mis_comp v3 v1 v2 in
  match ms1 with
  | true => Some (first)
  | false => match ms2 with
            | true => Some (second)
            | false => match ms3 with
                      | true => Some (third)
                      |false => None
                      end
            end
  end.
