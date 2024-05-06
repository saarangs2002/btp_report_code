Require Import MyProject.library.
(*Require Import Vectors.Vector.*)
Require Import Vector.
Import VectorNotations.

(*------------------------------Current Sensors----------------------------*)
Inductive currSensor (n : nat): axis ->  Type :=
  SID (I : {i | i < n}) (ax : axis) : currSensor n ax.

(*-----------------------------Isolation Status----------------------------*)
Inductive IsolatedSensors {n : nat}: axis -> Type :=
  iso (ax : axis) : vector bool n -> IsolatedSensors ax.

(* Eg; *)
Definition isolatedX_ax : IsolatedSensors x_ax := iso x_ax  [true; true; true; true].
Check isolatedX_ax.


Inductive AllIsolatedSensors {n : nat}:  Type :=
  alliso : (@IsolatedSensors n x_ax)*(@IsolatedSensors n y_ax )*(@IsolatedSensors n z_ax ) -> AllIsolatedSensors.


Inductive AcquisitionIsolated {n : nat}:  Type :=
  AcqIso : vector bool n -> AcquisitionIsolated.


Inductive CommIsolated {n : nat}: Type :=
  CommIso : vector bool n -> CommIsolated.
                  
(*---------------------Cumulative Health Count-----------------------------*)

Inductive SensorCumulativeHealthFailure {n : nat}: axis -> Type :=
  SenHFcount (ax : axis) : vector nat n -> SensorCumulativeHealthFailure ax.

Inductive AllSensorCumulativeHealthFailure {n : nat} : Type :=
  allSenHFcount : ( @SensorCumulativeHealthFailure n x_ax)*(@SensorCumulativeHealthFailure n y_ax)*( @SensorCumulativeHealthFailure n z_ax) -> AllSensorCumulativeHealthFailure.

Inductive CumulativeHealthFailureAcq {n : nat} : Type :=
  AcqHFcount : vector nat n -> CumulativeHealthFailureAcq.
 
Inductive CumulativeHealthFailureComm {n : nat} : Type :=
 CommHFcount : vector nat n -> CumulativeHealthFailureComm.

(*----------------------------Miscomparison Count-------------------------*)

Inductive MiscomparisonCount {n : nat} : axis -> Type :=
  misCount (ax : axis) : vector nat n -> MiscomparisonCount ax.


Inductive AllMiscomparisonCount {n : nat} : Type :=
  AllmisCount : (@MiscomparisonCount n x_ax)*(@MiscomparisonCount n  y_ax)*(@MiscomparisonCount n  z_ax) -> AllMiscomparisonCount.

(*Use below OBCflag type*)
Inductive OBCFlag : Type :=
| raised : OBCFlag
| notRaised : OBCFlag.

Check (raised).
Check (notRaised).
