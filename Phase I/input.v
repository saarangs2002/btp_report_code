Inductive relay {A:Type} : Type :=
| correct (n:A): relay 
| unhealthy (n:A): relay .

Definition sensor :=  @relay nat.

Check (correct 1).

Definition accusition :=  @relay sensor.

Check (correct(correct 1)).

Definition communication := @relay accusition.

Check (correct(correct(correct 1))).


Definition convert (i : communication) := match i with
                                          | correct(correct(correct n)) => Some n
                                          | correct(correct(unhealthy n)) => None n
                                          | correct(unhealthy(correct n)) => None n
                                          | unhealthy(correct(correct n)) => None n
                                          | correct(unhealthy(unhealthy n)) => None n
                                          | unhealthy(correct(unhealthy n)) => None n
                                          | unhealthy(unhealthy(correct n)) => None n
                                          | unhealthy(unhealthy(unhealthy n)) => None n
end.
