(* Inductive *)
Inductive ind :=
  | con1 :
      ind
  | con2 : ind
  | con3 : ind.

(* Match *)
Definition f (i j : ind) :=
  match i with
  | con1 =>
      true
  | con2 =>
      match j with
      | con1 => true
      | con2 =>
          false
      | _ => false
      end
  | con3 =>
      match j with
      | _ =>
          false
      end
  end.

(* Proof Body *)
Lemma p1 : True.
Proof.
  auto.
Qed.

Require Import Program.
Program Definition p2 (i : ind) : {i = i} + {i <> i} := _.
Next Obligation.
  idtac.
Abort.
Obligation 1.
  idtac.
Abort.
Next Obligation of p2.
  idtac.
Abort.
Obligation 1 of p2.
  decide equality.
Defined.

(* Empty Proof Body *)
Lemma p3 : True.
Proof.
Admitted.

Program Definition p4 (i : ind) : {i = i} + {i <> i} := _.
Next Obligation.
Abort.
Obligation 1.
Abort.
Next Obligation of p4.
Abort.
Obligation 1 of p4.
Admitted.

(* Sections and Modules *)
Section S1.
  Definition x := 1.

  Section S2.
    Definition y := 2.
  End S2.
  Section S3.
    Definition z := 3.
  End S3.
End S1.

Module M1.
  Definition x := 1.

  Module M2.
    Definition y := 2.
  End M2.
  Module M3.
    Definition z := 3.
  End M3.
End M1.

(* Records *)
Record r1 := {
  f1 : ind;
  f2 : ind
}.

Record r2 :=
  {
    f3 : r1;
    f4 : ind
  }.

Definition d1 : r1 := {|
  f1 := con1;
  f2 := con2;
|}.

Definition d2 : r2 :=
  {|
    f3 := d1;
    f4 := con3;
  |}.

Definition d3 : r2 :=
  {|
    f3 := {| f1 := con1; f2 := con3 |};
    f4 := con1
  |}.

(* Comments *)
Definition a1 := 1.
(* Line comment *)
Definition a2 := 2.
(* Block
   comment *)
Definition a3 := 3.

(* Proof Bullets *)
Lemma bul1 : forall i j k l m n : ind, True.
Proof.
  intros.
  destruct i.
  - idtac.
    destruct j.
    + destruct k.
      * idtac.
        destruct l.
        -- idtac.
           auto.
        -- auto.
        -- auto.
      * auto.
      * auto.
    + auto.
    + destruct k.
      * auto.
      * assert (l = l).
        {
          destruct l.
          - auto.
          - destruct m.
            + auto.
            + assert (n = n).
              { destruct n.
                - auto.
                - auto.
                - auto.
              }
              auto.
            + auto.
          - auto.
        }
        auto.
      * auto.
  - destruct j.
    + auto.
    + auto.
    + destruct k.
      * auto.
      * auto.
      * auto.
  - auto.
Qed.

Lemma bul2 : forall i j k : ind, True.
Proof.
  intros.
  destruct i.
  + destruct j; [auto | auto |].
    - idtac.
      destruct k.
      * auto.
      * auto.
      * auto.
  + auto.
  + auto.
Qed.
