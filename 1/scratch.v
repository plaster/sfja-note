Module Playground1.

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day
  .

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* Exercise nandb *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => match b2 with
    | false => true
    | true => false
    end
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | false => false
  | true => match b2 with
    | false => false
    | true => b3
    end
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n: nat) : nat :=
match n with
| O => O
| S n' => n'
end.

End Playground1.

Module Playground2.

Definition minustwo (n: nat) : nat :=
match n with
| O => O
| S O => O
| S (S n') => n'
end.

Check S( S( S( S O ) ) ).
Eval simpl in (minustwo 11).
Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => evenb n'
end.

Definition oddb (n:nat) : bool := negb (evenb n).

Eval simpl in ( evenb 10 ). (* true *)
Eval simpl in ( evenb 9).   (* false *)
Eval simpl in ( oddb 10 ).  (* oddb 10 (!?) *)
Eval simpl in ( oddb 9).    (* oddb 9 (!?) *)

Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n:nat) (m:nat) : nat :=
match n with
| O => m
(*
| S n' => plus n' (S m)
*)
| S n' => S( plus n' m )
end.

Eval simpl in (plus (S (S (S O))) (S (S O)) ).

Fixpoint mult (n m : nat) : nat :=
match n with
| O => O
| S n' => plus m (mult n' m)
end.

Fixpoint minus (n m : nat) : nat :=
match n, m with
| O, _ => O
| _, O => n
| S n', S m' => minus n' m'
end.

Fixpoint exp (base power : nat) : nat :=
match power with
| O => S O
| S power' => mult base (exp base power')
end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
match n with
| O => S O
| S n' => mult n (factorial n')
end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

(* nat_scope ってなんだろう？ *)

Check (0 + (1 + 1)).
Check (0 + 1) + 1.

Fixpoint beq_nat (n m : nat) : bool :=
match n with
| O => match m with
  | O => true
  | S _ => false
  end
| S n' => match m with
  | O => false
  | S m' => beq_nat n' m'
  end
end.

Fixpoint ble_nat (n m : nat) : bool :=
match n with
| O => true
| S n' => match m with
  | O => false
  | S m' => ble_nat n' m'
  end
end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool := ble_nat (S n) m.
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  simpl. reflexivity. Qed.

(*
Theorem plus_n_0 : forall n:nat, n + 0 = n.
Proof.
  simpl. reflexivity. Qed.
  (* Error: Impossible to unify "n" with "n + 0". *)
  (* see plus_0_r *)
*)

Eval simpl in (forall n:nat, n + 0 = n).
(*
scripts
     = forall n : nat, n + 0 = n
     : Prop
*)
Eval simpl in (forall n:nat, 0 + n = n).
(*
scripts
     = forall n : nat, n = n
     : Prop
*)
(* 違い：後者は、最初の引数が0なので、match clauseが選べる。再帰不要。 *)

Theorem plus_id_example : forall n m : nat,
  n = m ->
  n + m = m + n.

Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
  Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.

Proof.
  intros n m o.
  intros H.
  intros I.
  rewrite -> H.
  rewrite -> I.
  reflexivity.
  Qed.

Theorem mult_O_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
  Qed.

Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  intros n m.
  simpl.
  reflexivity.
  Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [|n'].
  simpl. reflexivity.
  simpl. reflexivity.
  Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b as [|].
  simpl. reflexivity.
  simpl. reflexivity.
  Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [|n'].
  simpl. reflexivity.
  simpl. reflexivity.
  Qed.


(* tactic Case *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.



Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c.
  intros H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H.
    reflexivity.
  Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
    destruct b.
    SCase "b = true".
      reflexivity.
    SCase "b = false".
      reflexivity.
  Qed.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
  Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite <- IHn'. reflexivity.
  Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S(n')".
    simpl. rewrite -> IHn'. reflexivity.
  Qed.

Theorem plus_n_Sm : forall n m : nat, S(n + m) = n + S(m).
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S(n')".
    simpl. rewrite -> IHn'. reflexivity.
  Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction m as [|m'].
  Case "m = 0".
    simpl. rewrite -> plus_0_r. reflexivity.
  Case "m = S(m')".
    simpl. rewrite <- IHm'. rewrite -> plus_n_Sm. reflexivity.
  Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | 0 => 0
  | S(n') => S( S( double n' ))
  end.

Lemma double_plus : forall n : nat, double n = n + n.
  intros n.
  induction n.
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S(n')".
    simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
  Qed.

(* Exercise destruct_induction
 * induction は コンテキストに induction hypothesis が入る。natでなくても使える。
 *)
(*
Inductive tree : Type :=
| Leaf
| Node : tree -> tree -> tree.

Fixpoint tree_size (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node t' t'' => tree_size t' + tree_size t''
  end.

Theorem tree_size_plus : forall t u : tree, tree_size(Node t u) = tree_size t + tree_size u.
  intros t u.
  destruct t.
  Case "t = Leaf". simpl. reflexivity.
  Case "t = Node(t1 t2)". simpl. reflexivity.
  Qed.

Theorem tree_size_swap : forall t u : tree, tree_size(Node t u) = tree_size(Node u t).
  intros t u.
  induction u.
  Case "u = Leaf". simpl.
    induction t.
      simpl. reflexivity.
      simpl. rewrite <- tree_size_plus. rewrite <- plus_n_Sm. rewrite -> plus_0_r. reflexivity.
  Case "u = Node(t1 t2)". simpl.
    ...
*)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = S(n')". simpl. rewrite -> IHn'. reflexivity.
  Qed.

(* Exercise plus_comm_informal

 定理：加法は可換である。すなわち、任意の n, m について、以下が成り立つ。

  n + m = m + n

 証明： m についての帰納法を適用する。

 * まず m = 0 とおくと、証明するべき式は以下のようになる。
   n + 0 = 0 + n
   右辺を + の定義にしたがって簡約すると、 n となる。
   ところで定理「任意のnについて n + 0 = n である」が成り立つので
   左辺も n である。したがって n = n となり、この式は真である。
 * つぎに m = S m' と置き、帰納法の仮定を
   n + m' = m' + n とすると、
   S(n + m') = S(m' + n) も成立する。
   定理「任意の n, m について、S(n + m) = n + S(m) である」で左辺を変形すると：
   S(n + m') = n + S(m') = n + m
   + の定義にしたがって右辺を変形すると：
   S(m' + n) = S(m') + n = m + n
   したがって n + m = m + n が成立する。これは、直後の値について帰納法の仮定が成り立つことを示している。
 (証明終わり)
 *)

Theorem beq_nat_refl : forall n, true = beq_nat n n.
Proof. induction n. simpl. reflexivity.
  simpl. rewrite <- IHn. reflexivity.
  Qed.

(* Exercise beq_nat_refl_informal
 定理：任意の n について n ≧ n は常に真である
 証明：n についての帰納法を適用する。
 * n = 0 のとき: 0 ≧ 0 は真である。これは「≧」の定義より直ちに導かれる。
 * n = S(n') のとき: 帰納法の仮定より n' ≧ n' は真である。
   ここで「≧」の定義より S(n') ≧ S(n') も真である。
   これは成立を示すべき式「n ≧ n は真である」そのものなので、直後の値について帰納法の仮定が成立することが示された。
 (証明終わり)
*)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: (m + n) + p = m + (n + p)).
    Case "Proof of assertion".
      rewrite <- plus_assoc. reflexivity.
  rewrite <- H.
  assert (H': m + n = n + m).
    Case "Proof of assertion".
      rewrite <- plus_comm. reflexivity.
  rewrite -> H'.
  rewrite <- plus_assoc.
  reflexivity.
  Qed.

Lemma mult_m_Sn: forall m n : nat,
  m + m * n = m * S n.
Proof.
  intros m n.
  induction m as [|m'].
    Case "m=0". reflexivity.
    Case "m=Sm'".
      simpl. rewrite <- IHm'.
      rewrite <- plus_swap.
      reflexivity.
  Qed.

Theorem mult_comm: forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction n as [| n'].
  Case "n=0".
    rewrite -> mult_0_r. reflexivity.
  Case "n=S(n')".
    simpl.
    rewrite <- IHn'.
    rewrite -> mult_m_Sn.
    reflexivity.
  Qed.

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  (* 予想: inductionが必要。そのままじゃ簡約できないし、destructしてもそこで詰む。 *)
  intros n.
  induction n as [|n'].
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. rewrite <- IHn'. reflexivity.
  Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* 予想: 簡約だけで終わる。 *)
  reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* 予想: 簡約のためにはbが邪魔。destructで十分。 *)
  intros b. destruct b. reflexivity. reflexivity. Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  (* 予想: pについてのinduction。 *)
  intros n m p. intro H.
  induction p as [|p'].
    Case "p=0". simpl. rewrite -> H. reflexivity.
    Case "p=Sp'". simpl. rewrite -> IHp'. reflexivity.
  Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof. (* 予想: reflexivityで終了 *)
  reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof. (* 予想: 簡約だけで終了。 *)
  intros n.
  simpl.
  rewrite -> plus_0_r. (* 残念 rewriteが必要だった。 これは中でinductionしてる。 *)
  reflexivity.
  Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
           (negb c))
  = true.
Proof. (* 予想: destructが必要。inductionいらない。 *)
  intros b c.
  destruct b.
    Case "b=true". simpl.
      destruct c. reflexivity. reflexivity.
    Case "b=false". reflexivity.
  Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof. (* 予想: pについてのinduction *)
  intros n m.
  intro p.
  induction p as [|p'].
    Case "p=0". rewrite -> mult_0_r.
                rewrite -> mult_0_r.
                rewrite -> mult_0_r. reflexivity.
    Case "p=Sp'". rewrite <- mult_m_Sn.
                  rewrite <- mult_m_Sn.
                  rewrite <- mult_m_Sn.
                  rewrite -> IHp'.
                  rewrite <- plus_assoc.
                  rewrite <- plus_assoc.
                  assert (H: m + (n * p' + m * p') = n * p' + (m + m * p')).
                         rewrite -> plus_swap. reflexivity.
                  rewrite -> H.
                  reflexivity.
  Qed.


Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof. (* 予想: nについてのinductionでできる。
          が、destructと分配則と交換則でいけそうな気もするので試してみる *)
  intros n m p.
  induction n as [|n'].
    Case "n=0". reflexivity.
    Case "n=Sn'".
      simpl. rewrite -> mult_plus_distr_r.
      (* n' * (m * p) = n' * m * p がでてきてしまったのでやっぱりinduction必要だった *)
      rewrite -> IHn'. reflexivity.
  Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  replace (n + p) with (p + n).
  replace (n + (m + p)) with ((m + p) + n).
  rewrite -> plus_assoc. reflexivity.
  Case "proof of replace 1".
    rewrite -> plus_comm. reflexivity.
  Case "proof of replace 2".
    rewrite -> plus_comm. reflexivity.
  Qed.


(* (a) *)
Inductive bin : Type :=
| B : bin
| Ev : bin -> bin
| Od : bin -> bin
.

(* (b) *)
Fixpoint bin_succ (x : bin) : bin :=
match x with
| B => Od B
| Ev x' => Od x'
| Od x' => Ev (bin_succ x')
end.

Fixpoint nat_from_bin ( x : bin ) : nat :=
match x with
| B => 0
| Ev x' => nat_from_bin x' + nat_from_bin x'
| Od x' => S(nat_from_bin x' + nat_from_bin x')
end.

(* (c) *)

Theorem binsucc_binnat_compatible: forall x : bin,
  nat_from_bin(bin_succ(x)) = S(nat_from_bin(x)).

Proof.
  intro x.
  induction x as [|x'|x'].
  Case "x=B".
    reflexivity.
  Case "x=Ev x'".
    simpl. reflexivity.
  Case "x=Od x'".
    simpl.
    rewrite -> IHx'. simpl. rewrite -> plus_comm. simpl.
    reflexivity.
    Qed.

(* exercise binary_inverse *)
(* (a) *)

Fixpoint bin_from_nat ( n : nat ) : bin :=
match n with
| O => B
| S n' => bin_succ (bin_from_nat n')
end.

Theorem nat_from_bin_from_nat : forall n : nat,
  nat_from_bin ( bin_from_nat n ) = n.

Proof.
  intros n.
  induction n as [|n'].
  Case "n=0". simpl. reflexivity.
  Case "n=S n'".
    simpl.
    rewrite -> binsucc_binnat_compatible.
    rewrite -> IHn'.
    reflexivity.
  Qed.

(* (b)
  O に対応する二進表現が複数、というか無限にあるため。
  B, Ev B, Ev( Ev B ), ...
  これらはいわゆる leading zero に相当する。
 *)

(* (c) *)


Fixpoint normalize ( x : bin ) : bin :=
  bin_from_nat ( nat_from_bin x ).

Theorem normalize_fixpoint : forall x : bin,
  normalize x = normalize(normalize x).

Proof.
  intros x.
  induction x as [|x'|x'].
  Case "x=B". reflexivity.
  Case "x=Ev x'".
    simpl.
    destruct (nat_from_bin x') as [|n'].
    SCase "n=0". reflexivity.
    SCase "n=Sn'". simpl. rewrite -> plus_comm.
    simpl.
    admit.
  Case "x=Od x'".
    admit.
  Qed.


End Playground2.