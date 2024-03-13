Set Warnings "-notation-overridden, -ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra order.
Require Import BinPos BinNat Coq.Strings.Byte String Ascii HexadecimalN.
Require Import FunInd Recdef.
Require Import Coq.Numbers.Natural.Abstract.NOrder.

Set Warnings "notation-overridden, ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope N_scope.

Lemma pred_to_nat p : N.to_nat (N.pos p - 1) = (N.to_nat (N.pos p)).-1.
Proof.
elim: p => //.
by move=> p IH; rewrite -N.pred_sub Nnat.N2Nat.inj_pred.
Qed.

Lemma pos_succn_predn p : N.to_nat (N.pos p) = (N.to_nat ((N.pos p) - 1)).+1.
Proof.
rewrite pred_to_nat -(Lt.S_pred_pos (N.to_nat (N.pos p))) => //.
by elim nposeq: (N.pos p) => //=; apply: Pnat.Pos2Nat.is_pos.
Qed.

Function iotaN m n {wf N.lt n} :=
  if n isn't 0 then m :: (iotaN (m + 1) (n - 1)) else [::].
Proof.
   2: by apply: N.lt_wf_0.
move=> m n p nEq; have nNeq0: n <> 0 by rewrite nEq.
by rewrite -nEq N.sub_1_r; apply: (N.lt_pred_l n nNeq0).
Defined.

Lemma iotaN_P m n :
  iotaN m n = map N.of_nat (iota (N.to_nat m) (N.to_nat n)).
Proof.
functional induction (iotaN m n) => //=.
rewrite IHl; move: y IHl; case neq: n => // _; rewrite pos_succn_predn.
have iota_n1 n0 n1: iota n0 n1.+1 = n0 :: iota n0.+1 n1 by [].
by rewrite iota_n1 Nnat.N2Nat.inj_add // -addn1 map_cons Nnat.N2Nat.id.
Qed.

Function iterN {T : Type} n (f : T -> T) x {wf N.lt n} :=
  if n is 0 then x else f (iterN (n - 1) f x).
Proof.
  2: by apply: N.lt_wf_0.
move=> T n f x p nEq; have nNeq0: n <> 0 by rewrite nEq.
by rewrite -nEq N.sub_1_r; apply: (N.lt_pred_l n nNeq0).
Defined.

Lemma iterN_P T n f x : iterN n f x = (@ssrnat.iter T (N.to_nat n) f x).
Proof.
functional induction (iterN n f x) => //=.
by rewrite IHt; move: y IHt; case neq: n => // _; rewrite -iterS pos_succn_predn.
Qed.

Function nthN {T : Type} (x0 : T) (s : seq T) n {wf N.lt n} :=
  if n is 0 then (head x0 s)
  else nthN x0 (behead s) (n - 1).
Proof.
move=> T x0 s n p nEq; have nNeq0: n <> 0 by rewrite nEq.
by rewrite -nEq N.sub_1_r; apply: (N.lt_pred_l n nNeq0).
by apply: N.lt_wf_0.
Qed.

Lemma nthN_P {T : Type} (x0 : T) (s : seq T) n :
  nthN x0 s n = nth x0 s (N.to_nat n).
Proof.
functional induction nthN x0 s n; first by elim: s.
rewrite IHt; move: y IHt; case neq: n => // _ _.
by rewrite nth_behead pos_succn_predn.
Qed.

Fixpoint sizeN {T : Type} (s : seq T) :=
  if s is _ :: s' then N.succ (sizeN s') else 0.

Lemma sizeN_P {T : Type} (s : seq T) : sizeN s = N.of_nat (size s).
Proof.
by elim: s => [//=| /= x s ->]; elim: (size s).
Qed.

Function takeN {T : Type} (n : N)  (s : seq T) {wf N.lt n} :=
  if n is 0 then [::]  else if s is x :: s' then x :: takeN (n - 1) s'
  else [::].
Proof.
  2: by apply: N.lt_wf_0.
move=> T n s p nEq x s' sEq; have nNeq0: n <> 0 by rewrite nEq.
by rewrite -nEq N.sub_1_r; apply: (N.lt_pred_l n nNeq0).
Qed.

Lemma takeN_P {T : Type} n (s : seq T) : takeN n s = take (N.to_nat n) s.
Proof.
functional induction takeN n s; first by elim: s.
  rewrite IHl; move: y IHl; case neq: n => // _.
  by rewrite pos_succn_predn.
by move: y y0; elim s.
Qed.

Function dropN {T : Type} (n : N)  (s : seq T) {wf N.lt n} :=
  if s is x :: s' then if n is 0 then s else dropN (n - 1) s'
  else s.
Proof.
  2: by apply: N.lt_wf_0.
move=> T n s x s' sEq p nEq; have nNeq0: n <> 0 by rewrite nEq.
by rewrite -nEq N.sub_1_r; apply: (N.lt_pred_l n nNeq0).
Qed.

Lemma dropN_P {T : Type} n (s : seq T) : dropN n s = drop (N.to_nat n) s.
Proof.
functional induction dropN n s => //.
  rewrite IHl; move: y IHl; case neq: n => // _.
  by rewrite pos_succn_predn.
by move: y; elim s.
Qed.

Fixpoint lengthN s :=
  match s with
  | ""%string => 0
  | String _ s' => (lengthN s') + 1
  end.

Lemma lengthN_P s : lengthN s = N.of_nat (length s).
Proof.
elim: s => //= a s IH.
rewrite IH N.add_1_r -Nnat.Nat2N.inj_succ Pos.of_nat_succ.
by rewrite -Znat.positive_nat_N Pnat.Nat2Pos.id_max.
Qed.
