Set Warnings "-notation-overridden, -ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra order.
From SHA256 Require Import N_sha256 SHA256_spec N_sha.
From SHA256 Require Import N_ssrnat_sha ssrnat_sha seq_sha.
Require Import BinPos BinNat Coq.Strings.Byte String Ascii HexadecimalN.
Set Warnings "notation-overridden, ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope N_scope.

(* Basic conversions *)

Definition rev_bool_B B := bool_B_of_seq (rev (bool_B_to_seq B)).

Definition byte_to_bool_B b := rev_bool_B (bool_B_decode (to_bits b)).
Definition byte_of_bool_B B := of_bits (bool_B_code (rev_bool_B B)).

Lemma byte_to_bool_BK : cancel byte_to_bool_B byte_of_bool_B.
Proof. by case. Qed.

Lemma byte_of_bool_BK : cancel byte_of_bool_B byte_to_bool_B.
Proof. by case; do 8! case. Qed.

Lemma bool_B_of_nat256_byte m :
    m < 256 -> bool_B_of_nat256 (N.to_nat m) = byte_to_bool_B (of_N256 m).
Proof. by case: m => // p; do 256! case: p => [p|p|] //. Qed.

Definition seq_byte_to_seq_bool_B s := map byte_to_bool_B s.
Definition seq_byte_of_seq_bool_B s := map byte_of_bool_B s.

Lemma seq_byte_to_seq_bool_BK :
  cancel seq_byte_to_seq_bool_B seq_byte_of_seq_bool_B.
Proof. by apply: mapK; apply byte_to_bool_BK. Qed.

Lemma seq_byte_of_seq_bool_BK :
  cancel seq_byte_of_seq_bool_B seq_byte_to_seq_bool_B.
Proof. by apply: mapK; apply byte_of_bool_BK. Qed.

Definition string_to_seq_bool_B s := map byte_to_bool_B (list_byte_of_string s).
Definition string_of_seq_bool_B b := string_of_list_byte (map byte_of_bool_B b).

Lemma string_to_seq_bool_BK : cancel string_to_seq_bool_B string_of_seq_bool_B.
Proof.
move=> s; rewrite /string_to_seq_bool_B /string_of_seq_bool_B mapK.
  by apply: string_of_list_byte_of_string.
by apply: byte_to_bool_BK.
Qed.

Lemma string_of_seq_bool_BK : cancel string_of_seq_bool_B string_to_seq_bool_B.
Proof.
move=> s; rewrite /string_to_seq_bool_B /string_of_seq_bool_B.
rewrite list_byte_of_string_of_list_byte mapK //.
by apply: byte_of_bool_BK.
Qed.

(* Conversions between bool_B/32/256/512 and N *)

Definition bool_B_to_N b := N.of_nat (bool_B_to_nat b).
Definition bool_B_of_N n := bool_B_of_nat256 (N.to_nat n).

Definition bool_32b_to_N s := N.of_nat (bool_32b_to_nat s).
Definition bool_32b_of_N n := bool_32b_of_nat2e32 (N.to_nat n).

Definition seq_32b_to_seq_N s := map bool_32b_to_N s.
Definition seq_32b_of_seq_N s := map bool_32b_of_nat2e32 (map N.to_nat s).

Definition bool_256b_to_N b :=
  let boolseq := [seq bool_32b_to_N i |
                   i <- [:: H0 b; H1 b; H2 b; H3 b; H4 b; H5 b; H6 b; H7 b]] in
  foldl (fun n => [eta N.add (n * (2 ^ 32) )]) 0 boolseq.

Definition bool_256b_of_N n :=
  Bool_256b
    (bool_32b_of_N (n / wexp ^ 7))
    (bool_32b_of_N ((n / wexp ^ 6) mod wexp))
    (bool_32b_of_N ((n / wexp ^ 5) mod wexp))
    (bool_32b_of_N ((n / wexp ^ 4) mod wexp))
    (bool_32b_of_N ((n / wexp ^ 3) mod wexp))
    (bool_32b_of_N ((n / wexp ^ 2) mod wexp))
    (bool_32b_of_N ((n / wexp) mod wexp))
    (bool_32b_of_N (n mod wexp)).

(* Definition bool_256b_to_seq_N s := ?. *)

Definition bool_256b_of_seq_N s :=
  if (size s) is 8%nat then
    let s0 := nth 0 s 0 in
    let s1 := nth 0 s 1 in
    let s2 := nth 0 s 2 in
    let s3 := nth 0 s 3 in
    let s4 := nth 0 s 4 in
    let s5 := nth 0 s 5 in
    let s6 := nth 0 s 6 in
    let s7 := nth 0 s 7 in
  Bool_256b
    (bool_32b_of_N s0) (bool_32b_of_N s1)
    (bool_32b_of_N s2) (bool_32b_of_N s3)
    (bool_32b_of_N s4) (bool_32b_of_N s5)
    (bool_32b_of_N s6) (bool_32b_of_N s7)
    else
  Bool_256b bool_32b00 bool_32b00 bool_32b00 bool_32b00
    bool_32b00 bool_32b00 bool_32b00 bool_32b00.

Definition bool_512b_to_seq_N B :=
  map N.of_nat (map bool_32b_to_nat (bool_512b_to_seq_bool_32b B)).
Definition bool_512b_of_seq_N s :=
  nth bool_512b00 (seq_32b_to_seq_512b (map bool_32b_of_N s)) 0.

Definition seq_512b_to_seq_seq_N s :=
  map seq_32b_to_seq_N (map bool_512b_to_seq_bool_32b s).
Definition seq_512b_of_seq_seq_N s := map bool_512b_of_seq_N s.

Lemma to_N_lt256 b : to_N b < 256.
Proof. by case b. Qed.

Lemma N_of_byte_bool b : bool_B_to_N (byte_to_bool_B b) = to_N b.
Proof. by case: b. Qed.

Lemma wexp' : wexp = 256 ^ 4.
Proof. by []. Qed.

Lemma bool_B_to_N_lt256 B : bool_B_to_N B < 256.
Proof.
rewrite /bool_B_to_N; apply/N_ltn; rewrite Nnat.Nat2N.id.
by apply: bool_B_to_nat_lt256.
Qed.

Lemma bool_B_of_N256K n : n < 256 -> bool_B_to_N (bool_B_of_N n) = n.
Proof.
move=> n_lt256; rewrite /bool_B_to_N /bool_B_of_N.
by rewrite bool_B_of_nat256K; try apply/Nat_lt; rewrite Nnat.N2Nat.id.
Qed.

Lemma bool_B_to_N_char B :
  bool_B_to_N B
    = N.of_nat (b0 B) * 2 ^ 7 + N.of_nat (b1 B) * 2 ^ 6 +
        N.of_nat (b2 B) * 2 ^ 5 + N.of_nat (b3 B) * 2 ^ 4 +
          N.of_nat (b4 B) * 2 ^ 3 + N.of_nat (b5 B) * 2 ^ 2 +
            N.of_nat (b6 B) * 2 + N.of_nat (b7 B).
Proof.
rewrite /bool_B_to_N bool_B_to_nat_char !Nat_add !Nat_mul !Nat_pow.
by rewrite !Nnat.N2Nat.id.
Qed.

Lemma bool_32b_to_N_char B :
  bool_32b_to_N B
    = bool_B_to_N (B0 B) * 256 ^ 3 + bool_B_to_N (B1 B) * 256 ^ 2 +
        bool_B_to_N (B2 B) * 256 + bool_B_to_N (B3 B).
Proof.
rewrite /bool_32b_to_N bool_32b_to_nat_char.
by rewrite !Nat_add !Nat_mul !Nat_pow ?{1}Nnat.N2Nat.id.
Qed.

Lemma bool_32b_to_NK : cancel bool_32b_to_N bool_32b_of_N.
Proof.
move=> k; rewrite /bool_32b_to_N /bool_32b_of_N Nnat.Nat2N.id.
by apply: bool_32b_to_natK.
Qed.

Lemma bool_32b_of_N2e32K n : n < 2 ^ 32 -> bool_32b_to_N (bool_32b_of_N n) = n.
Proof.
move=> nbound; rewrite /bool_32b_to_N /bool_32b_of_N bool_32b_of_nat2e32K.
  by rewrite Nnat.N2Nat.id.
by move: nbound; rewrite leq_ltn N_ltn Nat_pow.
Qed.

Lemma bool_32b_of_N2e32K_seq s :
  {in s, forall x : N, x < 2 ^ 32} -> s = map bool_32b_to_N (map bool_32b_of_N s).
Proof.
by move=> Hsx; rewrite all_mapK //; move=> y /Hsx; apply bool_32b_of_N2e32K.
Qed.

Lemma bool_32b_to_N_lt2e32 b : bool_32b_to_N b < 2 ^ 32.
Proof.
rewrite -/wexp wexp' N_expn; apply/N_ltn; rewrite !Nnat.Nat2N.id.
by rewrite ?expn_eq; apply: bool_32b_to_nat_lt_2e32.
Qed.

Lemma bool_256b_to_N_char b :
  bool_256b_to_N b
    = bool_32b_to_N (H0 b) * wexp ^ 7 + bool_32b_to_N (H1 b) * wexp ^ 6 +
        bool_32b_to_N (H2 b) * wexp ^ 5 + bool_32b_to_N (H3 b) * wexp ^ 4 +
          bool_32b_to_N (H4 b) * wexp ^ 3 + bool_32b_to_N (H5 b) * wexp ^ 2 +
            bool_32b_to_N (H6 b) * wexp + bool_32b_to_N (H7 b).
Proof.
have foldl8 a1 a2 a3 a4 a5 a6 a7 a8 c :
  foldl (fun n : N => [eta N.add (n * c)]) 0 [:: a1; a2; a3; a4; a5; a6; a7; a8]
    = a1 * c ^ 7 + a2 * c ^ 6 + a3 * c ^ 5 + a4 * c ^ 4 + a5 * c ^ 3 +
        a6 * c ^ 2 + a7 * c + a8.
  rewrite /foldl N.mul_0_l N.add_0_l !N.mul_add_distr_r.
  rewrite (N.pow_succ_r' _ 6) (N.pow_succ_r' _ 5) (N.pow_succ_r' _ 4).
  rewrite (N.pow_succ_r' _ 3) (N.pow_succ_r' _ 2) (N.pow_succ_r' _ 1).
  by rewrite N.pow_1_r !N.mul_assoc.
have char256_aux :
  [seq bool_32b_to_N i |
    i <- [:: H0 b; H1 b; H2 b; H3 b; H4 b; H5 b; H6 b; H7 b]]
      = [:: bool_32b_to_N (H0 b); bool_32b_to_N (H1 b);
          bool_32b_to_N (H2 b); bool_32b_to_N (H3 b);
            bool_32b_to_N (H4 b); bool_32b_to_N (H5 b);
              bool_32b_to_N (H6 b); bool_32b_to_N (H7 b)] by [].
by rewrite /bool_256b_to_N char256_aux.
Qed.

Lemma bool_256b_to_NK : cancel bool_256b_to_N bool_256b_of_N.
Proof.
move=> b.
elim b; move=> h0 h1 h2 h3 h4 h5 h6 h7.
rewrite /bool_256b_of_N bool_256b_to_N_char.
have Npow2_lt a1 a2 n: 0 < n -> a1 < n -> a2 < n -> a1 * n + a2 < n ^ 2.
  move=> n0 Ha1 Ha2; rewrite -{1}(N.pow_1_r n); apply: N_lt_bound_pow => //.
  by rewrite N.pow_1_r.
have bool_32b_to_N_lt2e32 := bool_32b_to_N_lt2e32.
rewrite -?N.add_assoc.
rewrite N.div_add_l; last by apply: N.pow_nonzero.
rewrite N.div_small; last by do 5! apply: N_lt_bound_pow => //; apply/Npow2_lt.
rewrite -[7]/(N.succ 6) N.pow_succ_r'.
rewrite N.mul_assoc N.add_assoc -N.mul_add_distr_r.
rewrite N.div_add_l; last by apply: N.pow_nonzero.
rewrite N.div_small; last by do 4! apply: N_lt_bound_pow => //; apply/Npow2_lt.
rewrite ?N.add_0_r N.add_comm N.mod_add //; rewrite N.mod_small //.
rewrite -[6]/(N.succ 5) !N.pow_succ_r'.
rewrite N.mul_assoc N.add_assoc -4?N.mul_add_distr_r.
rewrite N.div_add_l; last by apply: N.pow_nonzero.
rewrite N.div_small; last by do 3! apply: N_lt_bound_pow => //; apply/Npow2_lt.
rewrite N.add_0_r N.add_comm N.mod_add // N.mod_small //.
rewrite -[5]/(N.succ 4) !N.pow_succ_r'.
rewrite N.mul_assoc N.add_assoc -3?N.mul_add_distr_r.
rewrite N.div_add_l; last by apply: N.pow_nonzero.
rewrite N.div_small; last by do 2! apply: N_lt_bound_pow => //; apply/Npow2_lt.
rewrite N.add_0_r N.add_comm N.mod_add // N.mod_small //.
rewrite -[4]/(N.succ 3) !N.pow_succ_r'.
rewrite N.mul_assoc N.add_assoc -4?N.mul_add_distr_r.
rewrite N.div_add_l; last by apply: N.pow_nonzero.
rewrite N.div_small; last by apply: N_lt_bound_pow => //; apply/Npow2_lt.
rewrite N.add_0_r N.add_comm N.mod_add // N.mod_small //.
rewrite -[3]/(N.succ 2) !N.pow_succ_r'.
rewrite N.mul_assoc N.add_assoc -N.mul_add_distr_r.
rewrite N.div_add_l; last by apply: N.pow_nonzero.
rewrite N.div_small; last by apply/Npow2_lt.
rewrite N.add_0_r N.add_comm N.mod_add // N.mod_small //.
rewrite -[2]/(N.succ 1) !N.pow_succ_r'.
rewrite N.mul_assoc N.add_assoc -N.mul_add_distr_r.
rewrite N.div_add_l; last by apply: N.pow_nonzero.
rewrite N.div_small //.
rewrite N.add_0_r N.add_comm N.mod_add // N.mod_small //.
rewrite N.pow_1_r -7?N.mul_add_distr_r N.add_comm N.mod_add // ?N.mod_small //.
by rewrite !bool_32b_to_NK.
Qed.

Lemma bool_256b_to_N2e256K n :
  n < 2 ^ 256 -> bool_256b_to_N (bool_256b_of_N n) = n.
Proof.
have decomp7 m:
    m <> 0 ->
  n = n / m ^ 7 * m ^ 7 + (n / m ^ 6) mod m * m ^ 6 +
        (n / m ^ 5) mod m * m ^ 5 + (n / m ^ 4) mod m * m ^ 4 +
          (n / m ^ 3) mod m * m ^ 3 + (n / m ^ 2) mod m * m ^ 2 +
            (n / m) mod m * m + n mod m.
  move=> mneq0.
  have N_div_mod a b : a = (a / b) * b + a mod b.
    by rewrite {1}(N.div_mod' a b) N.mul_comm.
  rewrite {1}(N_div_mod n m).
  rewrite {1}(N_div_mod (n / m) m) Nmult_plus_distr_r.
  rewrite !N.div_div // -N.mul_assoc -!N.pow_2_r.
  rewrite {1}(N_div_mod (n / m ^ 2) m) !Nmult_plus_distr_r.
  rewrite !N.div_div //; last by apply: N.pow_nonzero.
  rewrite (N.mul_comm (m ^ 2)) -N.mul_assoc -!N.pow_succ_r'.
  rewrite {1}(N_div_mod (n / m ^ 3) m) !Nmult_plus_distr_r.
  rewrite !N.div_div //; last by apply: N.pow_nonzero.
  rewrite (N.mul_comm (m ^ 3)) -N.mul_assoc -!N.pow_succ_r'.
  rewrite {1}(N_div_mod (n / m ^ 4) m) !Nmult_plus_distr_r.
  rewrite !N.div_div //; last by apply: N.pow_nonzero.
  rewrite (N.mul_comm (m ^ 4)) -N.mul_assoc -!N.pow_succ_r'.
  rewrite {1}(N_div_mod (n / m ^ 5) m) !Nmult_plus_distr_r.
  rewrite !N.div_div //; last by apply: N.pow_nonzero.
  rewrite (N.mul_comm (m ^ 5)) -N.mul_assoc -!N.pow_succ_r'.
  rewrite {1}(N_div_mod (n / m ^ 6) m) !Nmult_plus_distr_r.
  rewrite !N.div_div //; last by apply: N.pow_nonzero.
  by rewrite (N.mul_comm (m ^ 6)) -N.mul_assoc -!N.pow_succ_r'.
move=> nbound; rewrite bool_256b_to_N_char.
have mod2e32 a: a mod 2 ^ 32 < 2 ^ 32 by apply: N.mod_upper_bound.
rewrite !bool_32b_of_N2e32K //; last by apply: N.div_lt_upper_bound.
by rewrite {9}(decomp7 (2 ^ 32)).
Qed.

(* Preprocessing correspondence *)

(* Correspondence tails *)

Lemma preprocessing_tailsE (s : seq bool_B) :
    N.of_nat (size s) * 8 < (256 ^ 8) ->
  [:: (nat2e64_to_bool_32b (size s * 8)).1; (nat2e64_to_bool_32b (size s * 8)).2]
    = seq_B_to_seq_32b [seq byte_to_bool_B i |
        i <- seq_byte_of_64bitN (N.of_nat (size s) * 8)].
Proof.
move=> leq256e8; rewrite /= /bool_32b_of_nat2e32  -!divnMA.
rewrite -!bool_B_of_nat256_byte; [|apply: N.mod_upper_bound => //..|].
  rewrite -!(expnD 256) -expnSr -[(4 + 3)%nat]/(7%nat) -[(4 + 2)%nat]/(6%nat).
  have N_nat_eq n m: N.of_nat m = n -> m = N.to_nat n.
    by move=> <-; rewrite Nnat.Nat2N.id.
  congr cons => //.
    apply: bool_32b_eq => /=; apply: f_equal; apply: N_nat_eq.
- by rewrite Nat_div Nat_mul Nat_pow !Nnat.N2Nat.id; apply: div_eq.
- rewrite Nat_mod Nat_div Nat_mul Nat_pow !Nnat.N2Nat.id.
  by apply: mod_eq => //; apply: div_eq.
- rewrite Nat_mod Nat_div Nat_mul Nat_pow !Nnat.N2Nat.id.
  by apply: mod_eq => //; apply: div_eq.
- rewrite Nat_mod Nat_div Nat_mul Nat_pow !Nnat.N2Nat.id.
  by apply: mod_eq => //; apply: div_eq.
  congr cons; apply: bool_32b_eq => /=; apply: f_equal; apply: N_nat_eq.
- rewrite (expnS 256 3) -modn_divl.
  rewrite Nat_mod Nat_div Nat_mul Nat_pow !Nnat.N2Nat.id.
  by apply: mod_eq => //; apply: div_eq.
- rewrite (expnD 256 2 2) -modn_divl -{2}mulnn modn_mult.
  rewrite Nat_mod Nat_div Nat_mul Nat_pow !Nnat.N2Nat.id.
  by apply: mod_eq => //; apply: div_eq.
- rewrite (expnSr 256 3) -modn_divl (expnS 256 2) modn_mult.
  rewrite Nat_mod Nat_div Nat_mul !Nnat.N2Nat.id.
  by apply: mod_eq => //; apply: div_eq.
- rewrite (expnS 256 3) modn_mult.
  rewrite Nat_mod Nat_mul !Nnat.N2Nat.id.
  by apply: mod_eq => //; apply: div_eq.
by apply: N.div_lt_upper_bound.
Qed.

(* Correspondence mod_padding *)

Lemma mod_paddingE n : mod_padding n = (N_sha256.mod_padding (N.of_nat n)).
Proof.
rewrite /mod_padding /N_sha256.mod_padding -addn1.
case: ifP => c1; case: ifP => c2; move: c1 c2; rewrite !nat_of_bin_N_to_nat.
- by rewrite N_subn N_addn N_modn !Nnat.Nat2N.id.
- by rewrite N_leq N_modn N_addn !Nnat.Nat2N.id => ->.
- by rewrite N_leq N_modn N_addn !Nnat.Nat2N.id => ->.
- by rewrite N_addn N_subn N_modn N_addn !Nnat.Nat2N.id.
Qed.

(* Correspondence padding_aux *)

Lemma padding_auxE n :
  padding_aux n = map byte_to_bool_B (N_sha256.padding_aux n).
Proof.
elim: n => // n; case: n => // n; rewrite map_cons => IH.
rewrite !map_cons; congr cons; rewrite !iterS; congr cons.
have eq_cons (a : bool_B) s s': a :: s = a :: s' -> s = s'.
  by move/eqP; rewrite eqseq_cons; move/andP => [_ /eqP y].
by move/eq_cons: IH.
Qed.

(* Other auxiliary lemmas and final proof *)

Lemma padding_aux_modE s :
  (s ++ padding_aux ((mod_padding ((size s) * 8)).+1 %/ 8))
    = (map byte_to_bool_B ((map byte_of_bool_B s) ++ N_sha256.padding_aux
        ((N_sha256.mod_padding
          (N.of_nat ((size (map byte_of_bool_B s)) * 8)) + 1) / 8))).
Proof.
rewrite map_cat; rewrite mapK; last by apply: byte_of_bool_BK.
congr cat; rewrite size_map -addn1 N_divn N_addn mod_paddingE padding_auxE.
by rewrite !nat_of_bin_N_to_nat !Nnat.Nat2N.id.
Qed.

Lemma _paddingE s : (* nombre? *)
    N.of_nat (size s) * 8 < 256 ^ 8 ->
  seq_B_to_seq_32b (s ++ padding_aux ((mod_padding ((size s) * 8)).+1 %/ 8)) ++
    [:: (nat2e64_to_bool_32b (size s * 8)).1;
      (nat2e64_to_bool_32b (size s * 8)).2]
        = seq_B_to_seq_32b
            (map byte_to_bool_B (N_sha256.padding (map byte_of_bool_B s))).
Proof.
rewrite padding_aux_modE !map_cat mapK => h_s; last by apply: byte_of_bool_BK.
rewrite catA [in RHS]seq_B_to_seq_32b_cat; last by rewrite !size_map.
congr cat; first by rewrite Nat_mul Nnat.N2Nat.id.
by rewrite preprocessing_tailsE // size_map.
Qed.

Lemma size_padding_div64 s :
    N.of_nat (size s) * 8 < 256 ^ 8 ->
  64 %| size (N_sha256.padding [seq byte_of_bool_B i | i <- s]).
Proof.
move=> h_s; rewrite !size_cat size_map /=.
have -> n:
  size (N_sha256.padding_aux n)
    = size (map byte_to_bool_B (N_sha256.padding_aux n)) by rewrite size_map.
rewrite -padding_auxE padding_aux_size.
rewrite nat_of_bin_N_to_nat N_divn N_addn N_muln.
rewrite -!nat_of_bin_N_to_nat -mod_paddingE !nat_of_bin_N_to_nat.
rewrite !Nnat.Nat2N.id /mod_padding.
have modn512:
  (muln (size s) 8).+1 %% N.to_nat 512 = ((muln (size s) 8) %% N.to_nat 512).+1.
  rewrite -addn1 -modnDC // addn1 //.
  rewrite -[N.to_nat 512]/(muln (N.to_nat 64) 8) -muln_modl.
  rewrite -{2}[N.to_nat 64]/(63.+1) mulSnr -addn1 addSnnS.
  by apply: leq_add => //; rewrite leq_pmul2r // -ltnS; apply: ltn_pmod.
have divn64: subn (size s) (size s %% 64) = muln (size s %/ 64) 64.
  by rewrite {1}(divn_eq (size s) 64) addnK.
case: ifP => H_ifP.
  rewrite modn512 subnS addn1 prednK; last first.
    by rewrite subn_gt0 -modn512 H_ifP //.
  rewrite ?divnBr; last first.
    by rewrite dvdn_modn -[N.to_nat 512]/(muln 8 64) modn_mult modnMl.
  rewrite addnA addnABC.
      rewrite -(@modn_divl _ 64 8) mulnK // divn64 -[448 %/ N.to_nat 8]/(56%nat).
      rewrite /= -addnA; apply: dvdn_add => //.
      by apply: dvdn_mull; apply: dvdnn.
    by rewrite -{2}(@mulnK (size s) 8) // leq_div2r // leq_mod.
  by rewrite leq_div2r // ltnW // -modn512.
rewrite modn512 subnS addn1 -addnS prednK; last first.
  by rewrite subn_gt0; apply: ltn_pmod.
rewrite (@divnDr _ _ 8); last first.
  apply: dvdn_sub => //; rewrite -[N.to_nat 512]/(muln 64 8) -muln_modl.
  by apply: dvdn_mull.
rewrite divnBr; last first.
  by rewrite dvdn_modn (modn_mult 8 _ 64) modnMl.
rewrite addnBA; last by apply: leq_div2r; apply ltnW; apply: ltn_pmod.
rewrite -[N.to_nat 512]/(muln 64 8) -(@modn_divl _ 64 8) !mulnK //.
rewrite addnA addnABC; last first.
    apply: leq_trans; first by apply: (ltnW (ltn_mod (size s) 64)).
    by apply: leq_addl.
  by apply: leq_mod.
by rewrite divn64 -addnA; apply: dvdn_add => //; apply: dvdn_mull; apply: dvdnn.
Qed.

Lemma w32_to_NE b1 b2 b3 b4:
  w32_to_N b1 b2 b3 b4 =
  bool_32b_to_N {| B0 := byte_to_bool_B b1; B1 := byte_to_bool_B b2;
                     B2 := byte_to_bool_B b3; B3 := byte_to_bool_B b4 |}.
Proof.
rewrite /w32_to_N /= bool_32b_to_N_char !N_of_byte_bool ?N.mul_add_distr_r.
by rewrite (N.pow_succ_r' _ 2) N.pow_2_r -!N.mul_assoc.
Qed.

Lemma seq_byte_to_32b_split_w32E s k :
    size s = (k * 64)%nat ->
  seq_B_to_seq_32b [seq byte_to_bool_B i | i <- s]
    = [seq bool_32b_of_N i | i <- split_w32 s].
Proof.
elim: k s => [s|k IH s size_s]; first by rewrite mul0n; move/size0nil => ->.
have seq_byte_to_32b_split_w32E64 s' :
    size s' = (N.to_nat 64) ->
  seq_B_to_seq_32b [seq byte_to_bool_B i | i <- s']
    = [seq bool_32b_of_N i | i <- split_w32 s'].
  move=> h64; rewrite /split_w32 /=.
  rewrite (seq_size x00 h64) => /=.
  by rewrite !w32_to_NE !bool_32b_to_NK.
have size_t: size (take 64 s) = N.to_nat 64.
  by rewrite size_takel // size_s mulnC leq_pmulr.
move: size_s; rewrite mulSn => size_s.
have size_d: size (drop 64 s) = (k * (N.to_nat 64))%nat.
  by rewrite size_drop size_s addnC addnK.
rewrite -(cat_take_drop 64 s) map_cat.
have size_d':
  size [seq byte_to_bool_B i | i <- drop 64 s] = (4 * (16 * k))%nat.
  by rewrite size_map size_d mulnC mulnA.
have size_d'':
  size [seq byte_to_bool_B i | i <- drop 64 s] = 4 * (N.of_nat (16 * k)).
  rewrite size_map size_d nat_of_bin_N_to_nat N_muln ?Nnat.Nat2N.id.
  by rewrite mulnC mulnA.
rewrite (seq_B_to_seq_32b_cat [seq byte_to_bool_B i | i <- take 64 s]).
  rewrite seq_byte_to_32b_split_w32E64 // (IH (drop 64 s)) //.
  have aux1: N.to_nat 64 = muln 4 16 by [].
  rewrite aux1 in size_t; rewrite size_map in size_d'.
  by rewrite (size_w32_mult4 size_t size_d') map_cat.
by rewrite size_d'' nat_of_bin_N_to_nat N_muln Nnat.Nat2N.id modnMr.
Qed.

Lemma seq_byte_to_seq_32bE s k : (*preprocessing_aux?*)
    size s = (k * 64)%nat ->
  seq_B_to_seq_32b [seq byte_to_bool_B i | i <- s]
    = [seq bool_32b_of_N i | i <- flatten [seq split_w32 x |
        x <- split_in_blocks s ((size s %/ N.to_nat 64) - 1)%nat]].
Proof.
elim: k s => [s|k IH s size_s]; first by rewrite mul0n; move/size0nil => ->.
have size_t: size (take 64 s) = N.to_nat 64.
  by rewrite size_takel // size_s mulnC leq_pmulr.
move: size_s; rewrite mulSn => size_s.
have size_d: size (drop 64 s) = (k * (N.to_nat 64))%nat.
  by rewrite size_drop size_s addnC addnK.
rewrite -(cat_take_drop 64 s).
case C: (leq (size s %/ 64) 1).
  rewrite size_cat size_t size_d -size_s.
  rewrite (split_in_blocks_dec0 C) map_cat /= ?cats0 -map_cat.
  rewrite (cat_take_drop 64 s).
  move: size_s; rewrite -mulSn => size_s.
  by rewrite (seq_byte_to_32b_split_w32E size_s).
rewrite leqNgt in C; move/negbFE: C => C.
rewrite size_cat size_t size_d -size_s.
rewrite (split_in_blocks_dec C) map_cons /= ?map_cat.
have size_s':
  size [seq byte_to_bool_B i | i <- drop 64 s] = 4 * (N.of_nat (16 * k)).
  rewrite size_map size_d nat_of_bin_N_to_nat N_muln.
  by rewrite ?Nnat.Nat2N.id mulnC mulnA.
rewrite (seq_B_to_seq_32b_cat [seq byte_to_bool_B i | i <- take 64 s]).
  congr cat.
    have size_t': size (take 64 s) = (1 * (N.to_nat 64))%nat => //.
    by rewrite (seq_byte_to_32b_split_w32E size_t').
  by rewrite (IH (drop 64 s)) size_d // size_s divnDl //.
rewrite size_s' nat_of_bin_N_to_nat N_muln.
by rewrite Nnat.Nat2N.id modnMr.
Qed.

Lemma preprocessingE s :
    N.of_nat (size s) * 8 < 256 ^ 8 ->
  preprocessing s
    = seq_32b_to_seq_512b (map bool_32b_of_N (flatten
        (N_sha256.preprocessing (string_of_seq_bool_B s)))).
Proof.
move=> size_bound; rewrite /preprocessing _paddingE // /N_sha256.preprocessing.
rewrite /string_of_seq_bool_B list_byte_of_string_of_list_byte.
move: (size_padding_div64 size_bound); move/dvdnP => [k prop].
by rewrite (seq_byte_to_seq_32bE prop).
Qed.

(* Properties about and, or, lxor, neg, shiftr, shiftl *)
(* Toda esta sección? A parte? *)

Lemma Nshiftr_bound_pow2 a n m : a < 2 ^ m -> N.shiftr a n < 2 ^ m.
Proof.
case: a => [|p]; first by rewrite N.shiftr_0_l.
move=> a_lt2m; apply: N.log2_lt_cancel.
rewrite N.log2_shiftr N.log2_pow2 //; last by apply: N.le_0_l.
apply: N.le_lt_trans; first by apply: N.le_sub_l.
by apply/N.log2_lt_pow2.
Qed.

Lemma Nland_bound_pow2 n n' m : n < 2 ^ m -> n' < 2 ^ m -> N.land n n' < 2 ^ m.
Proof.
case: n => [//|p n2m n'2m].
apply: N.log2_lt_cancel; apply: N.le_lt_trans; first by apply: N.log2_land.
apply/N.min_lt_iff; left; rewrite N.log2_pow2 //; last by apply: N.le_0_l.
by apply/N.log2_lt_pow2.
Qed.

Lemma Nland_mul_pow2_lt_pow2 a b n : b < 2 ^ n -> N.land (a * 2 ^ n) b = 0.
Proof.
have aux a' b' n': b' < 2 ^ N.of_nat n' -> N.land (a' * 2 ^ N.of_nat n') b' = 0.
  case: b' => [|p]; first by rewrite N.land_0_r.
  case: n' => [|n'].
    rewrite -[N.of_nat 0]/0 N.pow_0_r -{1}[1]/(N.succ 0).
    by move/N.lt_succ_r.
  rewrite Nnat.Nat2N.inj_succ => blt2eSn; apply: N.bits_inj_0 => m.
  rewrite N.land_spec.
  case Hm: (m <? N.succ (N.of_nat n')).
    by rewrite N.mul_pow2_bits_low //; apply: N.ltb_spec0.
  rewrite (N.bits_above_log2 (N.pos p) m); first by rewrite andbF.
  apply/N.log2_lt_pow2 => //.
  apply: (N.lt_le_trans (N.pos p) (2 ^ N.succ (N.of_nat n')) (2 ^ m)) => //.
  by apply: N.pow_le_mono_r => //; move/N.ltb_ge: Hm.
by rewrite -(Nnat.N2Nat.id n) => H; rewrite aux.
Qed.

Lemma Nlor_bound_pow2 n n' m : n < 2 ^ m -> n' < 2 ^ m -> N.lor n n' < 2 ^ m.
Proof.
case: n => [|p]; case: n' => [|p'] //.
move=> n_lt2m n'_lt2m; apply: N.log2_lt_cancel.
rewrite N.log2_pow2 //; last by apply: N.le_0_l.
by rewrite N.log2_lor; apply: N.max_lub_lt; apply/N.log2_lt_pow2.
Qed.

Lemma Nlor_mul_pow2 a a' n :
  N.lor (a * 2 ^ n) (a' * 2 ^ n) = (N.lor a a') * 2 ^ n.
Proof.
have N_lor_mul2 x y : N.lor (x * 2) (y * 2) = (N.lor x y) * 2.
  do 3! rewrite N.mul_comm -N.double_spec.
  by case: x => [//|x]; case: y => [//|y]; case: x; case: y.
have N_lor_mul_pow2_aux m b b':
  N.lor (b * 2 ^ (N.of_nat m)) (b' * 2 ^ (N.of_nat m))
    = (N.lor b b') * 2 ^ (N.of_nat m).
  elim: m b b' => [/=|m IH] b b'; first by rewrite !N.mul_1_r.
  rewrite Nnat.Nat2N.inj_succ N.pow_succ_r' !N.mul_assoc IH.
  by congr N.mul; rewrite N_lor_mul2.
by rewrite -(Nnat.N2Nat.id n) N_lor_mul_pow2_aux.
Qed.

Lemma Nlor_add_mul_pow2 a a' b b' n :
    b < 2 ^ n ->
    b' < 2 ^ n ->
  N.lor (a * 2 ^ n + b) (a' * 2 ^ n + b') = N.lor a a' * 2 ^ n + N.lor b b'.
Proof.
move=> b_lt2eS b'_lt2eS.
have Nlor_add_mul2:
    b < 2 ->
    b' < 2 ->
  N.lor (a * 2 + b) (a' * 2 + b') = N.lor a a' * 2 + N.lor b b'.
  move=> blt2 b'lt2.
  have Nland_mul2_lt2 x y : y < 2 -> N.land (x * 2) y = 0.
    by move=> Hy; rewrite -[2]/(2 ^ 1) Nland_mul_pow2_lt_pow2.
  have Nlor_bound2 : b < 2 -> b' < 2 -> N.lor b b' < 2.
    by rewrite -[2]/(2 ^ 1); apply: Nlor_bound_pow2.
  rewrite 2?N.add_nocarry_lxor; [|apply: Nland_mul2_lt2 => //..].
  rewrite !N.lxor_lor; [|apply: Nland_mul2_lt2 => //..].
  rewrite N.lor_comm N.lor_assoc -(N.lor_assoc _ b').
  rewrite (N.lor_comm b') N.lor_assoc -(N.lor_assoc _ _ b).
  rewrite (N.lor_comm (a' * 2)) (N.lor_comm b').
  rewrite -[2]/(2 ^ 1) Nlor_mul_pow2 -N.lxor_lor; last first.
    by apply: Nland_mul2_lt2; apply: Nlor_bound2.
  by rewrite -N.add_nocarry_lxor //; apply: Nland_mul2_lt2; apply: Nlor_bound2.
rewrite N.add_nocarry_lxor; last by rewrite Nland_mul_pow2_lt_pow2.
rewrite N.add_nocarry_lxor; last by rewrite Nland_mul_pow2_lt_pow2.
rewrite !N.lxor_lor; [|rewrite Nland_mul_pow2_lt_pow2 //..].
rewrite (N.lor_comm (a' * 2 ^ n)).
rewrite N.lor_assoc N.lor_comm N.lor_assoc (N.lor_assoc _ _ b).
rewrite -N.lor_assoc (N.lor_comm (a' * 2 ^ n)).
rewrite Nlor_mul_pow2 -N.lxor_lor.
  rewrite -N.add_nocarry_lxor //; apply: Nland_mul_pow2_lt_pow2.
  by apply: Nlor_bound_pow2.
by apply: Nland_mul_pow2_lt_pow2; apply: Nlor_bound_pow2.
Qed.

Lemma Nlor_mod_pow2_comm n n' m :
  N.lor (n mod 2 ^ m) (n' mod 2 ^ m) = (N.lor n n') mod 2 ^ m.
Proof.
rewrite -!N.land_ones; apply: N.bits_inj => b.
rewrite N.lor_spec !N.land_spec N.lor_spec.
case H: (m <=? b).
  rewrite N.ones_spec_high; first by rewrite !andbF.
  by apply/N.leb_spec0.
rewrite N.ones_spec_low; first by rewrite !andbT.
by apply/N.leb_gt.
Qed.

Lemma Nlxor_bound_pow2 n n' m : n < 2 ^ m -> n' < 2 ^ m -> N.lxor n n' < 2 ^ m.
Proof.
case: n => [//|p]; case: n' => [//|p' n2m n'2m].
apply: N.log2_lt_cancel; apply: N.le_lt_trans; first by apply N.log2_lxor.
rewrite N.log2_pow2 //; last by apply: N.le_0_l.
by apply: N.max_lub_lt; apply/N.log2_lt_pow2.
Qed.

Lemma Nlxor_mul_pow2 a a' n :
  N.lxor (a * 2 ^ n) (a' * 2 ^ n) = (N.lxor a a') * 2 ^ n.
Proof.
have Nlxor_mul2 x y: N.lxor (x * 2) (y * 2) = (N.lxor x y) * 2.
  do 3! rewrite N.mul_comm -N.double_spec.
  by case: x => [//|x]; case: y => [//|y]; case: x; case: y.
have N_lxor_mul_pow2_aux m b b':
  N.lxor (b * 2 ^ (N.of_nat m)) (b' * 2 ^ (N.of_nat m))
    = (N.lxor b b') * 2 ^ (N.of_nat m).
  elim: m b b' => [/=|m HI] b b'; first by rewrite !N.mul_1_r.
  rewrite Nnat.Nat2N.inj_succ N.pow_succ_r' !N.mul_assoc HI.
  by congr N.mul; rewrite Nlxor_mul2.
by rewrite -(Nnat.N2Nat.id n) N_lxor_mul_pow2_aux.
Qed.

Lemma Nlxor_add_mul_pow2 a a' b b' n :
    b < 2 ^ n ->
    b' < 2 ^ n ->
  N.lxor (a * 2 ^ n + b) (a' * 2 ^ n + b') = N.lxor a a' * 2 ^ n + N.lxor b b'.
Proof.
move=> blt2eS b'lt2eS.
have Nlxor_add_mul2:
    b < 2 ->
    b' < 2 ->
  N.lxor (a * 2 + b) (a' * 2 + b') = N.lxor a a' * 2 + N.lxor b b'.
  move=> blt2 b'lt2.
  have Nlxor_bound2 : b < 2 -> b' < 2 -> N.lxor b b' < 2.
    by rewrite -[2]/(2 ^ 1); apply: Nlxor_bound_pow2.
  have Nland_mul2_lt2 x y : y < 2 -> N.land (x * 2) y = 0.
    by move=> Hy; rewrite -[2]/(2 ^ 1) Nland_mul_pow2_lt_pow2.
  rewrite 2?N.add_nocarry_lxor; [|apply: Nland_mul2_lt2 => //..].
  rewrite {1}(N.lxor_comm _ b') N.lxor_assoc.
  rewrite {1}(N.lxor_comm b') {1}(N.lxor_comm b).
  rewrite !N.lxor_assoc -(N.lxor_assoc (a * 2)) (N.lxor_comm b').
  rewrite -[2]/(2 ^ 1) Nlxor_mul_pow2 -N.add_nocarry_lxor //.
  by apply: Nland_mul2_lt2; apply: Nlxor_bound2.
do 2! [rewrite N.add_nocarry_lxor; last by rewrite Nland_mul_pow2_lt_pow2].
rewrite {1}(N.lxor_comm b) (N.lxor_assoc _ b).
rewrite (N.lxor_comm b') {1}(N.lxor_comm b) N.lxor_assoc.
rewrite -(N.lxor_assoc _ _ (N.lxor b' b)) (N.lxor_comm _ b).
rewrite Nlxor_mul_pow2 -N.add_nocarry_lxor //.
by apply: Nland_mul_pow2_lt_pow2; apply: Nlxor_bound_pow2.
Qed.

Lemma Nlxor_mod_pow2_comm n n' m :
  N.lxor (n mod 2 ^ m) (n' mod 2 ^ m) = (N.lxor n n') mod 2 ^ m.
Proof.
rewrite -!N.land_ones; apply: N.bits_inj => b.
rewrite N.lxor_spec !N.land_spec N.lxor_spec.
case H: (m <=? b).
  rewrite N.ones_spec_high; first by rewrite !andbF.
  by apply/N.leb_spec0.
rewrite N.ones_spec_low; first by rewrite !andbT.
by apply/N.leb_gt.
Qed.

Lemma Nlnot_bound_pow2 n m : n < 2 ^ m -> N.lnot n m < 2 ^ m.
Proof.
move=> n_lt2em; rewrite /N.lnot; apply: Nlxor_bound_pow2 => //.
by rewrite N.ones_equiv; apply: N.lt_pred_l; apply: N.pow_nonzero.
Qed.

(* Correspondence right_shift *)

Lemma bool_32b_right_shift1E b :
  bool_32b_right_shift b 1 = bool_32b_of_N (N.shiftr (bool_32b_to_N b) 1).
Proof.
rewrite -(bool_32b_to_natK (bool_32b_right_shift b 1)).
rewrite /bool_32b_of_N; apply: f_equal; apply: Nnat.Nat2N.inj.
rewrite Nnat.N2Nat.id -/(bool_32b_to_N (bool_32b_right_shift b 1)).
rewrite /bool_32b_right_shift -N.div2_spec /bool_32b_to_seq /=.
rewrite !bool_32b_to_N_char !bool_B_to_N_char /= N.div2_div.
rewrite -[N.pos (2 ^ 7)]/(N.pos (2 ^ 6 * 2)).
rewrite -[N.pos (2 ^ 6)]/(N.pos (2 ^ 5 * 2)).
rewrite -[N.pos (2 ^ 5)]/(N.pos (2 ^ 4 * 2)).
rewrite -[N.pos (2 ^ 4)]/(N.pos (2 ^ 3 * 2)).
rewrite -[N.pos (2 ^ 3)]/(N.pos (2 ^ 2 * 2)).
rewrite -[N.pos (2 ^ 2)]/(N.pos (2 ^ 1 * 2)).
have A n m x: n * (N.pos (x * 2)) * m = n * m * (N.pos x) * 2.
  by rewrite -?N.mul_assoc; congr N.mul; rewrite N.mul_comm.
have B n m: n * 2 * m = n * m * 2.
  by rewrite -?N.mul_assoc; congr N.mul; rewrite N.mul_comm.
have C n x: n * (N.pos (x * 2)) = n * (N.pos x) * 2.
  by rewrite -N.mul_assoc.
have D3: N.pos (256 ^ 3) = (N.pos ((256 ^ 2) * (2 ^ 7))) * 2 by [].
have D2: N.pos (256 ^ 2) = (N.pos (256 * (2 ^ 7))) * 2 by [].
have D4: N.of_nat (b7 (B2 b)) * 256 = (N.of_nat (b7 (B2 b)) * 2 ^ 7) * 2.
  by rewrite -N.mul_assoc.
rewrite // !N.mul_add_distr_r.
rewrite !(A _ (N.pos (256 ^ 3)) _).
rewrite !(A _ (N.pos (256 ^ 2)) _).
rewrite !(A _ (N.pos (256)) _).
rewrite !(B _ (N.pos (256 ^ 3))).
rewrite !(B _ (N.pos (256 ^ 2))).
rewrite !(B _ (N.pos (256))).
rewrite {15}D3 (C (N.of_nat (b7 (B0 b)))).
rewrite {16}D2 (C (N.of_nat (b7 (B1 b)))) D4.
rewrite -?N.mul_add_distr_r N.div_add_l //.
rewrite !(C (N.of_nat (b0 (B3 b)))).
rewrite !(C (N.of_nat (b1 (B3 b)))).
rewrite !(C (N.of_nat (b2 (B3 b)))).
rewrite !(C (N.of_nat (b3 (B3 b)))).
rewrite !(C (N.of_nat (b4 (B3 b)))).
rewrite !(C (N.of_nat (b5 (B3 b)))).
rewrite -!N.mul_add_distr_r N.div_add_l //.
rewrite (N.div_small (N.of_nat (b7 (B3 b))) 2); last by case: b7.
by rewrite N.add_0_r !N.mul_add_distr_r !N.add_assoc -!N.mul_assoc.
Qed. (*mejorar haves?*)

Lemma bool_32b_right_shiftE b n :
  bool_32b_right_shift b n
    = bool_32b_of_N (N.shiftr (bool_32b_to_N b) (N.of_nat n)).
Proof.
elim: n => [|n IH].
  by rewrite bool_32b_to_NK; apply: bool_32b_eq => /=; rewrite -bool_B_aux.
rewrite -{1}addn1 bool_32b_right_shiftDr.
have -> k: N.of_nat k.+1 = N.succ (N.of_nat k) by elim: k.
rewrite N.shiftr_succ_r N.div2_spec IH bool_32b_right_shift1E bool_32b_of_N2e32K //.
apply: Nshiftr_bound_pow2; move: (bool_32b_to_N_lt2e32 b).
by rewrite N_ltn N_expn !Nnat.Nat2N.id.
Qed.

(* Correspondence left_shift *)

Lemma bool_32b_left_shift1E b :
  bool_32b_left_shift b 1
    = bool_32b_of_N ((N.shiftl (bool_32b_to_N b) 1) mod wexp).
Proof.
rewrite N.shiftl_mul_pow2 N.pow_1_r.
rewrite -(bool_32b_to_natK (bool_32b_left_shift b 1)).
rewrite /bool_32b_of_N; apply: f_equal; apply: Nnat.Nat2N.inj.
rewrite Nnat.N2Nat.id -/(bool_32b_to_N (bool_32b_left_shift b 1)).
rewrite /bool_32b_left_shift /bool_32b_to_seq.
rewrite !bool_32b_to_N_char !bool_B_to_N_char.
rewrite N.add_0_r ?N.mul_add_distr_r -N.mul_assoc.
have -> : N.of_nat (b0 (B0 b)) * N.pos (2 ^ 7) * N.pos (256 ^ 3) * 2
            = N.of_nat (b0 (B0 b)) * wexp.
  by rewrite -?N.mul_assoc.
rewrite -?N.add_assoc (N.add_comm (N.of_nat (b0 (B0 b)) * wexp)).
rewrite N.mod_add // ?N.add_assoc -?N.mul_assoc N.mod_small //.
have bound: (N.pos (2 ^ 7) * N.pos (256 ^ 3)) +
  (N.pos (2 ^ 6) * N.pos (256 ^ 3)) +
  (N.pos (2 ^ 5) * N.pos (256 ^ 3)) +
  (N.pos (2 ^ 4) * N.pos (256 ^ 3)) +
  (N.pos (2 ^ 3) * N.pos (256 ^ 3)) +
  (N.pos (2 ^ 2) * N.pos (256 ^ 3)) +
  (N.pos (256 ^ 3) * 2) + N.pos (256 ^ 3) +
  (N.pos (2 ^ 7) * N.pos (256 ^ 2)) +
  (N.pos (2 ^ 6) * N.pos (256 ^ 2)) +
  (N.pos (2 ^ 5) * N.pos (256 ^ 2)) +
  (N.pos (2 ^ 4) * N.pos (256 ^ 2)) +
  (N.pos (2 ^ 3) * N.pos (256 ^ 2)) +
  (N.pos (2 ^ 2) * N.pos (256 ^ 2)) +
  (N.pos (256 ^ 2) * 2) +
  (N.pos (2 ^ 8) * N.pos (2 ^ 8)) +
  (N.pos (2 ^ 7) * N.pos (2 ^ 8)) +
  (N.pos (2 ^ 6) * N.pos (2 ^ 8)) +
  (N.pos (2 ^ 5) * N.pos (2 ^ 8)) +
  (N.pos (2 ^ 4) * N.pos (2 ^ 8)) +
  (N.pos (2 ^ 3) * N.pos (2 ^ 8)) +
  (N.pos (2 ^ 2) * N.pos (2 ^ 8)) +
  N.pos (2 ^ (8 + 1)) + N.pos (2 ^ (7 + 1)) +
  N.pos (2 ^ (6 + 1)) + N.pos (2 ^ (5 + 1)) +
  N.pos (2 ^ (4 + 1)) + N.pos (2 ^ (3 + 1)) +
  N.pos (2 ^ (2 + 1)) + (2 * 2) + 2 < 2 ^ 32 => //.
apply: N.le_lt_trans; last by apply: bound.
have H (B : bool) n: (N.of_nat B) * n <= n.
  case: B; first by rewrite N.mul_1_l; apply: N.le_refl.
  by rewrite N.mul_0_l; apply: N.le_0_l.
by do 30! [apply: N.add_le_mono; last by apply: H]; apply: H.
Qed.

Lemma bool_32b_left_shiftE b n :
  bool_32b_left_shift b n
    = bool_32b_of_N ((N.shiftl (bool_32b_to_N b) (N.of_nat n)) mod wexp).
Proof.
elim: n => [|n IH].
  rewrite N.shiftl_0_r N.mod_small //.
    by rewrite bool_32b_to_NK; apply: bool_32b_eq => /=; rewrite -bool_B_aux.
  by move: (bool_32b_to_N_lt2e32 b).
rewrite -{1}addn1 bool_32b_left_shiftDr.
have -> k: N.of_nat k.+1 = N.succ (N.of_nat k) by elim: k.
rewrite N.shiftl_succ_r N.double_spec IH ?N.shiftl_mul_pow2.
rewrite bool_32b_left_shift1E bool_32b_of_N2e32K; last by apply: N.mod_lt.
rewrite ?N.shiftl_mul_pow2 -(N.mul_mod_idemp_l 2) // (N.mod_small 2) //.
by rewrite N.mul_comm // N.pow_1_r N.mul_mod_idemp_r //; apply: N.mod_lt.
Qed.

(* Correspondence (bool_b_op orb) *)

Lemma bool_B_op_orbE B B' :
  bool_B_op orb B B' = bool_B_of_N (N.lor (bool_B_to_N B) (bool_B_to_N B')).
Proof.
have corr_or_B_aux a a' b b' c c' d d' e e' f f' g g' h h':
      b < 2 -> b' < 2 -> c < 2 -> c' < 2 -> d < 2 -> d' < 2 ->
    e < 2 -> e' < 2 -> f < 2 -> f' < 2 -> g < 2 -> g' < 2 -> h < 2 -> h' < 2 ->
  N.lor(a * 2 ^ 7 + b * 2 ^ 6 + c * 2 ^ 5 + d * 2 ^ 4 +
        e * 2 ^ 3 + f * 2 ^ 2 + g * 2 + h)
       (a' * 2 ^ 7 + b' * 2 ^ 6 + c' * 2 ^ 5 + d' * 2 ^ 4 +
        e' * 2 ^ 3 + f' * 2 ^ 2 + g' * 2 + h') =
  N.lor a a' * 2 ^ 7 +
  N.lor b b' * 2 ^ 6 +
  N.lor c c' * 2 ^ 5 +
  N.lor d d' * 2 ^ 4 +
  N.lor e e' * 2 ^ 3 +
  N.lor f f' * 2 ^ 2 +
  N.lor g g' * 2 +
  N.lor h h'.
  move=> blt2 b'lt2 clt2 c'lt2 dlt2 d'lt2.
  move=> elt2 e'lt2 flt2 f'lt2 glt2 g'lt2 hlt2 h'lt2.
  rewrite (N.pow_succ_r' 2 6) (N.pow_succ_r' 2 5) (N.pow_succ_r' 2 4).
  rewrite (N.pow_succ_r' 2 3) (N.pow_succ_r' 2 2) (N.pow_succ_r' 2 1).
  rewrite N.pow_1_r !N.mul_assoc -!N.mul_add_distr_r.
  by rewrite -[2]/(2 ^ 1) !Nlor_add_mul_pow2.
rewrite -(bool_B_to_natK (bool_B_op orb B B')).
rewrite /bool_B_of_N; apply: f_equal.
rewrite !bool_B_to_N_char.
have bool_lt2 (b : bool): N.of_nat b < 2; first by case: b.
rewrite corr_or_B_aux; [|apply: bool_lt2..].
apply/Nnat.Nat2N.inj.
rewrite !Nnat.N2Nat.id -/(bool_B_to_N (bool_B_op orb B B')).
rewrite /bool_B_op /= bool_B_to_N_char /= !orbE.
congr N.add; last by case: (b7 B); case: (b7 B').
congr N.add; last by case: (b6 B); case: (b6 B').
congr N.add; last by case: (b5 B); case: (b5 B').
congr N.add; last by case: (b4 B); case: (b4 B').
congr N.add; last by case: (b3 B); case: (b3 B').
congr N.add; last by case: (b2 B); case: (b2 B').
congr N.add; last by case: (b1 B); case: (b1 B').
by congr N.mul; case: (b0 B); case: (b0 B'). (*acortar?*)
Qed.

(* Correspondence (bool_32b_op orb) *)

Lemma bool_32b_op_orbE b1 b2 :
  b1 B|| b2 = bool_32b_of_N (N.lor (bool_32b_to_N b1) (bool_32b_to_N b2)).
Proof.
have corr_or_aux a b c d a' b' c' d':
    b < 256 ->
    b' < 256 ->
    c < 256 ->
    c' < 256 ->
    d < 256 ->
    d' < 256 ->
  N.lor (a * 256 ^ 3 + b * 256 ^ 2 + c * 256 + d)
    (a' * 256 ^ 3 + b' * 256 ^ 2 + c' * 256 + d')
      = N.lor a a' * 256 ^ 3 + N.lor b b' * 256 ^ 2 + N.lor c c' * 256 +
          N.lor d d'.
  move=> blt256 b'lt256 clt256 c'lt256 dlt256 d'lt256.
  rewrite (N.pow_succ_r' (2 ^ 8) 2) (N.pow_succ_r' (2 ^ 8) 1).
  rewrite N.pow_1_r !N.mul_assoc -!N.mul_add_distr_r.
  by rewrite !(@Nlor_add_mul_pow2 _ _ _ _ 8).
rewrite !bool_32b_to_N_char corr_or_aux; [|apply: bool_B_to_N_lt256..].
rewrite -(bool_32b_to_natK (b1 B|| b2)) /bool_32b_of_N; apply: f_equal.
rewrite /bool_32b_op; apply/Nnat.Nat2N.inj_iff; rewrite !Nnat.N2Nat.id.
rewrite -/(bool_32b_to_N {|B0 := bool_B_op orb (B0 b1) (B0 b2);
  B1 := bool_B_op orb (B1 b1) (B1 b2); B2 := bool_B_op orb (B2 b1) (B2 b2);
  B3 := bool_B_op orb (B3 b1) (B3 b2)|}).
rewrite bool_32b_to_N_char !bool_B_op_orbE.
rewrite !bool_B_of_N256K //; apply: (@Nlor_bound_pow2 _ _ 8).
all: by apply bool_B_to_N_lt256.
Qed.

(* Correspondence (bool_B_op xorb) *)

Lemma bool_b_op_xorbE B B' :
  bool_B_op xorb B B' = bool_B_of_N (N.lxor (bool_B_to_N B) (bool_B_to_N B')).
Proof.
have corr_xor_aux a a' b b' c c' d d' e e' f f' g g' h h':
    b < 2 -> b' < 2 -> c < 2 -> c' < 2 -> d < 2 -> d' < 2 -> e < 2 -> e' < 2 ->
    f < 2 -> f' < 2 -> g < 2 -> g' < 2 -> h < 2 -> h' < 2 ->
  N.lxor (a * 2 ^ 7 + b * 2 ^ 6 + c * 2 ^ 5 + d * 2 ^ 4 + e * 2 ^ 3 +
    f * 2 ^ 2 + g * 2 + h) (a' * 2 ^ 7 + b' * 2 ^ 6 + c' * 2 ^ 5 + d' * 2 ^ 4 +
      e' * 2 ^ 3 + f' * 2 ^ 2 + g' * 2 + h')
        = N.lxor a a' * 2 ^ 7 + N.lxor b b' * 2 ^ 6 + N.lxor c c' * 2 ^ 5 +
            N.lxor d d' * 2 ^ 4 + N.lxor e e' * 2 ^ 3 + N.lxor f f' * 2 ^ 2 +
              N.lxor g g' * 2 + N.lxor h h'.
  move=> blt2 b'lt2 clt2 c'lt2 dlt2 d'lt2 elt2 e'lt2.
  move=> flt2 f'lt2 glt2 g'lt2 hlt2 h'lt2.
  rewrite (N.pow_succ_r' 2 6) (N.pow_succ_r' 2 5) (N.pow_succ_r' 2 4).
  rewrite (N.pow_succ_r' 2 3) (N.pow_succ_r' 2 2) (N.pow_succ_r' 2 1).
  rewrite N.pow_1_r !N.mul_assoc -!N.mul_add_distr_r.
  by rewrite -[2]/(2 ^ 1) !Nlxor_add_mul_pow2.
rewrite -(bool_B_to_natK (bool_B_op xorb B B')).
rewrite /bool_B_of_N; apply: f_equal.
rewrite !bool_B_to_N_char.
have bool_lt2 (b : bool): N.of_nat b < 2; first by case: b.
rewrite corr_xor_aux; [|apply: bool_lt2..].
apply/Nnat.Nat2N.inj; rewrite !Nnat.N2Nat.id.
rewrite -/(bool_B_to_N (bool_B_op xorb B B')).
rewrite /bool_B_op /= bool_B_to_N_char /= !xorbE.
congr N.add; last by case: (b7 B); case: (b7 B').
congr N.add; last by case: (b6 B); case: (b6 B').
congr N.add; last by case: (b5 B); case: (b5 B').
congr N.add; last by case: (b4 B); case: (b4 B').
congr N.add; last by case: (b3 B); case: (b3 B').
congr N.add; last by case: (b2 B); case: (b2 B').
congr N.add; last by case: (b1 B); case: (b1 B').
by case: (b0 B); case: (b0 B').
Qed.

(*Correspondencia (bool_32b_op xorb) *)

Lemma bool_32b_op_xorbE b1 b2 :
  b1 B(+) b2 = bool_32b_of_N (N.lxor (bool_32b_to_N b1) (bool_32b_to_N b2)).
Proof.
have corr_xor_aux a b c d a' b' c' d':
    b < 256 -> b' < 256 -> c < 256 -> c' < 256 -> d < 256 -> d' < 256 ->
  N.lxor (a * 256 ^ 3 + b * 256 ^ 2 + c * 256 + d)
    (a' * 256 ^ 3 + b' * 256 ^ 2 + c' * 256 + d')
      = N.lxor a a' * 256 ^ 3 + N.lxor b b' * 256 ^ 2 + N.lxor c c' * 256 +
          N.lxor d d'.
  move=> blt256 b'lt256 clt256 c'lt256 dlt256 d'lt256.
  rewrite (N.pow_succ_r' (2 ^ 8) 2) (N.pow_succ_r' (2 ^ 8) 1).
  rewrite N.pow_1_r !N.mul_assoc -!N.mul_add_distr_r.
  by rewrite !(@Nlxor_add_mul_pow2 _ _ _ _ 8).
have bool_b_to_N_lt_256 := bool_B_to_N_lt256.
rewrite !bool_32b_to_N_char.
rewrite corr_xor_aux; [| apply: bool_B_to_N_lt256..].
rewrite -(bool_32b_to_natK (b1 B(+) b2)).
rewrite /bool_32b_of_N; apply: f_equal.
rewrite /bool_32b_op; apply/Nnat.Nat2N.inj_iff; rewrite !Nnat.N2Nat.id.
rewrite -/(bool_32b_to_N {|B0 := bool_B_op xorb (B0 b1) (B0 b2);
  B1 := bool_B_op xorb (B1 b1) (B1 b2); B2 := bool_B_op xorb (B2 b1) (B2 b2);
    B3 := bool_B_op xorb (B3 b1) (B3 b2)|}).
rewrite bool_32b_to_N_char !bool_b_op_xorbE.
by rewrite !bool_B_of_N256K // -[256]/(2 ^ 8); apply: Nlxor_bound_pow2.
Qed.

(* Correspondence (bool_b_op negb) *)

Lemma bool_b_op_negbE b : (B~~ b) = bool_32b_of_N (N.lnot (bool_32b_to_N b) 32).
Proof.
rewrite /N.lnot.
suff -> : (N.ones 32) = bool_32b_to_N bool_32b11.
  by rewrite neg_32b_xorl_32b bool_32b_op_xorbE.
rewrite N.ones_equiv -(N.pred_succ (bool_32b_to_N bool_32b11)).
by rewrite bool_32b_to_N_char.
Qed.

(* Correspondence (bool_b_op andb) *)

Lemma bool_b_op_andbE b1 b2 :
  b1 B&& b2 = bool_32b_of_N (N.land (bool_32b_to_N b1) (bool_32b_to_N b2)).
Proof.
rewrite bool_32b_and_or !bool_32b_op_orbE !bool_b_op_negbE.
have bool_32b_to_N_lt2e32 := bool_32b_to_N_lt2e32.
have Nlog2_bound b: N.log2 (bool_32b_to_N b) < 32.
  case gt0: (0 <? bool_32b_to_N b).
    by apply/N.log2_lt_pow2; first by apply/N.ltb_lt.
  by move/N.ltb_ge: gt0; move/N.le_0_r ->.
rewrite !bool_32b_of_N2e32K; try apply: Nlnot_bound_pow2 => //.
rewrite -N.lnot_land_low //; first by rewrite N.lnot_involutive.
by apply: Nlor_bound_pow2; apply: Nlnot_bound_pow2.
Qed.

(* Correspondence ROTR *)

Lemma ROTRE n b :
  ROTR n b
    = bool_32b_of_N ((N_sha256.ROTR (bool_32b_to_N b) (N.of_nat n)) mod wexp).
Proof.
rewrite /ROTR /N_sha256.ROTR.
rewrite bool_32b_op_orbE bool_32b_left_shiftE bool_32b_right_shiftE.
rewrite !bool_32b_of_N2e32K; try by apply: N.mod_lt.
  rewrite N_subn Nnat.Nat2N.id.
  rewrite -{1}(N.mod_small (N.shiftr (bool_32b_to_N b) (N.of_nat n)) wexp).
  by rewrite Nlor_mod_pow2_comm.
all: by apply: Nshiftr_bound_pow2; apply: bool_32b_to_N_lt2e32.
Qed.

(* Correspondence bool_32b_add *)

Lemma bool_32b_addE b1 b2 :
  b1 B+ b2 = bool_32b_of_N (((bool_32b_to_N b1) + (bool_32b_to_N b2)) mod wexp).
Proof.
rewrite bool_32b_add_mod2e32 /bool_32b_of_N N_addn N_modn Nat_pow.
by rewrite !Nnat.Nat2N.id.
Qed.

(* Correspondence bigSigma_1 *)

Lemma bigSigma_1E b :
  (bigSigma_1 b)
    = bool_32b_of_N ((N_sha256.bigSigma_1 (bool_32b_to_N b)) mod wexp).
Proof.
rewrite /bigSigma_1 !ROTRE !bool_32b_op_xorbE.
rewrite !bool_32b_of_N2e32K; try by rewrite wexp'; apply: N.mod_lt.
  by rewrite N.lxor_assoc !Nlxor_mod_pow2_comm.
by apply: Nlxor_bound_pow2; apply: N.mod_lt.
Qed.

(* Correspondence bigSigma_0 *)

Lemma bigSigma_0E b :
  (bigSigma_0 b)
    = bool_32b_of_N ((N_sha256.bigSigma_0 (bool_32b_to_N b)) mod wexp).
Proof.
rewrite /bigSigma_0 !ROTRE !bool_32b_op_xorbE.
rewrite !bool_32b_of_N2e32K; try by apply: N.mod_lt.
  by rewrite !Nlxor_mod_pow2_comm N.lxor_assoc.
by apply: Nlxor_bound_pow2; apply: N.mod_lt.
Qed.

(* Correspondence Ch *)

Lemma ChE b c d :
  (Ch b c d)
    = bool_32b_of_N ((N_sha256.Ch (bool_32b_to_N b) (bool_32b_to_N c)
        (bool_32b_to_N d)) mod wexp).
Proof.
rewrite /Ch !bool_32b_op_xorbE !bool_b_op_andbE !bool_b_op_negbE.
have Nland256e4 B B': N.land (bool_32b_to_N B) (bool_32b_to_N B') < 2 ^ 32.
  by apply: Nland_bound_pow2; apply: bool_32b_to_N_lt2e32.
have Nlnot256e4 B: N.lnot (bool_32b_to_N B) 32 < 2 ^ 32.
  by apply: Nlnot_bound_pow2; apply: bool_32b_to_N_lt2e32.
rewrite !bool_32b_of_N2e32K //.
rewrite N.mod_small //; apply: Nlxor_bound_pow2 => //.
all: by apply: Nland_bound_pow2 => //; apply: bool_32b_to_N_lt2e32.
Qed.

(* Correspondence Maj *)

Lemma MajE b c d :
  (Maj b c d)
    = bool_32b_of_N ((N_sha256.Maj (bool_32b_to_N b) (bool_32b_to_N c)
        (bool_32b_to_N d)) mod wexp).
Proof.
rewrite /Maj /N_sha256.Maj !bool_32b_op_xorbE !bool_b_op_andbE.
have Nland256e4 B B': N.land (bool_32b_to_N B) (bool_32b_to_N B') < 2 ^ 32.
  by apply: Nland_bound_pow2; apply: bool_32b_to_N_lt2e32.
rewrite !bool_32b_of_N2e32K //; last by apply: Nlxor_bound_pow2.
by rewrite N.mod_small //; apply: Nlxor_bound_pow2 => //; apply: Nlxor_bound_pow2.
Qed.

(* Correspondence sigma_0 *)

Lemma sigma0E b :
  sigma_0 b = bool_32b_of_N ((N_sha256.sigma_0 (bool_32b_to_N b)) mod wexp).
Proof.
rewrite /sigma_0 !ROTRE !bool_32b_op_xorbE bool_32b_right_shiftE.
rewrite !bool_32b_of_N2e32K; try by apply: N.mod_lt.
    rewrite -{1}(N.mod_small (N.shiftr (bool_32b_to_N b) (N.of_nat 3)) wexp).
      by rewrite !Nlxor_mod_pow2_comm.
    by apply: Nshiftr_bound_pow2; apply: bool_32b_to_N_lt2e32.
  by apply: Nshiftr_bound_pow2; apply: bool_32b_to_N_lt2e32.
by apply: Nlxor_bound_pow2; apply: N.mod_lt.
Qed.

(* Correspondence sigma_1 *)

Lemma sigma1E b :
  sigma_1 b = bool_32b_of_N ((N_sha256.sigma_1 (bool_32b_to_N b)) mod wexp).
Proof.
rewrite /sigma_1 !ROTRE !bool_32b_op_xorbE bool_32b_right_shiftE.
rewrite !bool_32b_of_N2e32K; try by apply: N.mod_lt.
    rewrite -{1}(N.mod_small (N.shiftr (bool_32b_to_N b) (N.of_nat 10)) wexp).
      by rewrite !Nlxor_mod_pow2_comm.
    by apply: Nshiftr_bound_pow2; apply: bool_32b_to_N_lt2e32.
  by apply: Nshiftr_bound_pow2; apply: bool_32b_to_N_lt2e32.
by apply: Nlxor_bound_pow2; apply: N.mod_lt.
Qed.

(* Correspondence message_schedule *)

Lemma ms_bound_mem s :
    all (N.ltb^~ (2 ^ 32)) (take 16 s) ->
  all (N.ltb^~ (2 ^ 32)) (N_sha256.message_schedule s).
Proof.
have bound_all_ms s' m:
  all (N.ltb^~ (2 ^ 32)) s' -> all (N.ltb^~ (2 ^ 32))(msg_sch_aux s' m).
  move=> H; rewrite all_cat; apply/andP; split => //.
  by rewrite all_seq1; apply/N.ltb_spec0; apply: N.mod_lt.
have bound_all_fold_ms s' l :
    all (N.ltb^~ (2 ^ 32)) s' ->
  all (N.ltb^~ (2 ^ 32)) (foldl msg_sch_aux s' l).
  elim: l s' => [|x l HI] s' //=.
  move=> bound_all_s; move: (HI (msg_sch_aux s' x)) => bound_fold.
  by move/(@bound_all_ms _ x): bound_all_s; apply: bound_fold.
by move=> bound_all; apply: bound_all_fold_ms.
Qed.

Lemma message_scheduleE s :
  message_schedule s
    = seq_32b_of_seq_N (N_sha256.message_schedule (bool_512b_to_seq_N s)).
Proof.
have msg_sch_aux_ms s' :
  N_sha256.message_schedule s'
    = foldl msg_sch_aux (take 16 s') (iota 16 48) => //.
have aux0 m:
  N.of_nat (bool_32b_to_nat (bool_32b_of_nat2e32 (N.to_nat m)))
    = bool_32b_to_N (bool_32b_of_N m).
  by rewrite /bool_32b_to_N /bool_32b_of_N.
rewrite /message_schedule msg_sch_aux_ms.
have sz16: size (bool_512b_to_seq_N s) = 16%nat => //.
rewrite /msg_sch_aux -{5}sz16 take_size /bool_512b_to_seq_N.
rewrite -map_comp /bool_512b_to_seq_bool_32b.
apply: foldl_map.
move=> l; rewrite /seq_32b_of_seq_N -map_comp.
    rewrite mapK //; move=> n; rewrite /comp.
    by rewrite Nnat.Nat2N.id bool_32b_to_natK.
  move=> l n.
  rewrite /seq_32b_of_seq_N -map_comp.
  rewrite all_mapK //; move=> m; rewrite /comp.
  rewrite mem_cat; move/orP; case.
    move/mapP => [b Hb] ->; apply: f_equal.
    by rewrite Nnat.Nat2N.id bool_32b_to_natK.
  rewrite mem_seq1; move/eqP => Hm.
  by rewrite aux0 bool_32b_of_N2e32K // Hm; apply: N.mod_upper_bound.
move=> l n.
rewrite /seq_32b_of_seq_N -map_comp map_cat mapK; last first.
  by move=> z; rewrite /comp Nnat.Nat2N.id bool_32b_to_natK.
congr cat; rewrite map_cons; congr cons.
rewrite !bool_32b_add_mod2e32 /comp; apply: f_equal.
rewrite sigma0E sigma1E !N_modn.
have -> : N.to_nat (wexp) = (256 ^ 4)%nat.
  rewrite wexp' N_expn.
  by rewrite Nnat.Nat2N.id; apply: expn_eq.
rewrite /bool_32b_to_N /bool_32b_of_N !Nnat.Nat2N.id.
rewrite !bool_32b_of_nat2e32K; [|apply: ltn_pmod => // ..].
rewrite !modnDmr !modnDml !N_addn !Nnat.Nat2N.id.
have aux1 m: N.of_nat (bool_32b_to_nat m) = bool_32b_to_N m.
  by rewrite /bool_32b_to_N.
have aux2 l':
  [seq N.of_nat (bool_32b_to_nat x) | x <- l'] = map bool_32b_to_N l'.
by rewrite /bool_32b_to_N.
have modn4 a b c d e: (a + (b + (c + d) %% e) = (a + (b + (c + d))) %[mod e])%nat.
  by rewrite !addnA modnDmr !addnA.
rewrite modn4; apply: modn_eq; last by apply: expn_eq.
rewrite !aux1 !aux2.
congr addn; [|congr addn]; first by do 2! [apply: f_equal]; apply: nth_map2.
  by apply/Nnat.Nat2N.inj_iff; rewrite aux1 Nnat.N2Nat.id; apply: nth_map2.
congr addn; first by do 2! [apply: f_equal]; apply: nth_map2.
by apply/Nnat.Nat2N.inj_iff; rewrite aux1 Nnat.N2Nat.id; apply: nth_map2.
Qed.

(* Correspondence digest_vars *)

Definition K_s := [seq bool_32b_of_N i | i <- K].

Lemma K_bool_32b_to_N_K :
  [seq bool_32b_to_N i | i <- K_s] = K.
Proof.
rewrite -map_comp /comp.
by do 64! [rewrite map_cons {1}bool_32b_of_N2e32K; last by []].
Qed.

Lemma T1E W_vals e f g h m :
  (h B+ ((bigSigma_1 e) B+ ((Ch e f g) B+ ((nth bool_32b00 K_s m) B+
    (nth bool_32b00 W_vals m)))))
       = bool_32b_of_N (((bool_32b_to_N h) +
           (N_sha256.bigSigma_1 (bool_32b_to_N e) +
             (N_sha256.Ch (bool_32b_to_N e) (bool_32b_to_N f)
               (bool_32b_to_N g) +
                 (nth 0 K m + nth 0 (map bool_32b_to_N W_vals) m))))
                    mod wexp).
Proof.
have <- a' b' c' d' e':
  (a' + (b' mod wexp + (c' mod wexp + (d' + e') mod wexp)
    mod wexp) mod wexp) mod wexp
      = (a' + (b' + (c' + (d' + e')))) mod wexp.
  rewrite !N.add_mod_idemp_l //; rewrite (N.add_mod_idemp_r c') //.
  by rewrite (N.add_mod_idemp_r b') //; rewrite N.add_mod_idemp_r //.
rewrite bigSigma_1E ChE !bool_32b_addE.
rewrite !bool_32b_of_N2e32K; try apply: N.mod_lt; first last => //.
rewrite nth_map2 -[(bool_32b_to_N bool_32b00)]/0 K_bool_32b_to_N_K.
by rewrite (nth_map2 bool_32b_to_N).
Qed.

Lemma T2E a b c :
  (bigSigma_0 a) B+ (Maj a b c)
    = bool_32b_of_N ((N_sha256.bigSigma_0 (bool_32b_to_N a) +
        N_sha256.Maj (bool_32b_to_N a) (bool_32b_to_N b) (bool_32b_to_N c))
          mod wexp).
Proof.
rewrite bigSigma_0E MajE !bool_32b_addE !bool_32b_of_N2e32K.
rewrite N.add_mod_idemp_l // N.add_mod_idemp_r //.
all: apply: N.mod_lt => //.
Qed.

Lemma digest_vars_aux_32b_to_N_bound W_vals vars n x :
    x \in N_sha256.digest_vars_aux [seq bool_32b_to_N i | i <- W_vals]
                                   [seq bool_32b_to_N i | i <- vars] n ->
  (x < 256 ^ 4).
Proof.
case: n => [|n] /nthP => H; move: (H 0) => [i i_lt_size ix].
  move: (bool_32b_to_nat_lt_2e32 (nth bool_32b00 vars i)).
  rewrite -ix -(@nth_map2 _ _ _ vars bool_32b00).
  by rewrite N_ltn Nat_pow ?Nnat.Nat2N.id.
move: (ltn0Sn n); rewrite leq_ltn => c.
have digest_vars_aux_imple_size k:
    (0 < k)%nat ->
  size (N_sha256.digest_vars_aux [seq bool_32b_to_N i | i <- W_vals]
    [seq bool_32b_to_N i | i <- vars] k) = 8; first by elim: k.
rewrite digest_vars_aux_imple_size leq_ltn in i_lt_size => //.
suff bound_digest_vars_aux_imple k y :
    (y < 8)%nat ->
  nth 0 (N_sha256.digest_vars_aux [seq bool_32b_to_N i | i <- W_vals]
    [seq bool_32b_to_N i | i <- vars] k) y < 256 ^ 4.
  by move/(bound_digest_vars_aux_imple n.+1 i): i_lt_size; rewrite ix.
elim: k y => [y ltx8|k IH y].
  move: (bool_32b_to_nat_lt_2e32 (nth bool_32b00 vars y)).
  case C: (ltn y (size vars)).
    rewrite (nth_map bool_32b00) //.
    by rewrite N_ltn Nat_pow !Nnat.Nat2N.id.
  rewrite (nth_default 0) // size_map.
  by rewrite -leq_ltn ltnNge in C; move/negbFE: C.
case: y => [a|y]; first by apply: N.mod_lt.
do 3! [case: y => [a|y]; first by apply: IH].
case: y => [a|y]; first by apply: N.mod_lt.
do 3! [case: y => [/= a|y]; first by apply: IH].
by case: y => [// a|y]; first by case: y.
Qed.

Lemma digest_vars_auxE W_vals vars n :
    N.of_nat n < 256 ^ 4 ->
  digest_vars_aux W_vals vars n K_s
    = map bool_32b_of_N (N_sha256.digest_vars_aux (map bool_32b_to_N W_vals)
        (map bool_32b_to_N vars) n).
Proof.
elim: n => [|n IH nbound] //=; first by rewrite mapK //; apply: bool_32b_to_NK.
have ltnW: N.of_nat n < 256 ^ 4.
  by apply/N.le_succ_l; rewrite -Nnat.Nat2N.inj_succ; apply: N.lt_le_incl.
have H i:
  nth bool_32b00 (digest_vars_aux W_vals vars n K_s) i
    = bool_32b_of_N (nth 0 (N_sha256.digest_vars_aux
        [seq bool_32b_to_N i | i <- W_vals]
          [seq bool_32b_to_N i | i <- vars] n) i).
  by rewrite (@nth_map2 _ _ _ _ 0 i) (IH ltnW).
rewrite T1E T2E 2! bool_32b_addE !(nth_map2 bool_32b_to_N).
rewrite !bool_32b_of_N2e32K; [|apply: N.mod_upper_bound => //..].
congr cons; last do 3! [congr cons => //].
  rewrite !(IH ltnW) all_mapK //.
  by move=> x; move/digest_vars_aux_32b_to_N_bound; apply: bool_32b_of_N2e32K.
congr cons; last by do 3! [congr cons => //].
rewrite !(IH ltnW) all_mapK //.
move=> x; move/digest_vars_aux_32b_to_N_bound; apply: bool_32b_of_N2e32K.
Qed.

Lemma digest_varsE W_vals vars :
  digest_vars W_vals vars K_s
    = map bool_32b_of_N (N_sha256.digest_vars (map bool_32b_to_N W_vals)
                         (map bool_32b_to_N vars)).
Proof. by apply: digest_vars_auxE. Qed.

(* Correspondence hash_blocks *)

Definition H_s := [seq bool_32b_of_N i | i <- H].

Lemma H_bool_32b_to_N_K :
  [seq bool_32b_to_N i | i <- H_s] = H.
Proof.
rewrite -map_comp /comp.
by do 8! [rewrite map_cons {1}bool_32b_of_N2e32K; last by []].
Qed.

Lemma ms_bound_bool_32b x B :
  x \in N_sha256.message_schedule (bool_512b_to_seq_N B) -> x < 2 ^ 32.
Proof.
have: all (N.ltb^~ (2 ^ 32)) (bool_512b_to_seq_N B).
  apply/allP => [x0 +]; rewrite /bool_512b_to_seq_N -map_comp /comp.
  by move/mapP => [y _] ->; apply/N.ltb_spec0; apply: bool_32b_to_N_lt2e32.
by move/(all_take 16) /ms_bound_mem /allP => Hms /Hms /N.ltb_spec0.
Qed.

Lemma mem_digest_varsE B1 B2 x :
    x \in N_sha256.digest_vars [seq bool_32b_to_N i | i <- B1]
          [seq bool_32b_to_N i | i <- B2] ->
  (bool_32b_of_N x) \in digest_vars B1 B2 K_s.
Proof. by rewrite digest_varsE; apply: (map_f bool_32b_of_N). Qed.

Lemma bound_digest_vars_aux B1 B2 x n :
   x \in N_sha256.digest_vars_aux [seq bool_32b_to_N i | i <- B1]
                               [seq bool_32b_to_N i | i <- B2] n ->
  (x < 256 ^ 4).
Proof.
elim: n => [/mapP|n IH /=].
  elim => i memH ->; rewrite /bool_32b_to_N; apply: N.ltb_spec0.
  rewrite N_ltnb -leq_ltn N_expn !Nnat.Nat2N.id.
  by apply/(bool_32b_to_nat_lt_2e32 i).
set s_dig := (N_sha256.digest_vars_aux [seq bool_32b_to_N i | i <- B1]
                                       [seq bool_32b_to_N i | i <- B2] n).
rewrite -/s_dig in IH.
rewrite in_cons => /orP; case.
  by move=> /eqP ->; apply/N.mod_upper_bound.
rewrite in_cons => /orP; case.
  move=> /eqP; move: IH => /[swap] ->.
  case sizeH: (0 < size s_dig)%nat; first by apply; apply: mem_nth.
  by rewrite nth_default => //; move /negbT: sizeH; rewrite -leqNgt.
rewrite in_cons => /orP; case.
  move=> /eqP; move: IH => /[swap] ->.
  case sizeH: (1 < size s_dig)%nat; first by apply; apply: mem_nth.
  by rewrite nth_default => //; move /negbT: sizeH; rewrite -leqNgt.
rewrite in_cons => /orP; case.
  move=> /eqP; move: IH => /[swap] ->.
  case sizeH: (2 < size s_dig)%nat; first by apply; apply: mem_nth.
  by rewrite nth_default => //; move /negbT: sizeH; rewrite -leqNgt.
rewrite in_cons => /orP; case.
  by move=> /eqP ->; apply/N.mod_upper_bound.
rewrite in_cons => /orP; case.
  move=> /eqP; move: IH => /[swap] ->.
  case sizeH: (4 < size s_dig)%nat; first by apply; apply: mem_nth.
  by rewrite nth_default => //; move /negbT: sizeH; rewrite -leqNgt.
rewrite in_cons => /orP; case.
  move=> /eqP; move: IH => /[swap] ->.
  case sizeH: (5 < size s_dig)%nat; first by apply; apply: mem_nth.
  by rewrite nth_default => //; move /negbT: sizeH; rewrite -leqNgt.
rewrite mem_seq1 => /eqP; move: IH => /[swap] ->.
case sizeH: (6 < size s_dig)%nat; first by apply; apply: mem_nth.
by rewrite nth_default => //; move /negbT: sizeH; rewrite -leqNgt.
Qed.

Lemma bound_digest_vars B1 B2 x :
    x \in N_sha256.digest_vars [seq bool_32b_to_N i | i <- B1]
                               [seq bool_32b_to_N i | i <- B2] ->
  (x < 256 ^ 4).
Proof. by apply/bound_digest_vars_aux. Qed.

Lemma bound_digest_vars_gen s1 s2 x :
    {in s1, forall x : N, x < 2 ^ 32} ->
    {in s2, forall x : N, x < 2 ^ 32} ->
    x \in N_sha256.digest_vars s1 s2 ->
  (x < 256 ^ 4).
Proof.
move=> Hs1 Hs2.
rewrite (@bool_32b_of_N2e32K_seq s1) // (@bool_32b_of_N2e32K_seq s2) //.
by apply: bound_digest_vars.
Qed.

Lemma hash_blocksE s n :
    (n < size s)%nat ->
  hash_blocks s n H_s K_s
    = seq_32b_of_seq_N (N_sha256.hash_blocks (seq_512b_to_seq_seq_N s) n).
Proof.
have prod_32b_N:
  (fun x : bool_32b * bool_32b => bool_32b_add x.1 x.2) =1
    (fun x : N * N => bool_32b_of_nat2e32 (N.to_nat ((x.1 + x.2) mod wexp))) \o
      (fun x : bool_32b * bool_32b => (bool_32b_to_N x.1, bool_32b_to_N x.2)).
  rewrite /comp; move=> x.
  rewrite [(bool_32b_to_N x.1, bool_32b_to_N x.2).1]/(bool_32b_to_N x.1).
  rewrite [(bool_32b_to_N x.1, bool_32b_to_N x.2).2]/(bool_32b_to_N x.2).
  rewrite bool_32b_add_mod2e32; apply: f_equal.
  rewrite N_addn N_modn /wexp -[32]/(8 * 4).
  rewrite N.pow_mul_r -[2 ^ 8]/(256) N_expn !Nnat.Nat2N.id.
  by rewrite (@expn_eq _ _ (N.to_nat 256) (N.to_nat 4)).
elim: n => [sz|n HI sz].
  rewrite /seq_32b_of_seq_N -!map_comp !/comp.
  apply: (@map_eq _ _ _ _ _ (fun x : bool_32b * bool_32b =>
           (bool_32b_to_N x.1, bool_32b_to_N x.2))); last by [].
  rewrite -zip_map.
  rewrite map_zip1; last by rewrite {1}size_map => /=.
  rewrite map_zip2; last by move=> /=.
  rewrite {1}H_bool_32b_to_N_K; apply: f_equal.
  rewrite digest_varsE all_mapK.
    rewrite {1}H_bool_32b_to_N_K; apply: (f_equal (N_sha256.digest_vars^~ H)).
    rewrite message_scheduleE /seq_32b_of_seq_N -map_comp.
    rewrite all_mapK; first by apply: f_equal; move: sz; elim: s => [|x s HI].
    move=> x Hms; rewrite /comp  bool_32b_of_N2e32K //.
    by apply: ms_bound_bool_32b ; apply: Hms.
  move=> x Hdv; apply: bool_32b_of_N2e32K; move: Hdv.
  by apply: bound_digest_vars.
have: (n < size s)%nat; first by apply: (ltn_trans (ltnSn n) sz).
move/HI; rewrite /seq_32b_of_seq_N => IH2.
rewrite hash_blocks_Sn N_sha256_hash_blocks_Sn.
rewrite /seq_32b_of_seq_N -!map_comp.
apply: (@map_eq _ _ _ _ _ (fun x : bool_32b * bool_32b =>
         (bool_32b_to_N x.1, bool_32b_to_N x.2))) => //.
rewrite -zip_map.
rewrite map_zip1; last by rewrite digest_vars_size hash_blocks_size.
rewrite map_zip2; last by rewrite digest_vars_size hash_blocks_size.
rewrite digest_varsE message_scheduleE.
rewrite IH2 -map_comp.
rewrite all_mapK.
  apply: f_equal; rewrite all_mapK.
    apply: (f_equal (N_sha256.digest_vars^~ _)).
    rewrite /seq_32b_of_seq_N -map_comp all_mapK.
      rewrite /seq_512b_to_seq_seq_N -map_comp.
      by rewrite (nth_map bool_512b00).
    move=> x Hms; rewrite /comp bool_32b_of_N2e32K //.
    by apply: ms_bound_bool_32b; apply: Hms.
  move=> x Hdv; apply: bool_32b_of_N2e32K; move: Hdv.
  apply: bound_digest_vars_gen; move=> x0.
    rewrite /seq_32b_of_seq_N -map_comp /comp all_mapK.
      by apply: ms_bound_bool_32b.
    move=> x1 Hx1; rewrite bool_32b_of_N2e32K //.
    by apply: ms_bound_bool_32b; apply: Hx1.
  by apply: N_sha256_hash_blocks_mem_bound; apply Hhb.
move=> x2 Hx2; rewrite /comp bool_32b_of_N2e32K //.
by apply: N_sha256_hash_blocks_mem_bound; apply: Hx2.
Qed.

(* Correspondence SHA256 *)

Lemma seq_seq_NK s :
    {in s, forall x : seq N, size x = 16} ->
    (forall x y, x \in s -> y \in x -> y < 2 ^ 32) ->
  [seq seq_32b_to_seq_N i | i <- [seq bool_512b_to_seq_bool_32b i
    | i <- seq_32b_to_seq_512b [seq bool_32b_of_N i | i <- flatten s]]] = s.
Proof.
elim: s => [//|a l IH H_size H_bound]; rewrite map_cat.
have size_s: size ([seq bool_32b_of_N i | i <- a]) = (16 * 1)%nat.
  by rewrite size_map; apply: H_size; rewrite in_cons /=; apply/orP; left.
have IH_l: {in l, forall x : seq_eqType bin_nat_eqType, size x = 16}.
by move=> x Hx; apply: H_size; rewrite in_cons Hx orbT.
have shape_l: shape l = nseq (size l) 16%nat. by apply: shape_nseq.
have size_flatl: exists k, size ([seq bool_32b_of_N i | i <- flatten l]) = (16 * k)%nat.
  by rewrite size_map size_flatten shape_l sumn_nseq; exists(size l).
move: size_flatl => [k size_flatl].
rewrite (seq_32b_to_seq_512b_cat size_s size_flatl) !map_cat.
have IH_l':
  (forall (x : seq_eqType bin_nat_eqType) (y : bin_nat_eqType),
    x \in l -> y \in x -> y < 2 ^ 32).
  by move=> x y Hx Hy; apply: (H_bound x) => //; rewrite in_cons Hx orbT.
move: (IH IH_l IH_l') => ->.
rewrite bool_512b_to_seq_32b16K //= /seq_32b_to_seq_N all_mapK //.
move=> y y_a; move: (H_bound a y (mem_head a l)) => y_a32.
by move/y_a32: y_a => y32; rewrite bool_32b_of_N2e32K.
Qed.

Lemma bound_in_in_padd s k :
    size s = (k * 64)%nat ->
  {in map split_w32 (split_in_blocks s (size s %/ 64 - 1)),
      forall x : seq N, {in x, forall y : N, y < 2 ^ 32}}.
Proof.
have bound_in_in_padd64 s':
    size s' = 64 ->
  {in map split_w32 (split_in_blocks s' (size s' %/ 64 - 1)),
    forall x : seq N, {in x, forall y : N, y < 2 ^ 32}}.
  move=> h64 x.
  rewrite ?divnn (seq_size "000"%byte h64) mem_seq1; move/eqP => -> y.
  have w32_bound b1 b2 b3 b4: w32_to_N b1 b2 b3 b4 < 2 ^ 32.
    by rewrite w32_to_NE; apply: bool_32b_to_N_lt2e32.
  by do 16! [rewrite in_cons; move/orP; case; first by move/eqP => ->].
elim: k s => [s|k IH s sz_s x].
  rewrite mul0n; move/size0nil => -> x; rewrite mem_seq1.
  by move/eqP => -> y; rewrite in_nil.
have size_t: size (take 64 s) = 64 by rewrite size_takel // sz_s leq_pmull.
have size_d: (size (drop 64 s)) = (k * 64)%nat.
  by rewrite size_drop sz_s mulSn addKn.
case c: (size s %/ 64 <= 1)%nat.
  rewrite sz_s mulnK // in c.
  have k0: k = 0 by move: c; case k.
  by rewrite k0 /= mul1n in sz_s; apply: bound_in_in_padd64.
rewrite leqNgt in c; move/negbFE: c => c.
rewrite -{1}(cat_take_drop 64 s); move: (split_in_blocks_dec c) => ->.
rewrite map_cons in_cons; move/orP.
case; last by move: (IH _ size_d x); rewrite size_d sz_s !mulnK.
move/eqP => ->; apply: bound_in_in_padd64; first by apply: size_t.
by rewrite size_t divnn /= mem_seq1.
Qed.

Lemma N_preprocessingE s :
    N.of_nat (size s) * 8 < 256 ^ 8 ->
  (N_sha256.preprocessing (string_of_seq_bool_B s))
    = seq_512b_to_seq_seq_N (preprocessing s).
Proof.
move=> sz_s; rewrite /seq_512b_to_seq_seq_N preprocessingE //.
move/dvdnP: (size_padding_div64 sz_s) => [k prop].
rewrite seq_seq_NK /N_sha256.preprocessing // => x.
rewrite list_byte_of_string_of_list_byte.
  move=> l; apply: (size_in_padd _ prop) => //.
  by rewrite -(@ltn_pmul2r 64%nat _ _) // mul0n -{}prop {l sz_s}; elim s.
rewrite /string_of_seq_bool_B list_byte_of_string_of_list_byte.
by move=> y Hx yx; apply: (bound_in_in_padd prop Hx yx).
Qed.

Lemma size_preprocessingE s :
    N.of_nat (size s) * 8 < 256 ^ 8 ->
  size (preprocessing s)
    = size (N_sha256.preprocessing (string_of_seq_bool_B s)).
Proof. by move=> h; rewrite N_preprocessingE ?size_map. Qed.

Lemma sha256_noappE s :
    N.of_nat (size s) * 8 < 256 ^ 8 ->
  sha256 s H_s K_s
    = bool_256b_of_seq_N (N_sha256.sha256_noapp (string_of_seq_bool_B s)).
Proof.
move=> size_256e8.
rewrite /sha256 /N_sha256.sha256_noapp hash_blocksE; last first.
  by rewrite ltn_predL preprocessing_size addnS.
rewrite -N_preprocessingE // size_preprocessingE //.
rewrite /seq_32b_of_seq_N /seq_32b_to_seq_256b -map_comp.
rewrite /bool_256b_of_seq_N N_sha256_hash_blocks_size.
rewrite -!size_preprocessingE //.
set hb:= (N_sha256.hash_blocks
           (N_sha256.preprocessing (string_of_seq_bool_B s))
           (size (preprocessing s)).-1).
by rewrite (seq_nth 0 hb) N_sha256_hash_blocks_size.
Qed.

Lemma foldl_pow8 s k :
    size s = 8 ->
  (foldl (fun x : N => [eta N.add (x * k)]) 0 s)
    = ((nth 0 s 0) * k ^ 7) + ((nth 0 s 1) * k ^ 6) + ((nth 0 s 2) * k ^ 5) +
        ((nth 0 s 3) * k ^ 4) + ((nth 0 s 4) * k ^ 3) + ((nth 0 s 5) * k ^ 2) +
          ((nth 0 s 6) * k ^ 1) + (nth 0 s 7).
Proof.
rewrite {2}(seq_nth 0 s); move=> ->.
rewrite -[7]/(N.succ 6) -[6]/(N.succ 5) -[5]/(N.succ 4).
rewrite -[4]/(N.succ 3) -[3]/(N.succ 2) !N.pow_succ_r' !N.pow_2_r.
by rewrite N.pow_1_r !N.mul_assoc /= !N.mul_add_distr_r.
Qed.

Lemma bool_256b_of_seq_N_foldl s :
    size s = 8 ->
    (forall k : nat, nth 0 s k < 2 ^ 32) ->
  bool_256b_of_seq_N s
    = bool_256b_of_N (foldl (fun x : N => [eta N.add (x * 2 ^ 32)]) 0 s).
Proof.
move=> sz8.
rewrite foldl_pow8 // => bound2e32; apply: (canRL bool_256b_to_NK).
rewrite /bool_256b_of_seq_N sz8 bool_256b_to_N_char -!N.add_assoc.
congr N.add; do 6! [rewrite bool_32b_of_N2e32K //|congr N.add].
all: by rewrite bool_32b_of_N2e32K.
Qed.

Lemma sha256E s :
    N.of_nat (size s) * 8 < 256 ^ 8 ->
  sha256 s H_s K_s = bool_256b_of_N (N_sha256.sha256 (string_of_seq_bool_B s)).
Proof.
rewrite foldl_sha256_noapp -bool_256b_of_seq_N_foldl => [||k].
    by apply sha256_noappE.
  by rewrite N_sha256_hash_blocks_size.
by apply: N_sha256_hash_blocks_nth_bound.
Qed.

Lemma N_sha256_bound s :
  N_sha256.sha256 s < 2 ^ 256.
Proof.
rewrite /N_sha256.sha256 foldl_pow8; last by apply: N_sha256_hash_blocks_size.
have N_sha256_nth := (N_sha256_hash_blocks_nth_bound).
by rewrite -!N.add_assoc; do 7! apply: N_lt_bound_pow => //.
Qed.

Lemma N_sha256E s :
    N.of_nat (size (string_to_seq_bool_B s)) * 8 < 256 ^ 8 ->
  N_sha256.sha256 s = bool_256b_to_N (sha256 (string_to_seq_bool_B s) H_s K_s).
Proof.
move=> size_256e8.
rewrite sha256E // bool_256b_to_N2e256K string_to_seq_bool_BK //.
by apply: N_sha256_bound.
Qed.
