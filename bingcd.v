Require Import Arith PeanoNat Lia Bool.

(*ビットシフト版*)
Fixpoint bgcd_aux' (fuel a b : nat) : nat * nat :=
  match fuel with
  | 0 => (0, 0)
  | S f =>
    if a =? 0 then (b, 0)
    else if b =? 0 then (a, 0)
    else match Nat.testbit a 0, Nat.testbit b 0 with
      | false, false =>
          let r := bgcd_aux' f (Nat.shiftr a 1) (Nat.shiftr b 1) in
          (Nat.shiftl (fst r) 1, S (snd r))
      | false, true =>
          let r := bgcd_aux' f (Nat.shiftr a 1) b in
          (fst r, S (snd r))
      | true, false =>
          let r := bgcd_aux' f a (Nat.shiftr b 1) in
          (fst r, S (snd r))
      | true, true =>
          if b <=? a then
            let r := bgcd_aux' f (Nat.shiftr (a - b) 1) b in
            (fst r, S (snd r))
          else
            let r := bgcd_aux' f a (Nat.shiftr (b - a) 1) in
            (fst r, S (snd r))
    end
  end.

Definition bgcd' (a b : nat) : nat := fst (bgcd_aux' (a + b + 1) a b).
Definition bgcd_steps' (a b : nat) : nat := snd (bgcd_aux' (a + b + 1) a b).

Lemma bgcd_aux'_S : forall f a b, bgcd_aux' (S f) a b =
    if a =? 0 then (b, 0)
    else if b =? 0 then (a, 0)
    else match Nat.testbit a 0, Nat.testbit b 0 with
      | false, false =>
          let r := bgcd_aux' f (Nat.shiftr a 1) (Nat.shiftr b 1) in
          (Nat.shiftl (fst r) 1, S (snd r))
      | false, true =>
          let r := bgcd_aux' f (Nat.shiftr a 1) b in
          (fst r, S (snd r))
      | true, false =>
          let r := bgcd_aux' f a (Nat.shiftr b 1) in
          (fst r, S (snd r))
      | true, true =>
          if b <=? a then
            let r := bgcd_aux' f (Nat.shiftr (a - b) 1) b in
            (fst r, S (snd r))
          else
            let r := bgcd_aux' f a (Nat.shiftr (b - a) 1) in
            (fst r, S (snd r))
    end.
Proof. reflexivity. Qed.

Compute bgcd' 48 18.

Example bgcd'_ex : bgcd' 48 18 = 6.
Proof. reflexivity. Qed.

(*自然数版*)
Fixpoint bgcd_aux (fuel a b : nat) : nat * nat :=
  match fuel with
  | 0 => (0, 0)
  | S f =>
    if a =? 0 then (b, 0)
    else if b =? 0 then (a, 0)
    else match Nat.even a, Nat.even b with
      | true, true =>
          let r := bgcd_aux f (Nat.div2 a) (Nat.div2 b) in
          (2 * fst r, S (snd r))
      | true, false =>
          let r := bgcd_aux f (Nat.div2 a) b in
          (fst r, S (snd r))
      | false, true =>
          let r := bgcd_aux f a (Nat.div2 b) in
          (fst r, S (snd r))
      | false, false =>
          if b <=? a then
            let r := bgcd_aux f (Nat.div2 (a - b)) b in
            (fst r, S (snd r))
          else
            let r := bgcd_aux f a (Nat.div2 (b - a)) in
            (fst r, S (snd r))
    end
  end.

Definition bgcd (a b : nat) : nat := fst (bgcd_aux (a + b + 1) a b).
Definition bgcd_steps (a b : nat) : nat := snd (bgcd_aux (a + b + 1) a b).

Definition bound (a b : nat) : nat :=
  if (a =? 0) || (b =? 0) then 0 else Nat.log2 a + Nat.log2 b + 2.

Lemma even_double : forall a, Nat.even a = true -> a = 2 * Nat.div2 a.
Proof.
  intros a H. rewrite Nat.even_spec in H. destruct H as [k Hk].
  subst. rewrite Nat.div2_double. lia.
Qed.

Lemma odd_coprime2 : forall b, Nat.even b = false -> Nat.gcd 2 b = 1.
Proof.
  intros b H.
  assert (Nat.odd b = true) by (unfold Nat.odd; rewrite H; reflexivity).
  apply Nat.odd_spec in H0. destruct H0 as [k Hk]. subst.
  rewrite Nat.gcd_comm. rewrite Nat.gcd_comm.
  replace (2 * k + 1) with (1 + k * 2) by lia.
  rewrite Nat.gcd_add_mult_diag_r. simpl. reflexivity.
Qed.

Lemma gcd_halve_odd : forall x b, Nat.even b = false ->
  Nat.gcd (2 * x) b = Nat.gcd x b.
Proof.
  intros x b H. apply Nat.divide_antisym.
  - set (d := Nat.gcd (2 * x) b).
    assert (Hd1 : Nat.divide d (2 * x)) by apply Nat.gcd_divide_l.
    assert (Hd2 : Nat.divide d b) by apply Nat.gcd_divide_r.
    assert (Hc : Nat.gcd d 2 = 1).
    { assert (Hg : Nat.divide (Nat.gcd d 2) (Nat.gcd 2 b)).
      { apply Nat.gcd_greatest.
        - apply Nat.gcd_divide_r.
        - apply (Nat.divide_trans _ d); [apply Nat.gcd_divide_l | exact Hd2]. }
      rewrite (odd_coprime2 b H) in Hg.
      apply Nat.divide_1_r. exact Hg. }
    apply Nat.gcd_greatest.
    + apply (Nat.gauss d 2 x Hd1 Hc).
    + exact Hd2.
  - apply Nat.gcd_greatest.
    + apply Nat.divide_mul_r. apply Nat.gcd_divide_l.
    + apply Nat.gcd_divide_r.
Qed.

Lemma bound_nz : forall a b, a <> 0 -> b <> 0 ->
  bound a b = Nat.log2 a + Nat.log2 b + 2.
Proof.
  intros a b Ha Hb. unfold bound.
  apply Nat.eqb_neq in Ha. apply Nat.eqb_neq in Hb.
  rewrite Ha, Hb. reflexivity.
Qed.

Lemma bound_zero_l : forall b, bound 0 b = 0.
Proof. intros b. reflexivity. Qed.

Lemma bound_zero_r : forall a, bound a 0 = 0.
Proof. intros a. unfold bound. rewrite orb_true_r. reflexivity. Qed.

Lemma log2_half : forall a x, x <> 0 -> 2 * x <= a ->
  Nat.log2 x + 1 <= Nat.log2 a.
Proof.
  intros a x Hx Hle.
  pose proof (Nat.log2_double x (proj1 (Nat.neq_0_lt_0 _) Hx)) as H1.
  pose proof (Nat.log2_le_mono _ _ Hle) as H2. lia.
Qed.

Lemma bound_step : forall a b a' b', a <> 0 -> b <> 0 ->
  (a' = 0 \/ b' = 0 \/ Nat.log2 a' + Nat.log2 b' + 1 <= Nat.log2 a + Nat.log2 b) ->
  S (bound a' b') <= bound a b.
Proof.
  intros a b a' b' Ha Hb H. rewrite (bound_nz a b Ha Hb).
  destruct (Nat.eq_dec a' 0) as [->|Ha'].
  - rewrite bound_zero_l. lia.
  - destruct (Nat.eq_dec b' 0) as [->|Hb'].
    + rewrite bound_zero_r. lia.
    + rewrite (bound_nz a' b' Ha' Hb'). destruct H as [H|[H|H]]; [congruence|congruence|lia].
Qed.

Lemma bgcd_aux_S : forall f a b, bgcd_aux (S f) a b =
    if a =? 0 then (b, 0)
    else if b =? 0 then (a, 0)
    else match Nat.even a, Nat.even b with
      | true, true =>
          let r := bgcd_aux f (Nat.div2 a) (Nat.div2 b) in
          (2 * fst r, S (snd r))
      | true, false =>
          let r := bgcd_aux f (Nat.div2 a) b in
          (fst r, S (snd r))
      | false, true =>
          let r := bgcd_aux f a (Nat.div2 b) in
          (fst r, S (snd r))
      | false, false =>
          if b <=? a then
            let r := bgcd_aux f (Nat.div2 (a - b)) b in
            (fst r, S (snd r))
          else
            let r := bgcd_aux f a (Nat.div2 (b - a)) in
            (fst r, S (snd r))
    end.
Proof. reflexivity. Qed.

Lemma odd_odd_sub_even : forall a b, Nat.even a = false -> Nat.even b = false ->
  b <= a -> Nat.even (a - b) = true.
Proof.
  intros a b Ea Eb H. rewrite Nat.even_sub by exact H. rewrite Ea, Eb. reflexivity.
Qed.

Lemma gcd_ee : forall a b, Nat.even a = true -> Nat.even b = true ->
  Nat.gcd a b = 2 * Nat.gcd (Nat.div2 a) (Nat.div2 b).
Proof.
  intros a b Ea Eb. rewrite <- Nat.gcd_mul_mono_l.
  exact (f_equal2 Nat.gcd (even_double a Ea) (even_double b Eb)).
Qed.

Lemma gcd_eo : forall a b, Nat.even a = true -> Nat.even b = false ->
  Nat.gcd a b = Nat.gcd (Nat.div2 a) b.
Proof.
  intros a b Ea Eb. rewrite <- (gcd_halve_odd (Nat.div2 a) b Eb).
  exact (f_equal2 Nat.gcd (even_double a Ea) (eq_refl b)).
Qed.

Lemma gcd_oe : forall a b, Nat.even a = false -> Nat.even b = true ->
  Nat.gcd a b = Nat.gcd a (Nat.div2 b).
Proof.
  intros a b Ea Eb. rewrite (Nat.gcd_comm a b), (Nat.gcd_comm a (Nat.div2 b)).
  exact (gcd_eo b a Eb Ea).
Qed.

Lemma gcd_oo_ge : forall a b, Nat.even a = false -> Nat.even b = false -> b <= a ->
  Nat.gcd a b = Nat.gcd (Nat.div2 (a - b)) b.
Proof.
  intros a b Ea Eb H.
  rewrite <- (gcd_eo (a - b) b (odd_odd_sub_even a b Ea Eb H) Eb).
  rewrite (Nat.gcd_comm (a - b) b). rewrite (Nat.gcd_sub_diag_r b a H).
  apply Nat.gcd_comm.
Qed.

Lemma gcd_oo_lt : forall a b, Nat.even a = false -> Nat.even b = false -> a < b ->
  Nat.gcd a b = Nat.gcd a (Nat.div2 (b - a)).
Proof.
  intros a b Ea Eb H.
  rewrite <- (gcd_oe a (b - a) Ea (odd_odd_sub_even b a Eb Ea (Nat.lt_le_incl _ _ H))).
  symmetry. exact (Nat.gcd_sub_diag_r a b (Nat.lt_le_incl _ _ H)).
Qed.

Theorem bgcd_aux_fuel : forall fuel a b, a + b < fuel ->
  bgcd_aux (S fuel) a b = bgcd_aux fuel a b.
Proof.
  induction fuel as [|f IH]; intros a b Hf; [lia|].
  rewrite (bgcd_aux_S (S f) a b), (bgcd_aux_S f a b).
  destruct (a =? 0) eqn:Ha; [reflexivity|].
  apply Nat.eqb_neq in Ha.
  destruct (b =? 0) eqn:Hb; [reflexivity|].
  apply Nat.eqb_neq in Hb.
  destruct (Nat.even a) eqn:Ea; destruct (Nat.even b) eqn:Eb.
  - pose proof (even_double a Ea) as Da. pose proof (even_double b Eb) as Db.
    rewrite (IH (Nat.div2 a) (Nat.div2 b)) by lia. reflexivity.
  - pose proof (even_double a Ea) as Da.
    rewrite (IH (Nat.div2 a) b) by lia. reflexivity.
  - pose proof (even_double b Eb) as Db.
    rewrite (IH a (Nat.div2 b)) by lia. reflexivity.
  - destruct (b <=? a) eqn:Hba.
    + apply Nat.leb_le in Hba.
      pose proof (even_double _ (odd_odd_sub_even a b Ea Eb Hba)) as D.
      rewrite (IH (Nat.div2 (a - b)) b) by lia. reflexivity.
    + apply Nat.leb_gt in Hba.
      pose proof (even_double _ (odd_odd_sub_even b a Eb Ea (Nat.lt_le_incl _ _ Hba))) as D.
      rewrite (IH a (Nat.div2 (b - a))) by lia. reflexivity.
Qed.

Lemma bgcd_aux_fuel_extra : forall k fuel a b, a + b < fuel ->
  bgcd_aux (k + fuel) a b = bgcd_aux fuel a b.
Proof.
  induction k as [|k IH]; intros fuel a b H; [reflexivity|].
  rewrite Nat.add_succ_l. rewrite bgcd_aux_fuel by lia. apply IH. exact H.
Qed.

Theorem bgcd_aux_correct : forall fuel a b, a + b < fuel ->
  fst (bgcd_aux fuel a b) = Nat.gcd a b.
Proof.
  induction fuel as [|f IH]; intros a b Hf; [lia|].
  simpl. destruct (a =? 0) eqn:Ha.
  - apply Nat.eqb_eq in Ha. subst. reflexivity.
  - apply Nat.eqb_neq in Ha. destruct (b =? 0) eqn:Hb.
    + apply Nat.eqb_eq in Hb. subst. rewrite Nat.gcd_0_r. reflexivity.
    + apply Nat.eqb_neq in Hb.
      destruct (Nat.even a) eqn:Ea; destruct (Nat.even b) eqn:Eb; simpl.
      * pose proof (even_double a Ea) as Da. pose proof (even_double b Eb) as Db.
        assert (G : fst (bgcd_aux f (Nat.div2 a) (Nat.div2 b)) = Nat.gcd (Nat.div2 a) (Nat.div2 b))
          by (apply IH; lia).
        pose proof (gcd_ee a b Ea Eb) as E. lia.
      * pose proof (even_double a Ea) as Da.
        assert (G : fst (bgcd_aux f (Nat.div2 a) b) = Nat.gcd (Nat.div2 a) b)
          by (apply IH; lia).
        pose proof (gcd_eo a b Ea Eb) as E. lia.
      * pose proof (even_double b Eb) as Db.
        assert (G : fst (bgcd_aux f a (Nat.div2 b)) = Nat.gcd a (Nat.div2 b))
          by (apply IH; lia).
        pose proof (gcd_oe a b Ea Eb) as E. lia.
      * destruct (b <=? a) eqn:Hba; simpl.
        -- apply Nat.leb_le in Hba.
           pose proof (even_double _ (odd_odd_sub_even a b Ea Eb Hba)) as D.
           assert (G : fst (bgcd_aux f (Nat.div2 (a - b)) b) = Nat.gcd (Nat.div2 (a - b)) b)
             by (apply IH; lia).
           pose proof (gcd_oo_ge a b Ea Eb Hba) as E. lia.
        -- apply Nat.leb_gt in Hba.
           pose proof (even_double _ (odd_odd_sub_even b a Eb Ea (Nat.lt_le_incl _ _ Hba))) as D.
           assert (G : fst (bgcd_aux f a (Nat.div2 (b - a))) = Nat.gcd a (Nat.div2 (b - a)))
             by (apply IH; lia).
           pose proof (gcd_oo_lt a b Ea Eb Hba) as E. lia.
Qed.

Theorem bgcd_aux_steps : forall fuel a b, a + b < fuel ->
  snd (bgcd_aux fuel a b) <= bound a b.
Proof.
  induction fuel as [|f IH]; intros a b Hf; [lia|].
  simpl. destruct (a =? 0) eqn:Ha.
  - apply Nat.eqb_eq in Ha. subst. simpl. lia.
  - apply Nat.eqb_neq in Ha. destruct (b =? 0) eqn:Hb.
    + apply Nat.eqb_eq in Hb. subst. simpl. lia.
    + apply Nat.eqb_neq in Hb.
      destruct (Nat.even a) eqn:Ea; destruct (Nat.even b) eqn:Eb; simpl.
      * pose proof (even_double a Ea) as Da. pose proof (even_double b Eb) as Db.
        assert (Ha2 : Nat.div2 a <> 0) by lia.
        assert (Hb2 : Nat.div2 b <> 0) by lia.
        assert (N : snd (bgcd_aux f (Nat.div2 a) (Nat.div2 b)) <= bound (Nat.div2 a) (Nat.div2 b))
          by (apply IH; lia).
        pose proof (log2_half a _ Ha2 (ltac:(lia))) as La.
        pose proof (log2_half b _ Hb2 (ltac:(lia))) as Lb.
        assert (B : S (bound (Nat.div2 a) (Nat.div2 b)) <= bound a b)
          by (apply bound_step; [exact Ha|exact Hb|right; right; lia]).
        lia.
      * pose proof (even_double a Ea) as Da.
        assert (Ha2 : Nat.div2 a <> 0) by lia.
        assert (N : snd (bgcd_aux f (Nat.div2 a) b) <= bound (Nat.div2 a) b)
          by (apply IH; lia).
        pose proof (log2_half a _ Ha2 (ltac:(lia))) as La.
        assert (B : S (bound (Nat.div2 a) b) <= bound a b)
          by (apply bound_step; [exact Ha|exact Hb|right; right; lia]).
        lia.
      * pose proof (even_double b Eb) as Db.
        assert (Hb2 : Nat.div2 b <> 0) by lia.
        assert (N : snd (bgcd_aux f a (Nat.div2 b)) <= bound a (Nat.div2 b))
          by (apply IH; lia).
        pose proof (log2_half b _ Hb2 (ltac:(lia))) as Lb.
        assert (B : S (bound a (Nat.div2 b)) <= bound a b)
          by (apply bound_step; [exact Ha|exact Hb|right; right; lia]).
        lia.
      * destruct (b <=? a) eqn:Hba; simpl.
        -- apply Nat.leb_le in Hba.
           pose proof (even_double _ (odd_odd_sub_even a b Ea Eb Hba)) as D.
           assert (N : snd (bgcd_aux f (Nat.div2 (a - b)) b) <= bound (Nat.div2 (a - b)) b)
             by (apply IH; lia).
           destruct (Nat.eq_dec (Nat.div2 (a - b)) 0) as [Z|Z].
           ++ assert (B : S (bound (Nat.div2 (a - b)) b) <= bound a b)
                by (apply bound_step; [exact Ha|exact Hb|left; exact Z]).
              lia.
           ++ pose proof (log2_half a _ Z (ltac:(lia))) as La.
              assert (B : S (bound (Nat.div2 (a - b)) b) <= bound a b)
                by (apply bound_step; [exact Ha|exact Hb|right; right; lia]).
              lia.
        -- apply Nat.leb_gt in Hba.
           pose proof (even_double _ (odd_odd_sub_even b a Eb Ea (Nat.lt_le_incl _ _ Hba))) as D.
           assert (N : snd (bgcd_aux f a (Nat.div2 (b - a))) <= bound a (Nat.div2 (b - a)))
             by (apply IH; lia).
           destruct (Nat.eq_dec (Nat.div2 (b - a)) 0) as [Z|Z].
           ++ assert (B : S (bound a (Nat.div2 (b - a))) <= bound a b)
                by (apply bound_step; [exact Ha|exact Hb|right; left; exact Z]).
              lia.
           ++ pose proof (log2_half b _ Z (ltac:(lia))) as Lb.
              assert (B : S (bound a (Nat.div2 (b - a))) <= bound a b)
                by (apply bound_step; [exact Ha|exact Hb|right; right; lia]).
              lia.
Qed.

Theorem bgcd_correct : forall a b, bgcd a b = Nat.gcd a b.
Proof.
  intros a b. unfold bgcd. apply bgcd_aux_correct. lia.
Qed.

Theorem bgcd_steps_bound : forall a b, bgcd_steps a b <= bound a b.
Proof.
  intros a b. unfold bgcd_steps. apply bgcd_aux_steps. lia.
Qed.

Lemma bgcd_steps_log : forall a b, a <> 0 -> b <> 0 ->
  bgcd_steps a b <= Nat.log2 a + Nat.log2 b + 2.
Proof.
  intros a b Ha Hb. pose proof (bgcd_steps_bound a b) as H.
  rewrite (bound_nz a b Ha Hb) in H. exact H.
Qed.

Lemma bgcd_steps_linear : forall a b, bgcd_steps a b <= 2 * Nat.log2 (a + b) + 2.
Proof.
  intros a b. pose proof (bgcd_steps_bound a b) as H.
  destruct (Nat.eq_dec a 0) as [->|Ha]; [unfold bound in H; simpl in H; lia|].
  destruct (Nat.eq_dec b 0) as [->|Hb]; [rewrite bound_zero_r in H; lia|].
  rewrite (bound_nz a b Ha Hb) in H.
  pose proof (Nat.log2_le_mono a (a + b) ltac:(lia)).
  pose proof (Nat.log2_le_mono b (a + b) ltac:(lia)).
  lia.
Qed.

Example bgcd_ex : bgcd 48 18 = 6.
Proof. reflexivity. Qed.

Lemma tb_even : forall a, Nat.testbit a 0 = negb (Nat.even a).
Proof.
  intros a. exact (Nat.bit0_odd a).
Qed.

Lemma half_div2 : forall a, Nat.shiftr a 1 = Nat.div2 a.
Proof.
  intros a.
  first [ reflexivity
        | (rewrite Nat.shiftr_div_pow2, Nat.pow_1_r, Nat.div2_div; try reflexivity) ].
Qed.

Lemma dbl_mul : forall a, Nat.shiftl a 1 = 2 * a.
Proof.
  intros a.
  first [ reflexivity
        | (rewrite Nat.shiftl_mul_pow2, Nat.pow_1_r; lia) ].
Qed.

Theorem bgcd_aux'_eq : forall fuel a b,
  bgcd_aux' fuel a b = bgcd_aux fuel a b.
Proof.
  induction fuel as [|f IH]; intros a b; [reflexivity|].
  rewrite bgcd_aux'_S, bgcd_aux_S.
  destruct (a =? 0); [reflexivity|].
  destruct (b =? 0); [reflexivity|].
  cbv zeta.
  rewrite !tb_even, !half_div2, !dbl_mul.
  destruct (Nat.even a) eqn:Ea; destruct (Nat.even b) eqn:Eb;
    cbn [negb]; cbv beta iota zeta;
    rewrite ?IH; try reflexivity.
Qed.

Theorem bgcd'_eq : forall a b, bgcd' a b = bgcd a b.
Proof.
  intros a b. unfold bgcd', bgcd. rewrite bgcd_aux'_eq. reflexivity.
Qed.

Theorem bgcd_steps'_eq : forall a b, bgcd_steps' a b = bgcd_steps a b.
Proof.
  intros a b. unfold bgcd_steps', bgcd_steps. rewrite bgcd_aux'_eq. reflexivity.
Qed.

Theorem bgcd'_correct : forall a b, bgcd' a b = Nat.gcd a b.
Proof.
  intros a b. rewrite bgcd'_eq. apply bgcd_correct.
Qed.

Theorem bgcd_steps'_bound : forall a b, bgcd_steps' a b <= bound a b.
Proof.
  intros a b. rewrite bgcd_steps'_eq. apply bgcd_steps_bound.
Qed.

Lemma bgcd_steps'_log : forall a b, a <> 0 -> b <> 0 ->
  bgcd_steps' a b <= Nat.log2 a + Nat.log2 b + 2.
Proof.
  intros a b Ha Hb. rewrite bgcd_steps'_eq. apply bgcd_steps_log; assumption.
Qed.

Lemma bgcd_steps'_linear : forall a b,
  bgcd_steps' a b <= 2 * Nat.log2 (a + b) + 2.
Proof.
  intros a b. rewrite bgcd_steps'_eq. apply bgcd_steps_linear.
Qed.


Print Assumptions bgcd_aux_fuel_extra.
Print Assumptions bgcd_correct.
Print Assumptions bgcd_steps_log.
Print Assumptions bgcd'_correct.
Print Assumptions bgcd_steps'_log.
