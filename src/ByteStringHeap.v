Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Memory
  ByteString.Heap
  ByteString.HeapCanon
  ByteString.ByteString
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module ByteStringHeap (M : WSfun N_as_DT).

Module Import HeapCanonical := HeapCanonical M.

Import Heap.
Import HeapState.
Import FMapExt.

Open Scope N_scope.

Record PS := makePS {
  psBuffer : Ptr Word;
  psBufLen : Size;
  psOffset : Size;
  psLength : Size
}.

Definition buffer_to_list (h : Rep HeapSpec * PS) : list Word :=
  let r   := snd h in
  let len := psLength r in
  let off := psBuffer r + psOffset r in
  N.peano_rec _ []
    (fun k ws => match M.find (off + len - N.succ k) (bytes (fst h)) with
                 | Some w => w
                 | None   => Zero
                 end :: ws) len.

Example buffer_to_list_ex1 :
  buffer_to_list
    ({| resvs := M.add 0 2 (M.empty _)
      ; bytes := M.add 0 (Ascii.ascii_of_nat 1)
                       (M.add 1 (Ascii.ascii_of_nat 2)
                              (M.add 2 (Ascii.ascii_of_nat 3)
                                     (M.empty _))) |},
     {| psBuffer := 0
      ; psBufLen := 3
      ; psOffset := 0
      ; psLength := 3 |})
    = [ Ascii.ascii_of_nat 1
      ; Ascii.ascii_of_nat 2
      ; Ascii.ascii_of_nat 3 ].
Proof.
  unfold buffer_to_list; simpl.

  rewrite F.add_eq_o; auto.

  rewrite F.add_neq_o; [|nomega].
  rewrite F.add_eq_o; auto.

  rewrite F.add_neq_o; [|nomega].
  rewrite F.add_neq_o; [|nomega].
  rewrite F.add_eq_o; auto.
Qed.

(*
Program Definition buffer_of_list (h : Rep HeapSpec) (xs : list Word) :
  Comp (Rep HeapSpec * PS) :=
  let len := N.of_nat (length xs) in
  If 0 <? len
  Then
    a <- find_free_block len (resvs h);
    ret ({| resvs := M.add a len (resvs h)
          ; bytes :=
              fst (fold_left (fun (z : M.t Word * Ptr Word) x =>
                                let (h, a) := z in
                                (M.add a x h, N.succ a))
                             xs (bytes h, a)) |},
         {| psBuffer := a
          ; psBufLen := len
          ; psOffset := 0
          ; psLength := len |})
  Else
    ret (h, {| psBuffer := 0
             ; psBufLen := 0
             ; psOffset := 0
             ; psLength := 0 |}).

Lemma buffer_to_of_list : forall h h' xs r,
  buffer_of_list h xs ↝ (h', r) -> buffer_to_list h' r = xs.
Proof.
  intros.
  generalize dependent r.
  induction xs;
  unfold buffer_of_list in *;
  simpl in *; intros;
  destruct_computations; tsubst; simpl in *.
    reflexivity.
Admitted.
*)

Definition ByteString_list_AbsR
           (or : Rep ByteStringSpec) (nr : Rep HeapSpec * PS) :=
  or = buffer_to_list nr /\
  IF psBufLen (snd nr) = 0
  then psOffset (snd nr) = 0 /\ psLength (snd nr) = 0
  else M.MapsTo (psBuffer (snd nr)) (psBufLen (snd nr)) (resvs (fst nr))
         /\ psOffset (snd nr) + psLength (snd nr) <= psBufLen (snd nr).

Ltac destruct_AbsR H :=
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
  let H3 := fresh "H3" in
  let H4 := fresh "H4" in
  destruct H as [H1 [[H2 [H3 H4]]|[H2 [H3 H4]]]];
  [ rewrite ?H2, ?H3, ?H4 in * | ]; subst.

Ltac construct_AbsR := split; try split; simpl; try nomega.

(**************************************************************************)

Definition simply_widen_region (r : PS) (n : N) : PS :=
  {| psBuffer := psBuffer r
   ; psBufLen := psBufLen r
   ; psOffset := psOffset r - n
   ; psLength := psLength r + n |}.

Definition make_room_by_shifting_up
        (h : Rep HeapSpec) (r : PS) (n : N | 0 < n) :
  (* We could maybe be smarter by shifting the block so it sits mid-way within
     the buffer. *)
  Comp (Rep HeapSpec * PS) :=
  res <- memcpy h (psBuffer r) (psBuffer r + ` n) (psLength r);
  ret (res,
       {| psBuffer := psBuffer r
        ; psBufLen := psBufLen r
        ; psOffset := 0
        ; psLength := psLength r + ` n |}).

Program Definition make_room_by_growing_buffer
        (h : Rep HeapSpec) (r : PS) (n : N | 0 < n) :
  Comp (Rep HeapSpec * PS) :=
  (* We can make a trade-off here by allocating extra bytes in anticipation of
     future calls to [buffer_cons]. *)
  `(h, a) <- alloc h (psLength r + n);
  h <- memcpy h (psBuffer r) (a + n) (psLength r);
  h <- free h (psBuffer r);
  ret (h, {| psBuffer := a
           ; psBufLen := psLength r + n
           ; psOffset := 0
           ; psLength := psLength r + n |}).
Obligation 1. nomega_. Defined.

Program Definition allocate_buffer (h : Rep HeapSpec) (len : N | 0 < len) :
  Comp (Rep HeapSpec * PS) :=
  `(h, a) <- alloc h len;
  ret (h, {| psBuffer := a
           ; psBufLen := len
           ; psOffset := 0
           ; psLength := len |}).

Definition poke_at_offset (h : Rep HeapSpec) (r : PS) (d : Word) :
  Comp (Rep HeapSpec * PS) :=
  res <- poke h (psBuffer r + psOffset r) d;
  ret (res,
       {| psBuffer := psBuffer r
        ; psBufLen := psBufLen r
        ; psOffset := psOffset r
        ; psLength := psLength r |}).

(* This defines how much a buffer is grown by when more space is needed to
   [cons] on a new element. *)
Definition alloc_quantum := 1.
Arguments alloc_quantum /.

Program Definition buffer_cons (h : Rep HeapSpec) (r : PS) (d : Word) :
  Comp (Rep HeapSpec * PS) :=
  `(h, ps) <-
    If 0 <? psOffset r
    Then ret (h, simply_widen_region r 1)
    Else
    If psLength r + alloc_quantum <=? psBufLen r
    Then make_room_by_shifting_up h r alloc_quantum
    Else
    If 0 <? psBufLen r
    Then make_room_by_growing_buffer h r alloc_quantum
    Else allocate_buffer h alloc_quantum;
  poke_at_offset h ps d.
Obligation 1. nomega_. Defined.
Obligation 2. nomega_. Defined.
Obligation 3. nomega_. Defined.

Local Ltac if_computes_to_inv :=
  match goal with
    [ H : (If ?B Then _ Else _) ↝ _ |- _ ] =>
    let Heqe := fresh "Heqe" in
    destruct B eqn:Heqe;
    simpl in H;
    computes_to_inv
  end.

Corollary If_Then_Else_MapsTo : forall b k k' elt (e : elt) r,
  (If b
   Then M.MapsTo k  e r
   Else M.MapsTo k' e r) = M.MapsTo (If b Then k Else k') e r.
Proof. destruct b; trivial. Qed.

Lemma Npeano_rec_eq : forall (P : N -> Set) (z : P 0) f g n,
  (forall k x y, k < n -> x = y -> f k x = g k y)
    -> N.peano_rec P z f n = N.peano_rec P z g n.
Proof.
  intros.
  destruct n using N.peano_ind.
    reflexivity.
  rewrite !N.peano_rec_succ.
  apply H.
    nomega.
  apply IHn.
  intros; subst.
  apply H.
    nomega.
  reflexivity.
Qed.

Lemma buffer_cons_eq_shift_1 : forall x r_n buflen,
  0 < psOffset (snd r_n)
    -> psBufLen (snd r_n) <= buflen
    -> x :: buffer_to_list r_n
         = buffer_to_list
             ({| resvs := resvs (fst r_n)
               ; bytes :=
                   M.add (psBuffer (snd r_n) + (psOffset (snd r_n) - 1)) x
                         (bytes (fst r_n)) |},
              {| psBuffer := psBuffer (snd r_n)
               ; psBufLen := buflen
               ; psOffset := psOffset (snd r_n) - 1
               ; psLength := psLength (snd r_n) + 1 |}).
Proof.
  intros.
  unfold buffer_to_list; simpl.
  destruct r_n, p; simpl in *.
  generalize dependent buflen.
  destruct psLength0 using N.peano_ind; simpl; intros.
    rewrite F.add_eq_o; nomega.
  clear IHpsLength0.
  rewrite N.add_1_r, !N.peano_rec_succ, !N.add_sub, F.add_eq_o; trivial.
  rewrite F.add_neq_o; [|nomega].
  replace (psBuffer0 + (psOffset0 - 1)
             + N.succ (N.succ psLength0) - N.succ psLength0)
     with (psBuffer0 + psOffset0) by nomega.
  do 2 f_equal.
  apply Npeano_rec_eq with (P:= fun _ : N => list Word).
  intros; subst.
  f_equal.
  replace (psBuffer0 + (psOffset0 - 1) + N.succ (N.succ psLength0) - N.succ k)
     with (psBuffer0 + psOffset0 + N.succ psLength0 - N.succ k) by nomega.
  cut (forall k, k < psLength0 ->
          M.find (psBuffer0 + psOffset0 + N.succ psLength0 - N.succ k)
                 (bytes r)
            = M.find (psBuffer0 + psOffset0 + N.succ psLength0 - N.succ k)
                     (M.add (psBuffer0 + (psOffset0 - 1)) x (bytes r))).
    intro H3; rewrite H3; trivial.
  intros.
  rewrite F.add_neq_o; trivial.
  nomega.
Qed.

Lemma buffer_cons_eq_grow_1 : forall x r_n buflen,
  0 = psOffset (snd r_n)
    -> psBufLen (snd r_n) <= buflen
    -> x :: buffer_to_list r_n
         = buffer_to_list
             ({| resvs := resvs (fst r_n)
               ; bytes :=
                   M.add (psBuffer (snd r_n)) x
                         (copy_bytes (psBuffer (snd r_n))
                                     (psBuffer (snd r_n) + 1)
                                     (psLength (snd r_n))
                                     (bytes (fst r_n))
                                     (bytes (fst r_n))) |},
              {| psBuffer := psBuffer (snd r_n)
               ; psBufLen := buflen
               ; psOffset := 0
               ; psLength := psLength (snd r_n) + 1 |}).
Proof.
  intros.
  unfold buffer_to_list; simpl.
  destruct r_n, p; simpl in *.
  destruct psLength0 using N.peano_ind; simpl; intros.
    rewrite F.add_eq_o; nomega.
  subst; clear IHpsLength0.
  rewrite N.add_1_r, !N.peano_rec_succ, !N.add_sub,
          N.add_0_r, F.add_eq_o; [|nomega].
  rewrite F.add_neq_o; [|nomega].
  f_equal.
  rewrite <- !N.add_1_r.
  rewrite (N.add_comm (psLength0 + 1) 1).
  rewrite N.add_assoc, N.add_assoc, N.add_sub.
  rewrite copy_bytes_find_at; [|nomega].
  f_equal.
  apply Npeano_rec_eq with (P:= fun _ : N => list Word).
  intros; subst.
  f_equal.
  rewrite F.add_neq_o; [|nomega].
  rewrite copy_bytes_find.
  destruct (within_bool (psBuffer0 + 1) (psLength0 + 1)
                        (psBuffer0 + 1 + (psLength0 + 1) - N.succ k))
    eqn:Heqe; simpl.
    replace (psBuffer0 + 1 + (psLength0 + 1) - N.succ k - (psBuffer0 + 1) + psBuffer0)
       with (psBuffer0 + psLength0 + 1 - N.succ k) by nomega.
    reflexivity.
  nomega.
Qed.

Lemma buffer_cons_eq_alloc_new : forall x y r_n,
  0 = psOffset (snd r_n)
    -> y <> psBuffer (snd r_n)
    -> x :: buffer_to_list r_n
         = buffer_to_list
             ({| resvs :=
                   M.remove (psBuffer (snd r_n))
                            (M.add y (psLength (snd r_n) + 1)
                                   (resvs (fst r_n)))
               ; bytes :=
                   M.add y x (copy_bytes (psBuffer (snd r_n)) (y + 1)
                                         (psLength (snd r_n))
                                         (bytes (fst r_n))
                                         (bytes (fst r_n))) |},
              {| psBuffer := y
               ; psBufLen := psLength (snd r_n) + 1
               ; psOffset := 0
               ; psLength := psLength (snd r_n) + 1 |}).
Proof.
  intros.
  unfold buffer_to_list; simpl.
  destruct r_n, p; simpl in *.
  destruct psLength0 using N.peano_ind; simpl; intros.
    rewrite F.add_eq_o; nomega.
  subst; clear IHpsLength0.
  rewrite N.add_1_r, !N.peano_rec_succ, !N.add_sub,
          N.add_0_r, F.add_eq_o; [|nomega].
  rewrite F.add_neq_o; [|nomega].
  f_equal.
  rewrite N.add_0_r, <- !N.add_1_r.
  rewrite (N.add_comm (psLength0 + 1) 1).
  rewrite !N.add_assoc, <- (N.add_assoc (y + 1) psLength0 1).
  rewrite N.add_sub, copy_bytes_find_at; [|nomega].
  f_equal.
  apply Npeano_rec_eq with (P:= fun _ : N => list Word).
  intros; subst.
  f_equal.
  rewrite F.add_neq_o; [|nomega].
  rewrite copy_bytes_find.
  destruct (within_bool (y + 1) (psLength0 + 1)
                        (y + 1 + (psLength0 + 1) - N.succ k)) eqn:Heqe; simpl.
    replace (y + 1 + (psLength0 + 1) - N.succ k - (y + 1) + psBuffer0)
       with (psBuffer0 + psLength0 + 1 - N.succ k) by nomega.
    reflexivity.
  nomega.
Qed.

Lemma buffer_cons_sound : forall r_o r_n,
  ByteString_list_AbsR r_o r_n
    -> forall x r_n', buffer_cons (fst r_n) (snd r_n) x ↝ r_n'
    -> ByteString_list_AbsR (x :: r_o) r_n'.
Proof.
  unfold buffer_cons, Bind2; intros ? ? AbsR ???.
  destruct_computations.
  if_computes_to_inv; subst; simpl.
    destruct_AbsR AbsR; construct_AbsR.
      rewrite <- buffer_cons_eq_shift_1; nomega.
    right; intuition; nomega.
  if_computes_to_inv; subst.
    destruct_computations; simpl.
    destruct_AbsR AbsR; construct_AbsR.
      rewrite N.add_0_r, <- buffer_cons_eq_grow_1; nomega.
    right; intuition; nomega.
  if_computes_to_inv; subst.
    destruct_computations; simpl in *.
    destruct_AbsR AbsR; construct_AbsR.
      rewrite N.add_0_r, <- buffer_cons_eq_alloc_new; trivial.
        nomega.
      apply_for_all; nomega.
    right.
    split.
      nomega.
    split; [|nomega].
    apply F.remove_neq_mapsto_iff; trivial.
      apply_for_all; nomega.
    simplify_maps.
  destruct_computations; simpl in *.
  destruct_AbsR AbsR; construct_AbsR.
    unfold buffer_to_list; simpl.
    rewrite N.add_0_r, N.add_sub, F.add_eq_o; trivial.
    f_equal.
    replace (psLength (snd r_n)) with 0.
      reflexivity.
    nomega.
  right.
  split.
    nomega.
  split.
    simplify_maps.
  nomega.
Qed.

(**************************************************************************)

Definition buffer_uncons (h : Rep HeapSpec) (r : PS) :
  Comp ((Rep HeapSpec * PS) * option Word) :=
  If 0 <? psLength r
  Then
    `(h, w) <- peek h (psBuffer r + psOffset r);
    ret ((h, {| psBuffer := psBuffer r
              ; psBufLen := psBufLen r
              ; psOffset := if psLength r =? 1
                            then 0
                            else psOffset r + 1
              ; psLength := psLength r - 1 |}),
         Some w)
  Else
    ret ((h, r), None).

Lemma buffer_uncons_sound : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons (fst r_n) (snd r_n) ↝ a
    -> ByteString_list_AbsR (match r_o with
                             | [] => r_o
                             | _ :: xs => xs
                             end) (fst a).
Proof.
  unfold buffer_uncons; intros.
  if_computes_to_inv; subst; simpl.
    destruct_computations; simpl.
    destruct_AbsR H; construct_AbsR.
      unfold buffer_to_list.
      destruct r_n, p; simpl.
      destruct psLength0 using N.peano_ind; simpl; intros.
        reflexivity.
      rewrite !N.peano_rec_succ, <- N.pred_sub, N.pred_succ.
      apply Npeano_rec_eq with (P:= fun _ : N => list Word).
      intros; subst.
      f_equal.
      assert (N.succ psLength0 =? 1 = false) by nomega.
      rewrite H1.
      replace (psBuffer0 + (psOffset0 + 1) + psLength0 - N.succ k)
         with (psBuffer0 + psOffset0 + N.succ psLength0 - N.succ k) by nomega.
      reflexivity.
    right; intuition;
    destruct (psLength (@snd HeapState PS r_n) =? 1); nomega.
  assert (psLength (@snd HeapState PS r_n) = 0) by nomega.
  rewrite <- surjective_pairing.
  destruct_AbsR H; construct_AbsR.
  - unfold buffer_to_list; simpl.
    rewrite H0; trivial.
  - left; intuition.
  - unfold buffer_to_list; simpl.
    rewrite H0; trivial.
  - right; intuition.
Qed.

Lemma buffer_to_list_cons : forall r_n,
  0 < psLength (snd r_n) -> exists x xs, buffer_to_list r_n = x :: xs.
Proof.
  intros.
  unfold buffer_to_list.
  destruct r_n, p ; simpl in *.
  destruct psLength0 using N.peano_ind; simpl in *; intros.
    discriminate.
  clear IHpsLength0.
  rewrite N.peano_rec_succ, N.add_sub.
  remember (N.peano_rec _ _ _ _) as xs.
  destruct (M.find (psBuffer0 + psOffset0) (bytes r)).
    exists w.
    exists xs.
    reflexivity.
  exists Zero.
  exists xs.
  reflexivity.
Qed.

Lemma buffer_to_list_nil : forall r_n,
  0 = psLength (snd r_n) -> buffer_to_list r_n = [].
Proof.
  intros.
  unfold buffer_to_list.
  destruct r_n, p ; simpl in *.
  destruct psLength0 using N.peano_ind; simpl in *; intros.
    reflexivity.
  clear IHpsLength0.
  rewrite N.peano_rec_succ, N.add_sub.
  remember (N.peano_rec _ _ _ _) as xs.
  destruct (M.find (psBuffer0 + psOffset0) (bytes r)); nomega.
Qed.

Lemma buffer_uncons_impl : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons (fst r_n) (snd r_n) ↝ a
    -> snd a = match r_o with
               | [] => None
               | x :: _ => Some x
               end.
Proof.
  unfold buffer_uncons; intros.
  destruct H; subst.
  clear H1.
  if_computes_to_inv; subst; simpl.
    destruct_computations; simpl.
    assert (0 < psLength (snd r_n)) by nomega.
    apply buffer_to_list_cons in H0.
    destruct H0, H0.
    rewrite H0.
    f_equal.
    unfold buffer_to_list in H0.
    destruct r_n, p; simpl in *.
    destruct psLength0 using N.peano_ind; simpl in *; intros.
      discriminate.
    clear IHpsLength0.
    rewrite N.peano_rec_succ, N.add_sub in H0.
    inv H0.
    destruct H.
      apply F.find_mapsto_iff in H.
      rewrite H.
      reflexivity.
    destruct H; subst.
    assert (M.find (psBuffer0 + psOffset0) (bytes r) = None).
      apply F.not_find_in_iff.
      assumption.
    rewrite H0.
    reflexivity.
  unfold buffer_to_list; simpl.
  destruct r_n, p; simpl.
  destruct psLength0 using N.peano_ind; simpl in *; intros; trivial.
  rewrite N.peano_rec_succ, N.add_sub.
  nomega.
Qed.

(**************************************************************************)

(* jww (2016-12-21): For now, just allocate and copy from both. *)

Program Definition buffer_append
        (h1 : Rep HeapSpec) (r1 : PS)
        (h2 : Rep HeapSpec) (r2 : PS) :
  Comp (Rep HeapSpec * PS) :=
  IfDep 0 <? psLength r1
  Then fun _ =>
    IfDep 0 <? psLength r2
    Then fun _ =>
      `(h1, a) <- alloc h1 (psLength r1 + psLength r2);
      h1 <- memcpy h1 (psBuffer r1 + psOffset r1) a (psLength r1);
      let h1 := {| resvs := resvs h1
                 ; bytes :=
                     copy_bytes (psBuffer r2 + psOffset r2)
                                (a + psLength r1) (psLength r2)
                                (bytes h2) (bytes h1) |} in
      ret (h1, {| psBuffer := a
                ; psBufLen := psLength r1 + psLength r2
                ; psOffset := 0
                ; psLength := psLength r1 + psLength r2 |})
    Else fun _ => ret (h1, r1)
  Else fun _ => ret (h2, r2).
Obligation 1. nomega. Defined.

Lemma refineEquiv_buffer_append
      (h1 : Rep HeapSpec) (r1 : PS)
      (h2 : Rep HeapSpec) (r2 : PS) :
  refineEquiv
    (buffer_append h1 r1 h2 r2)
    (If 0 <? psLength r1
     Then If 0 <? psLength r2
       Then
         x0 <- find_free_block (psLength r1 + psLength r2) (resvs h1);
         h0 <- memcpy {| resvs := M.add x0 (psLength r1 + psLength r2) (resvs h1)
                       ; bytes := bytes h1 |}
                      (psBuffer r1 + psOffset r1) x0 (psLength r1);
         ret ({| resvs := resvs h0
               ; bytes :=
                   copy_bytes (psBuffer r2 + psOffset r2)
                              (x0 + psLength r1) (psLength r2)
                              (bytes h2) (bytes h0) |},
              {| psBuffer := x0
               ; psBufLen := psLength r1 + psLength r2
               ; psOffset := 0
               ; psLength := psLength r1 + psLength r2 |})
       Else ret (h1, r1)
     Else ret (h2, r2)).
Proof.
  unfold buffer_append.
  etransitivity.
    apply refineEquiv_IfDep_Then_Else.
      intros.
      apply refineEquiv_IfDep_Then_Else.
        intros.
        unfold allocate_buffer, Bind2,
               make_room_by_growing_buffer, Bind2.
        rewrite refineEquiv_unfold_alloc; simpl.
        Opaque memcpy.
        Opaque free.
        split.
          simplify with monad laws; simpl.
          finish honing.
        simpl.
        autorewrite with monad laws; simpl.
        Transparent memcpy.
        Transparent free.
        reflexivity.
      intros.
      finish honing.
    intros.
    finish honing.
  rewrite refineEquiv_strip_IfDep_Then_Else.
  apply refineEquiv_If_Then_Else.
    rewrite refineEquiv_strip_IfDep_Then_Else.
    reflexivity.
  reflexivity.
Qed.

Lemma buffer_to_list_app : forall r_n1 r_n2 v,
  buffer_to_list r_n1 ++ buffer_to_list r_n2 =
  buffer_to_list
    ({|
     resvs := M.add v (psLength (snd r_n1) + psLength (snd r_n2))
                    (resvs (fst r_n1));
     bytes :=
       copy_bytes (psBuffer (snd r_n2) + psOffset (snd r_n2))
                  (v + psLength (snd r_n1))
                  (psLength (snd r_n2))
                  (bytes (fst r_n2))
                  (copy_bytes (psBuffer (snd r_n1) + psOffset (snd r_n1)) v
                              (psLength (snd r_n1))
                              (bytes (fst r_n1)) (bytes (fst r_n1))) |},
    {|
    psBuffer := v;
    psBufLen := psLength (snd r_n1) + psLength (snd r_n2);
    psOffset := 0;
    psLength := psLength (snd r_n1) + psLength (snd r_n2) |}).
Proof.
  intros.
  destruct r_n1, p; simpl.
  destruct r_n2, p; simpl.
  destruct psLength0 using N.peano_ind; simpl in *; intros; trivial;
  try clear IHpsLength0;
  destruct psLength1 using N.peano_ind; simpl in *; intros; trivial;
  try clear IHpsLength1.
  - rewrite N.add_0_r.
    unfold buffer_to_list; simpl.
    apply Npeano_rec_eq with (P:= fun _ : N => list Word).
    intros; subst; f_equal.
    rewrite N.add_0_r, !copy_bytes_find.
    assert (within_bool v 0 (v + N.succ psLength1 - N.succ k) = false)
      by nomega.
    rewrite H0; clear H0; simpl.
    assert (within_bool v (N.succ psLength1)
                        (v + N.succ psLength1 - N.succ k) = true)
      by nomega.
    rewrite H0; clear H0; simpl.
    replace (v + N.succ psLength1 - N.succ k - v + (psBuffer1 + psOffset1))
       with (psBuffer1 + psOffset1 + N.succ psLength1 - N.succ k)
         by nomega.
    reflexivity.
  - remember (r0, _) as b.
    rewrite (buffer_to_list_nil b), app_nil_r, !N.add_0_r; [|nomega].
    clear Heqb b.
    unfold buffer_to_list; simpl.
    destruct psLength0 using N.peano_ind; simpl; intros.
      rewrite !N.add_sub, N.add_0_r, !copy_bytes_find.
      assert (within_bool (v + 1) 0 v = false) by nomega.
      rewrite H; clear H; simpl.
      assert (within_bool v 1 v = true) by nomega.
      rewrite H; clear H; simpl.
      replace (v - v + (psBuffer0 + psOffset0))
         with (psBuffer0 + psOffset0) by nomega.
      reflexivity.
    subst; clear IHpsLength0.
    apply Npeano_rec_eq with (P:= fun _ : N => list Word).
    intros; subst; f_equal.
    rewrite N.add_0_r, !copy_bytes_find.
    assert (within_bool (v + N.succ (N.succ psLength0)) 0
                        (v + N.succ (N.succ psLength0) - N.succ k) = false)
      by nomega.
    rewrite H0; clear H0; simpl.
    assert (within_bool v (N.succ (N.succ psLength0))
                        (v + N.succ (N.succ psLength0) - N.succ k) = true)
      by nomega.
    rewrite H0; clear H0; simpl.
    replace (v + N.succ (N.succ psLength0) - N.succ k - v + (psBuffer0 + psOffset0))
       with (psBuffer0 + psOffset0 + N.succ (N.succ psLength0) - N.succ k)
         by nomega.
    reflexivity.
  - unfold buffer_to_list; simpl.
    rewrite !N.peano_rec_succ, N.add_sub.
    rewrite N.add_succ_l.
    rewrite <- (N.add_succ_comm psLength0 psLength1).
    rewrite !N.peano_rec_succ, N.add_sub.
    rewrite N.add_succ_l.
    rewrite N.peano_rec_succ, N.add_sub.
    rewrite !N.add_0_r, !copy_bytes_find.
    assert (within_bool (v + N.succ psLength0) (N.succ psLength1) v = false)
      by nomega.
    rewrite H; clear H; simpl.
    assert (within_bool v (N.succ psLength0) v = true) by nomega.
    rewrite H; clear H; simpl.
    replace (v - v + (psBuffer0 + psOffset0)) with (psBuffer0 + psOffset0)
      by nomega.
    f_equal.
    replace (v + N.succ (N.succ (psLength0 + psLength1))
               - N.succ (psLength0 + psLength1))
       with (v + 1 + N.succ (psLength0 + psLength1)
                   - N.succ (psLength0 + psLength1))
         by nomega.
    rewrite !N.add_sub.
    destruct (within_bool (v + N.succ psLength0)
                          (N.succ psLength1) (v + 1)) eqn:Heqe; simpl.
      assert (0 = psLength0) by nomega.
      subst; simpl.
      replace (v + 1 - (v + 1) + (psBuffer1 + psOffset1))
         with (psBuffer1 + psOffset1) by nomega.
      f_equal.
      apply Npeano_rec_eq with (P:= fun _ : N => list Word).
      intros; subst; f_equal.
      rewrite !copy_bytes_find.
      assert (within_bool (v + 1) (N.succ psLength1)
                          (v + N.succ (N.succ psLength1) - N.succ k) = true)
        by nomega.
      rewrite H0; clear H0; simpl.
      replace (v + N.succ (N.succ psLength1) - N.succ k
                 - (v + 1) + (psBuffer1 + psOffset1))
         with (psBuffer1 + psOffset1 + N.succ psLength1 - N.succ k)
           by nomega.
      reflexivity.
    assert (within_bool v (N.succ psLength0) (v + 1) = true) by nomega.
    rewrite H; clear H; simpl.
    replace (v + 1 - v + (psBuffer0 + psOffset0))
       with (N.succ (psBuffer0 + psOffset0)) by nomega.
    assert (psLength0 <> 0) by nomega.
    apply N.neq_0_r in H.
    destruct H; subst.
    rewrite N.peano_rec_succ.
    replace (psBuffer0 + psOffset0 + N.succ (N.succ x) - N.succ x)
       with (N.succ (psBuffer0 + psOffset0)) by nomega.
    rewrite <- app_comm_cons.
    f_equal.
    rewrite N.add_succ_l, N.peano_rec_succ, !copy_bytes_find.
Admitted.

Lemma buffer_append_sound : forall r_o1 r_o2 r_n1 r_n2,
  ByteString_list_AbsR r_o1 r_n1
    -> ByteString_list_AbsR r_o2 r_n2
    -> forall r_n',
         buffer_append (fst r_n1) (snd r_n1) (fst r_n2) (snd r_n2) ↝ r_n'
    -> ByteString_list_AbsR (r_o1 ++ r_o2) r_n'.
Proof.
  intros.
  apply refine_computes_to in H1.
  rewrite refineEquiv_buffer_append in H1.
  apply computes_to_refine in H1.
  if_computes_to_inv.
    if_computes_to_inv.
      subst.
      destruct_computations; simpl in *.
      destruct_AbsR H.
        destruct_AbsR H0; construct_AbsR.
      construct_AbsR.
        destruct_AbsR H0;
        apply buffer_to_list_app.
      right.
      split.
        nomega.
      split.
        simplify_maps.
      nomega.
    rewrite <- surjective_pairing in H1.
    subst.
    assert (r_o2 = []).
      destruct H0; subst.
      destruct r_n2, p; simpl in *.
      unfold buffer_to_list; simpl.
      assert (psLength0 = 0) by nomega.
      rewrite H0; simpl.
      reflexivity.
    rewrite H1, app_nil_r.
    assumption.
  assert (r_o1 = []).
    destruct H; subst.
    destruct r_n1, p; simpl in *.
    unfold buffer_to_list; simpl.
    assert (psLength0 = 0) by nomega.
    rewrite H; simpl.
    reflexivity.
  rewrite <- surjective_pairing in H1.
  rewrite H2, app_nil_l, <- H1.
  assumption.
Qed.

(**************************************************************************)

Theorem ByteStringHeap (heap : Rep HeapSpec) :
  { adt : _ & refineADT ByteStringSpec adt }.
Proof.
  eexists.

  hone representation using ByteString_list_AbsR.

  {
    simplify with monad laws.
    refine pick val (heap,
                     {| psBuffer := 0
                      ; psBufLen := 0
                      ; psOffset := 0
                      ; psLength := 0 |}).
      finish honing.
    simpl.
    firstorder.
  }

  {
    simplify with monad laws.
    setoid_rewrite (@refine_skip2_pick _ (buffer_cons (fst r_n) (snd r_n) d)).
    etransitivity.
      refine_under.
        finish honing.
      refine pick val a.
        finish honing.
      eapply buffer_cons_sound; eauto.
    simplify with monad laws; simpl.
    finish honing.
  }

  {
    simplify with monad laws.
    setoid_rewrite (refine_skip2_bind (dummy:=buffer_uncons (fst r_n) (snd r_n))).
    etransitivity.
    - refine_under.
      + finish honing.
      + rewrite fst_match_list, snd_match_list;
          erewrite <- buffer_uncons_impl by eauto.
         refine pick val (fst a).
         simplify with monad laws.
         finish honing.
         eapply buffer_uncons_sound; eauto.
    - simpl; unfold buffer_uncons.
      rewrite refineEquiv_If_Then_Else_Bind.
      refine_under;
      simplify with monad laws; simpl;
      finish honing.
  }

  {
    simplify with monad laws.
    rewrite (refine_skip2_pick (dummy:=buffer_append (fst r_n) (snd r_n)
                                                     (fst r_n0) (snd r_n0))).
    refine_under.
      finish honing.
    refine pick val a.
      finish honing.
    eapply buffer_append_sound; eauto.
  }

  apply reflexivityT.
Defined.

End ByteStringHeap.
