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

Module ByteStringHeap (M : WSfun Ptr_as_DT).

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

Definition buffer_to_list (h : Rep HeapSpec) (ps : PS) : list Word :=
  let len := psLength ps in
  let off : Ptr Word := plusPtr (psBuffer ps) (psOffset ps) in
  N.peano_rec _ []
    (fun k ws =>
       match M.find (plusPtr off (len - N.succ k)) (bytes h) with
       | Some w => w
       | None   => Zero
       end :: ws) len.

Lemma buffer_to_list_Proper :
  Proper (HeapState_Equal ==> eq ==> eq) buffer_to_list.
Proof.
  relational.
  destruct H.
  unfold buffer_to_list.
  remember (fun _ _ => _) as f.
  remember (fun (k : N) (ws : list Word) =>
              match M.find _ (bytes y)
              with
              | Some w => w
              | None   => Zero
              end :: ws) as g.
  apply Npeano_rec_eq with (f:=f) (g:=g).
  intros; subst.
  f_equal.
  rewrite H0.
  reflexivity.
Qed.

Example buffer_to_list_ex1 :
  buffer_to_list
    {| resvs := M.add 0 2 (M.empty _)
     ; bytes := M.add 0 (Ascii.ascii_of_nat 1)
                      (M.add 1 (Ascii.ascii_of_nat 2)
                             (M.add 2 (Ascii.ascii_of_nat 3)
                                    (M.empty _))) |}
    {| psBuffer := 0
     ; psBufLen := 3
     ; psOffset := 0
     ; psLength := 3 |}
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

Definition ByteString_list_AbsR
           (or : Rep ByteStringSpec) (nr : Comp (Rep HeapSpec) * PS) :=
  let ps := snd nr in
  forall h, fst nr ↝ h
  -> or = buffer_to_list h ps
  /\ IF psBufLen ps = 0
     then psOffset ps = 0 /\ psLength ps = 0
     else M.MapsTo (psBuffer ps) (psBufLen ps) (resvs h)
            /\ plusPtr (A:=Word) (psOffset ps)
                       (psLength ps) <= psBufLen ps.

Ltac destruct_AbsR H :=
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
  let H3 := fresh "H3" in
  let H4 := fresh "H4" in
  destruct H as [H1 [[H2 [H3 H4]]|[H2 [H3 H4]]]];
  [ rewrite ?H2, ?H3, ?H4 in * | ]; subst.

Ltac construct_AbsR :=
  split; try split; try split; simpl;
  eauto; try nomega; simpl in *;
  destruct_computations.

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
  res <- memcpy h (psBuffer r) (plusPtr (psBuffer r) (` n)) (psLength r);
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
  h <- memcpy h (psBuffer r) (plusPtr a n) (psLength r);
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
  res <- poke h (plusPtr (psBuffer r) (psOffset r)) d;
  ret (res,
       {| psBuffer := psBuffer r
        ; psBufLen := psBufLen r
        ; psOffset := psOffset r
        ; psLength := psLength r |}).

(* This defines how much a buffer is grown by when more space is needed to
   [cons] on a new element. *)
Definition alloc_quantum := 1.
Arguments alloc_quantum /.

Definition bsrep := (Comp (Rep HeapSpec) * PS)%type.

Program Definition buffer_cons (r : bsrep) (d : Word) :
  Comp (Rep HeapSpec * PS) :=
  let ps := snd r in
  h <- fst r;
  `(h, ps) <-
    If 0 <? psOffset ps
    Then ret (h, simply_widen_region ps 1)
    Else
    If psLength ps + alloc_quantum <=? psBufLen ps
    Then make_room_by_shifting_up h ps alloc_quantum
    Else
    If 0 <? psBufLen ps
    Then make_room_by_growing_buffer h ps alloc_quantum
    Else allocate_buffer h alloc_quantum;
  poke_at_offset h ps d.
Obligation 1. nomega_. Defined.
Obligation 2. nomega_. Defined.
Obligation 3. nomega_. Defined.

Ltac reduce_find :=
  match goal with
  | [ |- context[M.find ?X (M.add ?Y _ _)] ] =>
    rewrite F.add_eq_o; [auto|nomega]
  | [ |- context[M.find ?X (M.add _ _ _)] ] =>
    rewrite F.add_neq_o; [auto|try nomega]
  | [ |- ?X :: _ = ?X :: _ ] => f_equal
  | [ |- N.peano_rec ?Q ?Z _ ?N = N.peano_rec ?Q ?Z _ ?N ] =>
    apply Npeano_rec_eq with (P:=Q);
    intros; subst; f_equal;
    rewrite_ptr; try reduce_find
  | [ |- context[M.find _ (copy_bytes _ _ _ _)] ] =>
    rewrite !copy_bytes_find
  | [ |- context[If ?B Then _ Else _] ] =>
    let H := fresh "H" in
    assert (H : B = true) by nomega;
    rewrite H; clear H; simpl
  | [ |- context[If ?B Then _ Else _] ] =>
    let H := fresh "H" in
    assert (H : B = false) by nomega;
    rewrite H; clear H; simpl
  | [ |- match M.find ?X _ with | _ => _ end :: _ =
         match M.find ?Y _ with | _ => _ end :: _ ] =>
    replace X with Y by nomega; f_equal
  | [ |- match M.find ?X _ with | _ => _ end =
         match M.find ?Y _ with | _ => _ end ] =>
    replace X with Y; auto; try nomega
  | [ |- match M.find ?X _ with | _ => _ end :: _ =
         match M.find ?Y _ with | _ => _ end :: _ ] =>
    replace X with Y; auto; try nomega
  end; auto.

Ltac destruct_ps ps :=
  unfold buffer_to_list; simpl;
  let psLength := fresh "psLength" in
  try destruct ps as [? ? ? psLength]; simpl in *;
  destruct psLength using N.peano_ind; simpl; intros;
  repeat (rewrite_ptr; repeat reduce_find).

Lemma buffer_cons_eq_shift_1 : forall x h ps buflen,
  0 < psOffset ps
    -> psBufLen ps <= buflen
    -> x :: buffer_to_list h ps
         = buffer_to_list
             {| resvs := resvs h
              ; bytes :=
                  M.add (plusPtr (psBuffer ps)
                                 (psOffset ps - 1)) x
                        (bytes h) |}
             {| psBuffer := psBuffer ps
              ; psBufLen := buflen
              ; psOffset := psOffset ps - 1
              ; psLength := psLength ps + 1 |}.
Proof. intros; destruct_ps ps. Qed.

Lemma buffer_cons_eq_grow_1 : forall x h ps buflen,
  0 = psOffset ps
    -> psBufLen ps <= buflen
    -> x :: buffer_to_list h ps
         = buffer_to_list
             {| resvs := resvs h
              ; bytes :=
                  M.add (psBuffer ps) x
                        (copy_bytes (psBuffer ps)
                                    (plusPtr (psBuffer ps) 1)
                                    (psLength ps)
                                    (bytes h)) |}
             {| psBuffer := psBuffer ps
              ; psBufLen := buflen
              ; psOffset := 0
              ; psLength := psLength ps + 1 |}.
Proof. intros; destruct_ps ps. Qed.

Lemma buffer_cons_eq_alloc_new : forall x y h ps,
  0 = psOffset ps
    -> y <> psBuffer ps
    -> x :: buffer_to_list h ps
         = buffer_to_list
             {| resvs :=
                  M.remove (psBuffer ps)
                           (M.add y (psLength ps + 1)
                                  (resvs h))
              ; bytes :=
                  M.add y x (copy_bytes (psBuffer ps) (plusPtr y 1)
                                        (psLength ps)
                                        (bytes h)) |}
             {| psBuffer := y
              ; psBufLen := psLength ps + 1
              ; psOffset := 0
              ; psLength := psLength ps + 1 |}.
Proof. intros; destruct_ps ps. Qed.

Lemma buffer_cons_sound : forall r_o r_n,
  ByteString_list_AbsR r_o r_n
    -> forall x r_n' ps', buffer_cons r_n x ↝ (r_n', ps')
    -> ByteString_list_AbsR (x :: r_o) (ret r_n', ps').
Proof.
  unfold buffer_cons, Bind2; intros ? ? AbsR ???.
  destruct_computations.
  intro H.
  destruct_computations; tsubst; simpl in *.
  specialize (AbsR _ H).
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
    right; intuition.
      nomega.
    apply F.remove_neq_mapsto_iff; trivial.
      apply_for_all; nomega.
    simplify_maps.
  destruct_computations; simpl in *.
  destruct_AbsR AbsR; construct_AbsR.
    destruct_ps (snd r_n); nomega.
  right; intuition.
    discriminate.
  simpl in *.
  simplify_maps.
Qed.

(**************************************************************************)

Definition buffer_uncons (r : bsrep) :
  Comp ((Rep HeapSpec * PS) * option Word) :=
  let ps := snd r in
  h <- fst r;
  If 0 <? psLength ps
  Then
    `(h, w) <- peek h (plusPtr (psBuffer ps) (psOffset ps));
    ret ((h, {| psBuffer := psBuffer ps
              ; psBufLen := psBufLen ps
              ; psOffset := if psLength ps =? 1
                            then 0
                            else psOffset ps + 1
              ; psLength := psLength ps - 1 |}),
         Some w)
  Else
    ret ((h, ps), None).

Lemma buffer_uncons_sound : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons r_n ↝ a
    -> ByteString_list_AbsR (match r_o with
                             | [] => r_o
                             | _ :: xs => xs
                             end) (ret (fst (fst a)), snd (fst a)).
Proof.
  unfold buffer_uncons; intros.
  destruct_computations.
  specialize (H _ H0).
  if_computes_to_inv; subst; simpl.
    destruct_computations; simpl.
    destruct_AbsR H; construct_AbsR.
      destruct_ps (snd r_n).
      assert (H2 : N.succ psLength0 =? 1 = false) by nomega.
      rewrite H2.
      nomega.
    right; intuition;
    destruct (psLength (@snd (Comp HeapState) PS r_n) =? 1); nomega.
  assert (psLength (@snd (Comp HeapState) PS r_n) = 0) by nomega.
  destruct_AbsR H; construct_AbsR.
  - unfold buffer_to_list; simpl.
    rewrite H1; trivial.
  - left; intuition.
  - unfold buffer_to_list; simpl.
    rewrite H1; trivial.
  - right; intuition.
Qed.

Lemma buffer_to_list_cons : forall h ps,
  0 < psLength ps -> exists x xs, buffer_to_list h ps = x :: xs.
Proof.
  intros.
  destruct_ps ps.
  clear IHpsLength0.
  remember (N.peano_rec _ _ _ _) as xs.
  destruct (M.find (plusPtr psBuffer0 psOffset0) (bytes h)).
    exists w, xs; reflexivity.
  exists Zero, xs; reflexivity.
Qed.

Lemma buffer_to_list_nil : forall h ps,
  0 = psLength ps -> buffer_to_list h ps = [].
Proof. intros; destruct_ps ps; nomega. Qed.

Lemma buffer_uncons_impl : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons r_n ↝ a
    -> snd a = match r_o with
           | [] => None
           | x :: _ => Some x
           end.
Proof.
  unfold buffer_uncons; intros.
  destruct_computations.
  specialize (H _ H0).
  if_computes_to_inv; subst; simpl.
    destruct_computations; simpl.
    destruct_AbsR H;
    destruct_ps (snd r_n); try nomega.
    clear IHpsLength0.
    f_equal.
    destruct H1.
      apply F.find_mapsto_iff in H.
      admit.
      (* rewrite H; reflexivity. *)
    destruct H; subst.
    assert (M.find (plusPtr psBuffer0 psOffset0) (bytes x) = None).
      apply F.not_find_in_iff; trivial.
      admit.
    admit.
    (* rewrite H0; trivial. *)
  destruct_AbsR H;
  destruct_ps (snd r_n).
    admit.
  admit.
Admitted.

(**************************************************************************)

(* jww (2016-12-21): For now, just allocate and copy from both. *)

Program Definition buffer_append (r1 r2 : bsrep) : Comp (Rep HeapSpec * PS) :=
  let ps1 := snd r1 in
  let ps2 := snd r2 in
  h1 <- fst r1;
  h2 <- fst r2;
  h <- { h : Rep HeapSpec | h = h1 /\ HeapState_Equal h1 h2 };
  IfDep 0 <? psLength ps1
  Then fun _ =>
    IfDep 0 <? psLength ps2
    Then fun _ =>
      `(h, a) <- alloc h (psLength ps1 + psLength ps2);
      h <- memcpy h (plusPtr (psBuffer ps1) (psOffset ps1))
                    a (psLength ps1);
      h <- memcpy h (plusPtr (psBuffer ps2) (psOffset ps2))
                    (a + psLength ps1) (psLength ps2);
      ret (h, {| psBuffer := a
               ; psBufLen := psLength ps1 + psLength ps2
               ; psOffset := 0
               ; psLength := psLength ps1 + psLength ps2 |})
    Else fun _ => ret (h1, ps1)
  Else fun _ => ret (h2, ps2).
Obligation 1. nomega. Defined.

Lemma refineEquiv_buffer_append (r1 r2 : bsrep) :
  refineEquiv
    (buffer_append r1 r2)
    (let ps1 := snd r1 in
     let ps2 := snd r2 in
     h1 <- fst r1;
     h2 <- fst r2;
     h <- { h : Rep HeapSpec | h = h1 /\ HeapState_Equal h1 h2 };
     If 0 <? psLength ps1
     Then If 0 <? psLength ps2
       Then
         a <- find_free_block (psLength ps1 + psLength ps2) (resvs h);
         h <- memcpy {| resvs :=
                          M.add a (psLength (snd r1) + psLength (snd r2))
                                (resvs h)
                      ; bytes := bytes h |}
                     (plusPtr (psBuffer ps1) (psOffset ps1))
                     a (psLength ps1);
         h <- memcpy h (plusPtr (psBuffer ps2) (psOffset ps2))
                       (a + psLength ps1) (psLength ps2);
         ret (h,
              {| psBuffer := a
               ; psBufLen := psLength ps1 + psLength ps2
               ; psOffset := 0
               ; psLength := psLength ps1 + psLength ps2 |})
       Else ret (h1, ps1)
     Else ret (h2, ps2)).
Proof.
  unfold buffer_append.
  f_equiv; intros ?.
  f_equiv; intros ?.
  f_equiv; intros ?.
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

Lemma buffer_to_list_app : forall h ps1 ps2 (v : Ptr Word),
  ~ overlaps (plusPtr (psBuffer ps1) (psOffset ps1)) (psLength ps1)
             v (psLength ps1 + psLength ps2) ->
  ~ overlaps (plusPtr (psBuffer ps2) (psOffset ps2)) (psLength ps2)
             v (psLength ps1 + psLength ps2) ->
  buffer_to_list h ps1 ++ buffer_to_list h ps2 =
  buffer_to_list
    {| resvs := M.add v (psLength ps1 + psLength ps2) (resvs h)
     ; bytes := copy_bytes (A:=Word)
                  (plusPtr (psBuffer ps2) (psOffset ps2))
                  (plusPtr v (psLength ps1))
                  (psLength ps2)
                  (copy_bytes (plusPtr (psBuffer ps1) (psOffset ps1)) v
                              (psLength ps1) (bytes h)) |}
    {| psBuffer := v
     ; psBufLen := psLength ps1 + psLength ps2
     ; psOffset := 0
     ; psLength := psLength ps1 + psLength ps2 |}.
Proof.
  intros.
  unfold buffer_to_list.
  rewrite Npeano_rec_list_app; simpl.
  rewrite N.add_0_r.
  set (f := fun (x : N) =>
              match M.find (plusPtr (A:=Word)
                                    (plusPtr (psBuffer ps1)
                                             (psOffset ps1))
                                    (psLength ps1 - N.succ x))
                           (bytes h) with
              | Some w => w
              | None => Zero
              end).
  set (g := fun (x : N) =>
              match M.find (plusPtr (A:=Word)
                                    (plusPtr (psBuffer ps2)
                                             (psOffset ps2))
                                    (psLength ps2 - N.succ x))
                           (bytes h) with
              | Some w => w
              | None => Zero
              end).
  rewrite <- Npeano_rec_list_add with (f:=f) (g:=g).
    reflexivity.
  intros; subst; f_equal.
  unfold f, g; clear f g.
  destruct_ps ps1; try clear IHpsLength0;
  destruct_ps ps2; try clear IHpsLength1.
  - destruct (k <? N.succ psLength0) eqn:Heqe; repeat reduce_find.
  - destruct (k <? 0) eqn:Heqe; repeat reduce_find.
  - destruct (k <? N.succ psLength1) eqn:Heqe; repeat reduce_find.
Qed.

Lemma buffer_append_sound : forall r_o1 r_o2 r_n1 r_n2,
  ByteString_list_AbsR r_o1 r_n1
    -> ByteString_list_AbsR r_o2 r_n2
    -> forall r_n' ps', buffer_append r_n1 r_n2 ↝ (r_n', ps')
    -> ByteString_list_AbsR (r_o1 ++ r_o2) (ret r_n', ps').
Proof.
  intros.
  apply refine_computes_to in H1.
  rewrite refineEquiv_buffer_append in H1.
  apply computes_to_refine in H1.
  destruct_computations.
  specialize (H _ H1); clear H1.
  specialize (H0 _ H2); clear H2.
  destruct H3; subst.
  if_computes_to_inv.
    if_computes_to_inv.
      tsubst.
      destruct_computations; simpl in *.
      destruct_AbsR H.
        destruct_AbsR H0; construct_AbsR.
      construct_AbsR.
        destruct_AbsR H0; tsubst.
          admit.
        admit.
        (* apply buffer_to_list_app; nomega. *)
      right.
      split.
        nomega.
      split; simpl.
        simplify_maps.
      nomega.
    tsubst.
    assert (r_o2 = []).
      destruct H0; subst.
      destruct r_n2, p; simpl in *.
      unfold buffer_to_list; simpl.
      assert (psLength0 = 0) by nomega.
      rewrite H0; simpl.
      reflexivity.
    rewrite H1, app_nil_r.
    destruct_AbsR H;
    destruct_AbsR H0;
    subst; intuition;
    construct_AbsR; auto;
    right; intuition.
  assert (r_o1 = []).
    destruct H; subst.
    destruct r_n1, p; simpl in *.
    unfold buffer_to_list; simpl.
    assert (psLength0 = 0) by nomega.
    rewrite H; simpl.
    reflexivity.
  subst.
  destruct_AbsR H;
  destruct_AbsR H0;
  subst; intuition;
  construct_AbsR; tsubst; auto;
  left; intuition.
  destruct H2.
  rewrite <- H in H9.
Admitted.

(**************************************************************************)

Theorem ByteStringHeap (heap : Rep HeapSpec) :
  { adt : _ & refineADT ByteStringSpec adt }.
Proof.
  eexists.

  hone representation using ByteString_list_AbsR.

  {
    simplify with monad laws.
    refine pick val (ret heap,
                     {| psBuffer := 0
                      ; psBufLen := 0
                      ; psOffset := 0
                      ; psLength := 0 |}).
      finish honing.
    construct_AbsR.
    firstorder.
  }

  {
    simplify with monad laws.
    setoid_rewrite (@refine_skip2_pick _ (buffer_cons r_n d)).
    etransitivity.
      refine_under.
        finish honing.
      refine pick val (ret (fst a), snd a).
        finish honing.
      eapply buffer_cons_sound; eauto.
      rewrite <- surjective_pairing; auto.
    simplify with monad laws; simpl.
    finish honing.
  }

  {
    simplify with monad laws.
    setoid_rewrite (refine_skip2_bind (dummy:=buffer_uncons r_n)).
    etransitivity.
      refine_under.
        finish honing.
      rewrite fst_match_list, snd_match_list.
      erewrite <- buffer_uncons_impl by eauto.
      refine pick val (ret (fst (fst a)), snd (fst a)).
        simplify with monad laws.
        finish honing.
      eapply buffer_uncons_sound; eauto.
    simpl; unfold buffer_uncons.
    simplify with monad laws.
    finish honing.
  }

  {
    simplify with monad laws.
    rewrite (refine_skip2_pick (dummy:=buffer_append r_n r_n0)).
    refine_under.
      finish honing.
    refine pick val (ret (fst a), snd a).
      finish honing.
    eapply buffer_append_sound; eauto.
    rewrite <- surjective_pairing; auto.
  }

  apply reflexivityT.
Defined.

End ByteStringHeap.
