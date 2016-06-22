Require Import Fiat.ADT Fiat.ADTNotation.

Require Import Coq.Sets.Ensembles.
Require Import Coq.NArith.NArith.

Require Import Here.ADTInduction.
Require Import Here.LibExt.
Require Import Here.Decidable.

Open Scope string_scope.
Open Scope N_scope.

Definition emptyS   := "empty".
Definition allocS   := "alloc".
Definition reallocS := "realloc".
Definition freeS    := "free".
Definition peekS    := "peek".
Definition pokeS    := "poke".
Definition memcpyS  := "memcpy".
Definition memsetS  := "memset".

Section Heap.

Variable Word8 : Type.

Definition within (addr : N) (len : N) (a : N) : Prop :=
  addr <= a < addr + len.

Definition within_le (addr : N) (len : N) (a : N) : Prop :=
  addr <= a <= addr + len.

Definition fits (addr len addr2 len2 : N) : Prop :=
  within addr len addr2 /\ within_le addr len (addr2 + len2).

Definition overlaps (addr len addr2 len2 : N) : Prop :=
  addr < addr2 + len2 /\ addr2 < addr + len.

Definition HeapSpec := Def ADT {
  (* a set of addr + len pairs to mark allocations,
     and another set to locate bytes *)
  rep := Ensemble (N * N) * Ensemble (N * Word8),

  Def Constructor0 emptyS : rep := ret (Empty_set _, Empty_set _),,

  Def Method1 allocS (r : rep) (len : N | 0 < len) : rep * N :=
    (* Allocate the block *)
    addr <- { addr : N
            | forall addr' len', In _ (fst r) (addr', len')
                -> ~ overlaps addr (proj1_sig len) addr' len' };
    ret ((Add _ (fst r) (addr, proj1_sig len), snd r), addr),

  Def Method1 freeS (r : rep) (addr : N) : rep * bool :=
    (* Does an allocated block exist at the given address? *)
    m <- { m : option N | forall l, m = Some l -> In _ (fst r) (addr, l) };
    (* If yes, remove it and all its associated memory; else do nothing *)
    ret (Ifopt m as len
         Then ((Subtract _ (fst r) (addr, len),
                Setminus _ (snd r) (fun p => within addr len (fst p))),
               true)
         Else (r, false)),

  Def Method2 reallocS (r : rep) (addr : N) (len : N | 0 < len) :
    rep * N :=
    (* Does an allocated block exist at the given address? *)
    m <- { m : option N | forall l, m = Some l -> In _ (fst r) (addr, l) };
    Ifopt m as olen
    Then
      (* Check whether to block to be reallocated would fit at its current
         position. If so, just update the length, otherwise deallocate and
         reallocate it, while copying its contents to the new position. *)
      let len := proj1_sig len in
      IfDec len <= olen
      Then ret (((fun p =>
                    IF fst p = addr
                    then snd p = len
                    else In _ (fst r) p),
                 (fun p =>
                    In _ (snd r) p /\
                    ~ within (addr + len) (addr + olen) (fst p))),
                addr)
      Else (
        (* Is there enough free space to allocate the new block? *)
        naddr <- { naddr : N
                 | forall addr' len', In _ (fst r) (addr', len')
                     -> ~ overlaps naddr len addr' len' };
        (* Free the old block, allocate the new one, and copy over as
           many bytes as possible from the previous block. *)
        ret ((Add _ (Subtract _ (fst r) (addr, olen)) (naddr, len),
                (fun p =>
                   IF within naddr (N.min olen len) (fst p)
                   then IF naddr < addr
                        then In _ (snd r) (fst p - (addr - naddr), snd p)
                        else In _ (snd r) (fst p + (naddr - addr), snd p)
                   else ~ within addr len (fst p) -> In _ (snd r) p)),
             naddr)
      )
    Else (
      (* Allocate a new block *)
      addr <- { addr : N
              | forall addr' len', In _ (fst r) (addr', len')
                  -> ~ overlaps addr (proj1_sig len) addr' len' };
      ret ((Add _ (fst r) (addr, proj1_sig len), snd r), addr)),

  Def Method1 peekS (r : rep) (addr : N) : rep * option Word8 :=
    (* Retrieve the word at the given location; note that since [pokeS] is the
       only way to set memory, and it only allows setting within an allocated
       block, we don't need to test whether the address is allocated here. *)
    p <- { p : option Word8 | forall x, p = Some x -> In _ (snd r) (addr, x) };
    ret (r, p),

  Def Method2 pokeS (r : rep) (addr : N) (w : Word8) : rep * unit :=
      (* Check whether the address is within an allocated block; if so, set the
       memory location, otherwise do nothing. *)
    ret ((fst r, Add _ (Setminus _ (snd r) (fun p => fst p = addr))
                       (addr, w)), tt),

  Def Method3 memcpyS (r : rep) (addr : N) (addr2 : N) (len : N) : rep * unit :=
    ret ((fst r, fun p =>
           (* If an attempt is made to access the new region, adjust it to
              look like an access to the old location. *)
           IF within addr2 len (fst p)
           then IF addr < addr2
                then In _ (snd r) (fst p - (addr2 - addr), snd p)
                else In _ (snd r) (fst p + (addr - addr2), snd p)
           else In _ (snd r) p),
         tt),

  Def Method3 memsetS (r : rep) (addr : N) (len : N) (w : Word8) : rep * bool :=
    (* Check that the memory to be set is within an allocated region. *)
    b <- { b | decides b
                 (exists addr' len',
                     In _ (fst r) (addr', len') /\
                     within_le addr' len' (addr + len)) };
    ret (If b
         Then
           ((fst r,
             fun p =>
               (* A reference to the set region appears as though all its
                  bytes have that value. *)
               IF within addr len (fst p)
               then snd p = w
               else In _ (snd r) p), true)
         Else (r, false))

}%ADTParsing.

Definition realloc (r : Rep HeapSpec) (addr : N) (len : N | 0 < len) :
  Comp (Rep HeapSpec * N) :=
  Eval simpl in callMeth HeapSpec reallocS r addr len.

Definition peek (r : Rep HeapSpec) (addr : N) :
  Comp (Rep HeapSpec * option Word8) :=
  Eval simpl in callMeth HeapSpec peekS r addr.

Definition poke (r : Rep HeapSpec) (addr : N) (w : Word8) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec pokeS r addr w.

Definition memcpy (r : Rep HeapSpec) (addr : N) (addr2 : N) (len : N) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec memcpyS r addr addr2 len.

Theorem allocations_have_size : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr len, Ensembles.In _ (fst r) (addr, len) -> 0 < len.
Proof.
  intros.
  generalize dependent len.
  generalize dependent addr.
  ADT induction r.
  - inversion H0.
  - simplify_ensembles.
      exact (IHfromADT _ _ H2).
    destruct x; trivial.
  - revert H0'.
    simplify_ensembles; intros;
    inv H0'; simplify_ensembles.
      exact (IHfromADT _ _ H2).
    exact (IHfromADT _ _ H1).
  - revert H0'.
    simplify_ensembles;
    destruct x0; simpl;
    unfold IfDec_Then_Else; simpl.
      destruct (x0 <=? n);
      simplify_ensembles; simpl in *;
      subst; trivial.
        exact (IHfromADT _ _ H2).
      destruct x0;
      simplify_ensembles; simpl in *;
      inv H3; inv H1; inv H3; trivial.
        exact (IHfromADT _ _ H1).
      exact (IHfromADT _ _ H1).
    inv H3; inv H1.
      exact (IHfromADT _ _ H3).
    inv H3.
    assumption.
  - revert H0'.
    destruct v; simpl; intros;
    inv H0'; simpl in *;
    exact (IHfromADT _ _ H1).
Qed.

Theorem allocations_unique : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr len1 len2,
    Ensembles.In _ (fst r) (addr, len1) /\ Ensembles.In _ (fst r) (addr, len2)
      -> len1 = len2.
Admitted.

Theorem allocations_no_overlap : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 len1 addr2 len2,
    Ensembles.In _ (fst r) (addr1, len1) /\ Ensembles.In _ (fst r) (addr2, len2)
      -> ~ overlaps addr1 len1 addr2 len2.
Admitted.

Theorem assignments_unique : forall r : Rep HeapSpec, fromADT _ r ->
  forall idx val1 val2,
    Ensembles.In _ (snd r) (idx, val1) /\ Ensembles.In _ (snd r) (idx, val2)
      -> val1 = val2.
Admitted.

Theorem assignments_correct : forall r : Rep HeapSpec, fromADT _ r ->
  forall i v, Ensembles.In _ (snd r) (i, v)
    -> exists a l, Ensembles.In _ (fst r) (a, l) /\ within a l i.
Admitted.

End Heap.