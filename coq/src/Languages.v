From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Lang.
  Variable A : eqType.

  (* A word over the alphabet A is a finite sequence of symbols from A.
     The empty word ε is written directly as [::]. *)
  Definition word := seq A.

  (* A language L ⊆ A* is a decidable predicate on words. *)
  Definition language := pred word.

  (* Language-side meanings for regex semantic interpretation. *)
  Definition void : language := pred0.
  Definition eps  : language := fun w => w == [::].
  Definition atom (a : A) : language := fun w => w == [:: a].

  Definition plus (L K : language) : language := fun w => L w || K w.
  Definition conc (L K : language) : language :=
    fun w => has (fun i =>
      let u := take i w in
      let v := drop i w in
      L u && K v) (iota 0 (size w).+1).

  (* Helpers for Kleene star. *)

  (* Checks that every word in sequence belongs to the language.
     This is needed to express membership in the Kleene star. *)
  Fixpoint all_in (L : language) (xs : seq word) : bool :=
    match xs with
    | [::] => true
    | x :: xs' => L x && all_in L xs'
    end.

  (* Enumerates all finite decompositions of a word into blocks.
     This is the executable counterpart of the union-of-powers view of L*. *)
  Fixpoint splits (w : word) : seq (seq word) :=
    match w with
    | [::] => [:: [::] ]
    | a :: w' =>
      flatten [seq
        match ds with
        | [::] => [:: [:: [:: a] ] ]
        | x :: xs => [:: [:: a] :: ds; (a :: x) :: xs]
        end
      | ds <- splits w']
    end.

  Definition star (L : language) : language := fun w => has (all_in L) (splits w).
  Definition prod (L K : language) : language := fun w => L w && K w.
  Definition compl (L : language)  : language := fun w => ~~ L w.

  
  (* Proof support for the language operations above. *)

  (* Concatenates a list of words back into one word. *)
  Fixpoint flatten_words (xs : seq word) : word :=
    match xs with
    | [::] => [::]
    | x :: xs' => x ++ flatten_words xs'
    end.

  (* Every decomposition produced by splits really concatenates back to the
     original word. This makes the explicit equality check in star redundant. *)
  Lemma splits_flatten (w : word) (xs : seq word) :
    xs \in splits w -> flatten_words xs = w.
  Proof.
    (* Follow the recursive construction of splits and compute the flattened word. *)
    elim: w xs => [|a w IH] xs /=.
    - rewrite in_cons.
      move/orP=> [/eqP ->|]; first by [].
      by rewrite in_nil.
    - move/flattenP=> [ys Hys Hinx].
      move/mapP: Hys => [ds Hds Hys].
      move: Hinx; rewrite Hys.
      clear Hys.
      have Hflat_ds : flatten_words ds = w := IH _ Hds.
      case: ds Hds Hflat_ds => [|x ds'] Hds Hflat_ds /=.
      + rewrite in_cons.
        move/orP=> [/eqP ->|].
        * by move: Hflat_ds => <-.
        by rewrite in_nil.
      + rewrite !in_cons.
        move/orP=> [/eqP ->|Hinx].
        * by move: Hflat_ds; rewrite /= => ->.
        * move/orP: Hinx => [/eqP ->|].
          -- by move: Hflat_ds; rewrite /= => ->.
          by rewrite in_nil.
  Qed.

  (* Turns the computable definition of concatenation into the existential split
     used in semantic proofs. *)
  Lemma concP (L K : language) (w : word) :
    conc L K w ->
    exists u v, w = u ++ v /\ L u /\ K v.
  Proof.
    (* The witness index picked by 'has' gives the required split. *)
    move=> /hasP [i Hi] /=.
    set u := take i w.
    set v := drop i w.
    move=> /andP [Hu Hv].
    exists u, v; split.
    - by rewrite /u /v cat_take_drop.
    - by split.
  Qed.

  (* Rebuilds the computable concatenation test from an explicit semantic split.
     This is the converse direction of concP. *)
  Lemma concP_inv (L K : language) (w : word) :
    (exists u v, w = u ++ v /\ L u /\ K v) -> conc L K w.
  Proof.
    (* Use the split point i = size u. *)
    move=> [u [v [-> [Hu Hv]]]].
    apply/hasP.
    exists (size u).
    - 
      rewrite mem_iota add0n.
      apply/andP; split.
      + exact: leq0n.
      + 
        have Hle : size u <= size (u ++ v) by rewrite size_cat leq_addr.
        by rewrite -ltnS.
    - 
      rewrite /conc /=.
      rewrite take_size_cat ?leqnn //.
      rewrite drop_size_cat ?leqnn //.
      by rewrite Hu Hv.
  Qed.

  (* Specializes concatenation to the empty word. This is used to justify the
     nullable semantics of concatenation. *)
  Lemma conc_nil (L K : language) :
  conc L K [::] = (L [::] && K [::]).
  Proof.
    (* The empty word has only the trivial split [] ++ []. *)
    apply/idP/idP.
    - move=> H.
      have [u [v [Huv [Hu Hv]]]] := concP H.
      have /andP [Hu0 Hv0] : (size u == 0) && (size v == 0).
      { move: (congr1 size Huv); rewrite size_cat /=.
        move/eqP; rewrite eq_sym addn_eq0.
        by []. }
      have Hu_nil : u = [::] by apply/eqP; rewrite -size_eq0 Hu0.
      have Hv_nil : v = [::] by apply/eqP; rewrite -size_eq0 Hv0.
      move: Hu Hv; rewrite Hu_nil Hv_nil.
      by move=> Hu Hv; rewrite Hu Hv.
    - move=> /andP [Hu Hv].
      apply: concP_inv.
      exists [::], [::]; split; first by [].
      by split.
  Qed.

  (* Concatenation depends only on the extensional behavior of its arguments.
     This is needed when transporting semantic equality through regex constructors. *)
  Lemma conc_ext (L1 L2 K1 K2 : language) :
  (L1 =i L2) -> (K1 =i K2) -> conc L1 K1 =i conc L2 K2.
  Proof.
    (* Each candidate split is evaluated pointwise in the same way. *)
    move=> HL HK w.
    rewrite /conc.
    apply: eq_has => i /=.
    have Hab : L1 (take i w) = L2 (take i w) := HL (take i w).
    have Hcd : K1 (drop i w) = K2 (drop i w) := HK (drop i w).
    by rewrite Hab Hcd.
  Qed.


  (* all_in also respects extensional equality; this is used by star_ext. *)
  Lemma all_in_ext (L1 L2 : language) :
    (L1 =i L2) -> forall xs, all_in L1 xs = all_in L2 xs.
  Proof.
    (* Rewrite each block test using the extensional hypothesis. *)
    move=> HL; elim=> [|x xs IH] //=.
    set a := L1 x.
    set b := L2 x.
    have Hab : a = b by rewrite /a /b; exact: HL.
    by rewrite Hab IH.
  Qed.

  (* Kleene star also depends only on the language extension, not on the chosen
     predicate representation. *)
  Lemma star_ext (L1 L2 : language) :
    (L1 =i L2) -> star L1 =i star L2.
  Proof.
    (* The list of decompositions is fixed; only the block tests are rewritten. *)
    move=> HL w; rewrite /star.
    apply: eq_has => xs.
    exact: (all_in_ext HL xs).
  Qed.

  (* Every Kleene star contains ε. This is the n = 0 case in the union-of-powers
     definition of L*. *)
  Lemma star_nil (L : language) : star L [::].
  Proof.
    (* The empty decomposition witnesses membership. *)
    by rewrite /star /=.
  Qed.

  (* Exposes the witness decomposition behind star membership. This is the main
     elimination principle used later for derivative and canonicalization proofs. *)
  Lemma starP (L : language) (w : word) :
    star L w ->
    exists xs,
      xs \in splits w /\ all_in L xs.
  Proof.
    (* Unpack the witness from has. The flattening equation now follows from splits_flatten. *)
    move=> /hasP [xs Hxs Hall].
    by exists xs.
  Qed.

  (* Packs an explicit decomposition back into a star membership proof. *)
  Lemma starP_inv (L : language) (w : word) (xs : seq word) :
    xs \in splits w ->
    all_in L xs ->
    star L w.
  Proof.
    (* Membership in splits w is already enough to recover the concatenated word. *)
    move=> Hxs Hall.
    rewrite /star.
    apply/hasP.
    by exists xs.
  Qed.

  (* Every decomposition of a non-empty word starts with a non-empty first block.
     This shape lemma is used to reason about one-symbol extensions in star proofs. *)
  Lemma splits_cons_shape (a : A) (w : word) (xs : seq word) :
    xs \in splits (a :: w) -> exists t ys, xs = (a :: t) :: ys.
  Proof.
    (* Inspect the one-step construction of splits (a :: w). *)
    move=> Hxs; rewrite /= in Hxs.
    move/flattenP: Hxs => [ys Hys Hxsin].
    move/mapP: Hys => [ds Hds Hys].
    move: Hxsin; rewrite Hys.
    clear Hds Hys.
    case: ds => [|x ds] /=.
    - rewrite in_cons.
      move/orP=> [/eqP ->|].
      + by exists [::], [::].
      + by rewrite in_nil.
    - rewrite !in_cons.
      move/orP=> [/eqP ->|].
      + by exists [::], (x :: ds).
      + move/orP=> [/eqP ->|].
        * by exists x, ds.
        * by rewrite in_nil.
  Qed.


  (* Prepends a new one-letter block to an existing decomposition. *)
  Lemma splits_start_new (a : A) (w : word) (ds : seq word) :
    ds \in splits w -> ([:: a] :: ds) \in splits (a :: w).
  Proof.
    (* Choose the branch of splits that starts a fresh block with a. *)
    move=> Hds; rewrite /=.
    apply/flattenP.
    exists (match ds with
            | [::] => [:: [:: [:: a] ] ]
            | x :: xs => [:: [:: a] :: ds; (a :: x) :: xs]
            end).
    - apply/mapP; exists ds => //.
    - case: ds Hds => [|x xs] Hds //=; by rewrite in_cons eqxx.
  Qed.

  (* Extends the first block of a decomposition by one symbol at the front. *)
  Lemma splits_extend_head (a : A) (w : word) (x : word) (xs : seq word) :
    (x :: xs) \in splits w -> ((a :: x) :: xs) \in splits (a :: w).
  Proof.
    (* Choose the branch of splits that grows the current first block. *)
    move=> Hx; rewrite /=.
    apply/flattenP.
    exists ([:: [:: a] :: (x :: xs); (a :: x) :: xs]).
    - apply/mapP; exists (x :: xs) => //.
    - rewrite in_cons.
      apply/orP; right.
      by rewrite in_cons eqxx.
  Qed.

  (* Lifts a decomposition of v to a decomposition of u ++ v when u is non-empty.
     This is the combinatorial step behind star concatenation proofs. *)
  Lemma splits_head_cat (u v : word) (ys : seq word) :
    u != [::] -> ys \in splits v -> (u :: ys) \in splits (u ++ v).
  Proof.
    (* Rebuild the decomposition by consuming u from left to right. *)
    elim: u ys => [|a [|b u] IH] ys //=.
    - move=> _ Hys.
      exact: (@splits_start_new a v ys Hys).
    - move=> _ Hys.
      have Hih : ((b :: u) :: ys) \in splits ((b :: u) ++ v).
      { apply: IH; first by [].
        exact: Hys. }
      exact: (@splits_extend_head a ((b :: u) ++ v) (b :: u) ys Hih).
  Qed.

  (* Removes the first block from a decomposition and recovers the decomposition
     of the remaining suffix. *)
  Lemma splits_tail (w : word) (x : word) (xs : seq word) :
    (x :: xs) \in splits w -> xs \in splits (drop (size x) w).
  Proof.
    (* Follow the recursive construction of splits and peel off the leading block. *)
    elim: w x xs => [|a w IH] x xs /=.
    - move=> H; move: H; rewrite in_cons; move/orP=> [/eqP H|];
        last by rewrite in_nil.
      discriminate.
    - move=> Hmem.
      move/flattenP: Hmem => [zs Hzs Hinx].
      move/mapP: Hzs => [ds Hds Hzs].
      move: Hinx; rewrite Hzs.
      clear Hzs.
      case: ds Hds => [|y ys] Hds Hinx /=.
      + rewrite in_cons in Hinx.
        move/orP: Hinx => [/eqP Hcase|]; last by rewrite in_nil.
        have Hx : x = [:: a] := congr1 (head [::]) Hcase.
        have Hxs : xs = [::] := congr1 behead Hcase.
        subst x xs.
        rewrite /= drop0 in Hds *.
        exact: Hds.
      + rewrite !in_cons in Hinx.
        move/orP: Hinx => [/eqP Hcase1|Hinx].
        * have Hx : x = [:: a] := congr1 (head [::]) Hcase1.
          have Hxs : xs = y :: ys := congr1 behead Hcase1.
          subst x xs.
          rewrite /= drop0 in Hds *.
          exact: Hds.
        * move/orP: Hinx => [/eqP Hcase2|]; last by rewrite in_nil.
          have Hx : x = a :: y := congr1 (head [::]) Hcase2.
          have Hxs : xs = ys := congr1 behead Hcase2.
          subst x xs.
          have Hih : ys \in splits (drop (size y) w) := IH y ys Hds.
          rewrite /=.
          exact Hih.
  Qed.

  (* The blocks produced by splits are non-empty. *)
  Lemma splits_nonempty (w : word) (xs : seq word) :
    xs \in splits w -> all (fun x => x != [::]) xs.
  Proof.
    elim: xs w => [//|x xs IH] w Hxs /=.
    apply/andP; split; last exact: (IH _ (splits_tail Hxs)).
    case: w Hxs => [|a w] Hxs; first by rewrite mem_seq1 in Hxs.
    by have [t [ys [-> _]]] := splits_cons_shape Hxs.
  Qed.

  (* Conversely, any list of non-empty blocks is a decomposition of its
     concatenation. *)
  Lemma splits_complete (xs : seq word) :
    all (fun x => x != [::]) xs -> xs \in splits (flatten_words xs).
  Proof.
    elim: xs => [|x xs IH] /=; first by rewrite mem_seq1.
    by move=> /andP [Hx /IH Hxs]; exact: splits_head_cat.
  Qed.

  (* Renaming letters commutes with concatenating blocks. *)
  Lemma map_flatten_words (f : A -> A) (xs : seq word) :
    map f (flatten_words xs) = flatten_words (map (map f) xs).
  Proof. by elim: xs => [//|x xs /= <-]; rewrite map_cat. Qed.

  (* If a::w belongs to L*, then its first block is of the form a::u and the
     remaining blocks witness a star decomposition of the suffix. *)
  Lemma star_cons_split (L : language) (a : A) (w : word) :
    star L (a :: w) ->
    exists u v, w = u ++ v /\ L (a :: u) /\ star L v.
  Proof.
    (* Decompose a::w, then isolate the first block and keep the tail decomposition. *)
    move=> Hs.
    have [xs [Hxs Hall]] := starP Hs.
    have [t [ys Hshape]] := splits_cons_shape Hxs.
    subst xs.
    move/andP: Hall => [HLhead HLtail].

    (* flatten_words ((a::t)::ys) = a::w follows from the splits invariant *)
    have Hcat0 : (a :: t) ++ flatten_words ys = a :: w.
    { have Hflat : flatten_words ((a :: t) :: ys) = a :: w := splits_flatten Hxs.
      by move: Hflat. }

    (* turn (a::t)++... into a::(t++...) so we can take tails *)
    have Hcat1 : a :: (t ++ flatten_words ys) = a :: w.
    { by move: Hcat0; rewrite -cat_cons. }

    have Hw : t ++ flatten_words ys = w := congr1 behead Hcat1.

    exists t, (flatten_words ys); split; first by rewrite Hw.
    split; first exact HLhead.

    apply: starP_inv.
    - (* ys ∈ splits (flatten_words ys) *)
      have Hy0 : ys \in splits (drop (size (a :: t)) (a :: w)) :=
        splits_tail Hxs.
      have Hdrop : drop (size (a :: t)) (a :: w) = flatten_words ys.
      { (* rewrite a::w as (a::t)++flatten_words ys via Hcat0 *)
        by rewrite -Hcat0 drop_size_cat ?leqnn. }
      rewrite Hdrop in Hy0.
      exact Hy0.
    - exact HLtail.
  Qed.


  (* Converse direction of star_cons_split: prepend one accepted block to a word
     already in L* and obtain a larger word in L*. *)
  Lemma star_cons_split_inv (L : language) (a : A) (w : word) :
    (exists u v, w = u ++ v /\ L (a :: u) /\ star L v) ->
    star L (a :: w).
  Proof.
    (* Build the new decomposition by placing a::u in front of a decomposition of v. *)
    move=> [u [v [-> [Hu Hv]]]].
    have [ys [Hys Hall]] := starP Hv.

    have Hspl : ((a :: u) :: ys) \in splits ((a :: u) ++ v).
    { apply: (splits_head_cat (u:=(a :: u)) (v:=v) (ys:=ys)).
      - by [].
      - exact Hys. }
    have Hspl' : ((a :: u) :: ys) \in splits (a :: (u ++ v)).
    { by rewrite cat_cons in Hspl. }

    apply: (starP_inv (xs := (a :: u) :: ys)).
    - exact Hspl'.
    - apply/andP; split.
      + exact Hu.
      + exact Hall.
  Qed.


  (* Corresponds to ( {ε} )* = {ε}. This normalization fact is used later by
     canonicalization correctness proofs. *)
  Lemma star_eps : star eps =i eps.
  Proof.
    (* Non-empty words cannot be decomposed into ε-blocks only. *)
    move=> w; case: w => [|a w].
    - by rewrite /star /eps /splits /= /flatten_words /all_in.
    - rewrite /star /eps /=.
      apply/negP => /hasP [xs Hxs Hall].
      have [t [ys Hshape]] := splits_cons_shape Hxs.
      by move: Hall; rewrite Hshape /= /eps.
  Qed.

  (* Corresponds to ( ∅ )* = {ε}. This is another normalization fact reused
     later in the development. *)
  Lemma star_void : star void =i eps.
  Proof.
    (* Non-empty words cannot be decomposed into blocks from the empty language. *)
    move=> w; case: w => [|a w].
    - by rewrite /star /void /eps /splits /= /flatten_words /all_in.
    - rewrite /star /void /eps /=.
      apply/negP => /hasP [xs Hxs Hall].
      have [t [ys Hshape]] := splits_cons_shape Hxs.
      by move: Hall; rewrite Hshape /= /void.
  Qed.

End Lang.
