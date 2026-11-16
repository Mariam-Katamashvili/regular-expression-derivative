From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Reals Lra.

From regexderiv Require Import Alphabet.
From regexderiv Require Import SimilarityRelations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.

(* ================================================================ *)
(* Section 4.2 of the paper: mu-fuzzy derivatives                   *)
(* ================================================================ *)

Module FuzzyDerivatives (X : SYM).
  Import X.

  Module Export S := SimilarityRelations X.

  (* boolean comparisons on values, used to filter the finite sums *)
  Definition Rleb (x y : simval) : bool := if Rle_dec x y then true else false.
  Definition Rltb (x y : simval) : bool := if Rlt_dec x y then true else false.

  Lemma RlebP (x y : simval) : Rleb x y = true <-> x <= y.
  Proof. by rewrite /Rleb; case: (Rle_dec x y). Qed.

  Lemma RltbP (x y : simval) : Rltb x y = true <-> x < y.
  Proof. by rewrite /Rltb; case: (Rlt_dec x y). Qed.

  (* the sum r_1 + ... + r_n of a list of expressions (Empty when n = 0) *)
  Fixpoint sum_re (l : seq regex) : regex :=
    if l is r :: l' then RS.Alt r (sum_re l') else RS.Empty.

  Lemma sum_reP (l : seq regex) (w : word) :
    RS.den (sum_re l) w <-> exists r, List.In r l /\ RS.den r w.
  Proof.
    elim: l => [|r l IH] /=.
    - by split => [//|[r []]].
    - rewrite /RS.plus /Languages.plus; split.
      + case/orP => [Hr|/IH [t [Ht Hw]]].
        * by exists r; split; [left|].
        * by exists t; split; [right|].
      + move=> [t [[<-|Ht] Hw]]; apply/orP; first by left.
        by right; apply/IH; exists t.
  Qed.

  (* D_char_correct, stated with RS.den instead of \in *)
  Lemma den_D_char (b : A) (s : regex) (w : word) :
    RS.den (D.D_char b s) w = RS.den s (b :: w).
  Proof. exact: D.D_char_correct. Qed.

  Section FuzzyDerivative.

    Variable T : tnorm.
    Variable R : fuzzy_rel A.
    Hypothesis R_tsim : is_T_similarity T R.

    (* Sigma is finite: [alphabet] lists every symbol *)
    Variable alphabet : seq A.
    Hypothesis alphabet_complete : forall a : A, a \in alphabet.

    Let R_range : forall a b, in01 (R a b) := tsim_range R_tsim.

    Let cands (r : regex) : seq regex := RE_candidates alphabet r.

    Let cands_complete (r s : regex) :
      RE T R s r <> 0 -> List.In s (cands r) :=
      @RE_candidates_complete T R R_tsim alphabet alphabet_complete r s.

    (* ============================================================ *)
    (* Definition 4.4: mu-fuzzy semantic derivative                 *)
    (* ============================================================ *)

    Definition fdlang_char (mu : simval) (a : A) (L : word -> Prop) : word -> Prop :=
      fun w => exists b v, mu <= T (R a b) (RwT T R w v) /\ L (b :: v).

    (* ============================================================ *)
    (* Definition 4.5: mu-fuzzy syntactic derivative                *)
    (*   D_a^mu(r) = sum of D_b(s) over R(a,b) ⊗ R^E(s,r) >= mu      *)
    (* the sum is finite: b ranges over the alphabet and s over the *)
    (* expressions with R^E(s,r) <> 0 (Lemma 3.5)                    *)
    (* ============================================================ *)

    Definition Dmu_char (mu : simval) (a : A) (r : regex) : regex :=
      sum_re (List.flat_map (fun b =>
                List.flat_map (fun s =>
                  if Rleb mu (T (R a b) (RE T R s r))
                  then [:: D.D_char b s] else [::])
                (cands r))
              alphabet).

    Lemma Dmu_charP (mu : simval) (a : A) (r : regex) (w : word) :
      0 < mu ->
      RS.den (Dmu_char mu a r) w <->
      exists b s, mu <= T (R a b) (RE T R s r) /\ RS.den s (b :: w).
    Proof.
      move=> Hmu.
      rewrite sum_reP; split.
      - move=> [t [Hin Hw]].
        move/List.in_flat_map: Hin => [b [_ Hb]].
        move/List.in_flat_map: Hb => [s [_ Hs]].
        move: Hs; case: ifP => [/RlebP Hle [Ht|[]]|_ []].
        exists b, s; split => //.
        by rewrite -den_D_char Ht.
      - move=> [b [s [Hle Hs]]].
        exists (D.D_char b s); split; last by rewrite den_D_char.
        apply/List.in_flat_map; exists b; split; first exact: mem_In.
        apply/List.in_flat_map; exists s; split.
        + apply: cands_complete.
          have [_ Hpos] := @tn_pos T _ _ (R_range a b) (RE_range R_tsim s r)
                             (Rlt_le_trans _ _ _ Hmu Hle).
          lra.
        + by move/RlebP: Hle => ->; left.
    Qed.

    (* ============================================================ *)
    (* Definition 4.6: mu-fuzzy semantic derivative by a word       *)
    (* ============================================================ *)

    Fixpoint fdlang (u : word) (mu : simval) (L : word -> Prop) : word -> Prop :=
      match u with
      | [::] => fun w => exists v, L v /\ mu_cut mu (RwT T R) w v
      | a :: v => fun w =>
          exists mu' mu'', cut_value mu' /\ cut_value mu'' /\
            mu <= T mu' mu'' /\ fdlang v mu' (fdlang_char mu'' a L) w
      end.

    (* ============================================================ *)
    (* Definition 4.7: mu-fuzzy syntactic derivative by a word      *)
    (*   D_{av}^mu(r) = sum of D_v^mu'(D_a^mu''(r)), mu' ⊗ mu'' >= mu *)
    (* mu'' ranges over Lambda_a(r), the nonzero values of           *)
    (* R(a,.) ⊗ R^E(.,r), and mu' over Lambda_v(D_a^mu''(r))         *)
    (* (remark after Definition 4.7)                                 *)
    (* ============================================================ *)

    Definition Lambda_char (a : A) (r : regex) : seq simval :=
      List.flat_map (fun b =>
        List.flat_map (fun s =>
          if Rltb 0 (T (R a b) (RE T R s r))
          then [:: T (R a b) (RE T R s r)] else [::])
        (cands r))
      alphabet.

    Fixpoint Lambda (u : word) (r : regex) : seq simval :=
      match u with
      | [::] => [:: 1]
      | a :: v =>
          List.flat_map (fun mu'' =>
            List.map (fun mu' => T mu' mu'') (Lambda v (Dmu_char mu'' a r)))
          (Lambda_char a r)
      end.

    Fixpoint Dmu (u : word) (mu : simval) (r : regex) : regex :=
      match u with
      | [::] => r
      | a :: v =>
          sum_re (List.flat_map (fun mu'' =>
                    List.flat_map (fun mu' =>
                      if Rleb mu (T mu' mu'')
                      then [:: Dmu v mu' (Dmu_char mu'' a r)] else [::])
                    (Lambda v (Dmu_char mu'' a r)))
                  (Lambda_char a r))
      end.

    Lemma Lambda_charP (a : A) (r : regex) (x : simval) :
      List.In x (Lambda_char a r) <->
      0 < x /\ exists b s, x = T (R a b) (RE T R s r).
    Proof.
      split.
      - move/List.in_flat_map => [b [_ Hb]].
        move/List.in_flat_map: Hb => [s [_ Hs]].
        move: Hs; case: ifP => [/RltbP Hpos [Hx|[]]|_ []].
        subst x; split => //.
        by exists b, s.
      - move=> [Hx [b [s Hxe]]].
        subst x.
        apply/List.in_flat_map; exists b; split; first exact: mem_In.
        apply/List.in_flat_map; exists s; split.
        + apply: cands_complete.
          have [_ Hpos] := @tn_pos T _ _ (R_range a b) (RE_range R_tsim s r) Hx.
          lra.
        + by move/RltbP: Hx => ->; left.
    Qed.

    Lemma Lambda_char_in01 (a : A) (r : regex) (x : simval) :
      List.In x (Lambda_char a r) -> in01 x.
    Proof.
      move/Lambda_charP => [_ [b [s ->]]].
      exact: (tn_in01 T (R_range a b) (RE_range R_tsim s r)).
    Qed.

    Lemma Lambda_in01 (u : word) (r : regex) (x : simval) :
      List.In x (Lambda u r) -> in01 x.
    Proof.
      elim: u r x => [|a v IH] r x /=.
      - by case=> [<-|//]; split; lra.
      - move/List.in_flat_map => [mu'' [Hmu'' Hx]].
        case/List.in_map_iff: Hx => [mu' [<- Hmu']].
        apply: tn_in01; [exact: (IH _ _ Hmu') | exact: (Lambda_char_in01 Hmu'')].
    Qed.

    Lemma Dmu_consP (a : A) (v : word) (mu : simval) (r : regex) (w : word) :
      RS.den (Dmu (a :: v) mu r) w <->
      exists mu'' mu',
        List.In mu'' (Lambda_char a r) /\
        List.In mu' (Lambda v (Dmu_char mu'' a r)) /\
        mu <= T mu' mu'' /\
        RS.den (Dmu v mu' (Dmu_char mu'' a r)) w.
    Proof.
      rewrite /= sum_reP; split.
      - move=> [t [Hin Hw]].
        move/List.in_flat_map: Hin => [mu'' [Hmu'' Ht]].
        move/List.in_flat_map: Ht => [mu' [Hmu' Ht]].
        move: Ht; case: ifP => [/RlebP Hle [Ht|[]]|_ []].
        exists mu'', mu'; do 2!split => //.
        by split; [| rewrite Ht].
      - move=> [mu'' [mu' [Hmu'' [Hmu' [Hle Hw]]]]].
        exists (Dmu v mu' (Dmu_char mu'' a r)); split => //.
        apply/List.in_flat_map; exists mu''; split => //.
        apply/List.in_flat_map; exists mu'; split => //.
        by move/RlebP: Hle => ->; left.
    Qed.

    (* ============================================================ *)
    (* Theorem 4.2(3): weak semantic-syntactic correspondence       *)
    (*   L(D_a^mu(r)) is included in d_a^mu(L(r))                    *)
    (* ============================================================ *)

    Theorem Dmu_char_sound (mu : simval) (a : A) (r : regex) (w : word) :
      cut_value mu ->
      RS.den (Dmu_char mu a r) w -> fdlang_char mu a (RS.den r) w.
    Proof.
      move=> [Hmu0 _] /(Dmu_charP _ _ _ Hmu0) [b [s [Hle Hs]]].
      have HRE := RE_range R_tsim s r.
      have [_ Hpos] := @tn_pos T _ _ (R_range a b) HRE (Rlt_le_trans _ _ _ Hmu0 Hle).
      case: (RE_witness R_tsim r Hs) => [H0|[y [Hy Hsy]]]; first lra.
      case: y Hy Hsy => [|c z] Hy Hsy /=.
      - by move: Hsy => /=; lra.
      - exists c, z; split => //.
        move: Hsy => /= Hsy.
        have Hbc := R_range b c.
        have Hab := R_range a b.
        have Hwz := RwT_range R_tsim w z.
        apply: (Rle_trans _ _ _ Hle).
        apply: (Rle_trans _ (T (R a b) (T (R b c) (RwT T R w z)))).
        + exact: (tn_mono_r T HRE (tn_in01 T Hbc Hwz) Hab Hsy).
        + rewrite -(@tn_assoc T _ _ _ Hab Hbc Hwz).
          apply: (@tn_mono T _ _ _ (tn_in01 T Hab Hbc) (R_range a c) Hwz).
          exact: (tsim_trans R_tsim a c b).
    Qed.

  End FuzzyDerivative.

End FuzzyDerivatives.
