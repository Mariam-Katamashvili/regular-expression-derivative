From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Reals Lra.

From regexderiv Require Import Languages.
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

  Lemma RlebP (x y : simval) : reflect (x <= y) (Rleb x y).
  Proof. by rewrite /Rleb; case: (Rle_dec x y) => H; constructor. Qed.

  Lemma RltbP (x y : simval) : reflect (x < y) (Rltb x y).
  Proof. by rewrite /Rltb; case: (Rlt_dec x y) => H; constructor. Qed.

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
    Let R_refl : forall a, R a a = 1 := prox_refl (tsim_prox R_tsim).

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

    (* ============================================================ *)
    (* Theorem 4.2(1): experimentum crucis                          *)
    (*   u ∈ L^mu(r)  iff  ε ∈ L(D_u^mu(r))                          *)
    (* ============================================================ *)

    (* a higher cut keeps fewer summands *)
    Lemma Dmu_antitone (u : word) (mu nu : simval) (r : regex) (w : word) :
      mu <= nu -> RS.den (Dmu u nu r) w -> RS.den (Dmu u mu r) w.
    Proof.
      case: u => [//|a v] Hle.
      move/Dmu_consP => [mu'' [mu' [Hmu'' [Hmu' [Hnu Hw]]]]].
      apply/Dmu_consP; exists mu'', mu'; do 2!split => //.
      split => //; exact: (Rle_trans _ _ _ Hle Hnu).
    Qed.

    (* if ε ∈ L(D_u^mu(r)), some v ∈ L(r) has R^w(u,v) >= mu *)
    Lemma Dmu_eps_sound (u : word) :
      forall (mu : simval) (r : regex), cut_value mu ->
      RS.den (Dmu u mu r) [::] -> exists v, RS.den r v /\ mu <= RwT T R u v.
    Proof.
      elim: u => [|a v IH] mu r [Hmu0 Hmu1].
      - by move=> Hr; exists [::]; split => //=.
      move/Dmu_consP => [mu'' [mu' [Hmu'' [Hmu' [Hle Hden]]]]].
      have Hin'' := Lambda_char_in01 Hmu''.
      have Hin' := Lambda_in01 Hmu'.
      have [Hpos' Hpos''] := @tn_pos T _ _ Hin' Hin'' (Rlt_le_trans _ _ _ Hmu0 Hle).
      have Hcut' : cut_value mu' by split; [|case: Hin'].
      have [x [Hx Hvx]] := IH mu' _ Hcut' Hden.
      move/(Dmu_charP _ _ _ Hpos''): Hx => [b [s [Hbs Hs]]].
      have HRE := RE_range R_tsim s r.
      have Hab := R_range a b.
      have HREpos : 0 < RE T R s r.
      { have [_ H] := @tn_pos T _ _ Hab HRE (Rlt_le_trans _ _ _ Hpos'' Hbs).
        exact: H. }
      case: (RE_witness R_tsim r Hs) => [H0|[y [Hy Hsy]]]; first lra.
      case: y Hy Hsy => [|c z] Hy /= Hsy; first lra.
      exists (c :: z); split => //=.
      have Hbc := R_range b c.
      have Hvx' := RwT_range R_tsim v x.
      have Hxz := RwT_range R_tsim x z.
      have Hbcxz := tn_in01 T Hbc Hxz.
      have Habbc := tn_in01 T Hab Hbc.
      (* mu <= mu' ⊗ mu'' <= R^w(v,x) ⊗ (R(a,b) ⊗ (R(b,c) ⊗ R^w(x,z))) *)
      apply: (Rle_trans _ _ _ Hle).
      apply: (Rle_trans _ (T (RwT T R v x) (T (R a b) (T (R b c) (RwT T R x z))))).
      { apply: (tn_mono2 T Hin' Hvx' Hin'' (tn_in01 T Hab Hbcxz) Hvx).
        apply: (Rle_trans _ _ _ Hbs).
        exact: (tn_mono_r T HRE Hbcxz Hab Hsy). }
      (* ... = (R(a,b) ⊗ R(b,c)) ⊗ (R^w(v,x) ⊗ R^w(x,z)) <= R(a,c) ⊗ R^w(v,z) *)
      have -> : T (RwT T R v x) (T (R a b) (T (R b c) (RwT T R x z))) =
                T (T (R a b) (R b c)) (T (RwT T R v x) (RwT T R x z)).
      { rewrite -(@tn_assoc T _ _ _ Hab Hbc Hxz).
        rewrite -(@tn_assoc T _ _ _ Hvx' Habbc Hxz).
        rewrite (@tn_comm T _ _ Hvx' Habbc).
        by rewrite (@tn_assoc T _ _ _ Habbc Hvx' Hxz). }
      apply: (tn_mono2 T Habbc (R_range a c) (tn_in01 T Hvx' Hxz)
                (RwT_range R_tsim v z)).
      - exact: (tsim_trans R_tsim a c b).
      - exact: (RwT_trans R_tsim v z x).
    Qed.

    (* if z ∈ L(t) and R^w(v,z) > 0, then R^w(v,z) is one of the values in
       Lambda_v(t) and ε ∈ L(D_v^{R^w(v,z)}(t)) *)
    Lemma Dmu_eps_complete (v : word) :
      forall (t : regex) (z : word), RS.den t z -> 0 < RwT T R v z ->
      List.In (RwT T R v z) (Lambda v t) /\
      RS.den (Dmu v (RwT T R v z) t) [::].
    Proof.
      elim: v => [|a v IH] t z Hz.
      - case: z Hz => [|c z] Hz /=; last lra.
        by move=> _; split; [left|].
      case: z Hz => [|c z] Hz /=; first lra.
      move=> Hpos.
      have Hac := R_range a c.
      have Hvz := RwT_range R_tsim v z.
      have [Hac0 Hvz0] := @tn_pos T _ _ Hac Hvz Hpos.
      have Hac_eq : R a c = T (R a c) (RE T R t t)
        by rewrite RE_refl (@tn_unit T _ Hac).
      (* z ∈ L(D_a^{R(a,c)}(t)), through the summand D_c(t) *)
      have Hz' : RS.den (Dmu_char (R a c) a t) z.
      { apply/(Dmu_charP _ _ _ Hac0); exists c, t; split => //.
        rewrite -Hac_eq; exact: Rle_refl. }
      have [Hin Hden] := IH _ _ Hz' Hvz0.
      have Hlam : List.In (R a c) (Lambda_char a t).
      { apply/Lambda_charP; split => //; by exists c, t. }
      rewrite (@tn_comm T _ _ Hac Hvz).
      split.
      - apply/List.in_flat_map; exists (R a c); split => //.
        apply/List.in_map_iff; by exists (RwT T R v z).
      - apply/Dmu_consP; exists (R a c), (RwT T R v z).
        by do 3!split => //; exact: Rle_refl.
    Qed.

    (* Theorem 4.2(1), for every T-norm and on all of E *)
    Theorem experimentum_crucis (u : word) (mu : simval) (r : regex) :
      cut_value mu ->
      fuzzy_den T R mu r u <-> RS.den (Dmu u mu r) [::].
    Proof.
      move=> Hmu; split.
      - move=> [v [Hv Huv]].
        have Hpos : 0 < RwT T R u v by case: Hmu => H0 _; exact: (Rlt_le_trans _ _ _ H0 Huv).
        have [_ Hden] := Dmu_eps_complete Hv Hpos.
        exact: (Dmu_antitone Huv Hden).
      - move=> Hden.
        have [v [Hv Huv]] := Dmu_eps_sound Hmu Hden.
        by exists v.
    Qed.

    (* ============================================================ *)
    (* Proposition 4.2: when R is godelian or mu ⊗ mu = mu, the      *)
    (* fuzzy derivatives only need the mu-cuts                       *)
    (* ============================================================ *)

    (* Proposition 4.2(1), right-hand side: the sum of D_b(s) over
       a ~_mu b and s ~_mu^E r *)
    Definition Dmu_char_cut (mu : simval) (a : A) (r : regex) : regex :=
      sum_re (List.flat_map (fun b =>
                List.flat_map (fun s =>
                  if Rleb mu (R a b) && Rleb mu (RE T R s r)
                  then [:: D.D_char b s] else [::])
                (cands r))
              alphabet).

    (* Proposition 4.2(2), right-hand side *)
    Definition fdlang_char_cut (mu : simval) (a : A) (L : word -> Prop) :
        word -> Prop :=
      fun w => exists b v,
        mu_cut mu R a b /\ mu_cut mu (RwT T R) w v /\ L (b :: v).

    (* Proposition 4.2(1), on all of E *)
    Theorem Dmu_char_cutE (mu : simval) (a : A) (r : regex) :
      cut_value mu -> is_godelian T R \/ T mu mu = mu ->
      Dmu_char mu a r = Dmu_char_cut mu a r.
    Proof.
      move=> [Hmu0 Hmu1] Hcase.
      have Hmu : in01 mu by split; lra.
      congr sum_re; apply: List.flat_map_ext => b.
      apply: List.flat_map_ext => s.
      have Hsplit := @tn_cut_split T _ _ _ Hmu (R_range a b) (RE_range R_tsim s r).
      have {}Hsplit : mu <= T (R a b) (RE T R s r) <->
                      mu <= R a b /\ mu <= RE T R s r.
      { apply: Hsplit; case: Hcase => [Hg|Hidem]; [right|by left].
        by split; [rewrite -Hg | rewrite -(RE_godelian R_tsim Hg)]. }
      suff -> : Rleb mu (T (R a b) (RE T R s r)) =
                Rleb mu (R a b) && Rleb mu (RE T R s r) by [].
      apply/RlebP/andP.
      - by move/Hsplit => [H1 H2]; split; apply/RlebP.
      - by move=> [/RlebP H1 /RlebP H2]; apply/Hsplit.
    Qed.

    (* Proposition 4.2(2) *)
    (* the cut R(a,b) ⊗ R^w(w,v) >= mu splits letter by letter *)
    Lemma RwT_cut_split (mu : simval) (a b : A) (w v : word) :
      cut_value mu -> is_godelian T R \/ T mu mu = mu ->
      mu <= T (R a b) (RwT T R w v) <-> mu <= R a b /\ mu <= RwT T R w v.
    Proof.
      move=> [Hmu0 Hmu1] Hcase.
      apply: (@tn_cut_split T _ _ _ _ (R_range a b) (RwT_range R_tsim w v));
        first by split; lra.
      case: Hcase => [Hg|Hidem]; [right|by left].
      by split; [rewrite -Hg | rewrite -(RwT_godelian R_tsim Hg)].
    Qed.

    Theorem fdlang_char_cutP (mu : simval) (a : A) (L : word -> Prop) (w : word) :
      cut_value mu -> is_godelian T R \/ T mu mu = mu ->
      fdlang_char mu a L w <-> fdlang_char_cut mu a L w.
    Proof.
      move=> Hmu Hcase; split.
      - move=> [b [v [/(RwT_cut_split _ _ _ _ Hmu Hcase) [Hab Hwv] HL]]].
        by exists b, v.
      - move=> [b [v [Hab [Hwv HL]]]].
        by exists b, v; split => //; apply/(RwT_cut_split _ _ _ _ Hmu Hcase).
    Qed.

    (* ============================================================ *)
    (* Definition 4.8: the quotient alphabet Sigma^mu, the quotient *)
    (* map q_mu, its extension q_mu^* to words, and [L]_mu           *)
    (* A class [a]_mu is represented by one fixed letter q_mu(a):    *)
    (* the first letter of the alphabet that is mu-similar to a.     *)
    (* Sigma^mu is the set of these representatives, and             *)
    (* q_mu(a) = q_mu(b) iff a ~_mu b (lemma [qmu_eq]).              *)
    (* ============================================================ *)

    Definition qmu (mu : simval) (a : A) : A :=
      nth a alphabet (find (fun b => Rleb mu (R a b)) alphabet).

    Definition qmu_word (mu : simval) (w : word) : word := map (qmu mu) w.

    Lemma qmu_word_cons (mu : simval) (b : A) (v : word) :
      qmu_word mu (b :: v) = qmu mu b :: qmu_word mu v.
    Proof. by []. Qed.

    Definition quot_lang (mu : simval) (L : word -> Prop) : word -> Prop :=
      fun x => exists w, L w /\ qmu_word mu w = x.

    Lemma qmu_has (mu : simval) (a : A) :
      cut_value mu -> has (fun b => Rleb mu (R a b)) alphabet.
    Proof.
      move=> [_ Hmu1]; apply/hasP; exists a; first exact: alphabet_complete.
      by apply/RlebP; rewrite R_refl.
    Qed.

    (* a is mu-similar to its representative *)
    Lemma qmu_cut (mu : simval) (a : A) :
      cut_value mu -> mu_cut mu R a (qmu mu a).
    Proof. by move=> Hmu; apply/RlebP/(nth_find a (qmu_has a Hmu)). Qed.

    (* q_mu is the quotient map: q_mu(a) = q_mu(b) iff a ~_mu b *)
    Lemma qmu_eq (mu : simval) (a b : A) :
      cut_value mu -> is_godelian T R \/ T mu mu = mu ->
      qmu mu a = qmu mu b <-> mu_cut mu R a b.
    Proof.
      move=> Hmu Hcase.
      have [_ Htrans Hsym] := R_cut_equivalence R_tsim Hmu Hcase.
      split.
      - move=> Hq.
        have Ha := qmu_cut a Hmu.
        rewrite Hq in Ha.
        exact: (Htrans _ _ _ Ha (Hsym _ _ (qmu_cut b Hmu))).
      - move=> Hab.
        have Hp : (fun c => Rleb mu (R a c)) =1 (fun c => Rleb mu (R b c)).
        { move=> c; apply/RlebP/RlebP => H.
          - exact: (Htrans _ _ _ (Hsym _ _ Hab) H).
          - exact: (Htrans _ _ _ Hab H). }
        rewrite /qmu (eq_find Hp).
        apply: set_nth_default.
        by rewrite -has_find; exact: qmu_has.
    Qed.

    (* w ~_mu v iff q_mu^*(w) = q_mu^*(v) *)
    Lemma qmu_word_eq (mu : simval) (w v : word) :
      cut_value mu -> is_godelian T R \/ T mu mu = mu ->
      mu_cut mu (RwT T R) w v <-> qmu_word mu w = qmu_word mu v.
    Proof.
      move=> Hmu Hcase; have [Hmu0 Hmu1] := Hmu.
      rewrite /mu_cut /qmu_word.
      elim: w v => [|a w IH] [|b v] /=.
      - by split => // _; lra.
      - by split => //; lra.
      - by split => //; lra.
      - rewrite (RwT_cut_split _ _ _ _ Hmu Hcase) IH; split.
        + by move=> [/(qmu_eq _ _ Hmu Hcase) -> ->].
        + by case=> /(qmu_eq _ _ Hmu Hcase) Hab ->.
    Qed.

    (* ============================================================ *)
    (* Proposition 4.3: d_a^mu(L) = {w | q_mu^*(w) ∈ d_[a](([L]_mu))} *)
    (* where w ∈ d_c(K) means c w ∈ K (Definition 4.2)               *)
    (* ============================================================ *)

    Theorem fdlang_char_quotP (mu : simval) (a : A) (L : word -> Prop) (w : word) :
      cut_value mu -> is_godelian T R \/ T mu mu = mu ->
      fdlang_char mu a L w <-> quot_lang mu L (qmu mu a :: qmu_word mu w).
    Proof.
      move=> Hmu Hcase.
      rewrite (fdlang_char_cutP _ _ _ Hmu Hcase); split.
      - move=> [b [v [Hab [Hwv HL]]]].
        exists (b :: v); split => //.
        by rewrite qmu_word_cons (proj2 (qmu_eq _ _ Hmu Hcase) Hab)
                   (proj1 (qmu_word_eq _ _ Hmu Hcase) Hwv).
      - move=> [[|b v] [HL //]]; rewrite qmu_word_cons => -[Hba Hvw].
        exists b, v; split; last split => //.
        + by apply/(qmu_eq _ _ Hmu Hcase).
        + by apply/(qmu_word_eq _ _ Hmu Hcase).
    Qed.

    (* Proposition 4.3, "hence": [d_a^mu(L)]_mu = d_[a]([L]_mu) *)
    Corollary quot_fdlang_char (mu : simval) (a : A) (L : word -> Prop) (x : word) :
      cut_value mu -> is_godelian T R \/ T mu mu = mu ->
      quot_lang mu (fdlang_char mu a L) x <-> quot_lang mu L (qmu mu a :: x).
    Proof.
      move=> Hmu Hcase; split.
      - move=> [w [Hw <-]].
        exact/(fdlang_char_quotP _ _ _ Hmu Hcase).
      - move=> [[|b v] [HL //]]; rewrite qmu_word_cons => -[Hba Hvx].
        exists v; split => //.
        apply/(fdlang_char_quotP _ _ _ Hmu Hcase).
        by exists (b :: v); rewrite qmu_word_cons Hba Hvx.
    Qed.

    (* ============================================================ *)
    (* Definition 4.8(2): q_mu^* on regular expressions,            *)
    (*   q_mu^*(r[a_1,...,a_n]) = r[[a_1]_mu,...,[a_n]_mu]           *)
    (* ============================================================ *)

    Fixpoint qmu_re (mu : simval) (r : regex) : regex :=
      match r with
      | RS.Char c => RS.Char (qmu mu c)
      | RS.Alt r1 r2 => RS.Alt (qmu_re mu r1) (qmu_re mu r2)
      | RS.Seq r1 r2 => RS.Seq (qmu_re mu r1) (qmu_re mu r2)
      | RS.Star r1 => RS.Star (qmu_re mu r1)
      | RS.And r1 r2 => RS.And (qmu_re mu r1) (qmu_re mu r2)
      | RS.Neg r1 => RS.Neg (qmu_re mu r1)
      | _ => r
      end.

    (* qmu_re is the paper's r[a_1,...,a_n] |-> r[[a_1],...,[a_n]]:
       same skeleton, every letter replaced by its class *)
    Lemma qmu_re_fill (mu : simval) (r : regex) :
      qmu_re mu r = fill (skel_of r) (map (qmu mu) (syms_of r)).
    Proof.
      elim: r => [| |c|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r1 IH1|r1 IH1 r2 IH2|r1 IH1]
                   //=; try by rewrite IH1.
      all: have Hs : size (map (qmu mu) (syms_of r1)) = holes (skel_of r1)
             by rewrite size_map size_syms_of.
      all: by rewrite map_cat (take_size_cat _ Hs) (drop_size_cat _ Hs) IH1 IH2.
    Qed.

    (* for restricted r, quotienting the expression quotients its language:
       L(q_mu^*(r)) = [L(r)]_mu *)
    Lemma den_qmu_re (mu : simval) (r : regex) :
      RS.restricted_regex r ->
      forall x, RS.den (qmu_re mu r) x <-> quot_lang mu (RS.den r) x.
    Proof.
      rewrite /quot_lang /qmu_word.
      elim=> [| |c|r1 r2 _ IH1 _ IH2|r1 r2 _ IH1 _ IH2|r1 _ IH1] x /=.
      - by split => // [[w []]].
      - split => [/eqP ->|[w [/eqP -> <-]] //]; by exists [::].
      - split => [/eqP ->|[w [/eqP -> <-]]]; last exact: eqxx.
        by exists [:: c]; split => //; exact: eqxx.
      - rewrite /RS.plus /Languages.plus; split.
        + case/orP => [/IH1|/IH2] [w [Hw <-]]; exists w; by rewrite Hw ?orbT.
        + move=> [w [/orP [Hw|Hw] <-]]; apply/orP; [left; apply/IH1|right; apply/IH2];
            by exists w.
      - split.
        + move/concP => [x1 [x2 [-> [/IH1 [w1 [Hw1 <-]] /IH2 [w2 [Hw2 <-]]]]]].
          exists (w1 ++ w2); split; last by rewrite map_cat.
          by apply: concP_inv; exists w1, w2.
        + move=> [w [/concP [w1 [w2 [-> [Hw1 Hw2]]]] <-]].
          apply: concP_inv; exists (map (qmu mu) w1), (map (qmu mu) w2).
          split; first by rewrite map_cat.
          by split; [apply/IH1; exists w1 | apply/IH2; exists w2].
      - (* the blocks of a decomposition stay non-empty under renaming *)
        have Hne (ws : seq word) :
          all (preim (map (qmu mu)) (fun v => v != [::])) ws =
          all (fun v => v != [::]) ws.
        { by apply: eq_all => -[]. }
        split.
        + move/starP => [xs [Hsplit Hall]].
          have [ws [Hws Hmap]] :
            exists ws, all_in (RS.den r1) ws /\ map (map (qmu mu)) ws = xs.
          { elim: xs Hall {Hsplit} => [|x0 xs IHxs] /=; first by exists [::].
            move/andP => [/IH1 [w0 [Hw0 Hq]] /IHxs [ws [Hws <-]]].
            by exists (w0 :: ws); rewrite /= Hw0 Hws Hq. }
          exists (flatten_words ws); split.
          * apply: (starP_inv _ Hws); apply: splits_complete.
            have Hxs := splits_nonempty Hsplit.
            by rewrite -Hmap all_map Hne in Hxs.
          * by rewrite map_flatten_words Hmap; exact: splits_flatten Hsplit.
        + move=> [w [/starP [ws [Hsplit Hall]] <-]].
          apply: (starP_inv (xs := map (map (qmu mu)) ws)).
          * rewrite -(splits_flatten Hsplit) map_flatten_words.
            by apply: splits_complete; rewrite all_map Hne; exact: splits_nonempty Hsplit.
          * elim: ws Hall {Hsplit} => [//|v ws IHws] /= /andP [Hv Hws].
            by apply/andP; split; [apply/IH1; exists v | exact: IHws].
    Qed.

    (* ============================================================ *)
    (* Proposition 4.4: for restricted r,                           *)
    (*   L(D_a^mu(r)) ⊆ {w | q^*(w) ∈ L(D_[a](q^*(r)))}              *)
    (*                = {w | q^*(w) ∈ d_[a](L(q^*(r)))}               *)
    (*                = d_a^mu(L(r))                                  *)
    (* ============================================================ *)

    Theorem Dmu_char_quot (mu : simval) (a : A) (r : regex) :
      RS.restricted_regex r -> cut_value mu -> is_godelian T R \/ T mu mu = mu ->
      (forall w, RS.den (Dmu_char mu a r) w ->
         RS.den (D.D_char (qmu mu a) (qmu_re mu r)) (qmu_word mu w)) /\
      (forall w, RS.den (D.D_char (qmu mu a) (qmu_re mu r)) (qmu_word mu w) <->
         D.dlang_char (qmu mu a) (RS.den (qmu_re mu r)) (qmu_word mu w)) /\
      (forall w, D.dlang_char (qmu mu a) (RS.den (qmu_re mu r)) (qmu_word mu w) <->
         fdlang_char mu a (RS.den r) w).
    Proof.
      move=> Hr Hmu Hcase.
      have HBC w : RS.den (D.D_char (qmu mu a) (qmu_re mu r)) (qmu_word mu w) <->
                   D.dlang_char (qmu mu a) (RS.den (qmu_re mu r)) (qmu_word mu w).
      { by rewrite den_D_char. }
      have HCD w : D.dlang_char (qmu mu a) (RS.den (qmu_re mu r)) (qmu_word mu w) <->
                   fdlang_char mu a (RS.den r) w.
      { rewrite (fdlang_char_quotP _ _ _ Hmu Hcase).
        exact: (den_qmu_re mu Hr). }
      split; [|split] => // w HA.
      by apply/HBC/HCD; exact: Dmu_char_sound Hmu HA.
    Qed.

  End FuzzyDerivative.

End FuzzyDerivatives.
