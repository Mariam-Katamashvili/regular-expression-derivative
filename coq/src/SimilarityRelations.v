From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Reals Lra ClassicalEpsilon FunctionalExtensionality.

From regexderiv Require Import Languages.
From regexderiv Require Import Alphabet.
From regexderiv Require Import RegexSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.


Module SimilarityRelations (X : SYM).
  Import X.

  Module RS := RegexSemantics X.

  (* ============================================================ *)
  (* Common numeric layer (values in [0,1])                       *)
  (* ============================================================ *)

  Definition simval := R.

  (* min T-norm *)
  Definition smin (x y : simval) : simval :=
    if Rle_dec x y then x else y.

  Lemma smin_lel (x y : simval) : smin x y <= x.
  Proof.
    unfold smin; destruct (Rle_dec x y) as [Hxy|Hnxy].
    - apply Rle_refl.
    - apply Rlt_le.
      apply Rnot_le_lt.
      exact Hnxy.
  Qed.

  Lemma smin_ler (x y : simval) : smin x y <= y.
  Proof.
    unfold smin; destruct (Rle_dec x y) as [Hxy|Hnxy].
    - exact Hxy.
    - apply Rle_refl.
  Qed.

  Lemma le_smin (z x y : simval) : z <= x -> z <= y -> z <= smin x y.
  Proof.
    move=> Hzx Hzy.
    unfold smin; destruct (Rle_dec x y) as [Hxy|Hnxy].
    - exact Hzx.
    - exact Hzy.
  Qed.

  Lemma sminxx (x : simval) : smin x x = x.
  Proof.
    unfold smin; destruct (Rle_dec x x) as [Hxx|Hnxx].
    - reflexivity.
    - exfalso.
      apply Hnxx.
      apply Rle_refl.
  Qed.

  Lemma smin0l (x : simval) : 0 <= x -> smin 0 x = 0.
  Proof.
    unfold smin.
    destruct (Rle_dec 0 x) as [H|H].
    - reflexivity.
    - contradiction.
  Qed.

  Lemma smin0r (x : simval) : 0 <= x -> smin x 0 = 0.
  Proof.
    move=> Hx.
    unfold smin.
    destruct (Rle_dec x 0) as [H|H].
    - assert (x = 0) by lra.
      subst x.
      destruct (Rle_dec 0 0) as [_|Hn].
      + reflexivity.
      + exfalso. apply Hn. lra.
    - reflexivity.
  Qed.

  Lemma smin_shuffle (a b c d : simval) :
    smin (smin a b) (smin c d) <= smin (smin a c) (smin b d).
  Proof.
    apply le_smin.
    - apply le_smin.
      + eapply Rle_trans. apply smin_lel. apply smin_lel.
      + eapply Rle_trans. apply smin_ler. apply smin_lel.
    - apply le_smin.
      + eapply Rle_trans. apply smin_lel. apply smin_ler.
      + eapply Rle_trans. apply smin_ler. apply smin_ler.
  Qed.

  (* ============================================================ *)
  (* fuzzy relation, cut, proximity, similarity                   *)
  (* ============================================================ *)

  Definition in01 (x : simval) : Prop := 0 <= x <= 1.

  (* 0 < cut <= 1 *)
  Definition cut_value (mu : simval) : Prop := 0 < mu /\ mu <= 1.

  Section FuzzyRelationLayer.
    Variable S : Type.

    Definition fuzzy_rel := S -> S -> simval.

    (* R_mu := {(s1,s2) | R(s1,s2) >= mu} *)
    Definition mu_cut (mu : simval) (R : fuzzy_rel) : S -> S -> Prop :=
      fun s1 s2 => mu <= R s1 s2.

    (* proximity = reflexive + symmetric *)
    Record is_proximity (R : fuzzy_rel) : Prop := {
      prox_refl : forall s, R s s = 1;
      prox_sym  : forall s1 s2, R s1 s2 = R s2 s1
    }.

    (* similarity = proximity + transitive wrt min T-norm *)
    Record is_similarity (R : fuzzy_rel) : Prop := {
      sim_prox : is_proximity R;
      sim_trans : forall s1 s2 s,
        smin (R s1 s) (R s s2) <= R s1 s2
    }.
  End FuzzyRelationLayer.

  (* ============================================================ *)
  (* Definition A.2: T-norm                                       *)
  (* ============================================================ *)

  (* A T-norm is an operation on [0,1]; on simval = R its laws are
     required only for arguments in [0,1]. *)
  Record tnorm : Type := TNorm {
    tn_op :> simval -> simval -> simval;
    tn_in01  : forall x y, in01 x -> in01 y -> in01 (tn_op x y);
    tn_comm  : forall x y, in01 x -> in01 y -> tn_op x y = tn_op y x;
    tn_assoc : forall x y z, in01 x -> in01 y -> in01 z ->
      tn_op (tn_op x y) z = tn_op x (tn_op y z);
    tn_mono  : forall x y z, in01 x -> in01 y -> in01 z ->
      x <= y -> tn_op x z <= tn_op y z;
    tn_unit  : forall x, in01 x -> tn_op x 1 = x
  }.

  Section TNormFacts.
    Variable T : tnorm.

    Lemma tn_mono_r (x y z : simval) :
      in01 x -> in01 y -> in01 z -> x <= y -> T z x <= T z y.
    Proof.
      move=> Hx Hy Hz Hxy.
      rewrite (@tn_comm T z x Hz Hx) (@tn_comm T z y Hz Hy).
      exact: (@tn_mono T x y z Hx Hy Hz Hxy).
    Qed.

    Lemma tn_mono2 (x x' y y' : simval) :
      in01 x -> in01 x' -> in01 y -> in01 y' ->
      x <= x' -> y <= y' -> T x y <= T x' y'.
    Proof.
      move=> Hx Hx' Hy Hy' Hxx' Hyy'.
      apply: (Rle_trans _ (T x' y)).
      - exact: (@tn_mono T x x' y Hx Hx' Hy Hxx').
      - exact: (@tn_mono_r y y' x' Hy Hy' Hx' Hyy').
    Qed.

    (* An idempotent x is below x ⊗ y for every y >= x. *)
    Lemma tn_idem_le (x y : simval) :
      in01 x -> in01 y -> T x x = x -> x <= y -> x <= T x y.
    Proof.
      move=> Hx Hy Hidem Hxy.
      have H := @tn_mono_r x y x Hx Hy Hx Hxy.
      rewrite Hidem in H.
      exact H.
    Qed.

    (* x ⊗ y > 0 forces x > 0 and y > 0. *)
    Lemma tn_pos (x y : simval) :
      in01 x -> in01 y -> 0 < T x y -> 0 < x /\ 0 < y.
    Proof.
      move=> Hx Hy Hpos.
      have H0 : in01 0 by split; lra.
      have H1 : in01 1 by split; lra.
      have Hz : forall z, in01 z -> T 0 z <= 0.
      { move=> z Hz.
        apply: (Rle_trans _ (T 0 1)).
        - apply: (@tn_mono_r z 1 0 Hz H1 H0).
          by case: Hz.
        - rewrite (@tn_unit T 0 H0).
          exact: Rle_refl. }
      have [Hx0 _] := Hx.
      have [Hy0 _] := Hy.
      split.
      - case: (Rle_lt_or_eq_dec 0 x Hx0) => // Hx_eq.
        rewrite -Hx_eq in Hpos.
        have := Hz y Hy.
        lra.
      - case: (Rle_lt_or_eq_dec 0 y Hy0) => // Hy_eq.
        rewrite -Hy_eq (@tn_comm T x 0 Hx H0) in Hpos.
        have := Hz x Hx.
        lra.
    Qed.
  End TNormFacts.

  (* ============================================================ *)
  (* Definition 3.1: T-similarity, godelian; Lemma 3.1            *)
  (* ============================================================ *)

  Section TSimilarityLayer.
    Variable S : Type.
    Variable T : tnorm.

    (* Definition 3.1(1),(4): values in [0,1], reflexive, symmetric,
       reverse triangle inequality wrt T *)
    Record is_T_similarity (R : fuzzy_rel S) : Prop := {
      tsim_range : forall s1 s2, in01 (R s1 s2);
      tsim_prox  : is_proximity R;
      tsim_trans : forall s1 s2 s, T (R s1 s) (R s s2) <= R s1 s2
    }.

    (* Definition 3.1(6) *)
    Definition is_godelian (R : fuzzy_rel S) : Prop :=
      forall s1 s2, R s1 s2 = T (R s1 s2) (R s1 s2).

    (* Lemma 3.1(1) *)
    Lemma T_equivalence_idem (R : fuzzy_rel S) (mu : simval) :
      is_T_similarity R -> cut_value mu -> T mu mu = mu ->
      Relation_Definitions.equivalence S (mu_cut mu R).
    Proof.
      move=> [Hrange [Hrefl Hsym] Htrans] [Hmu0 Hmu1] Hidem.
      have Hmu : in01 mu by split; lra.
      split.
      - move=> s.
        rewrite /mu_cut Hrefl.
        exact Hmu1.
      - move=> s1 s s2; rewrite /mu_cut => H1 H2.
        rewrite -Hidem.
        apply: (Rle_trans _ (T (R s1 s) (R s s2))); last exact: Htrans.
        exact: (@tn_mono2 T mu (R s1 s) mu (R s s2)
                  Hmu (Hrange s1 s) Hmu (Hrange s s2) H1 H2).
      - move=> s1 s2 H.
        rewrite /mu_cut Hsym.
        exact H.
    Qed.

    (* Lemma 3.1(2) *)
    Lemma T_equivalence_godelian (R : fuzzy_rel S) (mu : simval) :
      is_T_similarity R -> is_godelian R -> cut_value mu ->
      Relation_Definitions.equivalence S (mu_cut mu R).
    Proof.
      move=> [Hrange [Hrefl Hsym] Htrans] Hgod [Hmu0 Hmu1].
      split.
      - move=> s.
        rewrite /mu_cut Hrefl.
        exact Hmu1.
      - move=> s1 s s2; rewrite /mu_cut => H1 H2.
        apply: (Rle_trans _ (T (R s1 s) (R s s2))); last exact: Htrans.
        have Hx := Hrange s1 s.
        have Hy := Hrange s s2.
        destruct (Rle_dec (R s1 s) (R s s2)) as [Hxy|Hnxy].
        + apply: (Rle_trans _ (R s1 s) _ H1).
          exact: (@tn_idem_le T (R s1 s) (R s s2)
                    Hx Hy (esym (Hgod s1 s)) Hxy).
        + have Hyx : R s s2 <= R s1 s.
          { apply Rlt_le. apply Rnot_le_lt. exact Hnxy. }
          apply: (Rle_trans _ (R s s2) _ H2).
          rewrite (@tn_comm T (R s1 s) (R s s2) Hx Hy).
          exact: (@tn_idem_le T (R s s2) (R s1 s)
                    Hy Hx (esym (Hgod s s2)) Hyx).
      - move=> s1 s2 H.
        rewrite /mu_cut Hsym.
        exact H.
    Qed.
  End TSimilarityLayer.


  Definition word := RS.word.
  Definition language := RS.language.
  Definition regex := RS.regex.

  (* ============================================================ *)
  (* Base assumptions: a similarity R on symbols A×A              *)
  (* ============================================================ *)

  Section BaseSymbolSimilarity.

    Variable R : A -> A -> simval.

    Hypothesis R_range : forall a b, 0 <= R a b <= 1.    
    Hypothesis R_refl  : forall a, R a a = 1.
    Hypothesis R_sym   : forall a b, R a b = R b a.
    Hypothesis R_trans : forall a b c, smin (R a b) (R b c) <= R a c.

    (* ============================================================ *)
    (* Definition 3.2 (R^ω): similarity on words                    *)
    (* ============================================================ *)

    Fixpoint Rw (w1 w2 : word) : simval :=
      match w1, w2 with
      | [::], [::] => 1
      | [::], _    => 0
      | _   , [::] => 0
      | a1 :: t1, a2 :: t2 =>
          smin (R a1 a2) (Rw t1 t2)
      end.

    (* Helper: Rw stays in [0,1]. *)
    Lemma Rw_range : forall w1 w2, 0 <= Rw w1 w2 <= 1.
    Proof.
      elim=> [|a1 t1 IH] [|a2 t2] //=; try lra.
      have [H01a_lo H01a_hi] := R_range a1 a2.
      have [H01t_lo H01t_hi] := IH t2.
      split.
      - apply: le_smin; assumption.
      - eapply Rle_trans.
        + apply smin_lel.
        + exact H01a_hi.
    Qed.

    (* ============================================================ *)
    (* Lemma 3.3(2), min T-norm: R^ω is a similarity                *)
    (* ============================================================ *)

    Lemma Rw_refl : forall w, Rw w w = 1.
    Proof.
      elim=> [|a w IH] //=.
      by rewrite R_refl IH sminxx.
    Qed.

    Lemma Rw_sym : forall w1 w2, Rw w1 w2 = Rw w2 w1.
    Proof.
      elim=> [|a1 t1 IH] [|a2 t2] //=.
      by rewrite R_sym IH.
    Qed.

    Lemma Rw_trans : forall w1 w2 w,
      smin (Rw w1 w) (Rw w w2) <= Rw w1 w2.
    Proof.
      induction w1 as [|a1 t1 IH]; intros w2 w.
      - destruct w2 as [|a2 t2]; destruct w as [|a t]; simpl.
        + rewrite sminxx. apply Rle_refl.
        + rewrite sminxx. lra.
        + apply smin_ler.
        + apply smin_lel.
      - destruct w2 as [|a2 t2].
        + destruct w as [|a t]; simpl.
          * apply smin_lel.
          * apply smin_ler.
        + destruct w as [|a t]; simpl.
          * have [H0a _] := R_range a1 a2.
            have [H0t _] := Rw_range t1 t2.
            rewrite sminxx.
            apply le_smin; assumption.
          * have Hhead : smin (R a1 a) (R a a2) <= R a1 a2 := R_trans a1 a a2.
            have Htail : smin (Rw t1 t) (Rw t t2) <= Rw t1 t2 := IH t2 t.
            have Hsh :
              smin (smin (R a1 a) (Rw t1 t)) (smin (R a a2) (Rw t t2))
                <= smin (smin (R a1 a) (R a a2)) (smin (Rw t1 t) (Rw t t2)).
            { exact (smin_shuffle _ _ _ _). }
            eapply Rle_trans.
            { exact Hsh. }
            apply le_smin.
            - eapply Rle_trans. apply smin_lel. exact Hhead.
            - eapply Rle_trans. apply smin_ler. exact Htail.
    Qed.

    Record is_similarity_on_words : Prop := {
      Rw_is_reflexive : forall w, Rw w w = 1;
      Rw_is_symmetric : forall w1 w2, Rw w1 w2 = Rw w2 w1;
      Rw_is_transitive : forall w1 w2 w,
        smin (Rw w1 w) (Rw w w2) <= Rw w1 w2
    }.

    Lemma Rw_is_similarity : is_similarity_on_words.
    Proof.
      split; [exact: Rw_refl | exact: Rw_sym | exact: Rw_trans].
    Qed.

    (* ============================================================ *)
    (* Definition 3.3 (R^L): similarity on languages                *)
    (* ============================================================ *)

    Definition lang_nonempty (L : language) : Prop :=
      exists w, L w = true.

    Definition upper_bounded_on (L : language) (f : word -> simval) : Prop :=
      exists M, forall w, L w = true -> f w <= M.

    Definition lower_bounded_on (L : language) (f : word -> simval) : Prop :=
      exists m, forall w, L w = true -> m <= f w.

    Definition lang_image (L : language) (f : word -> simval) : simval -> Prop :=
      fun y => exists w, L w = true /\ y = f w.

    Lemma lang_image_nonempty (L : language) (f : word -> simval) :
      lang_nonempty L -> exists y, lang_image L f y.
    Proof.
      intros [w Hw].
      exists (f w).
      exists w; split; [exact Hw | reflexivity].
    Qed.

    Lemma lang_image_upper_bound (L : language) (f : word -> simval) :
      upper_bounded_on L f -> exists M, is_upper_bound (lang_image L f) M.
    Proof.
      intros [M HM].
      exists M.
      intros y [w [Hw ->]].
      apply HM; exact Hw.
    Qed.

    Lemma Rw_upper_bounded_right (w1 : word) (L : language) :
      upper_bounded_on L (fun w2 => Rw w1 w2).
    Proof.
      exists 1.
      intros w2 _.
      destruct (Rw_range w1 w2) as [_ H].
      exact H.
    Qed.

    Lemma Rw_upper_bounded_left (w2 : word) (L : language) :
      upper_bounded_on L (fun w1 => Rw w1 w2).
    Proof.
      exists 1.
      intros w1 _.
      destruct (Rw_range w1 w2) as [_ H].
      exact H.
    Qed.

    Definition SupL (L : language) (f : word -> simval)
      (Hub : upper_bounded_on L f) : simval :=
      match excluded_middle_informative (lang_nonempty L) with
      | left Hne =>
          proj1_sig
            (completeness (lang_image L f)
              (@lang_image_upper_bound L f Hub)
              (@lang_image_nonempty L f Hne))
      | right _ => 0
      end.

    Lemma SupL_is_lub :
      forall (L : language) (f : word -> simval) (Hub : upper_bounded_on L f),
        lang_nonempty L ->
        is_lub (lang_image L f) (@SupL L f Hub).
    Proof.
      intros L f Hub Hne.
      unfold SupL.
      destruct (excluded_middle_informative (lang_nonempty L)) as [H|H].
      - exact
          (proj2_sig
             (completeness (lang_image L f)
               (@lang_image_upper_bound L f Hub)
               (@lang_image_nonempty L f H))).
      - contradiction.
    Qed.

    Lemma SupL_upper :
      forall (L : language) (f : word -> simval) (Hub : upper_bounded_on L f) w,
        L w = true ->
        f w <= @SupL L f Hub.
    Proof.
      intros L f Hub w Hw.
      destruct (excluded_middle_informative (lang_nonempty L)) as [Hne|Hempty].
      - pose proof (proj1 (@SupL_is_lub L f Hub Hne)) as Hupper.
        apply Hupper.
        exists w; split; [exact Hw | reflexivity].
      - exfalso. apply Hempty. exists w. exact Hw.
    Qed.

    Lemma SupL_nonneg :
      forall (L : language) (f : word -> simval) (Hub : upper_bounded_on L f),
        (forall w, L w = true -> 0 <= f w) ->
        0 <= @SupL L f Hub.
    Proof.
      intros L f Hub Hnonneg.
      destruct (excluded_middle_informative (lang_nonempty L)) as [Hne|Hempty].
      - destruct Hne as [w Hw].
        eapply Rle_trans.
        + apply Hnonneg; exact Hw.
        + apply SupL_upper; exact Hw.
      - unfold SupL.
        destruct (excluded_middle_informative (lang_nonempty L)) as [H|H]; [contradiction|].
        lra.
    Qed.

    Lemma neg_upper_bounded_on :
      forall L f,
        lower_bounded_on L f ->
        upper_bounded_on L (fun w => - f w).
    Proof.
      intros L f [m Hm].
      exists (-m).
      intros w Hw.
      specialize (Hm w Hw).
      lra.
    Qed.

    Definition InfL (L : language) (f : word -> simval)
      (Hlb : lower_bounded_on L f) : simval :=
      match excluded_middle_informative (lang_nonempty L) with
      | left _  => - @SupL L (fun w => - f w) (@neg_upper_bounded_on L f Hlb)
      | right _ => 1
      end.

    Lemma InfL_lower :
      forall (L : language) (f : word -> simval) (Hlb : lower_bounded_on L f) w,
        L w = true ->
        @InfL L f Hlb <= f w.
    Proof.
      intros L f Hlb w Hw.
      unfold InfL.
      destruct (excluded_middle_informative (lang_nonempty L)) as [Hne|Hempty].
      - pose proof
          (@SupL_upper L (fun u => - f u) (@neg_upper_bounded_on L f Hlb) w Hw) as H.
        lra.
      - exfalso. apply Hempty. exists w. exact Hw.
    Qed.

    Lemma smin_comm (x y : simval) : smin x y = smin y x.
    Proof.
      unfold smin.
      destruct (Rle_dec x y) as [Hxy|Hnxy];
      destruct (Rle_dec y x) as [Hyx|Hnyx].
      - apply Rle_antisym; assumption.
      - reflexivity.
      - reflexivity.
      - exfalso.
        apply Hnxy.
        apply Rlt_le.
        apply Rnot_le_lt.
        exact Hnyx.
    Qed.

    Lemma smin_mono (a b a' b' : simval) :
      a <= a' -> b <= b' -> smin a b <= smin a' b'.
    Proof.
      intros Ha Hb.
      apply le_smin.
      - eapply Rle_trans. apply smin_lel. exact Ha.
      - eapply Rle_trans. apply smin_ler. exact Hb.
    Qed.

    Lemma SupL_empty :
      forall (L : language) (f : word -> simval) (Hub : upper_bounded_on L f),
        ~ lang_nonempty L ->
        @SupL L f Hub = 0.
    Proof.
      intros L f Hub Hempty.
      unfold SupL.
      destruct (excluded_middle_informative (lang_nonempty L)) as [H|H].
      - contradiction.
      - reflexivity.
    Qed.

    Lemma InfL_empty :
      forall (L : language) (f : word -> simval) (Hlb : lower_bounded_on L f),
        ~ lang_nonempty L ->
        @InfL L f Hlb = 1.
    Proof.
      intros L f Hlb Hempty.
      unfold InfL.
      destruct (excluded_middle_informative (lang_nonempty L)) as [H|H].
      - contradiction.
      - reflexivity.
    Qed.

    Lemma SupL_least_nonempty :
      forall (L : language) (f : word -> simval) (Hub : upper_bounded_on L f) M,
        lang_nonempty L ->
        (forall w, L w = true -> f w <= M) ->
        @SupL L f Hub <= M.
    Proof.
      intros L f Hub M Hne Hbound.
      pose proof (proj2 (@SupL_is_lub L f Hub Hne)) as Hleast.
      apply Hleast.
      intros y [w [Hw ->]].
      apply Hbound; exact Hw.
    Qed.

    Lemma SupL_mono_nonempty :
      forall (L : language) (f g : word -> simval)
             (Hubf : upper_bounded_on L f) (Hubg : upper_bounded_on L g),
        lang_nonempty L ->
        (forall w, L w = true -> f w <= g w) ->
        @SupL L f Hubf <= @SupL L g Hubg.
    Proof.
      intros L f g Hubf Hubg Hne Hfg.
      eapply (@SupL_least_nonempty L f Hubf (@SupL L g Hubg) Hne).
      intros w Hw.
      eapply Rle_trans.
      - apply Hfg; exact Hw.
      - apply (@SupL_upper L g Hubg w Hw).
    Qed.

    Lemma SupL_eq_ext :
      forall (L : language) (f g : word -> simval)
             (Hubf : upper_bounded_on L f) (Hubg : upper_bounded_on L g),
        (forall w, L w = true -> f w = g w) ->
        @SupL L f Hubf = @SupL L g Hubg.
    Proof.
      intros L f g Hubf Hubg Heq.
      destruct (excluded_middle_informative (lang_nonempty L)) as [Hne|Hempty].
      - apply Rle_antisym.
        + eapply (@SupL_least_nonempty L f Hubf (@SupL L g Hubg) Hne).
          intros w Hw.
          have Heqw : f w = g w by apply Heq; exact Hw.
          rewrite Heqw.
          apply (@SupL_upper L g Hubg w Hw).
        + eapply (@SupL_least_nonempty L g Hubg (@SupL L f Hubf) Hne).
          intros w Hw.
          have Heqw : f w = g w by apply Heq; exact Hw.
          rewrite -Heqw.
          apply (@SupL_upper L f Hubf w Hw).
      - rewrite (@SupL_empty L f Hubf Hempty).
        rewrite (@SupL_empty L g Hubg Hempty).
        reflexivity.
    Qed.

    Lemma InfL_eq_ext :
      forall (L : language) (f g : word -> simval)
             (Hlbf : lower_bounded_on L f) (Hlbg : lower_bounded_on L g),
        (forall w, L w = true -> f w = g w) ->
        @InfL L f Hlbf = @InfL L g Hlbg.
    Proof.
      intros L f g Hlbf Hlbg Heq.
      unfold InfL.
      destruct (excluded_middle_informative (lang_nonempty L)) as [Hne|Hempty].
      - f_equal.
        apply SupL_eq_ext.
        intros w Hw.
        have Heqw : f w = g w by apply Heq; exact Hw.
        rewrite Heqw.
        reflexivity.
      - destruct (excluded_middle_informative (lang_nonempty L)) as [H|H].
        + contradiction.
        + destruct (excluded_middle_informative (lang_nonempty L)) as [H'|H'].
          * contradiction.
          * reflexivity.
    Qed.

    Lemma SupL_nonempty_witness :
      forall (L : language) (f : word -> simval) (Hub : upper_bounded_on L f) s,
        lang_nonempty L ->
        s < @SupL L f Hub ->
        exists w, L w = true /\ s < f w.
    Proof.
      intros L f Hub s Hne Hlt.
      destruct (excluded_middle_informative (exists w, L w = true /\ s < f w)) as [Hex|Hno].
      - exact Hex.
      - exfalso.
        apply (Rlt_irrefl (@SupL L f Hub)).
        eapply Rle_lt_trans.
        + eapply (@SupL_least_nonempty L f Hub s Hne).
          intros w Hw.
          destruct (excluded_middle_informative (s < f w)) as [Hs|Hs].
          * exfalso. apply Hno. exists w. split; assumption.
          * lra.
        + exact Hlt.
    Qed.

    Lemma upper_bounded_on_smin_const :
      forall (L : language) (f : word -> simval)
             (Hub : upper_bounded_on L f) c,
        upper_bounded_on L (fun w => smin (f w) c).
    Proof.
      intros L f [M HM] c.
      exists M.
      intros w Hw.
      eapply Rle_trans.
      - apply smin_lel.
      - apply HM; exact Hw.
    Qed.

    Lemma InfL_greatest_nonempty :
      forall (L : language) (f : word -> simval)
             (Hlb : lower_bounded_on L f) m,
        lang_nonempty L ->
        (forall w, L w = true -> m <= f w) ->
        m <= @InfL L f Hlb.
    Proof.
      intros L f Hlb m Hne Hm.
      unfold InfL.
      destruct (excluded_middle_informative (lang_nonempty L)) as [H|H].
      - assert (HS :
          @SupL L (fun w => - f w) (@neg_upper_bounded_on L f Hlb) <= - m).
        {
          eapply (@SupL_least_nonempty
                    L (fun w => - f w) (@neg_upper_bounded_on L f Hlb) (- m) H).
          intros w Hw.
          specialize (Hm w Hw).
          lra.
        }
        lra.
      - contradiction.
    Qed.

    Lemma SupL_in01 :
      forall (L : language) (f : word -> simval) (Hub : upper_bounded_on L f),
        (forall w, L w = true -> 0 <= f w <= 1) ->
        0 <= @SupL L f Hub <= 1.
    Proof.
      intros L f Hub H01.
      split.
      - apply SupL_nonneg.
        intros w Hw.
        specialize (H01 w Hw).
        lra.
      - destruct (excluded_middle_informative (lang_nonempty L)) as [Hne|Hempty].
        + eapply (@SupL_least_nonempty L f Hub 1 Hne).
          intros w Hw.
          specialize (H01 w Hw).
          lra.
        + rewrite (@SupL_empty L f Hub Hempty).
          lra.
    Qed.

    Lemma InfL_in01 :
      forall (L : language) (f : word -> simval) (Hlb : lower_bounded_on L f),
        (forall w, L w = true -> 0 <= f w <= 1) ->
        0 <= @InfL L f Hlb <= 1.
    Proof.
      intros L f Hlb H01.
      destruct (excluded_middle_informative (lang_nonempty L)) as [Hne|Hempty].
      - split.
        + eapply (@InfL_greatest_nonempty L f Hlb 0 Hne).
          intros w Hw.
          specialize (H01 w Hw).
          lra.
        + destruct Hne as [w Hw].
          eapply Rle_trans.
          * apply (@InfL_lower L f Hlb w Hw).
          * specialize (H01 w Hw).
            lra.
      - rewrite (@InfL_empty L f Hlb Hempty).
        lra.
    Qed.

    Lemma InfL_const_nonempty :
      forall (L : language) (f : word -> simval)
             (Hlb : lower_bounded_on L f) c,
        lang_nonempty L ->
        (forall w, L w = true -> f w = c) ->
        @InfL L f Hlb = c.
    Proof.
      intros L f Hlb c Hne Hconst.
      apply Rle_antisym.
      - destruct Hne as [w Hw].
        rewrite -(Hconst w Hw).
        apply (@InfL_lower L f Hlb w Hw).
      - eapply (@InfL_greatest_nonempty L f Hlb c Hne).
        intros w Hw.
        rewrite (Hconst w Hw).
        lra.
    Qed.

    Lemma SupL_Rw_self_right (L : language) (w : word) :
      L w = true ->
      @SupL L (fun w2 => Rw w w2) (Rw_upper_bounded_right w L) = 1.
    Proof.
      intros Hw.
      apply Rle_antisym.
      - eapply (@SupL_least_nonempty L (fun w2 => Rw w w2)
                  (Rw_upper_bounded_right w L) 1).
        + exists w. exact Hw.
        + intros w2 Hw2.
          exact (proj2 (Rw_range w w2)).
      - rewrite <- (Rw_refl w).
        apply (@SupL_upper L (fun w2 => Rw w w2) (Rw_upper_bounded_right w L) w Hw).
    Qed.

    Lemma SupL_Rw_self_left (L : language) (w : word) :
      L w = true ->
      @SupL L (fun w1 => Rw w1 w) (Rw_upper_bounded_left w L) = 1.
    Proof.
      intros Hw.
      apply Rle_antisym.
      - eapply (@SupL_least_nonempty L (fun w1 => Rw w1 w)
                  (Rw_upper_bounded_left w L) 1).
        + exists w. exact Hw.
        + intros w1 Hw1.
          exact (proj2 (Rw_range w1 w)).
      - rewrite <- (Rw_refl w).
        apply (@SupL_upper L (fun w1 => Rw w1 w) (Rw_upper_bounded_left w L) w Hw).
    Qed.

    Lemma SupL_smin_const_nonempty :
      forall (L : language) (f : word -> simval)
             (Hub : upper_bounded_on L f) c,
        lang_nonempty L ->
        0 <= c <= 1 ->
        smin (@SupL L f Hub) c
          <= @SupL L (fun w => smin (f w) c)
               (@upper_bounded_on_smin_const L f Hub c).
    Proof.
      intros L f Hub c Hne Hc.
      destruct (Rle_dec (@SupL L f Hub) c) as [Hle|Hnle].
      - assert (Heq :
          forall w, L w = true -> f w = smin (f w) c).
        {
          intros w Hw.
          apply Rle_antisym.
          - unfold smin.
            destruct (Rle_dec (f w) c) as [Hfw|Hfw].
            + apply Rle_refl.
            + exfalso. apply Hfw.
              eapply Rle_trans.
              * apply (@SupL_upper L f Hub w Hw).
              * exact Hle.
          - apply smin_lel.
        }
        rewrite <- (@SupL_eq_ext
                      L f (fun w => smin (f w) c)
                      Hub (@upper_bounded_on_smin_const L f Hub c) Heq).
        unfold smin.
        destruct (Rle_dec (@SupL L f Hub) c) as [H|H].
        + apply Rle_refl.
        + contradiction.
      - assert (Hlt : c < @SupL L f Hub).
        { apply Rnot_le_lt. exact Hnle. }
        destruct (@SupL_nonempty_witness L f Hub c Hne Hlt) as [w [Hw Hwc]].
        unfold smin.
        destruct (Rle_dec (@SupL L f Hub) c) as [H|H].
        + lra.
        + simpl.
          eapply (Rle_trans _ (smin (f w) c) _).
          * 
            unfold smin.
            destruct (Rle_dec (f w) c) as [Hfw|Hfw].
            -- exfalso. lra.
            -- apply Rle_refl.
          * apply (@SupL_upper
                     L (fun u => smin (f u) c)
                     (@upper_bounded_on_smin_const L f Hub c) w Hw).
    Qed.

    Lemma sup_Rw_in01_left (L : language) (w1 : word) :
      0 <= @SupL L (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L) <= 1.
    Proof.
      apply SupL_in01.
      intros w2 Hw2.
      apply Rw_range.
    Qed.

    Lemma sup_Rw_in01_right (L : language) (w2 : word) :
      0 <= @SupL L (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L) <= 1.
    Proof.
      apply SupL_in01.
      intros w1 Hw1.
      apply Rw_range.
    Qed.

    Lemma outer_lower_bounded_left (L1 L2 : language) :
      lower_bounded_on L1
        (fun w1 => @SupL L2 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L2)).
    Proof.
      exists 0.
      intros w1 _.
      apply SupL_nonneg.
      intros w2 _.
      exact (proj1 (Rw_range w1 w2)).
    Qed.

    Lemma outer_lower_bounded_right (L1 L2 : language) :
      lower_bounded_on L2
        (fun w2 => @SupL L1 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L1)).
    Proof.
      exists 0.
      intros w2 _.
      apply SupL_nonneg.
      intros w1 _.
      exact (proj1 (Rw_range w1 w2)).
    Qed.

    Definition RL (L1 L2 : language) : simval :=
      smin
        (@InfL L1
          (fun w1 => @SupL L2 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L2))
          (outer_lower_bounded_left L1 L2))
        (@InfL L2
          (fun w2 => @SupL L1 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L1))
          (outer_lower_bounded_right L1 L2)).

    Lemma RL_empty_empty :
      forall L1 L2,
        ~ lang_nonempty L1 ->
        ~ lang_nonempty L2 ->
        RL L1 L2 = 1.
    Proof.
      intros L1 L2 Hempty1 Hempty2.
      unfold RL.
      rewrite (@InfL_empty
                L1
                (fun w1 => @SupL L2 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L2))
                (outer_lower_bounded_left L1 L2) Hempty1).
      rewrite (@InfL_empty
                L2
                (fun w2 => @SupL L1 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L1))
                (outer_lower_bounded_right L1 L2) Hempty2).
      apply sminxx.
    Qed.

    Lemma RL_in01 :
      forall (L1 L2 : language), 0 <= RL L1 L2 <= 1.
    Proof.
      intros L1 L2.
      unfold RL.
      split.
      - apply le_smin.
        + apply InfL_in01.
          intros w1 Hw1.
          apply sup_Rw_in01_left.
        + apply InfL_in01.
          intros w2 Hw2.
          apply sup_Rw_in01_right.
      - eapply Rle_trans.
        + apply smin_lel.
        + apply InfL_in01.
          intros w1 Hw1.
          apply sup_Rw_in01_left.
    Qed.

    Lemma RL_refl :
      forall L, RL L L = 1.
    Proof.
      intros L.
      destruct (excluded_middle_informative (lang_nonempty L)) as [Hne|Hempty].
      - unfold RL.
        rewrite (@InfL_const_nonempty
                  L
                  (fun w1 => @SupL L (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L))
                  (outer_lower_bounded_left L L) 1 Hne).
        2:{ intros w Hw. apply SupL_Rw_self_right. exact Hw. }
        rewrite (@InfL_const_nonempty
                  L
                  (fun w2 => @SupL L (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L))
                  (outer_lower_bounded_right L L) 1 Hne).
        2:{ intros w Hw. apply SupL_Rw_self_left. exact Hw. }
        apply sminxx.
      - apply RL_empty_empty; assumption.
    Qed.

    Lemma RL_sym :
      forall L1 L2, RL L1 L2 = RL L2 L1.
    Proof.
      intros L1 L2.
      unfold RL.
      assert (H1 :
        @InfL L1
          (fun w1 => @SupL L2 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L2))
          (outer_lower_bounded_left L1 L2)
        =
        @InfL L1
          (fun w2 => @SupL L2 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L2))
          (outer_lower_bounded_right L2 L1)).
      {
        apply InfL_eq_ext.
        intros w Hw.
        apply SupL_eq_ext.
        intros u Hu.
        apply Rw_sym.
      }
      assert (H2 :
        @InfL L2
          (fun w2 => @SupL L1 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L1))
          (outer_lower_bounded_right L1 L2)
        =
        @InfL L2
          (fun w1 => @SupL L1 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L1))
          (outer_lower_bounded_left L2 L1)).
      {
        apply InfL_eq_ext.
        intros w Hw.
        apply SupL_eq_ext.
        intros u Hu.
        apply Rw_sym.
      }
      rewrite H1 H2.
      rewrite smin_comm.
      reflexivity.
    Qed.

    Lemma RL_empty_nonempty_left :
      forall L1 L2,
        ~ lang_nonempty L1 ->
        lang_nonempty L2 ->
        RL L1 L2 = 0.
    Proof.
      intros L1 L2 Hempty1 Hne2.
      unfold RL.
      rewrite (@InfL_empty
                 L1
                 (fun w1 => @SupL L2 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L2))
                 (outer_lower_bounded_left L1 L2) Hempty1).
      assert (Hconst :
        forall w2, L2 w2 = true ->
          @SupL L1 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L1) = 0).
      {
        intros w2 Hw2.
        apply SupL_empty.
        exact Hempty1.
      }
      rewrite (@InfL_const_nonempty
                 L2
                 (fun w2 => @SupL L1 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L1))
                 (outer_lower_bounded_right L1 L2) 0 Hne2 Hconst).
      unfold smin.
      destruct (Rle_dec 1 0) as [H10|Hn10].
      - lra.
      - reflexivity.
    Qed.

    Lemma RL_empty_nonempty_right :
      forall L1 L2,
        lang_nonempty L1 ->
        ~ lang_nonempty L2 ->
        RL L1 L2 = 0.
    Proof.
      intros L1 L2 Hne1 Hempty2.
      rewrite RL_sym.
      apply RL_empty_nonempty_left; assumption.
    Qed.

    Lemma bridge_left_nonempty :
      forall L2 L3 w1,
        lang_nonempty L2 ->
        lang_nonempty L3 ->
        smin
          (@SupL L2 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L2))
          (@InfL L2
             (fun w2 => @SupL L3 (fun w3 => Rw w2 w3) (Rw_upper_bounded_right w2 L3))
             (outer_lower_bounded_left L2 L3))
        <=
        @SupL L3 (fun w3 => Rw w1 w3) (Rw_upper_bounded_right w1 L3).
    Proof.
      intros L2 L3 w1 Hne2 Hne3.
      set (a23 :=
        @InfL L2
          (fun w2 => @SupL L3 (fun w3 => Rw w2 w3) (Rw_upper_bounded_right w2 L3))
          (outer_lower_bounded_left L2 L3)).
      assert (Ha23 : 0 <= a23 <= 1).
      {
        unfold a23.
        apply InfL_in01.
        intros w2 Hw2.
        apply sup_Rw_in01_left.
      }
      eapply Rle_trans.
      - apply (@SupL_smin_const_nonempty
                 L2 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L2)
                 a23 Hne2 Ha23).
      - eapply (@SupL_least_nonempty
                  L2 (fun w2 => smin (Rw w1 w2) a23)
                  (@upper_bounded_on_smin_const L2 (fun w2 => Rw w1 w2)
                     (Rw_upper_bounded_right w1 L2) a23)
                  (@SupL L3 (fun w3 => Rw w1 w3) (Rw_upper_bounded_right w1 L3))
                  Hne2).
        intros w2 Hw2.
        assert (Ha23_le :
          a23 <= @SupL L3 (fun w3 => Rw w2 w3) (Rw_upper_bounded_right w2 L3)).
        {
          unfold a23.
          apply (@InfL_lower
                   L2
                   (fun w2 => @SupL L3 (fun w3 => Rw w2 w3) (Rw_upper_bounded_right w2 L3))
                   (outer_lower_bounded_left L2 L3) w2 Hw2).
        }
        eapply Rle_trans.
        + apply smin_mono.
          * apply Rle_refl.
          * exact Ha23_le.
        + rewrite smin_comm.
          eapply Rle_trans.
          * apply (@SupL_smin_const_nonempty
                     L3 (fun w3 => Rw w2 w3) (Rw_upper_bounded_right w2 L3)
                     (Rw w1 w2) Hne3).
            apply Rw_range.
          * apply (@SupL_mono_nonempty
                     L3
                     (fun w3 => smin (Rw w2 w3) (Rw w1 w2))
                     (fun w3 => Rw w1 w3)
                     (@upper_bounded_on_smin_const L3 (fun w3 => Rw w2 w3)
                        (Rw_upper_bounded_right w2 L3) (Rw w1 w2))
                     (Rw_upper_bounded_right w1 L3)
                     Hne3).
            intros w3 Hw3.
            rewrite smin_comm.
            apply (Rw_trans w1 w3 w2).
    Qed.

    Lemma bridge_right_nonempty :
      forall L1 L2 w3,
        lang_nonempty L1 ->
        lang_nonempty L2 ->
        smin
          (@InfL L2
            (fun w2 => @SupL L1 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L1))
            (outer_lower_bounded_right L1 L2))
          (@SupL L2 (fun w2 => Rw w2 w3) (Rw_upper_bounded_left w3 L2))
        <=
        @SupL L1 (fun w1 => Rw w1 w3) (Rw_upper_bounded_left w3 L1).
    Proof.
      intros L1 L2 w3 Hne1 Hne2.
      assert (HS2 :
        @SupL L2 (fun w2 => Rw w2 w3) (Rw_upper_bounded_left w3 L2)
        =
        @SupL L2 (fun w2 => Rw w3 w2) (Rw_upper_bounded_right w3 L2)).
      {
        apply SupL_eq_ext.
        intros w2 Hw2.
        apply Rw_sym.
      }
      assert (HI :
        @InfL L2
          (fun w2 => @SupL L1 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L1))
          (outer_lower_bounded_right L1 L2)
        =
        @InfL L2
          (fun w2 => @SupL L1 (fun w1 => Rw w2 w1) (Rw_upper_bounded_right w2 L1))
          (outer_lower_bounded_left L2 L1)).
      {
        apply InfL_eq_ext.
        intros w2 Hw2.
        apply SupL_eq_ext.
        intros w1 Hw1.
        apply Rw_sym.
      }
      assert (HS1 :
        @SupL L1 (fun w1 => Rw w1 w3) (Rw_upper_bounded_left w3 L1)
        =
        @SupL L1 (fun w1 => Rw w3 w1) (Rw_upper_bounded_right w3 L1)).
      {
        apply SupL_eq_ext.
        intros w1 Hw1.
        apply Rw_sym.
      }
      rewrite HS2 HI HS1.
      rewrite smin_comm.
      apply (@bridge_left_nonempty L2 L1 w3 Hne2 Hne1).
    Qed.

    Lemma RL_trans_nonempty :
      forall L1 L2 L3,
        lang_nonempty L1 ->
        lang_nonempty L2 ->
        lang_nonempty L3 ->
        smin (RL L1 L2) (RL L2 L3) <= RL L1 L3.
    Proof.
      intros L1 L2 L3 Hne1 Hne2 Hne3.
      unfold RL.
      set (a12 :=
        @InfL L1
          (fun w1 => @SupL L2 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L2))
          (outer_lower_bounded_left L1 L2)).
      set (b12 :=
        @InfL L2
          (fun w2 => @SupL L1 (fun w1 => Rw w1 w2) (Rw_upper_bounded_left w2 L1))
          (outer_lower_bounded_right L1 L2)).
      set (a23 :=
        @InfL L2
          (fun w2 => @SupL L3 (fun w3 => Rw w2 w3) (Rw_upper_bounded_right w2 L3))
          (outer_lower_bounded_left L2 L3)).
      set (b23 :=
        @InfL L3
          (fun w3 => @SupL L2 (fun w2 => Rw w2 w3) (Rw_upper_bounded_left w3 L2))
          (outer_lower_bounded_right L2 L3)).
      set (c := smin (smin a12 b12) (smin a23 b23)).
      apply le_smin.
      - eapply (@InfL_greatest_nonempty
                  L1
                  (fun w1 => @SupL L3 (fun w3 => Rw w1 w3) (Rw_upper_bounded_right w1 L3))
                  (outer_lower_bounded_left L1 L3) c Hne1).
        intros w1 Hw1.
        eapply Rle_trans.
        + apply le_smin.
          * eapply Rle_trans.
            -- unfold c. apply smin_lel.
            -- apply smin_lel.
          * eapply Rle_trans.
            -- unfold c. apply smin_ler.
            -- apply smin_lel.
        + eapply Rle_trans.
          * apply le_smin.
            -- eapply Rle_trans.
               ++ apply smin_lel.
               ++ apply (@InfL_lower
                            L1
                            (fun w1 => @SupL L2 (fun w2 => Rw w1 w2) (Rw_upper_bounded_right w1 L2))
                            (outer_lower_bounded_left L1 L2) w1 Hw1).
            -- apply Rle_refl.
          * eapply Rle_trans.
            -- apply smin_mono.
               ++ apply Rle_refl.
               ++ apply smin_ler.
            -- apply bridge_left_nonempty; assumption.
      - eapply (@InfL_greatest_nonempty
                  L3
                  (fun w3 => @SupL L1 (fun w1 => Rw w1 w3) (Rw_upper_bounded_left w3 L1))
                  (outer_lower_bounded_right L1 L3) c Hne3).
        intros w3 Hw3.
        eapply Rle_trans.
        + apply le_smin.
          * eapply Rle_trans.
            -- unfold c. apply smin_lel.
            -- apply smin_ler.
          * eapply Rle_trans.
            -- unfold c. apply smin_ler.
            -- apply smin_ler.
        + eapply Rle_trans.
          * apply le_smin.
            -- apply Rle_refl.
            -- eapply Rle_trans.
               ++ apply smin_ler.
               ++ apply (@InfL_lower
                            L3
                            (fun w3 => @SupL L2 (fun w2 => Rw w2 w3) (Rw_upper_bounded_left w3 L2))
                            (outer_lower_bounded_right L2 L3) w3 Hw3).
          * eapply Rle_trans.
            -- apply smin_mono.
               ++ apply smin_lel.
               ++ apply Rle_refl.
            -- apply bridge_right_nonempty; assumption.
    Qed.

    (* Lemma 3.3(3), min T-norm *)
    Lemma RL_is_similarity :
      (forall L, RL L L = 1) /\
      (forall L1 L2, RL L1 L2 = RL L2 L1) /\
      (forall L1 L2 L3, smin (RL L1 L2) (RL L2 L3) <= RL L1 L3).
    Proof.
      split.
      - exact RL_refl.
      - split.
        + exact RL_sym.
        + intros L1 L2 L3.
          destruct (excluded_middle_informative (lang_nonempty L1)) as [Hne1|Hempty1];
          destruct (excluded_middle_informative (lang_nonempty L2)) as [Hne2|Hempty2];
          destruct (excluded_middle_informative (lang_nonempty L3)) as [Hne3|Hempty3].
          * exact (RL_trans_nonempty Hne1 Hne2 Hne3).
          * rewrite (@RL_empty_nonempty_right L2 L3 Hne2 Hempty3).
            eapply Rle_trans.
            -- apply smin_ler.
            -- exact (proj1 (RL_in01 L1 L3)).
          * rewrite (@RL_empty_nonempty_right L1 L2 Hne1 Hempty2).
            eapply Rle_trans.
            -- apply smin_lel.
            -- exact (proj1 (RL_in01 L1 L3)).
          * rewrite (@RL_empty_nonempty_right L1 L2 Hne1 Hempty2).
            eapply Rle_trans.
            -- apply smin_lel.
            -- exact (proj1 (RL_in01 L1 L3)).
          * rewrite (@RL_empty_nonempty_left L1 L2 Hempty1 Hne2).
            eapply Rle_trans.
            -- apply smin_lel.
            -- exact (proj1 (RL_in01 L1 L3)).
          * rewrite (@RL_empty_nonempty_left L1 L2 Hempty1 Hne2).
            eapply Rle_trans.
            -- apply smin_lel.
            -- exact (proj1 (RL_in01 L1 L3)).
          * rewrite (@RL_empty_nonempty_left L2 L3 Hempty2 Hne3).
            eapply Rle_trans.
            -- apply smin_ler.
            -- exact (proj1 (RL_in01 L1 L3)).
          * rewrite (@RL_empty_empty L1 L2 Hempty1 Hempty2).
            rewrite (@RL_empty_empty L2 L3 Hempty2 Hempty3).
            rewrite (@RL_empty_empty L1 L3 Hempty1 Hempty3).
            rewrite sminxx.
            apply Rle_refl.
    Qed.

    (* ============================================================ *)
    (* Definition 3.4 (G^E): syntax-sensitive similarity on regex   *)
    (* ============================================================ *)

    Fixpoint Rr (r s : regex) : simval :=
      match s with
      | RS.Empty =>
          match r with
          | RS.Empty => 1
          | _ => 0
          end
      | RS.Eps =>
          match r with
          | RS.Eps => 1
          | _ => 0
          end
      | RS.Char a =>
          match r with
          | RS.Char b => R b a
          | _ => 0
          end
      | RS.Star s1 =>
          match r with
          | RS.Star r1 => Rr r1 s1
          | _ => 0
          end
      | RS.Seq s1 s2 =>
          match r with
          | RS.Seq r1 r2 => smin (Rr r1 s1) (Rr r2 s2)
          | _ => 0
          end
      | RS.Alt s1 s2 =>
          match r with
          | RS.Alt r1 r2 => smin (Rr r1 s1) (Rr r2 s2)
          | _ => 0
          end
      | RS.And s1 s2 =>
          match r with
          | RS.And r1 r2 => smin (Rr r1 s1) (Rr r2 s2)
          | _ => 0
          end
      | RS.Neg s1 =>
          match r with
          | RS.Neg r1 => Rr r1 s1
          | _ => 0
          end
      end.

    Lemma smin_in01 (x y : simval) :
      in01 x -> in01 y -> in01 (smin x y).
    Proof.
      move=> [Hx0 Hx1] [Hy0 Hy1].
      split.
      - apply le_smin; assumption.
      - eapply Rle_trans.
        + apply smin_lel.
        + exact Hx1.
    Qed.

    Lemma Rr_range : forall r s, 0 <= Rr r s <= 1.
    Proof.
      intros r s; revert r.
      induction s as [| | a | s1 IH1 s2 IH2 | s1 IH1 s2 IH2 | s IH
                     | s1 IH1 s2 IH2 | s IH];
        intros r.
      - destruct r; simpl; lra.
      - destruct r; simpl; lra.
      - destruct r; simpl; try lra.
        apply R_range.
      - destruct r; simpl; try lra.
        apply smin_in01; [apply IH1 | apply IH2].
      - destruct r; simpl; try lra.
        apply smin_in01; [apply IH1 | apply IH2].
      - destruct r; simpl; try lra.
        apply IH.
      - destruct r; simpl; try lra.
        apply smin_in01; [apply IH1 | apply IH2].
      - destruct r; simpl; try lra.
        apply IH.
    Qed.

    Lemma Rr_refl : forall r, Rr r r = 1.
    Proof.
      induction r as [| | a | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH
                     | r1 IH1 r2 IH2 | r IH].
      - reflexivity.
      - reflexivity.
      - exact (R_refl a).
      - simpl. by rewrite IH1 IH2 sminxx.
      - simpl. by rewrite IH1 IH2 sminxx.
      - simpl. exact IH.
      - simpl. by rewrite IH1 IH2 sminxx.
      - simpl. exact IH.
    Qed.

    Lemma Rr_sym : forall r s, Rr r s = Rr s r.
    Proof.
      intros r s; revert r.
      induction s as [| | a | s1 IH1 s2 IH2 | s1 IH1 s2 IH2 | s IH
                     | s1 IH1 s2 IH2 | s IH];
        intros r.
      - by destruct r.
      - by destruct r.
      - destruct r; simpl; try reflexivity.
        apply R_sym.
      - destruct r; simpl; try reflexivity.
        by rewrite IH1 IH2.
      - destruct r; simpl; try reflexivity.
        by rewrite IH1 IH2.
      - destruct r; simpl; try reflexivity.
        exact (IH r).
      - destruct r; simpl; try reflexivity.
        by rewrite IH1 IH2.
      - destruct r; simpl; try reflexivity.
        exact (IH r).
    Qed.

    Local Ltac solve_nonneg :=
      match goal with
      | |- 0 <= 0 => lra
      | |- 0 <= 1 => lra
      | |- 0 <= R ?a ?b =>
          exact (proj1 (R_range a b))
      | |- 0 <= Rr ?r ?s =>
          exact (proj1 (Rr_range r s))
      | |- 0 <= smin ?x ?y =>
          apply le_smin; [solve_nonneg | solve_nonneg]
      end.

    Lemma Rr_trans : forall r1 r2 r,
      smin (Rr r1 r) (Rr r r2) <= Rr r1 r2.
    Proof.
      intros r1 r2 r; revert r1 r2.
      induction r as [| | a | m1 IH1 m2 IH2 | m1 IH1 m2 IH2 | m IH
                     | m1 IH1 m2 IH2 | m IH];
        intros s1 s2; destruct s1; destruct s2; simpl;
        try solve [rewrite sminxx; apply Rle_refl];
        try solve [
          eapply Rle_trans; [apply smin_lel | solve_nonneg]
        ];
        try solve [
          eapply Rle_trans; [apply smin_ler | solve_nonneg]
        ];
        try solve [apply R_trans];
        try solve [exact (IH _ _)];
        try solve [
          eapply Rle_trans;
          [apply smin_shuffle |];
          apply le_smin;
          [ eapply Rle_trans; [apply smin_lel | exact (IH1 _ _)]
          | eapply Rle_trans; [apply smin_ler | exact (IH2 _ _)]
          ]
        ].
    Qed.


    Lemma Rr_is_similarity : @is_similarity regex Rr.
    Proof.
      split.
      - split.
        + exact Rr_refl.
        + exact Rr_sym.
      - intros r1 r2 r.
        exact (Rr_trans r1 r2 r).
    Qed.

    Inductive classical_regex : regex -> Prop :=
    | ClassicalEmpty : classical_regex RS.Empty
    | ClassicalEps : classical_regex RS.Eps
    | ClassicalChar : forall a, classical_regex (RS.Char a)
    | ClassicalAlt : forall r s,
        classical_regex r -> classical_regex s -> classical_regex (RS.Alt r s)
    | ClassicalSeq : forall r s,
        classical_regex r -> classical_regex s -> classical_regex (RS.Seq r s)
    | ClassicalStar : forall r,
        classical_regex r -> classical_regex (RS.Star r).

    Lemma Rw_cat :
      forall u1 u2 v1 v2,
        smin (Rw u1 u2) (Rw v1 v2) <= Rw (u1 ++ v1) (u2 ++ v2).
    Proof.
      elim=> [|a1 t1 IH] [|a2 t2] v1 v2 //=.
      - apply smin_ler.
      - eapply Rle_trans.
        + apply smin_lel.
        + exact (proj1 (Rw_range v1 (a2 :: t2 ++ v2))).
      - eapply Rle_trans.
        + apply smin_lel.
        + exact (proj1 (Rw_range (a1 :: t1 ++ v1) v2)).
      - eapply Rle_trans.
        + apply le_smin.
          * eapply Rle_trans.
            -- apply smin_lel.
            -- apply smin_lel.
          * eapply Rle_trans.
            -- apply le_smin.
               ++ eapply Rle_trans.
                  ** apply smin_lel.
                  ** apply smin_ler.
               ++ apply smin_ler.
            -- exact (IH t2 v1 v2).
        + apply Rle_refl.
    Qed.

    Lemma star_prepend_word (L : language) (u v : word) :
      L u = true ->
      Languages.star L v ->
      Languages.star L (u ++ v).
    Proof.
      case: u => [|a u] Hu Hv /=.
      - exact Hv.
      - apply: (Languages.star_cons_split_inv (A:=A) (L:=L) (a:=a) (w:=u ++ v)).
        exists u, v.
        by repeat split.
    Qed.

    Lemma classical_match_word :
      forall r s w,
        classical_regex r ->
        classical_regex s ->
        RS.den r w = true ->
        Rr r s = 0 \/
        exists u, RS.den s u = true /\ Rr r s <= Rw w u.
    Proof.
      move=> r s w Hr.
      move: s w.
      induction Hr as
        [| | a
        | r1 r2 Hr1 IH1 Hr2 IH2
        | r1 r2 Hr1 IH1 Hr2 IH2
        | r Hr IH];
        intros t x Ht Hx.
      - by rewrite /= in Hx.
      - inversion Ht; subst; simpl in *.
        + left; reflexivity.
        + move/eqP: Hx => ->.
          right. exists [::]. split; first by [].
          simpl.
          apply Rle_refl.
        + left; reflexivity.
        + left; reflexivity.
        + left; reflexivity.
        + left; reflexivity.
      - case: Ht => [| |b|r1 r2 ? ?|r1 r2 ? ?|r1 ?] /=.
        + left; reflexivity.
        + left; reflexivity.
        + move/eqP: Hx => ->.
          right. exists [:: b]. split.
          * by rewrite /RS.atom /Languages.atom eqxx.
          rewrite /=.
          apply le_smin.
          * apply Rle_refl.
          * exact (proj2 (R_range a b)).
        + left; reflexivity.
        + left; reflexivity.
        + left; reflexivity.
      - case: Ht => [| |b|s1 s2 Hs1 Hs2|s1 s2 Hs1 Hs2|s1 Hs1] /=.
        + left; reflexivity.
        + left; reflexivity.
        + left; reflexivity.
        + move/orP: Hx => [Hx1|Hx2].
          * have [H0|[u [Hu Hle]]] := IH1 _ _ Hs1 Hx1.
            -- left.
               rewrite H0.
               apply smin0l.
               exact (proj1 (Rr_range r2 s2)).
            -- right. exists u. split.
               ++ apply/orP. left. exact Hu.
                eapply Rle_trans.
                ++ apply smin_lel.
                ++ exact Hle.
          * have [H0|[u [Hu Hle]]] := IH2 _ _ Hs2 Hx2.
            -- left.
               rewrite H0.
               apply smin0r.
               exact (proj1 (Rr_range r1 s1)).
            -- right. exists u. split.
               ++ apply/orP. right. exact Hu.
                eapply Rle_trans.
                ++ apply smin_ler.
                ++ exact Hle.
        + left; reflexivity.
        + left; reflexivity.
      - case: Ht => [| |b|s1 s2 Hs1 Hs2|s1 s2 Hs1 Hs2|s1 Hs1] /=.
        + left; reflexivity.
        + left; reflexivity.
        + left; reflexivity.
        + left; reflexivity.
        + have [u1 [u2 [-> [Hu1 Hu2]]]] := Languages.concP (A:=A) Hx.
          have [H01|[v1 [Hv1 Hle1]]] := IH1 _ _ Hs1 Hu1.
          * left.
            rewrite H01.
            apply smin0l.
            exact (proj1 (Rr_range r2 s2)).
          * have [H02|[v2 [Hv2 Hle2]]] := IH2 _ _ Hs2 Hu2.
            -- left.
               rewrite H02.
               apply smin0r.
               exact (proj1 (Rr_range r1 s1)).
            -- right. exists (v1 ++ v2). split.
               ++ apply: (Languages.concP_inv (A:=A)).
                  exists v1, v2. by repeat split.
               ++ eapply Rle_trans.
                  ** apply le_smin.
                     --- eapply Rle_trans.
                         +++ apply smin_lel.
                         +++ exact Hle1.
                     --- eapply Rle_trans.
                         +++ apply smin_ler.
                         +++ exact Hle2.
                  ** apply Rw_cat.
        + left; reflexivity.
      - case: Ht => [| |b|s1 s2 Hs1 Hs2|s1 s2 Hs1 Hs2|s1 Hs1] /=.
        + left; reflexivity.
        + left; reflexivity.
        + left; reflexivity.
        + left; reflexivity.
        + left; reflexivity.
        + have [xs [Hxs Hall]] := Languages.starP (A:=A) Hx.
          have Hflatx : Languages.flatten_words xs = x
            by exact: (Languages.splits_flatten (A:=A) Hxs).
          have Hblocks :
            forall zs,
              Languages.all_in (RS.den r) zs ->
              Rr r s1 = 0 \/
              exists v, RS.star (RS.den s1) v = true /\
                        Rr r s1 <= Rw (Languages.flatten_words zs) v.
          {
            elim=> [|z zs IHz] /=.
            - move=> _.
              right. exists [::].
              split.
              + exact: (Languages.star_nil (A:=A) (RS.den s1)).
              + destruct (Rr_range r s1) as [_ H1].
                eapply Rle_trans.
                * exact H1.
                * simpl. apply Rle_refl.
            - move=> /andP [Hz Hzs].
              have [H0|[y [Hy Hzy]]] := IH _ _ Hs1 Hz.
              + left. exact H0.
              + have [H0'|[v [Hv Htailv]]] := IHz Hzs.
                * left. exact H0'.
                * right. exists (y ++ v). split.
                  -- apply star_prepend_word; assumption.
                  -- eapply Rle_trans.
                     ++ apply le_smin; [exact Hzy | exact Htailv].
                     ++ apply Rw_cat.
          }
          have [H0|[v [Hv Hle]]] := Hblocks xs Hall.
          * left. exact H0.
          * right. exists v. split; first exact Hv.
            rewrite -Hflatx.
            exact Hle.
    Qed.

    Lemma le_SupL_witness :
      forall (L : language) (f : word -> simval)
             (Hub : upper_bounded_on L f) c w,
        L w = true ->
        c <= f w ->
        c <= @SupL L f Hub.
    Proof.
      move=> L f Hub c w Hw Hle.
      eapply Rle_trans.
      - exact Hle.
      - apply (@SupL_upper L f Hub w Hw).
    Qed.

    Lemma syntax_semantics_sup_right :
      forall r s w,
        classical_regex r ->
        classical_regex s ->
        RS.den r w = true ->
        Rr r s <= @SupL (RS.den s) (fun w2 => Rw w w2)
                   (Rw_upper_bounded_right w (RS.den s)).
    Proof.
      move=> r s w Hr Hs Hw.
      have [H0|[u [Hu Hle]]] := classical_match_word Hr Hs Hw.
      - rewrite H0.
        apply SupL_nonneg.
        move=> w2 Hw2.
        exact (proj1 (Rw_range w w2)).
      - exact: (le_SupL_witness (Rw_upper_bounded_right w (RS.den s)) Hu Hle).
    Qed.

    Lemma syntax_semantics_directed :
      forall r s,
        classical_regex r ->
        classical_regex s ->
        Rr r s <=
        @InfL (RS.den r)
          (fun w1 => @SupL (RS.den s) (fun w2 => Rw w1 w2)
                      (Rw_upper_bounded_right w1 (RS.den s)))
          (outer_lower_bounded_left (RS.den r) (RS.den s)).
    Proof.
      move=> r s Hr Hs.
      destruct (excluded_middle_informative (lang_nonempty (RS.den r))) as [Hne|Hempty].
      - apply (@InfL_greatest_nonempty
                 (RS.den r)
                 (fun w1 => @SupL (RS.den s) (fun w2 => Rw w1 w2)
                             (Rw_upper_bounded_right w1 (RS.den s)))
                 (outer_lower_bounded_left (RS.den r) (RS.den s))
                 (Rr r s) Hne).
        move=> w Hw.
        exact: (syntax_semantics_sup_right Hr Hs Hw).
      - rewrite (@InfL_empty
                   (RS.den r)
                   (fun w1 => @SupL (RS.den s) (fun w2 => Rw w1 w2)
                               (Rw_upper_bounded_right w1 (RS.den s)))
                   (outer_lower_bounded_left (RS.den r) (RS.den s)) Hempty).
        destruct (Rr_range r s) as [_ H1].
        exact H1.
    Qed.

    Lemma syntax_semantics_inequality :
      forall r s,
        classical_regex r ->
        classical_regex s ->
        Rr r s <= RL (RS.den r) (RS.den s).
    Proof.
      move=> r s Hr Hs.
      unfold RL.
      apply le_smin.
      - exact: (syntax_semantics_directed Hr Hs).
      - assert (Heq :
          @InfL (RS.den s)
            (fun w2 => @SupL (RS.den r) (fun w1 => Rw w1 w2)
                        (Rw_upper_bounded_left w2 (RS.den r)))
            (outer_lower_bounded_right (RS.den r) (RS.den s))
          =
          @InfL (RS.den s)
            (fun w1 => @SupL (RS.den r) (fun w2 => Rw w1 w2)
                        (Rw_upper_bounded_right w1 (RS.den r)))
            (outer_lower_bounded_left (RS.den s) (RS.den r))).
        {
          apply InfL_eq_ext.
          intros w Hw.
          apply SupL_eq_ext.
          intros u Hu.
          apply Rw_sym.
        }
        rewrite Heq (Rr_sym r s).
        exact: (syntax_semantics_directed Hs Hr).
    Qed.

    Lemma re_equiv_den_eq :
      forall r s, RS.re_equiv r s -> RS.den r = RS.den s.
    Proof.
      move=> r s H.
      apply functional_extensionality=> w.
      exact: (H w).
    Qed.

    Definition classical_Rr_candidate_values (r s : regex) : simval -> Prop :=
      fun x =>
        exists r' s' t u,
          classical_regex r' /\
          classical_regex s' /\
          classical_regex t /\
          classical_regex u /\
          RS.re_equiv r' r /\
          RS.re_equiv s' s /\
          RS.re_equiv t u /\
          x = smin (Rr r' t) (Rr s' u).

    Lemma classical_Rr_candidate_values_upper :
      forall r s x,
        classical_regex r ->
        classical_regex s ->
        classical_Rr_candidate_values r s x ->
        x <= RL (RS.den r) (RS.den s).
    Proof.
      move=> r s x Hr Hs [r' [s' [t [u [Hr' [Hs' [Ht [Hu [Hrr [Hss [Htu ->]]]]]]]]]]].
      have Hrt : Rr r' t <= RL (RS.den r') (RS.den t).
      { exact: (syntax_semantics_inequality Hr' Ht). }
      have Hsu : Rr s' u <= RL (RS.den s') (RS.den u).
      { exact: (syntax_semantics_inequality Hs' Hu). }
      have Hrr_eq : RS.den r' = RS.den r := re_equiv_den_eq Hrr.
      have Hss_eq : RS.den s' = RS.den s := re_equiv_den_eq Hss.
      have Htu_eq : RS.den t = RS.den u := re_equiv_den_eq Htu.
      have Hsu_t : Rr s' u <= RL (RS.den s') (RS.den t).
      { rewrite -Htu_eq in Hsu. exact Hsu. }
      have Hstep :
        smin (RL (RS.den r') (RS.den t)) (RL (RS.den s') (RS.den t))
        <= RL (RS.den r') (RS.den s').
      {
        have HtransRL :
          forall L1 L2 L3, smin (RL L1 L2) (RL L2 L3) <= RL L1 L3 :=
          proj2 (proj2 RL_is_similarity).
        rewrite (RL_sym (RS.den s') (RS.den t)).
        exact: (HtransRL (RS.den r') (RS.den t) (RS.den s')).
      }
      eapply Rle_trans.
      - apply smin_mono; [exact Hrt | exact Hsu_t].
      - eapply Rle_trans.
        + exact Hstep.
        + rewrite Hrr_eq Hss_eq.
          apply Rle_refl.
    Qed.

    Theorem Rr_RL_bridge :
      forall r s,
        classical_regex r ->
        classical_regex s ->
        is_lub (classical_Rr_candidate_values r s) (RL (RS.den r) (RS.den s)).
    Proof.
      (* TODO:
         The upper-bound direction now follows from
         [classical_Rr_candidate_values_upper].
         The missing lower-bound direction is a completeness result:
         one must show that every semantic similarity value between two
         classical regex languages can be realized by suitable classical
         equivalent rewrites. *)
    Admitted.


  End BaseSymbolSimilarity.

  (* ============================================================ *)
  (* Definition 3.5 (R^E): similarity on regex, general T-norm    *)
  (* ============================================================ *)

  Section GeneralRegexSimilarity.

    Variable T : tnorm.
    Variable R : fuzzy_rel A.
    Hypothesis R_tsim : is_T_similarity T R.

    Let R_range : forall a b, in01 (R a b) := tsim_range R_tsim.
    Let R_refl : forall a, R a a = 1 := prox_refl (tsim_prox R_tsim).

    (* inf_n f(n), built from the completeness axiom as [InfL] is;
       0 if f is not bounded below *)
    Definition nat_image (f : nat -> simval) : simval -> Prop :=
      fun y => exists n, y = - f n.

    Lemma nat_image_nonempty (f : nat -> simval) : exists y, nat_image f y.
    Proof. by exists (- f O), O. Qed.

    Definition InfN (f : nat -> simval) : simval :=
      match excluded_middle_informative (bound (nat_image f)) with
      | left Hb =>
          - proj1_sig (completeness (nat_image f) Hb (nat_image_nonempty f))
      | right _ => 0
      end.

    Lemma nat_image_bound (f : nat -> simval) (m : simval) :
      (forall k, m <= f k) -> bound (nat_image f).
    Proof.
      move=> Hm.
      exists (- m).
      move=> y [k ->].
      have := Hm k.
      lra.
    Qed.

    Lemma InfN_lower (f : nat -> simval) (m : simval) (n : nat) :
      (forall k, m <= f k) -> InfN f <= f n.
    Proof.
      move=> Hm.
      rewrite /InfN.
      case: (excluded_middle_informative (bound (nat_image f))) => [Hb|Hnb].
      - case: (completeness _ _ _) => s [Hup _] /=.
        have := Hup (- f n) (ex_intro _ n erefl).
        lra.
      - exfalso.
        apply: Hnb.
        exact: (nat_image_bound Hm).
    Qed.

    Lemma InfN_greatest (f : nat -> simval) (m : simval) :
      (forall k, m <= f k) -> m <= InfN f.
    Proof.
      move=> Hm.
      rewrite /InfN.
      case: (excluded_middle_informative (bound (nat_image f))) => [Hb|Hnb].
      - case: (completeness _ _ _) => s [_ Hleast] /=.
        have : s <= - m.
        { apply: Hleast => y [k ->].
          have := Hm k.
          lra. }
        lra.
      - exfalso.
        apply: Hnb.
        exact: (nat_image_bound Hm).
    Qed.

    (* ⊗^n x, with ⊗^0 x = 1 *)
    Fixpoint tpow (n : nat) (x : simval) : simval :=
      match n with
      | O => 1
      | S n' => T x (tpow n' x)
      end.

    Lemma tpow_in01 (n : nat) (x : simval) : in01 x -> in01 (tpow n x).
    Proof.
      move=> Hx.
      elim: n => [|n IH] /=.
      - split; lra.
      - exact: tn_in01.
    Qed.

    Lemma tpow_one (n : nat) : tpow n 1 = 1.
    Proof.
      elim: n => [|n IH] //=.
      rewrite IH.
      apply: tn_unit.
      split; lra.
    Qed.

    Lemma InfN_tpow_in01 (x : simval) :
      in01 x -> in01 (InfN (fun n => tpow n x)).
    Proof.
      move=> Hx.
      have H0 : forall k, 0 <= tpow k x.
      { move=> k. by case: (tpow_in01 k Hx). }
      split.
      - exact: (InfN_greatest H0).
      - apply: (Rle_trans _ (tpow 0 x)).
        + exact: (InfN_lower 0 H0).
        + rewrite /=. lra.
    Qed.

    Lemma InfN_tpow_le (x : simval) :
      in01 x -> InfN (fun n => tpow n x) <= x.
    Proof.
      move=> Hx.
      have H0 : forall k, 0 <= tpow k x.
      { move=> k. by case: (tpow_in01 k Hx). }
      apply: (Rle_trans _ (tpow 1 x)).
      - exact: (InfN_lower 1 H0).
      - rewrite /= (@tn_unit T x Hx).
        lra.
    Qed.

    Lemma InfN_tpow_one : InfN (fun n => tpow n 1) = 1.
    Proof.
      have H1 : forall k, 1 <= tpow k 1.
      { move=> k. rewrite tpow_one. lra. }
      apply: Rle_antisym.
      - apply: (Rle_trans _ (tpow 0 1)).
        + exact: (InfN_lower 0 H1).
        + rewrite /=. lra.
      - exact: (InfN_greatest H1).
    Qed.

    Definition regex_eq_dec (r s : regex) : {r = s} + {r <> s}.
    Proof. decide equality. exact: eq_comparable. Defined.

    Arguments regex_eq_dec : simpl never.

    (* Definition 3.5 *)
    Fixpoint RE (r s : regex) {struct r} : simval :=
      if regex_eq_dec r s then 1 else
      match r, s with
      | RS.Char a, RS.Char b => R a b
      | RS.Alt r1 r2, RS.Alt s1 s2 => smin (RE r1 s1) (RE r2 s2)
      | RS.Seq r1 r2, RS.Seq s1 s2 => T (RE r1 s1) (RE r2 s2)
      | RS.Star r1, RS.Star s1 => InfN (fun n => tpow n (RE r1 s1))
      | _, _ => 0
      end.

    Lemma RE_range (r s : regex) : in01 (RE r s).
    Proof.
      have H0 : in01 0 by split; lra.
      have H1 : in01 1 by split; lra.
      elim: r s => [| |a|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r1 IH1|r1 IH1 r2 IH2|r1 IH1]
                     s /=;
        case: (regex_eq_dec _ s) => /= _; try exact H1;
        case: s => [| |b|s1 s2|s1 s2|s1|s1 s2|s1] /=; try exact H0.
      - exact: R_range.
      - exact: (smin_in01 (IH1 s1) (IH2 s2)).
      - exact: (@tn_in01 T _ _ (IH1 s1) (IH2 s2)).
      - exact: (InfN_tpow_in01 (IH1 s1)).
    Qed.

    (* The clauses of Definition 3.5 hold as equations. *)
    Lemma RE_refl (r : regex) : RE r r = 1.
    Proof.
      case: r => [| |a|r1 r2|r1 r2|r1|r1 r2|r1] //=;
        case: (regex_eq_dec _ _) => /= [//|H]; by case: H.
    Qed.

    Lemma RE_Char (a b : A) : RE (RS.Char a) (RS.Char b) = R a b.
    Proof.
      rewrite /=.
      case: (regex_eq_dec _ _) => /= [[<-]|_] //;
        by rewrite R_refl.
    Qed.

    Lemma RE_Alt (r1 r2 s1 s2 : regex) :
      RE (RS.Alt r1 r2) (RS.Alt s1 s2) = smin (RE r1 s1) (RE r2 s2).
    Proof.
      rewrite /=.
      case: (regex_eq_dec _ _) => /= [[<- <-]|_] //;
        by rewrite !RE_refl sminxx.
    Qed.

    Lemma RE_Seq (r1 r2 s1 s2 : regex) :
      RE (RS.Seq r1 r2) (RS.Seq s1 s2) = T (RE r1 s1) (RE r2 s2).
    Proof.
      rewrite /=.
      case: (regex_eq_dec _ _) => /= [[<- <-]|_] //;
        rewrite !RE_refl tn_unit //; split; lra.
    Qed.

    Lemma RE_Star (r1 s1 : regex) :
      RE (RS.Star r1) (RS.Star s1) = InfN (fun n => tpow n (RE r1 s1)).
    Proof.
      rewrite /=.
      case: (regex_eq_dec _ _) => /= [[<-]|_] //;
        by rewrite RE_refl InfN_tpow_one.
    Qed.

    Definition same_head (r s : regex) : bool :=
      match r, s with
      | RS.Char _, RS.Char _
      | RS.Alt _ _, RS.Alt _ _
      | RS.Seq _ _, RS.Seq _ _
      | RS.Star _, RS.Star _ => true
      | _, _ => false
      end.

    Lemma RE_otherwise (r s : regex) :
      r <> s -> ~~ same_head r s -> RE r s = 0.
    Proof.
      case: r => [| |a|r1 r2|r1 r2|r1|r1 r2|r1];
        case: s => [| |b|s1 s2|s1 s2|s1|s1 s2|s1] //= Hne _;
        by case: (regex_eq_dec _ _).
    Qed.

    (* ============================================================ *)
    (* Lemma 3.2: R^E > 0 forces a common skeleton                  *)
    (* ============================================================ *)

    (* r[a1,...,an]: a regex with a hole at every symbol occurrence *)
    Inductive skeleton : Type :=
    | SkEmpty
    | SkEps
    | SkHole
    | SkAlt  : skeleton -> skeleton -> skeleton
    | SkSeq  : skeleton -> skeleton -> skeleton
    | SkStar : skeleton -> skeleton
    | SkAnd  : skeleton -> skeleton -> skeleton
    | SkNeg  : skeleton -> skeleton.

    Fixpoint holes (k : skeleton) : nat :=
      match k with
      | SkEmpty | SkEps => 0
      | SkHole => 1
      | SkAlt k1 k2 | SkSeq k1 k2 | SkAnd k1 k2 => (holes k1 + holes k2)%nat
      | SkStar k1 | SkNeg k1 => holes k1
      end.

    (* fills the holes of k with xs, left to right *)
    Fixpoint fill (k : skeleton) (xs : seq A) : regex :=
      match k with
      | SkEmpty => RS.Empty
      | SkEps => RS.Eps
      | SkHole => if xs is a :: _ then RS.Char a else RS.Empty
      | SkAlt k1 k2 =>
          RS.Alt (fill k1 (take (holes k1) xs)) (fill k2 (drop (holes k1) xs))
      | SkSeq k1 k2 =>
          RS.Seq (fill k1 (take (holes k1) xs)) (fill k2 (drop (holes k1) xs))
      | SkStar k1 => RS.Star (fill k1 xs)
      | SkAnd k1 k2 =>
          RS.And (fill k1 (take (holes k1) xs)) (fill k2 (drop (holes k1) xs))
      | SkNeg k1 => RS.Neg (fill k1 xs)
      end.

    (* the skeleton of r and its symbols, left to right *)
    Fixpoint skel_of (r : regex) : skeleton :=
      match r with
      | RS.Empty => SkEmpty
      | RS.Eps => SkEps
      | RS.Char _ => SkHole
      | RS.Alt r1 r2 => SkAlt (skel_of r1) (skel_of r2)
      | RS.Seq r1 r2 => SkSeq (skel_of r1) (skel_of r2)
      | RS.Star r1 => SkStar (skel_of r1)
      | RS.And r1 r2 => SkAnd (skel_of r1) (skel_of r2)
      | RS.Neg r1 => SkNeg (skel_of r1)
      end.

    Fixpoint syms_of (r : regex) : seq A :=
      match r with
      | RS.Empty | RS.Eps => [::]
      | RS.Char a => [:: a]
      | RS.Alt r1 r2 | RS.Seq r1 r2 | RS.And r1 r2 => syms_of r1 ++ syms_of r2
      | RS.Star r1 | RS.Neg r1 => syms_of r1
      end.

    Lemma size_syms_of (r : regex) : size (syms_of r) = holes (skel_of r).
    Proof.
      elim: r => [| |a|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r1 IH1|r1 IH1 r2 IH2|r1 IH1]
                   //=;
        by rewrite size_cat IH1 IH2.
    Qed.

    Lemma fill_skel_of (r : regex) : fill (skel_of r) (syms_of r) = r.
    Proof.
      elim: r => [| |a|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r1 IH1|r1 IH1 r2 IH2|r1 IH1]
                   //=;
        try by rewrite IH1.
      all: by rewrite (take_size_cat _ (size_syms_of r1))
                      (drop_size_cat _ (size_syms_of r1)) IH1 IH2.
    Qed.

    (* R^E(r,s) > 0 forces r and s to have the same skeleton, on all of E *)
    Lemma RE_pos_skel_of (r s : regex) :
      0 < RE r s -> skel_of r = skel_of s.
    Proof.
      elim: r s => [| |a|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r1 IH1|r1 IH1 r2 IH2|r1 IH1]
                     s /=;
        case: (regex_eq_dec _ s) => /= [<- //|_];
        case: s => [| |b|s1 s2|s1 s2|s1|s1 s2|s1] //=;
        try (move=> ?; exfalso; lra).
      - move=> H.
        have H1 : 0 < RE r1 s1 := Rlt_le_trans _ _ _ H (smin_lel _ _).
        have H2 : 0 < RE r2 s2 := Rlt_le_trans _ _ _ H (smin_ler _ _).
        by rewrite (IH1 _ H1) (IH2 _ H2).
      - move=> /(tn_pos (RE_range _ _) (RE_range _ _)) [H1 H2].
        by rewrite (IH1 _ H1) (IH2 _ H2).
      - move=> H.
        have H1 : 0 < RE r1 s1 :=
          Rlt_le_trans _ _ _ H (InfN_tpow_le (RE_range r1 s1)).
        by rewrite (IH1 _ H1).
    Qed.

    (* Lemma 3.2 *)
    Theorem RE_pos_skeleton (r1 r2 : regex) :
      RS.restricted_regex r1 -> RS.restricted_regex r2 ->
      0 < RE r1 r2 ->
      exists (r : skeleton) (xs ys : seq A),
        size xs = holes r /\ size ys = holes r /\
        r1 = fill r xs /\ r2 = fill r ys.
    Proof.
      move=> _ _ /RE_pos_skel_of Hsk.
      exists (skel_of r1), (syms_of r1), (syms_of r2).
      split; first exact: size_syms_of.
      split; first by rewrite Hsk size_syms_of.
      split; first by rewrite fill_skel_of.
      by rewrite Hsk fill_skel_of.
    Qed.

    (* ============================================================ *)
    (* Lemma 3.5: Finite Syntactic Similarity                       *)
    (* ============================================================ *)

    Section FiniteSyntacticSimilarity.

      (* a finite alphabet: [alphabet] lists every symbol *)
      Variable alphabet : seq A.
      Hypothesis alphabet_complete : forall a : A, a \in alphabet.

      (* all sequences of n symbols *)
      Fixpoint sym_seqs (n : nat) : seq (seq A) :=
        if n is n'.+1 then [seq a :: xs | a <- alphabet, xs <- sym_seqs n']
        else [:: [::]].

      Lemma sym_seqs_complete (xs : seq A) : xs \in sym_seqs (size xs).
      Proof.
        elim: xs => [|a xs IH] /=; first by rewrite mem_seq1.
        apply: allpairs_f; [exact: alphabet_complete | exact: IH].
      Qed.

      Lemma In_map_mem (T1 : eqType) (T2 : Type) (f : T1 -> T2) (x : T1) (l : seq T1) :
        x \in l -> List.In (f x) (map f l).
      Proof.
        elim: l => [|y l IH]; first by rewrite in_nil.
        rewrite in_cons /= => /orP [/eqP ->|/IH H]; by [left|right].
      Qed.

      (* Lemma 3.5, on all of E: only finitely many s have R^E(s,r) <> 0 *)
      Theorem RE_nonzero_finite (r : regex) :
        exists l : seq regex, forall s, RE s r <> 0 -> List.In s l.
      Proof.
        exists [seq fill (skel_of r) xs | xs <- sym_seqs (holes (skel_of r))].
        move=> s Hs.
        have Hpos : 0 < RE s r.
        { case: (RE_range s r) => H0 _.
          apply: Rnot_le_lt => Hle.
          exact: Hs (Rle_antisym _ _ Hle H0). }
        have Hsk := RE_pos_skel_of Hpos.
        rewrite -(fill_skel_of s) Hsk.
        apply: In_map_mem.
        rewrite -Hsk -size_syms_of.
        exact: sym_seqs_complete.
      Qed.

    End FiniteSyntacticSimilarity.

  End GeneralRegexSimilarity.

End SimilarityRelations.
