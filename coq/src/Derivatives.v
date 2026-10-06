From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import RegexSemantics.
From regexderiv Require Import Nullable.
From regexderiv Require Import Languages.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Derivatives (X : OSYM).
  Import X.

  Module Export N := Nullable X.

  Definition language := pred word.

  (* semantic derivatives *)
  Definition dlang_char (a : A) (L : language) : language :=
    fun w => L (a :: w).

  Definition dlang (u : word) (L : language) : language :=
    fun w => L (u ++ w).

  Lemma dlang_nil : forall L, dlang [::] L =i L.
  Proof. by move=> L w /=. Qed.

  Lemma dlang_cat : forall u v L, dlang (u ++ v) L =i dlang v (dlang u L).
  Proof. by move=> u v L w /=; rewrite /dlang /= /in_mem /= catA. Qed.

  (* syntactic derivatives *)
  Fixpoint D_char (a : A) (r : regex) : regex :=
    match r with
    | Empty      => Empty
    | Eps        => Empty
    | Char b     => if a == b then Eps else Empty
    | Alt r1 r2  => Alt (D_char a r1) (D_char a r2)
    | And r1 r2  => And (D_char a r1) (D_char a r2)
    | Seq r1 r2  => Alt (Seq (D_char a r1) r2)
                       (Seq (nu r1) (D_char a r2))
    | Star r1    => Seq (D_char a r1) (Star r1)
    | Neg r1     => Neg (D_char a r1)
    end.

  Fixpoint D (u : word) (r : regex) : regex :=
    if u is a :: v then D v (D_char a r) else r.

  Lemma D_nil : forall r, D [::] r = r.
  Proof. by []. Qed.

  Lemma D_cat : forall u v r, D (u ++ v) r = D v (D u r).
  Proof.
    elim=> [|a u IHu] v r /=; first by [].
    by rewrite IHu.
  Qed.

  Lemma D_char_correct : forall a r w, (w \in D_char a r) = ((a :: w) \in r).
  Proof.
    move=> a; elim=> //=.

    - (* Char *)
      move=> b w.
      rewrite /in_mem /=.
      case: ifP=> [/eqP ->|hab] /=.
      + (* a=b *)
        by rewrite /eps /atom
                   /Languages.eps /Languages.atom
                   /= eqseq_cons eqxx /=.
      + (* a!=b *)
        move/negPf: hab=>hab.
        by rewrite /void /atom
                   /Languages.void /Languages.atom
                   /= eqseq_cons hab /=.

    - (* Alt *)
      move=> r1 IH1 r2 IH2 w.
      rewrite /in_mem /= /plus /Languages.plus /=.
      exact: (congr2 orb (IH1 w) (IH2 w)).

    - (* Seq *)
      move=> r1 IH1 r2 IH2 w.
      apply/idP/idP.

      + (* -> *)
        move/orP=> [H | H].

        * (* from D_a(r1)·r2 *)
          move/Languages.concP: H => [u [v [Huv [Hu Hv]]]].
          have Har1 : (a :: u) \in r1 by rewrite -(IH1 u).
          apply/Languages.concP_inv.
          exists (a :: u), v; split.
          -- by rewrite Huv -cat_cons.
          -- by split.

        * (* from nu(r1)·D_a(r2) *)
          move/Languages.concP: H => [u [v [Huv [Hu Hv]]]].
          have Hu_nu : (u \in nu r1) := Hu.
          move: Hu_nu; rewrite mem_nu.
          move/andP=> [/eqP Hu_nil Heps].
          have -> : w = v by move: Huv; rewrite Hu_nil cat0s.
          have Har2 : (a :: v) \in r2 by rewrite -(IH2 v).
          apply/Languages.concP_inv.
          exists [::], (a :: v); split.
          -- by rewrite cat0s.
          -- split.
             ++ have Hnil : ([::] \in r1) by move: Heps; rewrite nullable_correct.
                exact Hnil.
             ++ exact Har2.

      + (* <- *)
        move=> Hseq.
        have [u [v [Hcat [Hu Hv]]]] := Languages.concP Hseq.

        case: u Hcat Hu => [|b u] Hcat Hu.

        * (* u = [] *)
          apply/orP; right.
          apply/Languages.concP_inv.
          exists [::], w; split; first by rewrite cat0s.
          split.
          -- (* [] ∈ nu r1 *)
             have Heps : has_eps r1 by move: Hu; rewrite nullable_correct.
             rewrite /in_mem /nu Heps /= /eps.
             by [].
          -- (* w ∈ D_a(r2) from (a::w) ∈ r2 *)
             have Har2 : (a :: w) \in r2.
             { have -> : a :: w = v by move: Hcat; rewrite cat0s.
               exact Hv. }
             by move: Har2; rewrite -(IH2 w).

        * (* u = b::u *)
          move/eqP: Hcat; rewrite eqseq_cons; move/andP=> [/eqP Hb /eqP Htail].
          apply/orP; left.
          apply/Languages.concP_inv.
          exists u, v; split; first exact: Htail.
          split.
          -- (* u ∈ D_a(r1) from (a::u) ∈ r1 *)
             have Hu_a : (a :: u) \in r1 by move: Hu; rewrite Hb.
             have Hu' : u \in D_char a r1 by move: Hu_a; rewrite -(IH1 u).
             exact Hu'.
          -- exact Hv.

    - (* Star *)
      move=> r IHr w.
      apply/idP/idP.

      + move/Languages.concP=> [u [v [-> [Hu Hv]]]].
        have Har : (a :: u) \in r by rewrite -(IHr u).
        apply: (Languages.star_cons_split_inv (A:=A) (L:=den r) (a:=a)).
        exists u, v; split=> //; split=> //.

      + move=> Hstar.
        have [u [v [-> [Har Hv]]]] :=
          Languages.star_cons_split (A:=A) (L:=den r) (a:=a) (w:=w) Hstar.
        have Hu : u \in D_char a r by rewrite (IHr u).
        apply/Languages.concP_inv.
        exists u, v; split=> //; split=> //.

    - (* And *)
      move=> r1 IH1 r2 IH2 w.
      rewrite /in_mem /= /prod /Languages.prod /=.
      exact: (congr2 andb (IH1 w) (IH2 w)).

    - (* Neg *)
      move=> r IHr w.
      rewrite /in_mem /= /compl /Languages.compl /=.
      exact: (congr1 negb (IHr w)).
  Qed.

  Lemma D_correct : forall u r w, (w \in D u r) = ((u ++ w) \in r).
  Proof.
    elim=> [|a u IHu] r w //=.
    rewrite IHu D_char_correct.
    by rewrite -cat_cons.
  Qed.


  Definition regular (L : language) : Prop :=
    exists r : regex, L =i den r.

  Lemma dlang_correct (u : word) (L : language) (w : word) :
    dlang u L w = L (u ++ w).
  Proof. by []. Qed.

  Lemma dlang_charE (a : A) (L : language) :
    dlang [:: a] L =i dlang_char a L.
  Proof. by move=> w. Qed.

  Theorem derivative_regular (L : language) (u : word) :
    regular L -> regular (dlang u L).
  Proof.
    move=> [r Hr].
    exists (D u r) => w.
    rewrite /dlang.
    (* rewrite L (u++w) using the witness r *)
    rewrite /dlang /in_mem /=.
    have HL : L (u ++ w) = ((u ++ w) \in r).
      by move: (Hr (u ++ w)); rewrite /in_mem /=.
    rewrite HL.
    by rewrite -(D_correct u r w).
  Qed.

End Derivatives.
