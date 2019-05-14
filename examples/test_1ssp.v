Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rtrigo_def.
Require Import Logic.Logic.

Require Import Logic.DifferentialInduction.
Require Import Logic.ContinuousProofRules.
Require Import ChargeCore.Tactics.Lemmas.
Require Import ArithFacts.

Require Import Logic.BasicProofRules.

Require Import Examples.System.


Open Scope string_scope.
Open Scope HP_scope.


Section test_1ssp.

  Variable d : R.
  Variable a : R.
  Variable b : R.
  Variable kP : R.
  Variable x0 : R.
  Hypothesis d_gt_0 : (d > 0)%R.
  (* Hypothesis a_neq_0 : (a =/= 0)%R.
  Hypothesis kP_bound : (0 < ((1-b/a*kP)* 
    eval_term exp(a*d) _ _
    +b/a*kP) < 1)%R.  *)

  Definition w : Evolution :=
    fun st' =>
      st' "x" = a * "x" //\\ st' "t" = 1.

  Definition Ctrl : Formula :=
    "T"! = d //\\ Unchanged ("x"::"t"::nil).

  Definition Init : Formula :=
    "x"=x0 //\\ "T" = d //\\ "t" = 0.

  Definition Next : ActionFormula :=
    Sys (Ctrl //\\ "T" <= d) w d.

  Definition Spec : Formula :=
    Init //\\ []Next.

  Definition Abs (t : Term) (f : Term -> Formula) : Formula :=
    (t > 0 -->> f t) //\\ (t <= 0 -->> f (--t)).

  Lemma trivial_test_exp :
    |-- exp(0)=1.
  Proof.
    breakAbstraction. intros. apply exp_0.
  Qed.

  Lemma exp0_testR :
    |-- forall a : R , a-a=0.
  Proof.
    breakAbstraction. intros.
  Admitted.
  
  Lemma test :
    Continuous w
    |-- Exists x : R, "x" = x //\\
      Exists t : R, "t" = t //\\
                    "x"! = x * exp(a*"t"! - a*t) //\\
                    "t"! >= t.
  Proof.
    apply Exists_with_st with (t:="x"). intros.
    charge_intros. charge_split; [ charge_tauto | ].
    apply Exists_with_st with (t:="t"). intros.
    charge_intros. charge_split; [ charge_tauto | ].
    match goal with
      |- _ |-- ?GG => eapply diff_ind
                      with (Hyps:=TRUE)
                             (G:=unnext GG)
    end.
    + tlaIntuition.
    + tlaIntuition.
    + charge_tauto.
    + tlaIntuition.
    + charge_tauto.
    + solve_linear. rewrite -> H1. rewrite -> H2.
      assert(exp (a*x1-a*x1)=1%R).
      - admit.
      - rewrite H0. solve_linear.
    + tlaIntuition.
    + solve_linear. rewrite H2. rewrite H1. admit.
    Admitted.
    
  
(*  
  Lemma test_exp : 
    |-- Spec -->> []("x"=x0*exp(a*"t")).
  Proof.
    charge_intros.
    eapply BasicProofRules.discr_indX.
    + tlaIntuition.
    + unfold Spec. charge_tauto.
    + unfold Spec, Init, Next.
      rewrite BasicProofRules.Always_now.
      2: charge_assumption.
      unfold Sys, Ctrl, w, World.
      solve_linear.
      - rewrite H4.
*)

  Definition Stable x : Formula :=
    Forall a : R,
      a > 0 -->>
      Exists b : R,
        b > 0 //\\
        ((Abs x (fun t => t < b)) -->> []Abs x (fun t => t < a)).

  Ltac decompose_hyps :=
    repeat first [rewrite land_lor_distr_R |
                  rewrite land_lor_distr_L |
                  apply lorL ].

  Definition IndInv : Formula :=
    ("v" < 0 -->> --"v"*"T" <= "x") //\\
    ("v" >= 0 -->> "v"*"T" <= --"x").

  Lemma indinv_direction :
    IndInv //\\ "T" >= 0 |-- "v"*"x" <= 0.
  Proof.
    solve_nonlinear.
  Qed.

  Lemma spec_indinv :
    |-- Spec -->> []IndInv.
  Proof.
    charge_intros.
    eapply BasicProofRules.discr_indX.
    + tlaIntuition.
    + unfold Spec. charge_tauto.
    + unfold Spec, IndInv, Init.
      charge_split.
      { unfold Next, Sys, Discr. rewrite landC. tlaRevert.
        rewrite BasicProofRules.Always_now.
        2: charge_assumption.
        tlaRevert. apply forget_prem. charge_intros.
        tlaAssert ("v"*d = --"x").
        { solve_linear. rewrite H0.
          rewrite Raxioms.Rmult_assoc.
          rewrite <- RIneq.Rinv_l_sym;
            solve_linear.
          rewrite H0.
          rewrite Raxioms.Rmult_assoc.
          rewrite <- RIneq.Rinv_l_sym;
            solve_linear.  }
        { solve_nonlinear. } }
      { unfold Next, Sys, Discr. rewrite landC. tlaRevert.
        rewrite BasicProofRules.Always_now.
        2: charge_assumption.
        tlaRevert. apply forget_prem. charge_intros.
        tlaAssert ("v"*d = --"x").
        { solve_linear. rewrite H0.
          rewrite Raxioms.Rmult_assoc.
          rewrite <- RIneq.Rinv_l_sym;
            solve_linear.
          rewrite H0.
          rewrite Raxioms.Rmult_assoc.
          rewrite <- RIneq.Rinv_l_sym;
            solve_linear. }
        { solve_nonlinear. } }
    + unfold Next.
      unfold Sys. decompose_hyps.

      * simpl. restoreAbstraction. charge_split.
        { solve_linear. rewrite_next_st.
          repeat rewrite RIneq.Rminus_0_l.
          rewrite <- RIneq.Ropp_mult_distr_l_reverse.
          rewrite RIneq.Ropp_involutive. rewrite Raxioms.Rmult_comm.
          rewrite <- Raxioms.Rmult_assoc. apply Rmult_le_algebra; [ auto | ].
          assert (Stream.hd tr "x" > 0)%R.
          { clear - H0 d_gt_0. assert (/ d > 0)%R.
            { solve_linear. }
            { clear d_gt_0. solve_nonlinear. } }
          { solve_nonlinear. } }
        { solve_linear. rewrite_next_st.
          repeat rewrite RIneq.Rminus_0_l.
          rewrite Raxioms.Rmult_comm.
          rewrite <- Raxioms.Rmult_assoc. apply Rmult_le_algebra; [ auto | ].
          assert (Stream.hd tr "x" <= 0)%R.
          { clear - H0 d_gt_0. assert (/ d > 0)%R.
            { solve_linear. }
            { clear d_gt_0. solve_nonlinear. } }
          { solve_nonlinear. } }

      * unfold World.
        eapply diff_ind with (Hyps:=ltrue).
        { tlaIntuition. }
        { tlaIntuition. }
        { charge_tauto. }
        { tlaIntuition. }
        { charge_tauto. }
        { charge_tauto. }
        { repeat tlaSplit;
          try solve [solve_linear |
                     tlaIntro; eapply unchanged_continuous;
                     [ tlaAssume | solve_linear ] ]. }
        { simpl deriv_formula. restoreAbstraction.
          charge_intros.
          unfold lift2, mkEvolution, w.
          repeat charge_split; charge_intros;
          try solve [ solve_linear
                    | eapply zero_deriv with (x:="v");
                      [ charge_tauto | tlaIntuition |
                        solve_linear ] ].
          solve_nonlinear.
          solve_nonlinear.
          }
  Qed.

(*
  Lemma indinv_stable :
    |-- []IndInv -->> Stable "x".
  Proof.
    unfold Stable. charge_intros.
    eapply lexistsR. instantiate (1:=x).
    charge_split.
    + charge_tauto.
    + charge_intros.
      tlaAssert ([]IndInv).
      * charge_tauto.
      * apply forget_prem. apply BasicProofRules.always_imp.
        unfold IndInv, Abs. charge_intros. charge_split; charge_intros.
        - tlaAssert ("v" < 0 \\// "v" >= 0);
          [ solve_linear | charge_intros ].
          decompose_hyps.
          { solve_linear. clear H3. z3 solve_dbg.
     *)   
          
  Lemma spec_stable :
    |-- Spec -->> Stable "x".
  Proof.
    charge_intros. tlaAssert ([]IndInv).
    { apply lrevert. apply spec_indinv. }
    { unfold Stable. charge_intros.
      eapply lexistsR. instantiate (1:=x).
      charge_split.
      - charge_tauto.
      - charge_intros.
        eapply BasicProofRules.discr_indX
        with (A:=IndInv //\\ Next //\\ BasicProofRules.next IndInv).
        + tlaIntuition.
        + unfold Spec. repeat rewrite <- BasicProofRules.Always_and.
           
          admit.
        + charge_tauto.
        + unfold Next, Sys. simpl BasicProofRules.next.
          restoreAbstraction. decompose_hyps.
          * solve_linear. 
          * unfold World.
            tlaAssert ("v"! < 0 \\// "v"! >= 0);
              [ solve_linear | ].
            charge_intros. decompose_hyps.
            { charge_split; charge_intros.
              + eapply diff_ind with (Hyps:="v" < 0) (G:="x" < x).
                - tlaIntuition.
                - tlaIntuition.
                - charge_tauto.
                - tlaIntuition.
                - eapply zero_deriv with (x:="v").
                  * charge_tauto.
                  * solve_linear.
                  * solve_linear.
                - solve_linear.
                - unfold mkEvolution, w.
                  repeat charge_split; charge_intros;
                  try solve [ solve_linear
                            | eapply zero_deriv with (x:="v");
                              [ charge_tauto | tlaIntuition |
                                solve_linear ] ].
                - simpl deriv_formula. restoreAbstraction.
                  charge_intros.
                  unfold mkEvolution, w.
                  repeat charge_split; charge_intros;
                  try solve [ solve_linear
                            | eapply zero_deriv with (x:="v");
                              [ charge_tauto | tlaIntuition |
                                solve_linear ] ].
              + admit. }
            { charge_split; charge_intros.
              + admit.
              + eapply diff_ind with (Hyps:="v" >= 0) (G:=--"x" < x).
                - tlaIntuition.
                - tlaIntuition.
                - charge_tauto.
                - tlaIntuition.
                - eapply zero_deriv with (x:="v").
                  * charge_tauto.
                  * solve_linear.
                  * solve_linear.
                - solve_linear.
                - unfold mkEvolution, w.
                  repeat charge_split; charge_intros;
                  try solve [ solve_linear
                            | eapply zero_deriv with (x:="v");
                              [ charge_tauto | tlaIntuition |
                                solve_linear ] ].
                - simpl deriv_formula. restoreAbstraction.
                  charge_intros.
                  unfold mkEvolution, w.
                  repeat charge_split; charge_intros;
                  try solve [ solve_linear
                            | eapply zero_deriv with (x:="v");
                              [ charge_tauto | tlaIntuition |
                                solve_linear ] ]. }
Qed.

End P.

Close Scope string_scope.
Close Scope HP_scope.