(* Require Import CRIS.
Require Import IncrHeader IncrI IncrA.
Require Import ProphecyHeader ProphecyA.
Require Import MemHeader MemA.
Require Import SchHeader SchTactics SchA.

(* Prophecy variables related lemmas *)
CoInductive bstream : Type :=
| bnil
| bcons (b : bool) (tl : bstream).

CoFixpoint bstream_gen (obs_seq : nat → bool) (n : nat) : bstream :=
  bcons (obs_seq n) (bstream_gen obs_seq (S n)).

Definition bstream_unf (b : bstream) := match b with bnil => bnil | bcons b tl => bcons b tl end.
Lemma bstream_unf_eq (b : bstream) : b = bstream_unf b. Proof. destruct b; ss. Qed.

Fixpoint prefix (l : list bool) (s : bstream) : Prop :=
  match l with
  | nil => True
  | b :: tl =>
      match s with
      | bnil => False
      | bcons b' btl => b' = b ∧ prefix tl btl
      end
  end.

Fixpoint app (l : list bool) (s : bstream) : bstream :=
  match l with
  | nil => s
  | b :: tl => bcons b (app tl s)
  end.

Lemma app_app (l1 l2 : list bool) (s : bstream) :
  app (l1 ++ l2) s = app l1 (app l2 s).
Proof. induction l1; ss. f_equal; ss. Qed.

Lemma app_prefix (l : list bool) (s : bstream) :
  prefix l (app l s).
Proof. induction l; ss. Qed.

Lemma bstream_gen_app (obs_seq : nat → bool) (n : nat) :
  bstream_gen obs_seq 0 = app (rev (Prophecy.firstn obs_seq n)) (bstream_gen obs_seq n).
Proof.
  induction n; ss. rewrite IHn /= app_app /=. f_equal. erewrite (bstream_unf_eq _). ss.
Qed.

Lemma bstream_gen_prefix (obs_seq : nat → bool) (n : nat) :
  prefix (rev (Prophecy.firstn obs_seq n)) (bstream_gen obs_seq 0).
Proof. rewrite (bstream_gen_app _ n); eauto using app_prefix. Qed.

Fixpoint nth (bs : bstream) (n : nat) :=
  match bs with
  | bnil => None
  | bcons b btl =>
      match n with
      | O => Some b
      | S n' => nth btl n'
      end
  end.

Variant inf_failF coself : bstream → Prop :=
| inf_fail_fail tl (CONT : coself tl) : inf_failF coself (bcons false tl).
Definition inf_fail := paco1 inf_failF bot1.
Lemma inf_failF_mon : monotone1 inf_failF. Proof. ii; inv IN; econs; eauto. Qed.
Hint Constructors inf_failF : core.
Hint Unfold inf_fail : core.
Hint Resolve inf_failF_mon : paco.

Lemma not_inf_fail (bs : bstream) : ¬ inf_fail bs → ∃ n, nth bs n <> Some false.
Proof.
  destruct (classic (∃ n, nth bs n <> Some false)); eauto.
  intros NINF; exfalso; eapply NINF; clear NINF.
  depgen bs. pcofix CIH. intros bs EX.
  destruct bs.
  { exfalso; eapply EX; exists 0; ss. }
  destruct b.
  { exfalso; eapply EX; exists 0; ss. }
  pstep. econs. right. eapply CIH. intros [n NEQ]; eapply EX; exists (S n); ss.
Qed.

Local Program Definition incr_proph : Prophecy.t := {|
  Prophecy.Pro := bstream;
  Prophecy.Obs := bool;
  Prophecy.consistent := λ l p, prefix (rev l) p;
  Prophecy.obs_default := true;
|}.
Next Obligation.
  intros obs_seq; exists (bstream_gen obs_seq 0); eauto using bstream_gen_prefix.
Qed.

Module IncrIA. Section IncrIA.
  Import IncrI.
  
  Context `{_crisG: !crisG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
  Context `{_prophG: !prophG}.

  Definition x := ProphecyA.t.
  
  Context (q : Qp) (E : coPset) (sp : sp_type).
  Context (sp_user : spl_type).
  Context `{sp_incl (SchAS.sp sp_user E q) sp}.


  Local Definition MA := IncrA.t q sp.
  Local Definition MI := IncrI.t ★  ProphecyA.t sp.
  Local Definition Ist : alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ st_t,
      ∃ n,
        ⌜st_t = [(v_cnt, n↑)]⌝
        ∗ ProphecyRA.free_id (λ i, i.1 = "Incr" ∧ ∃ n', i.2↓↓ = Some n' ∧ n' >= n)%type)
    %I.

  (* Lemma simF_incr : HSim.sim_fun open MA MI Ist IncrHdr.incr. *)
  (* Proof. *)
  (*   init_simF u 0. *)
  (*   iDestruct "IST" as "[%n [-> F]]". *)
  (*   steps_l. iDestruct "ASM" as "[TID [-> ->]]". hss. inv G0. rename q3 into b, q4 into ofs. *)
  (*   steps_r. hss. steps_r. *)

  (*   inline_r. *)
  (*   iPoseProof (ProphecyAS.free_id_split _ (id_incr n) with "F") as "> [ID F]". *)
  (*   { ss. esplits; eauto. hss. } *)
  (*   force_r (id_incr n, incr_proph). steps_r. forces_r. *)
  (*   iFrame. iSplit; eauto. *)
  (*   steps_r. iDestruct "GRT" as "[[%p [-> P]] ->]". hss. steps_r. *)
  (*   sch_yield_r. iFrame. iSplitR "P". *)
  (*   { iExists (1 + n); iSplit; eauto. iApply (ProphecyAS.free_id_iff with "F"). *)
  (*     intros [name sany]; s; split. *)
  (*     { rewrite /id_incr; intros [-> [n' [? ?]]]. des_ifs; esplits; eauto; hss; lia. } *)
  (*     { des_ifs. intros; des; clarify; esplits; eauto. *)
  (*       assert (n' ≠ n). *)
  (*       { ii; clarify; apply n0. rewrite /id_incr. hexploit SAny.downcast_upcast; eauto. *)
  (*         i; clarify; hss. *)
  (*       } *)
  (*       lia. *)
  (*     } *)
  (*   } *)
  (*   clear dependent nths st_src; iIntros (nths st_s st_t NODS NODD) "IST TID". *)

  (*   destruct (classic (inf_fail p)). *)
  (*   {  *)
  (*   } *)

  (*     split; des_ifs. ; destruct i; ss. *)
  (*     split; ii; des_ifs; destruct (id_incr n); ss; des; clarify; eauto.  } *)
End IncrIA. End IncrIA. *)
