From CRIS.common Require Import CRIS.
From CRIS.promise_free.pfmem Require Import PFMemHeader PFMemI PFMemA.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.gpfsl Require Import base.
From CRIS.promise_free.model Require Import
  Time TView View Cell Memory Global Time.
From CRIS.promise_free.pfmem Require Import
  PFMemIAproof PFMemIAAlloc PFMemIAFree PFMemIAWrite PFMemIARead
  PFMemIACAS PFMemIAFence PFMemIASpawn.

Module PFMemIA. Section PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Lemma ctxr sp :
    PFMemA.init_cond ⊢ ctx_refines (PFMemI.t PFMemA.syn []) (PFMemA.t sp).
  Proof using.
    etrans; cycle 1.
    { eapply (main_adequacy
        (PFMemI.t PFMemA.syn []) (PFMemA.t sp)). }
    cStartModSim
      (fun STATE : stateGS Σ => PFMemIA.Ist (STATE := STATE)).
    { iPoseProof (state_init_tgt_acc _ _ PFMemI.v_config with "TGT") as
        (ov) "(%Hconfig & CONFIG & _)".
      { set_solver. }
      simpl_map. subst ov.
      iDestruct "INIT" as "[TVA [HA HFA]]"; ss.
      rewrite /PFMemIA.Ist.
      iExists (Global.init []), _, (View.init []); iSplit; cycle 1.
      { iFrame. rewrite Memory.cut_init //. }
      iPureIntro; splits; ss.
      { intros loc t f val V [-> [-> Hget]]%Memory.init_get Hacc.
        rewrite /Memory.init /Memory.accessible /= /Block.accessible /= in Hacc.
        repeat case_match; ss;
          bsimpl; destruct Hacc as [?%Z.leb_le ?%Z.ltb_lt]; clarify; lia.
      }
      { apply Memory.closed_view_init. }
      { apply Configuration.init_wf; auto. }
      { intros loc Hpre.
        rewrite /Memory.is_prealloced /Block.is_prealloced in Hpre.
        rewrite /Memory.get_cell /=; des_ifs; ss.
      }
      { intros tid l lc; rewrite IdentMap.Facts.mapi_o; cycle 1.
        { ii; subst; ss. }
        destruct (decide (tid = 1%positive)); subst; ss.
        { i; clarify; ss. }
        rewrite IdentMap.singleton_neq //=.
      }
    }
    { iApply simF_alloc. }
    { iApply simF_free. }
    { iApply simF_read. }
    { iApply simF_write. }
    { iApply simF_cas. }
    { iApply simF_fence. }
    { iApply simF_spawn. }
  Qed.
End PFMemIA. End PFMemIA.
