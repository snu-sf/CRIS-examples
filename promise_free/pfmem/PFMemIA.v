Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import
  PFMemIAproof PFMemIAInit PFMemIAAlloc PFMemIAFree PFMemIAWrite PFMemIARead
  PFMemIACAS PFMemIAFence PFMemIASpawn.

Module PFMemIA. Section PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Lemma ctxr sp :
    ctx_refines
      (PFMemA.t sp, PFMemA.init_cond)
      (PFMemI.t PFMemA.syn [], emp%I).
  Proof using.
    eapply main_adequacy with (Ist := PFMemIA.Ist).
    cStartModSim.
    { iIntros "[TVA [HA HFA]]"; ss.
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
    { apply simF_alloc. }
    { apply simF_free. }
    { apply simF_read. }
    { apply simF_write. }
    { apply simF_cas. }
    { apply simF_fence. }
    { apply simF_spawn. }
  Qed.
End PFMemIA. End PFMemIA.