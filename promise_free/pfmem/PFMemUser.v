(* Require Import CRIS.
Require Import SchHeader SchA.
Require Import PFMemHeader PFMemA PFMemI.
Require Import Time Cell View TView base.
Require Import ITactics.
Require Import PMod HMod.

Definition PFM : string := "PFMem".

Module PFMem. Section PFMem.
  Context {E : Type → Type}.
  Context `{coreE -< E, callE -< E}.

  Definition alloc : Z → itree E Val.t :=
    Seal.sealing PFM
      (λ sz,
        'tid : nat <- ccallU SchHdr.get_tid tt;;
        let tid : Ident.t := Tid.of_succ_nat tid in
        ccallU PFMemHdr.alloc (tid, sz)).

  Definition free : Loc.t → itree E Val.t :=
    Seal.sealing PFM
      (λ loc,
        'tid : nat <- ccallU SchHdr.get_tid tt;;
        let tid : Ident.t := Tid.of_succ_nat tid in
        ccallU PFMemHdr.free (tid, loc)).

  Definition read : Loc.t * Ordering.t → itree E Val.t :=
    Seal.sealing PFM
      (λ '(loc, ord),
        'tid : nat <- ccallU SchHdr.get_tid tt;;
        let tid : Ident.t := Tid.of_succ_nat tid in
        ccallU PFMemHdr.read (tid, loc, ord)).
  
  Definition write : Loc.t * Val.t * Ordering.t → itree E Val.t :=
    Seal.sealing PFM
      (λ '(loc, val, ord),
        'tid : nat <- ccallU SchHdr.get_tid tt;;
        let tid : Ident.t := Tid.of_succ_nat tid in
        ccallU PFMemHdr.write (tid, loc, val, ord)).

  Definition cmp : Val.t * Val.t → itree E Val.t :=
    Seal.sealing PFM
      (λ '(val1, val2),
        'tid : nat <- ccallU SchHdr.get_tid tt;;
        let tid : Ident.t := Tid.of_succ_nat tid in
        ccallU PFMemHdr.cmp (tid, val1, val2)).
  
  Definition cas : Loc.t * Val.t * Val.t * Ordering.t * Ordering.t → itree E Val.t :=
    Seal.sealing PFM
      (λ '(loc, old, new, ordr, ordw),
        'tid : nat <- ccallU SchHdr.get_tid tt;;
        let tid : Ident.t := Tid.of_succ_nat tid in
        ccallU PFMemHdr.cas (tid, loc, old, new, ordr, ordw)).

  Definition faa : Loc.t * Val.t * Ordering.t * Ordering.t → itree E Val.t :=
    Seal.sealing PFM
      (λ '(loc, addendum, ordr, ordw),
        'tid : nat <- ccallU SchHdr.get_tid tt;;
        let tid : Ident.t := Tid.of_succ_nat tid in
        ccallU PFMemHdr.faa (tid, loc, addendum, ordr, ordw)).

  Definition fence : Ordering.t * Ordering.t → itree E Val.t :=
    Seal.sealing PFM
      (λ '(ordr, ordw),
        'tid : nat <- ccallU SchHdr.get_tid tt;;
        let tid : Ident.t := Tid.of_succ_nat tid in
        ccallU PFMemHdr.fence (tid, ordr, ordw)).

  (* Definition init : Ident.t → itree E Val.t :=
    Seal.sealing PFM
      (λ tid_c,
        'tid : nat <- ccallU SchHdr.get_tid tt;;
        let tid : Ident.t := Tid.of_succ_nat tid in
        ccallU PFMemHdr.init (tid, tid_c)). *)

End PFMem. Section PFMemTac.
  Import SchAS HistoryRA AtomicRA.
  Context `{_sinvGpreS: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !schG}.
  Context `{_histGS: !histGS}.
  Context `{_atomicG: !atomicG}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := nat → state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → nat → state * itree hmodE R_s → state * itree hmodE R_t → iProp Σ.

  Implicit Types r g : rel.
  Implicit Types ps pt : bool.
  Implicit Types nths : nat.
  Implicit Types E : coPset.

  Context (fl_s fl_t : alist string (Any.t → itree hmodE Any.t)).
  Context (Ist : nat → alist key Any.t → alist key Any.t → iProp Σ).
  Context (t : option bool).
  Context (υ ν : univ_id).
  Context (E : coPset).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (nths : nat).
  Context (st_s st_t : state).

  Context (LE: ν < υ).

  Local Notation pfmem_fn f sp := (HModTr.sandbox_body (wmask_all, PFMemA.scopes, (SModTr.trans_ktree sp (mk_specbody f fbody_trivial)))).
  Local Notation sch_get_tid sp w := (HModTr.sandbox_body (wmask_all, SchAPure.scopes, (SModTr.trans_ktree sp (mk_specbody (SchAS.get_tid_spec w) fbody_trivial)))).
  
  Lemma wsim_alloc_tgt r g (msk_t:_→bool) sc_t sp_t i_s k_t my_tid
      (MemInFLT : alist_find PFMemHdr.alloc fl_t = Some (pfmem_fn PFMemA.alloc_spec sp_t))
      (TidInFLT : alist_find SchHdr.get_tid fl_t = Some (sch_get_tid sp_t ν)) 
      (MASKTID : msk_t SchHdr.get_tid)
      (MASKMEM : msk_t PFMemHdr.alloc)
      sz 𝓥
    :
    Ist nths st_s st_t ∗ tid_user my_tid ∗
    precond (PFMemA.alloc_spec) (Tid.of_succ_nat my_tid, sz, 𝓥) (Tid.of_succ_nat my_tid, sz)↑ (Tid.of_succ_nat my_tid, sz)↑ ∗
    (∀ nths st_s st_t ret,
      Ist nths st_s st_t -∗ tid_user my_tid -∗
      (postcond (PFMemA.alloc_spec) (Tid.of_succ_nat my_tid, sz, 𝓥) ret↑ ret↑) -∗
      wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, i_s)
        (st_t, k_t ret))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, i_s)
      (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans (alloc sz))) >>= k_t).
  Proof using LE.
    rewrite !WSim.wsim_eq /WSim.wsim_def.
    iIntros "[IST [TID [PRE SIM]]] P".
    rewrite /WSim.wsim_pre.
    iApply isim_nodup. iIntros (????).
    rewrite /alloc. unseal PFM. steps_r. inline_r.
    iPoseProof (winv_split υ ν with "P") as "> [V U]"; first eauto.
    forces_r. iSplitL "TID V"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[V [[-> TID] ->]]". hss.
    steps_r. inline_r. hss. force_r (Tid.of_succ_nat my_tid, sz, 𝓥). steps_r.
    force_r ((Tid.of_succ_nat my_tid, sz)↑). steps_r.
    force_r. iSplitL "PRE".
    { iDestruct "PRE" as "[[% TV] %]". iSplit; eauto. }
    steps_r. iDestruct "GRT" as "[POST ->]". iDestruct "POST" as (??) "[-> [TV [LOC PT]]]".
    hss. steps_r.
    iAssert ( |==> winv υ ⊤ )%I with "[U V]" as ">P".
    { iDestruct "U" as "[A [W C]]". iFrame. iApply "C". iFrame. }    
    iApply ("SIM" with "IST TID [TV LOC PT]"); iFrame; eauto.
  Qed.

  Lemma wsim_free_tgt r g (msk_t:_→bool) sc_t sp_t i_s k_t my_tid
      (MemInFLT : alist_find PFMemHdr.free fl_t = Some (pfmem_fn PFMemA.free_spec sp_t))
      (TidInFLT : alist_find SchHdr.get_tid fl_t = Some (sch_get_tid sp_t ν)) 
      (MASKTID : msk_t SchHdr.get_tid)
      (MASKMEM : msk_t PFMemHdr.free)
      loc n 𝓥
    :
    Ist nths st_s st_t ∗ tid_user my_tid ∗
    precond (PFMemA.free_spec) (Tid.of_succ_nat my_tid, loc, n, 𝓥)
      (Tid.of_succ_nat my_tid, loc)↑ (Tid.of_succ_nat my_tid, loc)↑ ∗
    (∀ nths st_s st_t ret,
      Ist nths st_s st_t -∗ tid_user my_tid -∗
      (postcond (PFMemA.free_spec) (Tid.of_succ_nat my_tid, loc, n, 𝓥) ret↑ ret↑) -∗
      wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, i_s)
        (st_t, k_t ret))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, i_s)
      (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans (free loc))) >>= k_t).
  Proof using LE.
    rewrite !WSim.wsim_eq /WSim.wsim_def.
    iIntros "[IST [TID [PRE SIM]]] P".
    rewrite /WSim.wsim_pre.
    iApply isim_nodup. iIntros (????).
    rewrite /free. unseal PFM. steps_r. inline_r.
    iPoseProof (winv_split υ ν with "P") as "> [V U]"; first eauto.
    forces_r. iSplitL "TID V"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[V [[-> TID] ->]]". hss.
    steps_r. inline_r. hss. force_r (Tid.of_succ_nat my_tid, loc, n, 𝓥). steps_r.
    force_r ((Tid.of_succ_nat my_tid, loc)↑). steps_r.
    force_r. iSplitL "PRE".
    { iDestruct "PRE" as "[[% TV] %]". iSplit; eauto. }
    steps_r. iDestruct "GRT" as "[-> ->]".
    hss. steps_r.
    iAssert ( |==> winv υ ⊤ )%I with "[U V]" as ">P".
    { iDestruct "U" as "[A [W C]]". iFrame. iApply "C". iFrame. }
    iApply ("SIM" with "IST TID"); iFrame; eauto.
  Qed.

  Lemma wsim_read_na_tgt r g (msk_t:_→bool) sc_t sp_t i_s k_t my_tid
      (MemInFLT : alist_find PFMemHdr.read fl_t = Some (pfmem_fn PFMemA.read_spec sp_t))
      (TidInFLT : alist_find SchHdr.get_tid fl_t = Some (sch_get_tid sp_t ν)) 
      (MASKTID : msk_t SchHdr.get_tid)
      (MASKMEM : msk_t PFMemHdr.read)
      loc ord v q 𝓥
    :
    Ist nths st_s st_t ∗ tid_user my_tid ∗
    precond (PFMemA.read_spec_0) (Tid.of_succ_nat my_tid, loc, ord, v, q, 𝓥)
      (Tid.of_succ_nat my_tid, loc, ord)↑ (Tid.of_succ_nat my_tid, loc, ord)↑ ∗
    (∀ nths st_s st_t ret,
      Ist nths st_s st_t -∗ tid_user my_tid -∗
      (postcond (PFMemA.read_spec_0) (Tid.of_succ_nat my_tid, loc, ord, v, q, 𝓥) ret↑ ret↑) -∗
      wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, i_s)
        (st_t, k_t ret))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, i_s)
      (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans (read (loc, ord)))) >>= k_t).
  Proof using LE.
    rewrite !WSim.wsim_eq /WSim.wsim_def.
    iIntros "[IST [TID [PRE SIM]]] P".
    rewrite /WSim.wsim_pre.
    iApply isim_nodup. iIntros (????).
    rewrite /read. unseal PFM. steps_r. inline_r.
    iPoseProof (winv_split υ ν with "P") as "> [V U]"; first eauto.
    forces_r. iSplitL "TID V"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[V [[-> TID] ->]]". hss.
    steps_r. inline_r. hss. force_r (existT 0 (Tid.of_succ_nat my_tid, loc, ord, v, q, 𝓥)). steps_r.
    force_r ((Tid.of_succ_nat my_tid, loc, ord)↑). steps_r.
    force_r. iSplitL "PRE".
    { iDestruct "PRE" as "[[% TV] %]". iSplit; eauto. }
    steps_r. iDestruct "GRT" as "[POST ->]".
    iDestruct "POST" as (??) "[% POST]"; des; subst.
    hss. steps_r.
    iAssert ( |==> winv υ ⊤ )%I with "[U V]" as ">P".
    { iDestruct "U" as "[A [W C]]". iFrame. iApply "C". iFrame. }
    iApply ("SIM" with "IST TID [POST]"); iFrame; eauto.
  Qed.

  Lemma wsim_read_a_tgt r g (msk_t:_→bool) sc_t sp_t i_s k_t my_tid
      (MemInFLT : alist_find PFMemHdr.read fl_t = Some (pfmem_fn PFMemA.read_spec sp_t))
      (TidInFLT : alist_find SchHdr.get_tid fl_t = Some (sch_get_tid sp_t ν)) 
      (MASKTID : msk_t SchHdr.get_tid)
      (MASKMEM : msk_t PFMemHdr.read)
      loc ord ζ ζ' t0 γ q mode 𝓥 Vb
    :
    Ist nths st_s st_t ∗ tid_user my_tid ∗
    precond (PFMemA.read_spec_1) (Tid.of_succ_nat my_tid, loc, ord, ζ, ζ', t0, γ, q, mode, 𝓥, Vb)
      (Tid.of_succ_nat my_tid, loc, ord)↑ (Tid.of_succ_nat my_tid, loc, ord)↑ ∗
    (∀ nths st_s st_t ret,
      Ist nths st_s st_t -∗ tid_user my_tid -∗
      (postcond (PFMemA.read_spec_1) (Tid.of_succ_nat my_tid, loc, ord, ζ, ζ', t0, γ, q, mode, 𝓥, Vb) ret↑ ret↑) -∗
      wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, i_s)
        (st_t, k_t ret))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, i_s)
      (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans (read (loc, ord)))) >>= k_t).
  Proof using LE.
    rewrite !WSim.wsim_eq /WSim.wsim_def.
    iIntros "[IST [TID [PRE SIM]]] P".
    rewrite /WSim.wsim_pre.
    iApply isim_nodup. iIntros (????).
    rewrite /read. unseal PFM. steps_r. inline_r.
    iPoseProof (winv_split υ ν with "P") as "> [V U]"; first eauto.
    forces_r. iSplitL "TID V"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[V [[-> TID] ->]]". hss.
    steps_r. inline_r. hss. force_r (existT 1 (Tid.of_succ_nat my_tid, loc, ord, ζ, ζ', t0, γ, q, mode, 𝓥, Vb)). steps_r.
    force_r ((Tid.of_succ_nat my_tid, loc, ord)↑). steps_r.
    force_r. iSplitL "PRE".
    { iDestruct "PRE" as "[[% TV] %]". iSplit; eauto. }
    steps_r. iDestruct "GRT" as "[POST ->]".
    iDestruct "POST" as (???????) "[% POST]"; des; subst.
    hss. steps_r.
    iAssert ( |==> winv υ ⊤ )%I with "[U V]" as ">P".
    { iDestruct "U" as "[A [W C]]". iFrame. iApply "C". iFrame. }
    iApply ("SIM" with "IST TID [POST]"); iFrame; eauto.
    iPureIntro; esplits; eauto.
  Qed.

  Lemma wsim_write_a_tgt r g (msk_t:_→bool) sc_t sp_t i_s k_t my_tid
      (MemInFLT : alist_find PFMemHdr.write fl_t = Some (pfmem_fn PFMemA.write_spec sp_t))
      (TidInFLT : alist_find SchHdr.get_tid fl_t = Some (sch_get_tid sp_t ν)) 
      (MASKTID : msk_t SchHdr.get_tid)
      (MASKMEM : msk_t PFMemHdr.write)
      loc val ord ζ ζ' 𝓥 Vb γ q mode tx tx'
    :
    Ist nths st_s st_t ∗ tid_user my_tid ∗
    precond (PFMemA.write_spec_1) (Tid.of_succ_nat my_tid, loc, val, ord, 𝓥, γ, ζ', Vb, tx, ζ, mode, q, tx')
      (Tid.of_succ_nat my_tid, loc, val, ord)↑ (Tid.of_succ_nat my_tid, loc, val, ord)↑ ∗
    (∀ nths st_s st_t ret,
      Ist nths st_s st_t -∗ tid_user my_tid -∗
      (postcond (PFMemA.write_spec_1) (Tid.of_succ_nat my_tid, loc, val, ord, 𝓥, γ, ζ', Vb, tx, ζ, mode, q, tx') ret↑ ret↑) -∗
      wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, i_s)
        (st_t, k_t ret))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, i_s)
      (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans (write (loc, val, ord)))) >>= k_t).
  Proof using LE.
    rewrite !WSim.wsim_eq /WSim.wsim_def.
    iIntros "[IST [TID [PRE SIM]]] P".
    rewrite /WSim.wsim_pre.
    iApply isim_nodup. iIntros (????).
    rewrite /write. unseal PFM. steps_r. inline_r.
    iPoseProof (winv_split υ ν with "P") as "> [V U]"; first eauto.
    forces_r. iSplitL "TID V"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[V [[-> TID] ->]]". hss.
    steps_r. inline_r. hss. force_r (existT 1 (Tid.of_succ_nat my_tid, loc, val, ord, 𝓥, γ, ζ', Vb, tx, ζ, mode, q, tx')). steps_r.
    force_r ((Tid.of_succ_nat my_tid, loc, val, ord)↑). steps_r.
    force_r. iSplitL "PRE".
    { iDestruct "PRE" as "[[% TV] %]". iSplit; eauto. }
    steps_r. iDestruct "GRT" as "[POST ->]".
    iDestruct "POST" as (??????) "[% POST]"; des; subst.
    hss. steps_r.
    iAssert ( |==> winv υ ⊤ )%I with "[U V]" as ">P".
    { iDestruct "U" as "[A [W C]]". iFrame. iApply "C". iFrame. }
    iApply ("SIM" with "IST TID [POST]"); iFrame; eauto.
  Qed.

  Lemma wsim_cas_tgt r g (msk_t:_→bool) sc_t sp_t i_s k_t my_tid
      (MemInFLT : alist_find PFMemHdr.cas fl_t = Some (pfmem_fn PFMemA.cas_spec sp_t))
      (TidInFLT : alist_find SchHdr.get_tid fl_t = Some (sch_get_tid sp_t ν)) 
      (MASKTID : msk_t SchHdr.get_tid)
      (MASKMEM : msk_t PFMemHdr.cas)
      loc old new ordr ordw 𝓥 γ ζ' Vb tx ζ mode Pr
    :
    Ist nths st_s st_t ∗ tid_user my_tid ∗
    precond (PFMemA.cas_spec) (Tid.of_succ_nat my_tid, loc, old, new, ordr, ordw, 𝓥, γ, ζ', Vb, tx, ζ, mode, Pr)
      (Tid.of_succ_nat my_tid, loc, old, new, ordr, ordw)↑ (Tid.of_succ_nat my_tid, loc, old, new, ordr, ordw)↑ ∗
    (∀ nths st_s st_t ret,
      Ist nths st_s st_t -∗ tid_user my_tid -∗
      (postcond (PFMemA.cas_spec) (Tid.of_succ_nat my_tid, loc, old, new, ordr, ordw, 𝓥, γ, ζ', Vb, tx, ζ, mode, Pr) ret↑ ret↑) -∗
      wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps true nths
        (st_s, i_s)
        (st_t, k_t ret))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, i_s)
      (st_t, (HModTr.sandbox msk_t sc_t (PModTr.trans (cas (loc, old, new, ordr, ordw)))) >>= k_t).
  Proof using LE.
    rewrite !WSim.wsim_eq /WSim.wsim_def.
    iIntros "[IST [TID [PRE SIM]]] P".
    rewrite /WSim.wsim_pre.
    iApply isim_nodup. iIntros (????).
    rewrite /cas. unseal PFM. steps_r. inline_r.
    iPoseProof (winv_split υ ν with "P") as "> [V U]"; first eauto.
    forces_r. iSplitL "TID V"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[V [[-> TID] ->]]". hss.
    steps_r. inline_r. hss. force_r (Tid.of_succ_nat my_tid, loc, old, new, ordr, ordw, 𝓥, γ, ζ', Vb, tx, ζ, mode, Pr). steps_r.
    force_r ((Tid.of_succ_nat my_tid, loc, old, new, ordr, ordw)↑). steps_r.
    force_r. iSplitL "PRE".
    { iDestruct "PRE" as "[[% TV] %]". iSplit; eauto. }
    steps_r. iDestruct "GRT" as "[POST ->]".
    iDestruct "POST" as (??????????) "[% POST]"; des; subst.
    hss. steps_r.
    iAssert ( |==> winv υ ⊤ )%I with "[U V]" as ">P".
    { iDestruct "U" as "[A [W C]]". iFrame. iApply "C". iFrame. }
    iApply ("SIM" with "IST TID [POST]"); iFrame; eauto.
    Unshelve. all: eauto.
  Qed.

End PFMemTac. End PFMem. *)