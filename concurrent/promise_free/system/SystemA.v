Require Import CRIS.common.CRIS.
Require Export PFMemHeader SystemHeader SystemI.
Require Import HistoryRA AtomicRA LatticeRA.
From iris.algebra Require Export csum gmap_view.
From iris.bi Require Export fractional.

Definition sysRA := (gmap_viewUR Ident.t (agreeR (TViewO * natO)%type)).
Class sysGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] sys_inG :: inG sysRA Γ
}.
Class sysGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] sysGS_sysGpreS :: sysGpreS;
  sys_name : gname
}.
Definition sysΓ : HRA := #[sysRA].
Global Instance subG_sysGpreS `{!crisG Γ Σ α β τ _S _I} : subG sysΓ Γ → sysGpreS.
Proof. solve_inG. Defined.

Section SystemRA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _SYS: !sysGS}.

  Definition tview_sys_auth (ths : gmap Ident.t (TView.t * nat)) : iProp Σ :=
    (own sys_name (gmap_view_auth (DfracOwn 1) (to_agree <$> ths)) ∗
    [∗ map] tid ↦ '(V, _) ∈ ths, tview tid V).

  Definition tview_sys_gen (q : Qp) (mtid : Ident.t) (stid : nat) (V : TView.t) : iProp Σ :=
    own sys_name (gmap_view_frag mtid (DfracOwn q) (to_agree (V, stid))).
  Definition tview_sys (tid : Ident.t) (stid : nat) (V : TView.t) : iProp Σ :=
    (tview_sys_gen 1 tid stid V ∗ TID stid ∗ YIELD stid)%I.

  Lemma tview_sys_lookup
      (ths : gmap Ident.t (TView.t * nat)) (tid : Ident.t) (stid : nat) (𝓥 : TView.t) (q : Qp) :
    tview_sys_auth ths -∗
    tview_sys_gen q tid stid 𝓥 -∗
    ⌜ ths !! tid = Some (𝓥, stid) ⌝.
  Proof.
    rewrite /tview_sys_auth /tview_sys /tview_sys_gen; iIntros "[TA TVS] TV".
    iCombine "TA TV" gives %[𝓥' [? [_ [Hlookup [_ Hincl]]]]]%gmap_view_both_dfrac_valid_discrete.
    rewrite lookup_fmap fmap_Some in Hlookup; destruct Hlookup as [𝓥'' [Hlookup ->]].
    eapply Some_pair_included_r in Hincl.
    rewrite Some_included_total to_agree_included_L in Hincl; subst; done.
  Qed.

  Instance tview_sys_gen_fractional tid stid V : Fractional (λ q, tview_sys_gen q tid stid V).
  Proof. ii; by rewrite /tview_sys_gen -own_op -gmap_view_frag_add agree_idemp. Qed.

  #[global] Instance tview_sys_gen_as_fractional tid stid V q :
    AsFractional (tview_sys_gen q tid stid V) (λ q, tview_sys_gen q tid stid V) q.
  Proof. split; ss; typeclasses eauto. Qed.

End SystemRA.

Lemma sys_alloc `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, !sysGpreS} :
  tview 1 (TView.init []) o==∗
    ∃ (_ : sysGS), tview_sys_auth {[1%positive := (TView.init [], 0)]} ∗
      tview_sys_gen 1 1 0 (TView.init []).
Proof.
  iIntros "TV".
  iMod (own_alloc
    (gmap_view_auth (DfracOwn 1) {[1%positive := (to_agree (TView.init [], 0))]} ⋅
    gmap_view_frag 1%positive (DfracOwn 1) (to_agree (TView.init [], 0)))) as "[%γs [? ?]]".
  { apply gmap_view_both_dfrac_valid_discrete; esplits; eauto.
    { apply: dfrac_valid_own_1. }
    { split; s; [apply: dfrac_valid_own_1|ss]. }
  }
  iExists (Build_sysGS _ _ _ _ _ _ _ _ _ γs).
  iFrame. rewrite big_sepM_singleton; iFrame. done.
Qed.

Module SystemA. Section SystemA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS}.
  Context (sp_user : specmap).

  (* Specifications *)
  Definition fspec_spawnable (fn : string) (pre : TView.t → SAny.t → SAny.t → iProp Σ) : iProp Σ :=
    ∃ fsp, ⌜sp_user.1 !! (funid fn) = Some fsp⌝ ∗
      fspec_imply
        fsp
        (fspec_winv ⊤
          (fspec_virtual (λ '(tid, stid),
            ((λ (varg : SAny.t) (arg : Any.t),
              ∃ V, tview_sys tid stid V ∗ ∃ sarg, ⌜arg = sarg↑⌝ ∗ pre V varg sarg),
            (λ (vret : SAny.t) _, ∃ V, tview_sys tid stid V)))))%I.

  Definition _spawn_spec : fspec := 
    fspec_mk
      (λ '(_ : ()) varg arg,
        ∃ (stid : nat) (tid : Ident.t) V pre fvarg farg fn,
          ⌜varg = (tid, fn, fvarg)↑ ∧ arg = (tid, fn, farg)↑⌝ ∗
          winv (⊤, ⊤) ∗ fspec_spawnable fn pre ∗
          tview_sys tid stid V ∗
          pre V fvarg farg)%I
      (λ _ vret _, ∃ (vr : SAny.t), ⌜vret = vr↑⌝ ∗ False)%I.

  Definition spawn_spec : fspec :=
    (fspec_virtual (λ '(tid, stid, pre, 𝓥),
      ((λ varg arg,
        ∃ fvarg farg fn, ⌜varg = (fn, fvarg) ∧ arg = (fn, farg)↑⌝  ∗
          fspec_spawnable fn pre ∗
          tview_sys tid stid 𝓥 ∗ pre 𝓥 fvarg farg),
      (λ vret ret, tview_sys tid stid 𝓥 ∗ ⌜vret = tt ∧ ret = tt↑⌝))))%I.

  Definition yield_spec (E : coPset) : fspec :=
    fspec_winv E
      (fspec_simple (λ '(tid, stid, 𝓥),
        ((λ varg, ⌜varg = tt↑⌝ ∗ tview_sys tid stid 𝓥),
        (λ vret, ⌜vret = tt↑⌝ ∗ tview_sys tid stid 𝓥))))%I.

  Definition get_tid_spec : fspec :=
    fspec_simple (λ '(tid, stid, 𝓥),
      ((λ varg, ⌜varg = tt↑⌝ ∗ tview_sys tid stid 𝓥),
       (λ vret, ⌜vret = tid↑⌝ ∗ tview_sys tid stid 𝓥)))%I.

  Definition alloc_spec : fspec :=
    fspec_simple (X := Ident.t * nat * nat * TView.t)
      (λ '(tid, stid, sz, 𝓥),
        ((λ varg, ⌜varg = sz↑⌝ ∗ tview_sys tid stid 𝓥),
        (λ vret, ∃ loc 𝓥', ⌜vret = (Val.Vptr loc)↑ ∧ TView.le 𝓥 𝓥'⌝ ∗
          tview_sys tid stid 𝓥' ∗
          †loc…sz ∗
          @{TView.cur 𝓥'} loc ↦∗ repeat Val.Vundef sz)))%I.

  (* non-atomic read *)
  Definition read_spec_0 : fspec :=
    fspec_simple (X:=Ident.t * nat * Loc.t * Ordering.t * Val.t * Qp * TView.t)
      (λ '(tid, stid, loc, ord, v, q, V),
        ((λ varg, ⌜varg = (loc, ord)↑⌝ ∗
          @{TView.cur V} loc ↦{q} v ∗ tview_sys tid stid V),
         (λ vret, ∃ v' V', ⌜vret = v'↑ ∧ Val.le v' v⌝ ∗
          @{TView.cur V'} loc ↦{q} v ∗ tview_sys tid stid V')))%I.

  (* atomic read *)
  (* TODO : give variants of this specification (SW, SYNC, CAS, ...) *)
  Definition read_spec_1 : fspec :=
    fspec_simple
      (X:=Ident.t * nat * Loc.t * Ordering.t * Cell.t * Cell.t * Time.t * positive * Qp * AtomicMode * TView.t * View.t)
      (λ '(tid, stid, loc, ord, ζ, ζ', t, γ, q, mode, 𝓥, Vb),
        ((λ varg,
          ⌜varg = (loc, ord)↑ ∧ Ordering.le Ordering.relaxed ord⌝ ∗
          @{TView.cur 𝓥} loc sn⊒{γ} ζ' ∗ (* ζ' abstract history seen by current thread *)
          @{Vb} AtomicPtsToX loc γ t ζ mode ∗ (* ζ global abstract history *)
          tview_sys tid stid 𝓥), (* 𝓥 current thread view *)
        (λ vret, ∃ ζ'' f' na v' v'' V' 𝓥',
          ⌜vret = v'↑ ∧
          Val.le v' v'' ∧
          Cell.le ζ' ζ'' ∧
          Cell.le ζ'' ζ ∧
          Cell.get (Cell.max_ts ζ'') ζ'' = Some (f', Message.message v'' V' na) ∧
          (TView.cur 𝓥) ⊑ (TView.cur 𝓥') ∧
          V' ⊑ (if Ordering.le Ordering.acqrel ord then TView.cur 𝓥' else TView.acq 𝓥')⌝ ∗
          @{TView.cur 𝓥'} loc sn⊒{γ} ζ'' ∗
          @{Vb} AtomicPtsToX loc γ t ζ mode ∗
          tview_sys tid stid 𝓥')))%I.

  Definition read_spec : fspec :=
    [read_spec_0; read_spec_1]%cris.

  (* non-atomic write *)
  Definition write_spec_0 : fspec :=
    fspec_simple (X:=Ident.t * nat * Loc.t * Val.t * Ordering.t * TView.t)
      (λ '(tid, stid, loc, val, ord, V),
        ((λ varg, ⌜varg = (loc, val, ord)↑⌝ ∗
          @{TView.cur V} loc ↦ ? ∗ tview_sys tid stid V),
        (λ vret, ∃ V', ⌜vret = Val.zero↑ ∧ TView.le V V'⌝ ∗
          @{TView.cur V'} loc ↦ val ∗ tview_sys tid stid V')))%I.

  #[local] Definition own_writer γ (m : AtomicMode) (q : frac) ζ tx : iProp Σ :=
    match m with
    | SingleWriter => at_writer γ ζ ∗ at_exclusive_write γ tx 1%Qp
    | CASOnly => at_exclusive_write γ tx q
    | ConcurrentWriter => True
    end.

  (* atomic write *)
  Definition write_spec_1 : fspec :=
    fspec_simple
      (X:=Ident.t * nat * Loc.t * Val.t * Ordering.t * TView.t * gname * Cell.t * View.t * Time.t * Cell.t * AtomicMode * Qp * Time.t)
      (λ '(tid, stid, loc, val, ord, 𝓥, γ, ζ', Vb, tx, ζ, mode, q, tx'),
        ((λ varg,
          ⌜varg = (loc, val, ord)↑ ∧ Ordering.le Ordering.relaxed ord⌝ ∗
          @{TView.cur 𝓥} loc sn⊒{γ} ζ' ∗
          @{Vb} AtomicPtsToX loc γ tx ζ mode ∗
          tview_sys tid stid 𝓥 ∗
          own_writer γ mode q ζ' tx'),
        (λ vret, ∃ f t (LT : Time.lt f t) V' ζ'' ζn,
          let 𝓥' := TView.write_tview 𝓥 loc t ord in
          ⌜vret = Val.zero↑
          ∧ Time.lt (Cell.max_ts ζ') t
          ∧ (if Ordering.le Ordering.acqrel ord
            then V' = TView.cur 𝓥'
            else (TView.rel 𝓥 loc) ⊑ V' ∧ V' ⊑ TView.cur 𝓥')
          ∧ Cell.add ζ' f t (Message.message val V' false) ζ''
          ∧ Cell.add ζ f t (Message.message val V' false) ζn⌝ ∗
          @{TView.cur 𝓥'} loc sn⊒{γ} ζ'' ∗
          own_writer γ mode q ζ'' (if mode is SingleWriter then t else tx') ∗
          @{TView.cur 𝓥'} loc sy⊒{γ} Cell.singleton (Message.message val V' false) LT ∗
          @{Vb ⊔ TView.cur 𝓥'} AtomicPtsToX loc γ (if mode is SingleWriter then t else tx') ζn mode ∗
          tview_sys tid stid 𝓥')))%I.

  Definition write_spec : fspec := 
    [write_spec_0; write_spec_1]%cris.

  Definition sp (E : coPset) : specmap :=
    {[fid SystemHdr._spawn  @ _spawn_spec;
      fid SystemHdr.spawn   @ spawn_spec;
      fid SystemHdr.yield   @ (yield_spec E);
      fid SystemHdr.get_tid @ get_tid_spec;
      fid SystemHdr.alloc   @ alloc_spec;
      fid SystemHdr.write   @ write_spec;
      fid SystemHdr.read    @ read_spec]}.

  (* Module definitions *)
  Definition scopes : list string := ["System"].
  Definition v_tid := "System" ↯ "tid".
  Definition v_tids := "System" ↯ "tids".

  Definition _spawn : Ident.t * string * SAny.t → itree crisE unit :=
    λ '(my_tid, fn, arg),
      trigger (Call fn arg↑);;;
      System.terminate.

  Definition spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      'my_tid : Ident.t <- cgetN v_tid;;
      'tids : tidmap <- cgetN v_tids;;
      '(exist _ tid_new _) : _ <- trigger (Choose ({tid_new : Ident.t | tids !! tid_new = None}));;
      stid <- trigger (Spawn SystemHdr._spawn.1 (tid_new, fn, arg)↑);;
      let newtids : tidmap := <[tid_new := stid]> tids in
      cput v_tids newtids.

  Definition yield : unit → itree crisE unit :=
    λ _,
      'tids : tidmap <- cgetN v_tids;;
      '(exist _ (mtid, stid) _) : _ <- trigger (Choose {p : Ident.t * nat | tids !! p.1 = Some p.2});;
      cput v_tid mtid;;;
      trigger (Yield stid).

  Definition get_tid : () → itree crisE Ident.t :=
    λ _, cgetN v_tid.

  Definition alloc : nat → itree crisE Val.t :=
    λ sz,
      'tid : Ident.t <- get_tid ();;
      ccallN (PFMemHdr.alloc) (tid, Z.of_nat sz).

  Definition write : Loc.t * Val.t * Ordering.t → itree crisE Val.t :=
    λ '(loc, val, ord),
      'tid : Ident.t <- get_tid ();;
      ccallN (PFMemHdr.write) (tid, loc, val, ord).

  Definition read : Loc.t * Ordering.t → itree crisE Val.t :=
    λ '(loc, ord),
      'tid : Ident.t <- get_tid ();;
      ccallN (PFMemHdr.read) (tid, loc, ord).

  Definition fnsems (E : coPset) : fnsemmap :=
    {[fid SystemHdr._spawn  # (msk_scp scopes msk_true, (fsp_some (_spawn_spec), cfunN (fntyp _ _) _spawn));
      fid SystemHdr.spawn   # (msk_scp scopes msk_true, (fsp_some (spawn_spec), cfunN (fntyp _ _) spawn));
      fid SystemHdr.yield   # (msk_scp scopes msk_true, (fsp_some (yield_spec E), cfunN (fntyp _ _) yield));
      fid SystemHdr.get_tid # (msk_scp scopes msk_true, (fsp_some get_tid_spec, cfunN (fntyp _ _) get_tid));
      fid SystemHdr.alloc   # (msk_scp scopes msk_true, (fsp_some alloc_spec, fbody_trivial));
      fid SystemHdr.write   # (msk_scp scopes msk_true, (fsp_some write_spec, fbody_trivial));
      fid SystemHdr.read    # (msk_scp scopes msk_true, (fsp_some read_spec, fbody_trivial))]}.

  Program Definition Mod E : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems E;
    SMod.initial_st := 
      {[v_tid # 1%positive↑; v_tids # ({[1%positive := 0]} : tidmap)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond size : iProp Σ :=
    tview_sys_auth {[1%positive := (TView.init size, 0)]}.

  Definition t E sp : Mod.t := SMod.to_mod sp (Mod E).
End SystemA. End SystemA.
