Require Import CRIS.
Require Import PFMemHeader HistoryRA AtomicRA.
Require Import Time Cell View TView base Language.

(* Specification of promise-free memory module *)
Module PFMemA. Section PFMemA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !histGS, !atomicG}.
  Definition scopes : list string := ["PFMem"].

  Definition alloc_spec : fspec :=
    fspec_simple (X:=Ident.t * nat * TView.t)
      (λ '(tid, n, 𝓥),
        ((λ varg, ⌜varg = (tid, Z.of_nat n)↑⌝
          ∗ tview tid 𝓥),
        (λ vret, ∃ loc 𝓥', ⌜vret = (Val.Vptr loc)↑ ∧ TView.le 𝓥 𝓥'⌝
          ∗ tview tid 𝓥'
          ∗ †loc…n
          ∗ @{TView.cur 𝓥'} loc ↦∗ repeat Val.Vundef n)))%I.

  Definition free_spec : fspec :=
    fspec_simple (X:=Ident.t * Loc.t * nat * TView.t)
      (λ '(tid, loc, n, 𝓥),
        ((λ varg, ⌜varg = (tid, loc)↑⌝
          ∗ tview tid 𝓥
          ∗ own_loc_vec loc 1 n (TView.cur 𝓥)
          ∗ †loc…n),
        (λ vret, ⌜vret = (Val.zero)↑⌝)))%I.

  (* non-atomic read *)
  Definition read_spec_0 : fspec :=
    fspec_simple (X:=Ident.t * Loc.t * Ordering.t * Val.t * Qp * TView.t)
      (λ '(tid, loc, ord, v, q, 𝓥),
        ((λ varg, ⌜varg = (tid, loc, ord)↑⌝
          ∗ @{TView.cur 𝓥} loc ↦{q} v ∗ tview tid 𝓥),
        (λ vret, ∃ v' 𝓥', ⌜vret = v'↑ ∧ Val.le v' v⌝
          ∗ @{TView.cur 𝓥'} loc ↦{q} v ∗ tview tid 𝓥')))%I.

  (* atomic read *)
  (* TODO : give variants of this specification (SW, SYNC, CAS, ...) *)
  Definition read_spec_1 : fspec :=
    fspec_simple
      (X:=Ident.t * Loc.t * Ordering.t * Cell.t * Cell.t * Time.t * positive * Qp * AtomicMode * TView.t * View.t)
      (λ '(tid, loc, ord, ζ, ζ', t, γ, q, mode, 𝓥, Vb),
        ((λ varg,
          ⌜varg = (tid, loc, ord)↑ ∧ Ordering.le Ordering.relaxed ord⌝
          ∗ @{TView.cur 𝓥} loc sn⊒{γ} ζ' (* ζ' abstract history seen by current thread *)
          ∗ @{Vb} AtomicPtsToX loc γ t ζ mode (* ζ global abstract history *)
          ∗ tview tid 𝓥), (* 𝓥 current thread view *)
        (λ vret, ∃ ζ'' f' na v' v'' V' 𝓥',
          ⌜vret = v'↑
          ∧ Val.le v' v''
          ∧ Cell.le ζ' ζ'' ∧ Cell.le ζ'' ζ
          ∧ Cell.get (Cell.max_ts ζ'') ζ'' = Some (f', Message.message v'' V' na)
          (* ∧ TView.readable (TView.cur 𝓥) loc (Cell.max_ts ζ'') ord *)
          ∧ (TView.cur 𝓥) ⊑ (TView.cur 𝓥')
          ∧ V' ⊑ (if Ordering.le Ordering.acqrel ord then TView.cur 𝓥' else TView.acq 𝓥')⌝
          ∗ @{TView.cur 𝓥'} loc sn⊒{γ} ζ''
          ∗ @{Vb} AtomicPtsToX loc γ t ζ mode
          ∗ tview tid 𝓥')))%I.

  Definition read_spec : fspec_rel :=
    λ P Q, fspec_to_rel read_spec_0 P Q ∨ fspec_to_rel read_spec_1 P Q.

  (* non-atomic write *)
  Definition write_spec_0 : fspec :=
    fspec_simple (X:=Ident.t * Loc.t * Val.t * Ordering.t * TView.t)
      (λ '(tid, loc, val, ord, 𝓥),
        ((λ varg, ⌜varg = (tid, loc, val, ord)↑⌝
          ∗ @{TView.cur 𝓥} loc ↦ ? ∗ tview tid 𝓥),
        (λ vret, ∃ 𝓥',
          ⌜vret = Val.zero↑ ∧ TView.le 𝓥 𝓥'⌝ ∗
          @{TView.cur 𝓥'} loc ↦ val ∗ tview tid 𝓥')))%I.

  #[local] Definition own_writer γ (m : AtomicMode) (q : frac) ζ tx : iProp Σ :=
    match m with
    | SingleWriter => at_writer γ ζ ∗ at_exclusive_write γ tx 1%Qp
    | CASOnly => at_exclusive_write γ tx q
    | ConcurrentWriter => True
    end.

  (* atomic write *)
  Definition write_spec_1 : fspec :=
    fspec_simple
      (X:=Ident.t * Loc.t * Val.t * Ordering.t * TView.t * gname * Cell.t * View.t * Time.t * Cell.t * AtomicMode * Qp * Time.t)
      (λ '(tid, loc, val, ord, 𝓥, γ, ζ', Vb, tx, ζ, mode, q, tx'),
        ((λ varg,
          ⌜varg = (tid, loc, val, ord)↑ ∧ Ordering.le Ordering.relaxed ord⌝
          ∗ @{TView.cur 𝓥} loc sn⊒{γ} ζ' (* ζ' abstract history seen by current thread *)
          ∗ @{Vb} AtomicPtsToX loc γ tx ζ mode (* ζ global abstract history *)
          ∗ tview tid 𝓥 (* 𝓥 current thread view *)
          ∗ own_writer γ mode q ζ' tx'),
        (λ vret, ∃ f t (LT : Time.lt f t) V' ζ'' ζn,
          let 𝓥' := TView.write_tview 𝓥 loc t ord in
          ⌜vret = Val.zero↑
          ∧ Time.lt (Cell.max_ts ζ') t
          ∧ (if Ordering.le Ordering.acqrel ord (* TODO : maybe this can be just V' = TView.write_released *)
            then V' = TView.cur 𝓥'
            else (TView.rel 𝓥 loc) ⊑ V' ∧ V' ⊑ TView.cur 𝓥')
          ∧ Cell.add ζ' f t (Message.message val V' false) ζ''
          ∧ Cell.add ζ f t (Message.message val V' false) ζn⌝
          ∗ @{TView.cur 𝓥'} loc sn⊒{γ} ζ''
          ∗ own_writer γ mode q ζ'' (if mode is SingleWriter then t else tx')
          ∗ @{TView.cur 𝓥'} loc sy⊒{γ} Cell.singleton (Message.message val V' false) LT
          (* ∗ @{V'} loc sn⊒{γ} Cell.singleton (Message.message val V' false) LT *)
          (* TODO : the condition above is improvable since release view may not have observed
            allocation
          *)
          ∗ @{Vb ⊔ TView.cur 𝓥'} AtomicPtsToX loc γ (if mode is SingleWriter then t else tx') ζn mode
          ∗ tview tid 𝓥')))%I.

  Definition write_spec : fspec_rel :=
    λ P Q, fspec_to_rel write_spec_0 P Q ∨ fspec_to_rel write_spec_1 P Q.

  (* TODO : Move to appropriate space *)
  Definition comparable (v1 v2 : Val.t) : Prop :=
    match v1, v2 with
    | Val.Vnum _, Val.Vnum _
    | Val.Vptr _, Val.Vptr _ => True
    | _, _ => False
    end.

  Definition cas_spec : fspec :=
    fspec_simple
      (X:=Ident.t * Loc.t * Val.t * Val.t * Ordering.t * Ordering.t * TView.t * gname * Cell.t * View.t * Time.t * Cell.t * AtomicMode * iProp Σ)
      (λ '(tid, loc, old, new, ordr, ordw, 𝓥, γ, ζ', Vb, tx, ζ, mode, Pr),
        let Wv ζ : iProp Σ := (if mode is SingleWriter then at_writer γ ζ else True)%I in
        ((λ varg,
          ⌜ varg = (tid, loc, old, new, ordr, ordw)↑
            ∧ Ordering.le Ordering.relaxed ordr
            ∧ Ordering.le Ordering.relaxed ordw
            ∧ (∀ t f v V b,
              Time.le (Cell.max_ts ζ') t
              → Cell.get t ζ = Some (f, Message.message v V b)
              → comparable old v
                ∧ if v is Val.Vptr loc
                  then
                    if Ordering.le Ordering.acqrel ordr
                    then (View.alloc_view V) (Loc.get_tbid loc)
                    else (View.alloc_view (TView.cur 𝓥)) (Loc.get_tbid loc)
                  else True) ⌝
          ∗ tview tid 𝓥
          ∗ @{TView.cur 𝓥} loc sn⊒{γ} ζ'
          ∗ @{Vb} AtomicPtsToX loc γ tx ζ mode
          ∗ Wv ζ
          ∗ Pr
          ∗ □ if old is (Val.Vptr lr) then
                (Pr ==∗ ((∃ qr Cr Vr γ Cr', @{Vr} lr p↦{qr} Cr ∗ @{TView.cur 𝓥} lr sn⊒{γ} Cr') ∧
                  (∀ t f (l' : Loc.t) V' b,
                    ⌜Time.le (Cell.max_ts ζ') t
                      ∧ Cell.get t ζ = Some (f, Message.message (Val.Vptr l') V' b)
                      ∧ l' <> lr⌝
                    -∗ ∃ q' C' V'', @{V''} l' p↦{q'} C')))
              else emp
          ),
        (λ vret, ∃ ret ζ'' ζn t' f' (LT : Time.lt f' t') v' Vr b 𝓥',
          ⌜vret = ret↑
            ∧ Cell.le ζ' ζ'' ∧ Cell.le ζ'' ζn
            ∧ Cell.get t' ζ'' = Some (f', Message.message v' Vr b)
            ∧ Time.le (Cell.max_ts ζ') t'
            ∧ TView.le 𝓥 𝓥'⌝
          ∗ tview tid 𝓥'
          (* ∗ @{TView.cur 𝓥'} loc sn⊒{γ} (Cell.singleton (Message.message v' Vr b) LT) *)
          ∗ @{TView.cur 𝓥'} loc sn⊒{γ} ζ''
          ∗ Pr
          ∗ ((⌜ret = Val.zero ∧ old <> v'
              ∧ (Vr ⊑ if Ordering.le Ordering.acqrel ordr then TView.cur 𝓥' else TView.acq 𝓥')
              ∧ ζ = ζn⌝
              ∗ @{Vb} AtomicPtsToX loc γ tx ζ mode)
            ∨ (∃ Vw,
                ⌜ret = Val.one ∧ old = v'
                ∧ ∃ t'', Cell.add ζ t' t'' (Message.message new Vw false) ζn
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ ¬ (TView.cur 𝓥') ⊑ Vr
                ∧ 𝓥' ≠ 𝓥
                ∧ if Ordering.le Ordering.acqrel ordw
                  then if Ordering.le Ordering.acqrel ordr
                      then Vw = TView.cur 𝓥'
                      else TView.cur 𝓥' ⊑ Vw (* This seems to be because of liftings in gpfsl *)
                  else (TView.rel 𝓥' loc) ⊑ Vw
                ∧ Vw ⊑ if Ordering.le Ordering.acqrel ordr then TView.cur 𝓥' else TView.acq 𝓥'⌝
                ∗ Wv ζn
                ∗ @{Vb ⊔ TView.cur 𝓥'} AtomicPtsToX loc γ tx ζn mode))
          )))%I.

  Definition spawn_spec : fspec :=
    fspec_simple
      (λ '(tid, 𝓥),
        ((λ varg, ⌜varg = tid↑⌝ ∗ tview tid 𝓥),
         (λ vret, ∃ tid_new, ⌜vret = tid_new↑⌝ ∗ tview tid 𝓥 ∗ tview tid_new 𝓥)))%I.
  (* TODO : cmp, faa, fence *)

  (* For now, we don't consider the case where "ordw = seqcst" *)
  Definition fence_spec : fspec :=
    fspec_simple
      (λ '(tid, ordr, ordw, 𝓥),
        ((λ varg, 
          ⌜varg = (tid, ordr, ordw)↑  ∧ Ordering.le ordw Ordering.acqrel⌝ ∗
          tview tid 𝓥),
         (λ vret, ∃ 𝓥',
          ⌜vret = Val.zero↑ ∧
           (TView.cur 𝓥' = if Ordering.le Ordering.acqrel ordr then TView.acq 𝓥 else TView.cur 𝓥) ∧
           (TView.rel 𝓥' = λ loc, if Ordering.le Ordering.acqrel ordw then TView.cur 𝓥' else TView.rel 𝓥 loc) ∧
           (TView.acq 𝓥' = TView.acq 𝓥)⌝ ∗
          tview tid 𝓥')))%I.

  Definition sp : specmap :=  
    {[speckey_fn PFMemHdr.alloc := fspec_to_rel alloc_spec;
      speckey_fn PFMemHdr.free := fspec_to_rel free_spec;
      speckey_fn PFMemHdr.read := read_spec;
      speckey_fn PFMemHdr.write := write_spec;
      speckey_fn PFMemHdr.cas := fspec_to_rel cas_spec;
      speckey_fn PFMemHdr.fence := fspec_to_rel fence_spec;
      speckey_fn PFMemHdr.spawn := fspec_to_rel spawn_spec
    ]}.

  Definition fnsems : fnsemmap :=
    {[Some PFMemHdr.alloc := Some (msk_scp scopes msk_true, (fsp_some alloc_spec, fbody_trivial));
      Some PFMemHdr.free := Some (msk_scp scopes msk_true, (fsp_some free_spec, fbody_trivial));
      Some PFMemHdr.read := Some (msk_scp scopes msk_true, (fsp_some read_spec, fbody_trivial));
      Some PFMemHdr.write := Some (msk_scp scopes msk_true, (fsp_some write_spec, fbody_trivial));
      Some PFMemHdr.cas := Some (msk_scp scopes msk_true, (fsp_some cas_spec, fbody_trivial));
      Some PFMemHdr.fence := Some (msk_scp scopes msk_true, (fsp_some fence_spec, fbody_trivial));
      Some PFMemHdr.spawn := Some (msk_scp scopes msk_true, (fsp_some spawn_spec, fbody_trivial))]}.

  (* Module definition *)
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp : Mod.t := SMod.to_mod sp smod.

  Definition lang := Language.mk (λ _ : (), tt) (const False) (λ _ : ProgramEvent.t, λ _ _, True).
  Definition syn : Threads.syntax := IdentMap.singleton 1%positive (existT lang tt).
  Definition init : Configuration.t := Configuration.init syn [].

  Definition init_cond : iProp Σ :=
    tview_auth (Threads.init syn []) ∗
    hist_auth (Memory.init []) ∗
    hist_freeable_auth (Memory.init []).
End PFMemA. End PFMemA.

Lemma hist_alloc `{!crisG Γ Σ α β τ _I _S, !histGpreS} :
  ⊢ o=> ∃ (_ : histGS), PFMemA.init_cond ∗ tview 1 (TView.init []).
Proof.
  Local Existing Instances histGS_histGpreS histGS_view histGS_hist histGS_free.
  iMod (own_alloc
    (● ((λ tid, (option_map (Excl ∘ Local.tview ∘ snd) (IdentMap.find tid (Threads.init PFMemA.syn []))))
      : Ident.t -d> optionUR (exclR TViewO)) ⋅
    ◯ ((discrete_fun_singleton 1%positive (Some (Excl (TView.init []))))) : viewR)) as "[%γv V]".
  { apply auth_both_valid_discrete; split.
    { exists ε; rewrite right_id; intros i; destruct (decide (i = 1%positive)); subst.
      { rewrite discrete_fun_lookup_singleton //=. }
      { rewrite discrete_fun_lookup_singleton_ne //= /Threads.init /PFMemA.syn.
        rewrite IdentMap.gmapi IdentMap.singleton_neq //.
      }
    }
    intros i; destruct (decide (i = 1%positive)); subst; ss.
    { rewrite //= /Threads.init /PFMemA.syn IdentMap.gmapi IdentMap.singleton_neq //. }
  }
  iMod (own_alloc
    (● ((λ l,
        if Memory.accessible l (Memory.init [])
        then
          Some (DfracOwn 1, to_agree (Memory.get_cell l (Memory.init [])))
        else None) : Loc.t -d> optionUR (prodR dfracR (agreeR CellO))) : histR)) as "[%γh H]".
  { rewrite auth_auth_valid; intros l; des_ifs. }
  iMod (own_alloc
    (● ((λ '(tid, bid),
          if Memory.is_freeable (Loc.mk (Some tid) bid 0) (Memory.init [])
          then
            match Memory.get_size (Loc.mk (Some tid) bid 0) (Memory.init []) with
            | Some sz => Some (1%Qp, Excl sz)
            | None => None
            end
          else None
        ) : Tid.t * Bid.t -d> optionUR (prodR fracR (exclR ZO))))) as "[%γf F]".
  { rewrite auth_auth_valid; intros l; des_ifs. }
  iExists (Build_histGS _ _ _ _ _ _ _ _ _ γv γh γf); rewrite !own_op.
  iDestruct "V" as "[V ?]".
  rewrite /PFMemA.init_cond tview_auth_eq hist_auth_eq hist_freeable_auth_eq tview_eq; iFrame.
  done.
Qed.