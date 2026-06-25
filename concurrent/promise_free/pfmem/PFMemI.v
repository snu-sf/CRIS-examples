Require Import CRIS.
Require Import Promises Memory.
Require Export PFMemHeader.

Module PFMemI. Section PFMemI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["PFMem"].
  Definition v_config := "PFMem" ↯ "config".
  Definition v_tid := "PFMem" ↯ "tid".
  Definition v_tids := "PFMem" ↯ "tids".

  Definition check_ident (c : Configuration.t) (tid : Ident.t) (itr : itree crisE Val.t)
      : itree crisE Val.t :=
    match IdentMap.find tid (Configuration.threads c) with
    | None => triggerUB
    | Some _ => itr
    end.

  Definition alloc : Ident.t * Z → itree crisE Val.t :=
    λ '(tid, sz),
      config <- cgetU v_config;;
      check_ident config tid (
        '(exist _ (loc, config') _) : _ <- trigger (Choose (
          { '(loc, config') | PFConfiguration.estep (ThreadEvent.alloc loc sz) tid config config' }
        ));;
        cput v_config config';;;
        Ret (Val.Vptr loc)
      ).

  Definition free : Ident.t * Loc.t → itree crisE Val.t :=
    λ '(tid, loc),
      config <- cgetU v_config;;
      check_ident config tid (
        '(exist _ (e, config') _) : _ <- trigger (Choose (
          { '(e, config') |
            ThreadEvent.get_program_event e = ProgramEvent.free loc
            ∧ PFConfiguration.estep e tid config config' }));;
        if (excluded_middle_informative (ThreadEvent.is_failure e))
        then triggerUB
        else cput v_config config';;; Ret Val.zero
      ).

  Definition read : Ident.t * Loc.t * Ordering.t → itree crisE Val.t :=
    λ '(tid, loc, ord),
      config <- cgetU v_config;;
      check_ident config tid (
        '(exist _ (e, val, config') _) : _ <- trigger (Choose (
          { '(e, val, config') |
            ThreadEvent.get_program_event e = ProgramEvent.read loc val ord
            ∧ PFConfiguration.estep e tid config config'
          }));;
        if (excluded_middle_informative (ThreadEvent.is_failure e))
        then triggerUB
        else cput v_config config';;; Ret val
      ).

  Definition write : Ident.t * Loc.t * Val.t * Ordering.t → itree crisE Val.t :=
    λ '(tid, loc, val, ord),
      config <- cgetU v_config;;
      check_ident config tid (
        '(exist _ (e, config') _) : _ <- trigger (Choose (  
          { '(e, config') |
            ThreadEvent.get_program_event e = ProgramEvent.write loc val ord
            ∧ PFConfiguration.estep e tid config config'
          }));;
        if (excluded_middle_informative (ThreadEvent.is_failure e))
        then triggerUB
        else cput v_config config';;; Ret Val.zero
      ).

  Definition cmp : Ident.t * Val.t * Val.t → itree crisE Val.t :=
    λ '(tid, val1, val2),
      config <- cgetU v_config;;
      check_ident config tid (
        match val1, val2 with
        | Val.Vnum n1, Val.Vnum n2 =>
            if decide (n1 = n2) then Ret Val.one else Ret Val.zero
        | Val.Vptr loc1, Val.Vptr loc2 =>
            '(exist _ (e, valret) _) : _ <- trigger (Choose (
              { '(e, valret) |
                ThreadEvent.get_program_event e = ProgramEvent.ptr_eq loc1 loc2 valret
                ∧ PFConfiguration.estep e tid config config }
            ));;
            if (excluded_middle_informative (ThreadEvent.is_failure e))
            then triggerUB
            else
              match (valret : option bool) with
              | Some b => if b then Ret Val.one else Ret Val.zero
              | None => triggerUB (* Unreachable *)
              end
        | _, _ => triggerUB
        end).

  Definition cas : Ident.t * Loc.t * Val.t * Val.t * Ordering.t * Ordering.t → itree crisE Val.t :=
    λ '(tid, loc, old, new, ordr, ordw),
      config <- cgetU v_config;;
      check_ident config tid (
        '(exist _ (e, valret, config') _) : _ <- trigger (Choose (
          { '(e, valret, config') |
            ∃ valr,
              ThreadEvent.get_program_event e = ProgramEvent.cas loc valr old new valret ordr ordw
              ∧ PFConfiguration.estep e tid config config'
          }
        ));;
        if (excluded_middle_informative (ThreadEvent.is_failure e))
        then triggerUB
        else
          match (valret : option bool) with
          | Some b => cput v_config config';;; if b then Ret Val.one else Ret Val.zero
          | None => triggerUB (* Unreachable *)
          end
      ).

  Definition faa : Ident.t * Loc.t * Val.t * Ordering.t * Ordering.t → itree crisE Val.t :=
    λ '(tid, loc, addendum, ordr, ordw),
      config <- cgetU v_config;;
      check_ident config tid (
        '(exist _ (e, valr, config') _) : _ <- trigger (Choose (
          { '(e, valr, config') |
              ThreadEvent.get_program_event e = ProgramEvent.faa loc valr addendum ordr ordw
              ∧ PFConfiguration.estep e tid config config'
          }
        ));;
        if (excluded_middle_informative (ThreadEvent.is_failure e))
        then triggerUB
        else cput v_config config';;; Ret valr
      ).

  Definition fence : Ident.t * Ordering.t * Ordering.t → itree crisE Val.t :=
    λ '(tid, ordr, ordw),
      config <- cgetU v_config;;
      check_ident config tid (
        '(exist _ config' _) : _ <- trigger (Choose (
          { config' | PFConfiguration.estep (ThreadEvent.fence ordr ordw) tid config config' }));;
        cput v_config config';;;
        Ret Val.zero
      ).

  Definition spawn : Ident.t → itree crisE Ident.t :=
    λ tid,
      config <- cgetU v_config;;
      let ths := Configuration.threads config in
      '(exist _ tid_new _) : _ <- trigger (Choose ({ tid : Ident.t | ¬ IdentMap.mem tid ths }));;
      '(l, lc) : _ <- (IdentMap.find tid ths)?;;
      let lc_new := Local.mk (Local.tview lc) Promises.bot Memory.bot FreePromises.bot tid_new in
      let ths' := (IdentMap.add tid_new (l, lc_new) ths) in
      let config' := Configuration.mk ths' (Configuration.global config) in
      cput v_config config';;;
      Ret tid_new.

  Definition fnsems : fnsemmap :=
    {[fid PFMemHdr.alloc # (msk_real (msk_scp scopes msk_true), (None, cfunU PFMemHdr.alloc alloc));
      fid PFMemHdr.free  # (msk_real (msk_scp scopes msk_true), (None, cfunU PFMemHdr.free free));
      fid PFMemHdr.read  # (msk_real (msk_scp scopes msk_true), (None, cfunU PFMemHdr.read read));
      fid PFMemHdr.write # (msk_real (msk_scp scopes msk_true), (None, cfunU PFMemHdr.write write));
      fid PFMemHdr.cmp   # (msk_real (msk_scp scopes msk_true), (None, cfunU PFMemHdr.cmp cmp));
      fid PFMemHdr.cas   # (msk_real (msk_scp scopes msk_true), (None, cfunU PFMemHdr.cas cas));
      fid PFMemHdr.faa   # (msk_real (msk_scp scopes msk_true), (None, cfunU PFMemHdr.faa faa));
      fid PFMemHdr.fence # (msk_real (msk_scp scopes msk_true), (None, cfunU PFMemHdr.fence fence));
      fid PFMemHdr.spawn # (msk_real (msk_scp scopes msk_true), (None, cfunU PFMemHdr.spawn spawn))]}.

  Program Definition Mod s size : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_config # (Configuration.init s size)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t s size : Mod.t := (SMod.to_mod ∅ (Mod s size)).
End PFMemI. End PFMemI.
