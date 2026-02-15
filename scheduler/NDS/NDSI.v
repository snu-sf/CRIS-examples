Require Import CRIS.
Require Import NDSHeader.

Definition thpool : Type := list (nat * option SAny.t).

Module NDSI. Section NDSI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Variable (parent_yield : string).

  Definition scp : list string := [ NDS ].
  Definition v_ths := NDS ↯ "ths".
  Definition v_tid := NDS ↯ "tid".
  Definition v_sch := NDS ↯ "sch".

  (* function which would be called by "spawn" of parent scheduler *)
  Definition init : SAny.t → itree crisE unit :=
    λ sfn,
      (* initialization with given function *)
      'fn: string <- (sfn↓↓)?;;
      stid <- trigger GetTid;;
      cput v_sch stid;;;
      'ths: thpool <- cgetU v_ths;;
      new_stid <- trigger (Spawn NDSHdr._spawn (fn, tt↑↑)↑);;
      cput v_ths (ths ++ [(new_stid, None)]);;;
      cput v_tid (List.length ths);;;
      trigger (Yield new_stid);;;
      (* infinite global yield *)
      iterC (λ _,
        trigger (Call parent_yield tt↑);;;
        'ths: thpool <- cgetU v_ths;;
        'mtid: nat <- cgetU v_tid;;
        match ths !! mtid with
        | Some (stid, _) => trigger (Yield stid);;; Ret (inl tt)
        | None => triggerUB
        end
      ) tt.

  Definition inner_spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      'rv : SAny.t <- ccallU fn arg;;
      'ths : thpool <- cgetU v_ths;;
      'tid : nat <- cgetU v_tid;;
      match ths !! tid with
      | Some (stid, _) =>
          let ths2 := <[tid := (stid, Some rv)]> ths in
          cput v_ths ths2;;;
          NDS.terminate
      | _ => triggerUB
      end.

  Definition spawn : string * SAny.t → itree crisE nat :=
    λ '(fn, arg),
      'ths : thpool <- cgetU v_ths;;
      new_stid <- trigger (Spawn NDSHdr._spawn (fn, arg)↑);;
      cput v_ths (ths ++ [(new_stid, None)]);;;
      Ret (List.length ths).

  Definition yield : unit → itree crisE unit :=
    λ _,
      (* sanity checking *)
      'ths : thpool <- cgetU v_ths;;
      tid <- trigger GetTid;;
      'mtid : nat <- cgetU v_tid;;
      match ths !! mtid with
      | Some (stid, _) => if (decide (stid = tid)) then Ret () else triggerUB
      | None => triggerUB
      end;;;
      (* yield *)
      '(exist _ (mtid, stid) _) : _ <- trigger (Choose {p : nat * nat | ths.*1 !! p.1 = Some p.2});;
      cput v_tid mtid;;;
      trigger (Yield stid).

  Definition yield_global : unit → itree crisE unit :=
    λ _,
      'sch: nat <- cgetU v_sch;;
      trigger (Yield sch).

  Definition join : nat → itree crisE (option SAny.t) :=
    λ tid,
      (* possibly infinite loop while waiting for the thread to terminate *)
      orv <- (iterC (λ _,
        'ths : thpool <- cgetU v_ths;;
        match ths !! tid with
        | None => Ret (inr None)
        | Some (_, Some rv) => Ret (inr (Some rv))
        | Some (_, None) => '() : _ <- ccallU NDSHdr.yield tt;; Ret (inl tt)
        end
      ) tt);;
      Ret orv.

  Definition get_tid : unit → itree crisE nat :=
    λ _, cgetU v_tid.

  Definition fnsems : fnsemmap :=
    {[fid NDSHdr.init # (msk_real (msk_scp scp msk_true), (None, cfunU init));
      fid NDSHdr._spawn # (msk_real (msk_scp scp msk_true), (None, cfunU inner_spawn));
      fid NDSHdr.spawn # (msk_real (msk_scp scp msk_true), (None, cfunU spawn));
      fid NDSHdr.yield # (msk_real (msk_scp scp msk_true), (None, cfunU yield));
      fid NDSHdr.yield_global # (msk_real (msk_scp scp msk_true), (None, cfunU yield_global));
      fid NDSHdr.join # (msk_real (msk_scp scp msk_true), (None, cfunU join));
      fid NDSHdr.get_tid # (msk_real (msk_scp scp msk_true), (None, cfunU get_tid))]}.

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scp;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_ths # ([] : thpool)↑; v_tid # 0↑; v_sch # 0↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End NDSI. End NDSI.
