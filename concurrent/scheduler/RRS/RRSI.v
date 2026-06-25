Require Import CRIS.
Require Import RRSHeader SchHeader.

Definition thpool : Type := list nat.

Module RRSI. Section RRSI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Context (parent_yield : string).

  Definition scp : list string := [RRS].
  Definition v_ths := RRS ↯ "ths".
  Definition v_tid := RRS ↯ "tid".
  Definition v_sch := RRS ↯ "sch".

  (* function which would be called by "spawn" of parent scheduler *)
  Definition init : SAny.t → itree crisE unit :=
    λ sfn,
      (* initialize RRS with given function *)
      'fn: string <- (sfn↓↓)?;;
      stid <- trigger GetTid;;
      cput v_sch stid;;;
      'ths: thpool <- cgetU v_ths;;
      new_stid <- trigger (Spawn RRSHdr._spawn.1 (fn, tt↑↑)↑);;
      cput v_ths (ths ++ [new_stid]);;;
      cput v_tid (List.length ths);;;
      trigger (Yield new_stid);;;
      (* infinite global yield *)
      iterC (λ _,
        trigger (Call parent_yield tt↑);;;
        'ths: thpool <- cgetU v_ths;;
        'mtid: nat <- cgetU v_tid;;
        match ths !! mtid with
        | Some stid => trigger (Yield stid);;; Ret (inl tt)
        | None => triggerUB
        end
      ) tt.

  (* spawnable function *)
  Definition inner_spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      trigger (Call fn arg↑);;;
      RRS.spin.

  Definition spawn : string * SAny.t → itree crisE nat :=
    λ '(fn, arg),
      'ths : thpool <- cgetU v_ths;;
      new_stid <- trigger (Spawn RRSHdr._spawn.1 (fn, arg)↑);;
      cput v_ths (ths ++ [new_stid]);;;
      Ret (List.length ths).

  Definition yield : unit → itree crisE unit :=
    λ _,
      (* sanity checking *)
      'ths : thpool <- cgetU v_ths;;
      tid <- trigger GetTid;;
      'mtid : nat <- cgetU v_tid;;
      match ths !! mtid with
      | Some stid => if (decide (stid = tid)) then Ret () else triggerUB
      | None => triggerUB
      end;;;
      (* yield *)
      let mtid : nat := succ_rr mtid (List.length ths) in
      match ths !! mtid with
      | Some stid =>
          cput v_tid mtid;;;
          trigger (Yield stid)
      | None => triggerUB
      end.

  Definition yield_global : unit → itree crisE unit :=
    λ _,
      'sch: nat <- cgetU v_sch;;
      trigger (Yield sch).

  Definition get_tid : unit → itree crisE nat :=
    λ _, cgetU v_tid.

  Definition fnsems : fnsemmap :=
    {[fid RRSHdr.init # (msk_real (msk_scp scp msk_true), (None, cfunU RRSHdr.init init));
      fid RRSHdr._spawn # (msk_real (msk_scp scp msk_true), (None, cfunU RRSHdr._spawn inner_spawn));
      fid RRSHdr.spawn # (msk_real (msk_scp scp msk_true), (None, cfunU RRSHdr.spawn spawn));
      fid RRSHdr.yield # (msk_real (msk_scp scp msk_true), (None, cfunU RRSHdr.yield yield));
      fid RRSHdr.yield_global # (msk_real (msk_scp scp msk_true), (None, cfunU RRSHdr.yield_global yield_global));
      fid RRSHdr.get_tid # (msk_real (msk_scp scp msk_true), (None, cfunU RRSHdr.get_tid get_tid))]}.

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scp;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_ths # ([] : thpool)↑; v_tid # 0↑; v_sch # 0↑]};
  |}.
  Solve All Obligations with mod_tac.
  
  Definition t := SMod.to_mod ∅ smod.
End RRSI. End RRSI.
