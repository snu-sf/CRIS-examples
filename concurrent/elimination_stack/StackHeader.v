Require Import CRIS.common.Common.
From CRIS.imp_system Require Import imp.ImpPrelude.

Module StackHdr.
  Definition new_stack := fnsig "Stack.new_stack" imp_fun_t.
  Definition push := fnsig "Stack.push" imp_fun_t.
  Definition pop := fnsig "Stack.pop" imp_fun_t.
End StackHdr.