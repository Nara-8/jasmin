From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params_proof
  compiler_util
  expr
  fexpr
  fexpr_sem
  linear
  fexpr_facts
  psem
  psem_facts
  one_varmap
  sem_one_varmap.
Require Import
  linearization
  linearization_proof
  lowering
  propagate_inline_proof
  slh_lowering
  slh_lowering_proof
  stack_alloc
  stack_alloc_proof.
Require
  register_zeroization
  register_zeroization_proof
  register_zeroization_proof_utils.
Require arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof
  sem_params_of_arch_extra.
Require Import
  x86_decl
  x86_extra
  x86_instr_decl
  x86_lowering
  x86_lowering_proof.
Require Export x86_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.

Context
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

(* ------------------------------------------------------------------------ *)
(* Flag combination hypotheses. *)

Lemma x86_cf_xsemP gd s e0 e1 e2 e3 cf v :
  let e := PappN (Ocombine_flags cf) [:: e0; e1; e2; e3 ] in
  let e' := cf_xsem enot eand eor expr.eeq e0 e1 e2 e3 cf in
  sem_pexpr gd s e = ok v
  -> sem_pexpr gd s e' = ok v.
Proof.
  rewrite /=.

  t_xrbindP=> vs0 v0 hv0 vs1 v1 hv1 vs2 v2 hv2 vs3 v3 hv3 ? ? ? ?;
    subst vs0 vs1 vs2 vs3.
  rewrite /sem_opN /=.
  t_xrbindP=> b b0 hb0 b1 hb1 b2 hb2 b3 hb3 hb ?; subst v.
  move: hb0 => /to_boolI ?; subst v0.
  move: hb1 => /to_boolI ?; subst v1.
  move: hb2 => /to_boolI ?; subst v2.
  move: hb3 => /to_boolI ?; subst v3.

  move: hb.
  rewrite /sem_combine_flags.
  rewrite /cf_xsem.

  case: cf_tbl => -[] [] [?] /=; subst b.
  all: by rewrite ?hv0 ?hv1 ?hv2 ?hv3.
Qed.

Definition x86_hpiparams : h_propagate_inline_params :=
  {|
    pip_cf_xsemP := x86_cf_xsemP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

  Variable (P' : sprog).

  Lemma lea_ptrP s1 e i x tag ofs w s2 :
    P'.(p_globs) = [::]
    -> (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
    -> write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2
    -> psem.sem_i (pT := progStack) P' w s1 (lea_ptr x e tag ofs) s2.
  Proof.
    move=> P'_globs he hx.
    constructor.
    rewrite /sem_sopn /= P'_globs /sem_sop2 /=.
    move: he; t_xrbindP=> _ -> /= -> /=.
    by rewrite /exec_sopn truncate_word_u /= truncate_word_u /= hx.
  Qed.

Lemma x86_mov_ofsP s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs x86_saparams x tag vpk e ofs = Some ins
  -> write_lval [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> psem.sem_i (pT := progStack) P' w s1 ins s2.
Proof.
  move=> P'_globs he.
  rewrite /x86_saparams /= /x86_mov_ofs.
  case: (mk_mov vpk).
  - move=> [<-]. exact: lea_ptrP.
  case: eqP => [-> | _] [<-].
  + by rewrite wrepr0 GRing.addr0 -P'_globs; apply mov_wsP; rewrite // P'_globs.
  exact: lea_ptrP.
Qed.

Lemma x86_immediateP w s (x: var_i) z :
  vtype x = sword Uptr
  -> psem.sem_i (pT := progStack) P' w s (x86_immediate x z) (with_vm s (evm s).[x <- pof_val x.(vtype) (Vword (wrepr Uptr z))])%vmap.
Proof.
  case: x => - [] [] // [] // x xi _ /=.
  have := mov_wsP (pT := progStack) AT_none _ (cmp_le_refl _).
  move => /(_ _ _ _ _ _ P').
  apply; last reflexivity.
  by rewrite /= truncate_word_u.
Qed.

End STACK_ALLOC.

Definition x86_hsaparams : h_stack_alloc_params (ap_sap x86_params) :=
  {|
    mov_ofsP := x86_mov_ofsP;
    sap_immediateP := x86_immediateP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Definition x86_lassign_eval_instr
  (lp : lprog) s0 s1 fn pc ii x e ws ws' w (w' : word ws') :
  sem_rexpr (emem s0) (evm s0) e = ok (Vword w')
  -> truncate_word ws w' = ok w
  -> write_lexpr x (Vword w) s0 = ok s1
  -> let: li := li_of_lopn_args ii (x86_lassign x ws e) in
     let: ls0 := of_estate s0 fn pc in
     let: ls1 := of_estate s1 fn (pc + 1) in
     eval_instr lp li ls0 = ok ls1.
Proof.
  move=> hseme hw hwritex.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite to_estate_of_estate.
  rewrite hseme {hseme} /=.

  case: ws w hw hwritex => /= w hw hwritex.
  all: rewrite /exec_sopn /=.
  all: rewrite hw {hw} /=.
  all: rewrite hwritex {hwritex} /=.
  all: by rewrite addn1.
Qed.

Definition x86_op_align_eval_instr (lp : lprog) ls ii xname vi ws al w :
  let: x :=
    {|
      v_var := {| vname := xname; vtype := sword ws; |};
      v_info := vi;
    |}
  in
  (ws <= U64)%CMP
  -> get_var (lvm ls) (v_var x) = ok (Vword w)
  -> let: li := li_of_lopn_args ii (x86_op_align x ws al) in
     let w' := align_word al w in
     let: vm' :=
       (lvm ls)
         .[to_var OF <- ok false]
         .[to_var CF <- ok false]
         .[to_var SF <- ok (SF_of_word w')]
         .[to_var PF <- ok (PF_of_word w')]
         .[to_var ZF <- ok (ZF_of_word w')]
         .[v_var x <- ok (pword_of_word w')]%vmap
     in
     let: ls' :=
       {|
         lscs := lscs ls;
         lmem := lmem ls;
         lvm := vm';
         lfn := lfn ls;
         lpc := lpc ls + 1;
       |}
     in
     eval_instr lp li ls = ok ls'.
Proof.
  set x := {| vname := xname; |}.
  set xi := {| v_var := x; |}.
  set w' := align_word _ _.
  move=> hws hgetx.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /=.
  rewrite hgetx {hgetx} /=.
  rewrite /exec_sopn /=.
  rewrite !truncate_word_u /=.
  rewrite /sopn_sem /=.
  rewrite /x86_AND /check_size_8_64.
  rewrite hws {hws} /=.
  rewrite sumbool_of_boolET.
  rewrite /with_vm /of_estate pword_of_wordE -/(align_word al w) /=.
  by rewrite addn1.
Qed.


Context
  (lp : lprog)
  (sp_rsp : Ident.ident)
  (fn : funname).

Let vrsp : var := mk_ptr sp_rsp.
Let vrspi : var_i := VarI vrsp dummy_var_info.
Let vtmp : var := mk_ptr (lip_tmp x86_liparams).
Let vtmpi : var_i := VarI vtmp dummy_var_info.

Definition x86_spec_lip_allocate_stack_frame s pc ii ts sz :
  let: args := lip_allocate_stack_frame x86_liparams vrspi sz in
  let: i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let: ts' := pword_of_word (ts - wrepr Uptr sz) in
  let: s' := with_vm s (evm s).[vrsp <- ok ts']%vmap in
  (evm s).[vrsp]%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  by rewrite /sem_sop2 /exec_sopn /= !truncate_word_u /= truncate_word_u /= pword_of_wordE.
Qed.

Definition x86_spec_lip_free_stack_frame s pc ii ts sz :
  let args := lip_free_stack_frame x86_liparams vrspi sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts + wrepr Uptr sz) in
  let s' := with_vm s (evm s).[vrsp <- ok ts']%vmap in
  (evm s).[vrsp]%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
    = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  by rewrite /sem_sop2 /exec_sopn /= !truncate_word_u /= truncate_word_u /= pword_of_wordE.
Qed.

Lemma x86_spec_lip_set_up_sp_register s r ts al sz P Q :
  let: ts' := align_word al (ts - wrepr Uptr sz) in
  let: lcmd := set_up_sp_register x86_liparams vrspi sz al r in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> isSome (lip_set_up_sp_register x86_liparams vrspi sz al r)
  -> vtype r = sword Uptr
  -> vtmp <> vrsp
  -> vname (v_var r) \notin (lip_not_saved_stack x86_liparams)
  -> v_var r <> vrsp
  -> get_var (evm s) vrsp = ok (Vword ts)
  -> wf_vm (evm s)
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: s' := with_vm s vm' in
       let: ls' := of_estate s' fn (size P + size lcmd) in
       [/\ lsem lp ls ls'
         , wf_vm vm'
         , vm' = (evm s)
             [\ Sv.add (v_var r) (Sv.add vtmp (Sv.add vrsp vflags)) ]
         , get_var vm' vrsp = ok (Vword ts')
         , get_var vm' (v_var r) = ok (Vword ts)
         & forall x,
             Sv.In x vflags
             -> ~ is_ok (vm'.[x]%vmap)
             -> (evm s).[x]%vmap = vm'.[x]%vmap
       ].
Proof.
  move=> hbody _ hr.
  set ts' := align_word _ _.
  move: r hr hbody => [[rtype rname] rinfo] /= ?; subst rtype.
  set r := {| v_info := rinfo; |}.
  move=> hbody _ _ hneq_r_rsp hgetrsp hwf_vm.

  move: hbody.
  set i_mov_r := _ _ (x86_lassign (LLvar r) _ _).
  set i_sub_rsp := _ _ (x86_allocate_stack_frame vrspi _).
  set i_align_rsp := _ _ (x86_op_align vrspi _ _).
  move=> hbody.

  set vm0 := (evm s).[v_var r <- ok (pword_of_word ts)]%vmap.
  set vm2 := vm0.[vrsp <- ok (pword_of_word (ts - wrepr Uptr sz))]%vmap.

  eexists.
  split.

  - apply: lsem_step3; rewrite /lsem1 /step.

    (* R[r] := R[rsp]; *)
    + rewrite -{1}(addn0 (size P)).
      rewrite (find_instr_skip hbody) /=.
      apply: x86_lassign_eval_instr.
      * exact: hgetrsp.
      * exact: truncate_word_u.
        rewrite /write_lval /write_var /=.
        rewrite /with_vm pword_of_wordE -/vm0.
        reflexivity.

    (* R[rsp] := R[rsp] - sz; *)
    + rewrite (find_instr_skip hbody) /=.
      apply: x86_spec_lip_allocate_stack_frame.
      rewrite Fv.setP_neq; last by apply/eqP.
      move: hgetrsp.
      rewrite get_varE.
      case: _.[_]%vmap => //= -[pws w ?].
      move=> [?]; subst pws.
      move=> [?]; subst w.
      rewrite pword_of_wordE.
      reflexivity.

    (* R[rsp] := R[rsp] & alignment; *)
    rewrite addn1 -addn2.
    rewrite (find_instr_skip hbody) /=.
    rewrite -(addn1 2) addnA.
    rewrite -/vm2.
    apply:
      (x86_op_align_eval_instr
         (w := ts - wrepr Uptr sz)
         _ _ _
         (cmp_le_refl _)).
    by t_get_var.

  - repeat apply: wf_vm_set. exact: hwf_vm.

  - move=> x. t_notin_add. by t_vm_get.

  - by t_get_var.

  - by t_get_var.

  rewrite /= -/ts'.
  move=> x /sv_of_listP /mapP [f _ ->].
  rewrite Fv.setP_neq //.
  case: f;
    by repeat (rewrite Fv.setP_neq; last by apply /eqP => h; have := inj_to_var h); rewrite Fv.setP_eq.
Qed.

Lemma x86_spec_lip_set_up_sp_stack s ts m' al sz off P Q :
  let: ts' := align_word al (ts - wrepr Uptr sz) in
  let: lcmd := set_up_sp_stack x86_liparams vrspi sz al off in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> isSome (lip_set_up_sp_stack x86_liparams vrspi sz al off)
  -> vtmp <> vrsp
  -> get_var (evm s) vrsp = ok (Vword ts)
  -> wf_vm (evm s)
  -> write (emem s) (ts' + wrepr Uptr off)%R ts = ok m'
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: s' := {| escs := escs s; evm := vm'; emem := m'; |} in
       let: ls' := of_estate s' fn (size P + size lcmd) in
       [/\ lsem (spp := mk_spp) lp ls ls'
         , wf_vm vm'
         , vm' = (evm s) [\ Sv.add vtmp (Sv.add vrsp vflags) ]
         , get_var vm' vrsp = ok (Vword ts')
         & forall x,
             Sv.In x vflags
             -> ~ is_ok (vm'.[x]%vmap)
             -> (evm s).[x]%vmap = vm'.[x]%vmap
       ].
Proof.
  set ts' := align_word _ _.
  move=> hbody _ hneq_tmp_rsp hgetrsp hwf_vm hwrite.

  move: hbody.
  rewrite /=.
  rewrite -[[:: _, _, _, _ & Q]]/([:: _; _; _ ] ++ [:: _ & Q]).
  rewrite -[[:: _; _; _]]/(map _ (x86_set_up_sp_register vrspi sz al vtmpi)).
  move=> hbody.

  have [vm0 [hsem hwf_vm0 hvm0 hgetrsp0 hgettmp0 hflags]] :=
    x86_spec_lip_set_up_sp_register
      (r := vtmpi)
      hbody
      erefl
      erefl
      hneq_tmp_rsp
      erefl
      hneq_tmp_rsp
      hgetrsp
      hwf_vm.

  exists vm0.
  split.

  - apply: (lsem_trans hsem).
    apply: LSem_step.
    rewrite /lsem1 /step /=.
    rewrite (find_instr_skip hbody) /=.
    rewrite
      (x86_lassign_eval_instr
         _
         (s1 := {| escs := escs s; emem := m'; evm := vm0; |})
         _ _ _
         (w := ts)
         (w' := ts)).
    + by rewrite -addnA addn1.
    + exact: hgettmp0.
    + exact: truncate_word_u.
    + rewrite /=.
      rewrite hgetrsp0 {hgetrsp0} /=.
      rewrite !truncate_word_u.
      rewrite -/ts'.
      by rewrite /= hwrite {hwrite}.

  - exact: hwf_vm0.

  - move=> x hx.
    rewrite hvm0; first done.
    rewrite Sv_equal_add_add.
    exact: hx.

  - exact: hgetrsp0.

  exact: hflags.
Qed.

Definition x86_hlip_lassign
  (s1 s2 : estate) pc ii x e ws li ws' (w : word ws) (w' : word ws') :
  lassign x86_liparams x ws e = Some li
  -> sem_rexpr (emem s1) (evm s1) e = ok (Vword w')
  -> truncate_word ws w' = ok w
  -> write_lexpr x (Vword w) s1 = ok s2
  -> eval_instr lp (MkLI ii li) (of_estate s1 fn pc)
     = ok (of_estate s2 fn pc.+1).
Proof.
  move=> [<-] hseme hw hwritex.
  rewrite (x86_lassign_eval_instr _ _ _ _ hseme hw hwritex).
  by rewrite addn1.
Qed.

End LINEARIZATION.

Definition x86_hliparams : h_linearization_params (ap_lip x86_params) :=
  {|
    spec_lip_allocate_stack_frame := x86_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame := x86_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register := x86_spec_lip_set_up_sp_register;
    spec_lip_set_up_sp_stack := x86_spec_lip_set_up_sp_stack;
    hlip_lassign := x86_hlip_lassign;
  |}.

Lemma x86_ok_lip_tmp :
  exists r : reg_t, of_ident (lip_tmp (ap_lip x86_params)) = Some r.
Proof.
  by exists RAX; rewrite /= to_identK.
Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

(* Due to the order of the parameters we can't defined this as a record. *)
Definition x86_hloparams : h_lowering_params (ap_lop x86_params).
Proof.
  split. exact: @lower_callP.
Defined.


(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

(* FIXME: Is there a way of avoiding this import? *)
Import arch_sem.

Lemma not_condtP (c : cond_t) rf b :
  eval_cond rf c = ok b -> eval_cond rf (not_condt c) = ok (negb b).
Proof.
  case: c => /=.
  1,3,5,9,11: by case: (rf _) => //= ? [->].
  1,2,3,6,7: by case: (rf _) => //= ? [<-]; rewrite negbK.
  + by case: (rf CF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negb_or.
  + by case: (rf CF) => //= ?; case: (rf _) => //= ? [<-]; rewrite -negb_or negbK.
  + by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negbK.
  + by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  + by case: (rf ZF) => //= ?; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negb_or negbK.
  by case: (rf ZF) => //= ?; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negb_and negbK.
Qed.

Lemma or_condtP ii e c1 c2 c rf b1 b2:
  or_condt ii e c1 c2 = ok c ->
  eval_cond rf c1 = ok b1 ->
  eval_cond rf c2 = ok b2 ->
  eval_cond rf c  = ok (b1 || b2).
Proof.
  case: c1 => //; case: c2 => //= -[<-] /=.
  + by case: (rf _) => // ? [->]; case: (rf _) => // ? [->].
  + by case: (rf _) => // ? [->]; case: (rf _) => // ? [->] /=; rewrite orbC.
  + by case: (rf ZF) => // ? [->]; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; case: (rf _) => //= ? [->]; rewrite orbC.
Qed.

Lemma and_condtP ii e c1 c2 c rf b1 b2:
  and_condt ii e c1 c2 = ok c ->
  eval_cond rf c1 = ok b1 ->
  eval_cond rf c2 = ok b2 ->
  eval_cond rf c  = ok (b1 && b2).
Proof.
  case: c1 => //; case: c2 => //= -[<-] /=.
  + by case: (rf _) => // ? [<-]; case: (rf _) => // ? [<-].
  + by case: (rf _) => // ? [<-]; case: (rf _) => // ? [<-] /=; rewrite andbC.
  + by case: (rf ZF) => // ? [<-]; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; case: (rf _) => //= ? [->]; rewrite andbC.
Qed.

Lemma of_var_e_boolP ii x f :
  of_var_e_bool ii x = ok f ->
  of_var_e ii x = ok f.
Proof. by rewrite /of_var_e_bool /of_var_e; case: of_var. Qed.

Lemma eval_assemble_cond : assemble_cond_spec x86_agparams.
Proof.
  move=> ii m rf e c v; rewrite /x86_agparams /eval_cond /get_rf /=.
  move=> eqv; elim: e c v => //.
  + move=> x c v /=; t_xrbindP=> r /of_var_e_boolP ok_r ok_ct ok_v.
    have := xgetflag_ex eqv ok_r ok_v.
    case: {ok_r ok_v} r ok_ct => // -[<-] {c} /= h;
      eexists;
      eauto;
      by case: (rf _).
  + case => //= e hrec; t_xrbindP => c v ce hce <- ve hve.
    rewrite /sem_sop1 /=; t_xrbindP => b hb <-.
    have := hrec _ _ hce hve.
    move=> /(value_of_bool_uincl hb).
    move=> -/not_condtP /=.
    move=> ->.
    by exists (~~b).
  case => //=.
  + move=> e1 _ e2 _ c v.
    case: e1 => //= x1; case: e2 => //= x2; t_xrbindP => f1 /of_var_e_boolP ok_f1 f2 /of_var_e_boolP ok_f2.
    case: ifP => // /orP hor [<-] v1 /(xgetflag eqv ok_f1) hv1 v2 /(xgetflag eqv ok_f2) hv2.
    move=> /sem_sop2I /= [b1 [b2 [b3 [hb1 hb2 [<-] ->]]]].
    move: (hv1 _ hb1) (hv2 _ hb2) => hfb1 hfb2.
    exists (b1 == b2); last done.
    by case: hor => /andP [] /eqP ? /eqP ?; subst f1 f2; rewrite hfb1 hfb2 //= eq_sym.
  + move=> e1 hrec1 e2 hrec2 c v; t_xrbindP => c1 hc1 c2 hc2 hand v1 hv1 v2 hv2.
    move=> /sem_sop2I /= [b1 [b2 [b3 [hb1 hb2 [<-] ->]]]].
    have /(value_of_bool_uincl hb1) hec1 := hrec1 _ _ hc1 hv1.
    have /(value_of_bool_uincl hb2) hec2 := hrec2 _ _ hc2 hv2.
    have /= -> := and_condtP hand hec1 hec2.
    by exists (b1 && b2).
  move=> e1 hrec1 e2 hrec2 c v; t_xrbindP => c1 hc1 c2 hc2 hor v1 hv1 v2 hv2.
  move=> /sem_sop2I /= [b1 [b2 [b3 [hb1 hb2 [<-] ->]]]].
  have /(value_of_bool_uincl hb1) hec1 := hrec1 _ _ hc1 hv1.
  have /(value_of_bool_uincl hb2) hec2 := hrec2 _ _ hc2 hv2.
  have /= -> := or_condtP hor hec1 hec2.
  by exists (b1 || b2).
Qed.

Lemma assemble_mov ii rip m m' s i x op args:
  lom_eqv rip m s ->
  write_lexpr x (Vword (wrepr U64 i)) m = ok m' ->
  assemble_asm_op x86_agparams rip ii (None, MOV U64) [:: x] [:: re_i U64 i] = ok (op, args) ->
  exists2 s' : asmmem, Let acc := eval_op op args s in ok acc = ok s' & lom_eqv rip m' s'.
Proof.
  move=> hlo hw hass; assert (h := assemble_asm_opI hass).
  case: h => hca hcd hidc -> /=.
  have he : sem_rexprs m [:: re_i U64 i] = ok [:: Vword (wrepr U64 i)] by done.
  have hws : write_lexprs [:: x] [::Vword (wrepr U64 i)] m = ok m' by rewrite /= hw.
  have [] := compile_asm_opn_aux eval_assemble_cond he _ hws hca hcd hidc hlo.
  + by rewrite /exec_sopn /= truncate_word_u.
  by rewrite /eval_op => s' -> ?; exists s'.
Qed.

Lemma lom_eqv_set_xreg rip (xr : xreg_t) m s :
  lom_eqv rip m s ->
  let: pw :=
    {|
      pw_size := U256;
      pw_word := asm_xreg s xr;
      pw_proof := erefl (U256 ≤ U256)%CMP;
    |}
  in
  lom_eqv rip (with_vm m (evm m).[to_var xr <- ok pw]%vmap) s.
Proof.
  case => h1 h2 h3 h4 h5 h6 h7 h9; split => //; rewrite /eqflags /get_var /=.
  + by rewrite Fv.setP_neq //; apply/eqP; case: h4; auto.
  1,2,4: by move=> x v; rewrite Fv.setP_neq; auto.
  move=> x v; case: (to_var xr =P to_var x) => [h | /eqP hne].
  + move: (inj_to_var h) => ->. by rewrite Fv.setP_eq => -[<-].
  by rewrite Fv.setP_neq; auto.
Qed.

Lemma check_sopn_args_xmm rip ii oargs es ads cond n k ws:
  check_sopn_args x86_agparams rip ii oargs es ads ->
  check_i_args_kinds [::cond] oargs ->
  nth (E 0, sword8) ads n = (E k, sword ws) ->
  nth xmm cond k = xmm ->
  n < size es ->
  exists (r: xreg_t),
   exists2 vi,
    nth (Rexpr (Fconst 0)) es n = Rexpr (Fvar {| v_var := to_var r;  v_info := vi |}) &
    oseq.onth oargs k = Some (XReg r).
Proof.
  rewrite /= orbF => hca hc hE hxmm hn.
  have /(_ n):= all2_nth (Rexpr (Fconst 0)) (E 0, sword8) _ hca.
  rewrite hn => /(_ erefl) ha.
  assert (hcIaux := check_sopn_argP ha).
  move: hcIaux; rewrite hE => h; inversion_clear h.
  rewrite H; move: H => /(oseq.onthP (Imm (wrepr U8 0))) /andP [hk] /eqP heqa.
  have : check_arg_kinds (nth (Imm (wrepr U8 0)) oargs k) (nth xmm cond k).
  + by have /(_ k) := all2_nth (Imm (wrepr U8 0)) xmm _ hc; rewrite hk; apply.
  rewrite heqa hxmm.
  rewrite /check_arg_kinds /= orbF.
  move: H1; rewrite /compat_imm /= => {heqa H2}.
  case: a => // r /orP [/eqP ? _ | ]; last by case a'.
  subst a'; case: nth H0 => /=; first by t_xrbindP.
  case => //; last by case=> // ? -[] //=; t_xrbindP.
  move=> [v vi] h;
    assert (h1 := xreg_of_varI h);
    move: (of_varI h1) => /= <-;
    eauto.
Qed.

Lemma check_sopn_dests_xmm rip ii oargs xs ads cond n k ws:
  check_sopn_dests x86_agparams rip ii oargs xs ads ->
  check_i_args_kinds [::cond] oargs ->
  nth (E 0, sword8) ads n = (E k, sword ws) ->
  nth xmm cond k = xmm ->
  n < size xs ->
  exists (r: xreg_t),
   exists2 vi,
    nth (LLvar {| v_var := rip; v_info := dummy_var_info|}) xs n =
       LLvar {| v_var := to_var r;  v_info := vi |} &
    oseq.onth oargs k = Some (XReg r).
Proof.
  rewrite /= orbF => hca hc hE hxmm hn.
  have /(_ n):= all2_nth (Rexpr (Fconst 0)) (E 0, sword8) _ hca.
  rewrite size_map hn => /(_ erefl).
  rewrite (nth_map (LLvar {| v_var := rip; v_info := dummy_var_info |})) //.
  set e := nth (LLvar _) _ _.
  rewrite /check_sopn_dest hE /=.
  case H : oseq.onth => [a | //].
  move: H => /(oseq.onthP (Imm (wrepr U8 0))) /andP [hk] /eqP heqa.
  have : check_arg_kinds (nth (Imm (wrepr U8 0)) oargs k) (nth xmm cond k).
  + by have /(_ k) := all2_nth (Imm (wrepr U8 0)) xmm _ hc; rewrite hk; apply.
  rewrite heqa hxmm.
  case heq : assemble_word_load => [ a' | //]; rewrite andbT.
  rewrite /check_arg_kinds /= orbF => ha /eqP ?; subst a' => {heqa}.
  case: a heq ha => // r heq _; exists r.
  case: e heq => /=; t_xrbindP => //.
  move=> [v vi] h;
    assert (h1 := xreg_of_varI h);
    move: (of_varI h1) => /= <-;
    eauto.
Qed.

Lemma assemble_extra_concat128 rip ii lvs args m xs ys m' s ops ops' :
  sem_rexprs m args = ok xs ->
  exec_sopn (Oasm (ExtOp Oconcat128)) xs = ok ys ->
  write_lexprs lvs ys m = ok m' ->
  to_asm ii Oconcat128 lvs args = ok ops ->
  mapM (fun '(op0, ls, rs) => assemble_asm_op x86_agparams rip ii op0 ls rs) ops = ok ops' ->
  lom_eqv rip m s ->
  exists2 s' : asmmem,
    foldM (fun '(op'', asm_args) => [eta eval_op op'' asm_args]) s ops' = ok s' & lom_eqv rip m' s'.
Proof.
  case: args => // h [] // [] // [] // [l li] [] //=.
  rewrite /exec_sopn /sopn_sem /=.
  t_xrbindP => vh hvh _ vl hvl <- <-{xs}.
  t_xrbindP => _ wh hwh wl hwl <- <-{ys} /=.
  case: lvs => // y [] /=; t_xrbindP => // z hw ? hops hmap hlow; subst z.
  have hwr : write_lexprs [::y] [::Vword (make_vec U256 [:: wl; wh])] m = ok m' by rewrite /= hw.
  move: hmap; rewrite -hops /=; t_xrbindP => -[op oargs] hass hops'.
  assert (h1 := assemble_asm_opI hass); case: h1 => hca hcd hidc ?; subst op => {hass}.
  have [lr [vi /= [??] hlr]]:= check_sopn_args_xmm (n:= 0) hca hidc erefl erefl erefl; subst l vi.
  have [yr [vi /= ? hyr]] := check_sopn_dests_xmm (n:=0) hcd hidc erefl erefl erefl; subst y ops ops'.
  have [s' hwm hlow'] :=
    compile_lvals (asm_e:=x86_extra)
     (id_out := [:: E 0]) (id_tout := [:: sword256]) MSB_CLEAR refl_equal hwr hlow hcd refl_equal.
  exists s'; last done.
  move: hca; rewrite /check_sopn_args /= => /and4P [] _ hE2 hE3 _.
  have [vh' hev2 /= hvh']:= check_sopn_arg_sem_eval eval_assemble_cond hlow hE2 hvh hwh.
  have := check_sopn_arg_sem_eval eval_assemble_cond hlow hE3.
  move=> /(_ (Vword (wrepr U8 1)) (wrepr U8 1) erefl (truncate_word_u _)) [v1 hev3 /= hv1] {hcd hwr hlow' hE2 hE3 hw}.
  move: hidc hyr hlr hev2 hev3 hwm.
  case: oargs => // a0 [] // a1 [] // a2 [] // a3 l hcheck /= [?] [?] hev2 hev3 /= hwm; subst a0 a1.
  rewrite /eval_op /= /exec_instr_op /= /eval_instr_op hcheck /= hev2 hev3 /= hvh' hv1 /=.
  move: hwm; rewrite /mem_write_vals /= /mem_write_val /= !truncate_word_u /= truncate_word_u /= => <-; do 2!f_equal.
  rewrite  /winserti128 /split_vec /=; f_equal.
  congr (fun x => [::x; wh]).
  case: hlow => _ _ _ _ _ _ /(_ _ _ hvl) hu _.
  move: hwl hu; rewrite /to_word.
  case: (vl) => // [ws wl' /= | []//].
  rewrite /word_uincl mul0n => /truncate_wordP[] hle ? /andP[] _ /eqP ?; subst.
  by rewrite (@subword0 U128 U256) zero_extend_idem.
Qed.

Lemma assemble_extra_op rip ii op lvs args m xs ys m' s ops ops':
  sem_rexprs m args = ok xs ->
  exec_sopn (Oasm (ExtOp op)) xs = ok ys ->
  write_lexprs lvs ys m = ok m' ->
  to_asm ii op lvs args = ok ops ->
  mapM (fun '(op0, ls, rs) => assemble_asm_op x86_agparams rip ii op0 ls rs) ops = ok ops' ->
  lom_eqv rip m s ->
  exists2 s' : asmmem,
    foldM (fun '(op'', asm_args) => eval_op op'' asm_args) s ops' = ok s' &
    lom_eqv rip m' s'.
Proof.
  case: op => //.
  (* Oset0 *)
  + move=> sz; rewrite /exec_sopn /sopn_sem /=.
    rewrite /Oset0_instr; case: ifP => /= hsz64.
    + case: args => /=; t_xrbindP; last by move => *; subst.
      move => <-{xs} _ /ok_inj <- /= <-{ys} hw x.
      case: rev => [ // | [ // | d ] ds ] /ok_inj <-{x} <- /=.
      t_xrbindP => -[op' asm_args] hass <- hlo /=.
      assert (h := assemble_asm_opI hass); case: h=> hca hcd hidc -> /= {hass}.
      move: hca; rewrite /check_sopn_args /= => /and3P [].
      rewrite /check_sopn_arg /=.
      case: asm_args hidc hcd => //= a0 [ // | ] a1 [] //= hidc hcd;
       last by rewrite /check_args_kinds /= !andbF.
      case ok_y: xreg_of_var => [y|//].
      assert (h := xreg_of_varI ok_y); move: h => {ok_y} ok_y.
      rewrite !andbT /compat_imm.
      case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a0 a1; only 2-3: by [].
      rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
      rewrite truncate_word_le // /x86_XOR /check_size_8_64 hsz64 /= wxor_xx.
      set id := instr_desc_op (XOR sz).
      rewrite /SF_of_word msb0.
      by have [s' -> /= ?]:= (@compile_lvals _ _ _ _ _ _ _ _ _ _ _
             rip ii m lvs m' s [:: Reg r; Reg r]
             id.(id_out) id.(id_tout)
             (let vf := Some false in let: vt := Some true in (::vf, vf, vf, vt, vt & (0%R: word sz)))
             (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)); eauto.
    case: xs => // ok_xs /ok_inj <-{ys} hw.
    case: rev => [ // | [ // | d ] ds ] /ok_inj <-{ops} /=.
    t_xrbindP => -[op' asm_args] hass <- hlo /=.
    assert (h := assemble_asm_opI hass); case: h=> hca hcd hidc -> /= {hass}.
    move: hca; rewrite /check_sopn_args /= => /and3P [].
    rewrite /check_sopn_arg /=.
    case: asm_args hidc hcd => //= a0 [// | ] a1 [] //= a2 [] //=;
      last by rewrite /check_args_kinds /= !andbF.
    rewrite orbF => hidc hcd.
    case ok_y: xreg_of_var => [y|//].
    assert (h := xreg_of_varI ok_y); move: h => {ok_y} ok_y.
    rewrite !andbT /compat_imm.
    case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a1 a2.
    1-2: by move: hidc; rewrite /check_args_kinds /= andbF.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
    rewrite truncate_word_le; last exact: wsize_ge_U256.
    rewrite /x86_VPXOR hidc /= /x86_u128_binop /check_size_128_256 wsize_ge_U256.
    have -> /= : (U128 ≤ sz)%CMP by case: (sz) hsz64.
    rewrite wxor_xx; set id := instr_desc_op (VPXOR sz).
    by have [s' -> /= ?] := (@compile_lvals _ _ _ _ _ _ _ _ _ _ _
               rip ii m lvs m' s [:: a0; XReg r; XReg r]
               id.(id_out) id.(id_tout)
               (0%R: word sz)
               (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)); eauto.
  (* Oconcat128 *)
  + by apply assemble_extra_concat128.

  (* Ox86MOVZX32 *)
  + case: lvs => // -[] // x [] //.
    rewrite /exec_sopn /sopn_sem /=.
    case: xs => //; t_xrbindP => vs1 [] // hva _ va htwa /ok_inj <- <-{ys}.
    t_xrbindP => _ m1 hwx <- <-{m'} <-{ops} /=.
    t_xrbindP => -[op' asm_args] hass <- hlow /=.
    assert (h1 := assemble_asm_opI hass); case: h1 => hca hcd hidc -> /= {hass}.
    case: asm_args hidc hcd hca => // a0 [ | a1 [] ]; only 1, 3: by rewrite /check_args_kinds /= !andbF.
    move => hidc hcd.
    have := size_mapM hva.
    case: args hva => // r0 [] //=; t_xrbindP => q hva ? _; subst q.
    rewrite andbT => hca1.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
    rewrite /= in hidc;rewrite hidc.
    have [v' /= -> /= -> /=] :=
      check_sopn_arg_sem_eval eval_assemble_cond hlow hca1 hva htwa.
    move: hcd; rewrite /check_sopn_dests /= /check_sopn_dest /= => /andP -[].
    case ok_y: xreg_of_var => [y|//].
    assert (h := xreg_of_varI ok_y); move: h => {ok_y} ok_y.
    rewrite andbT => /eqP ? _; subst a0.
    case: y hidc hca1 ok_y => // r hidc hca1 xr.
    have {xr} xr := of_varI xr.
    rewrite /mem_write_vals.
    eexists.
    * by rewrite /mem_write_val /= truncate_word_u /=.
    move: (hlow) => [h0 h1 hrip hd h2 h2x h3 h4].
    move: hwx; rewrite /write_var /set_var.
    rewrite -xr => -[<-]{m1}.
    rewrite -/(to_pword _ (Vword (zero_extend U64 _))).
    apply: (lom_eqv_write_reg _ _ hlow).
    by right.

  (* SLHinit *)
  + rewrite /exec_sopn /= /sopn_sem /assemble_slh_init /=; t_xrbindP.
    case: xs => // hargs _ [<-] <-.
    case: lvs => // x [] /=; t_xrbindP => // m1 hw ? <- /=; subst m1.
    t_xrbindP => z [op oargs] hass <- <- hlo /=.
    by rewrite -(wrepr0 U64) in hw; apply (assemble_mov hlo hw hass).

  (* SLHupdate *)
  + rewrite /exec_sopn /= /sopn_sem /= /x86_se_update_sem /=; t_xrbindP.
    case: xs => // vb; t_xrbindP => -[] // vw; t_xrbindP => -[] // hargs.
    move=> _ b hb w hw [<-] <- /=.
    case: lvs => //= aux; t_xrbindP => -[] //= x []; t_xrbindP => //=.
    move=> m1 hw1 m2 hw2 [<-].
    rewrite /assemble_slh_update.
    case: aux hw1 => // vaux hw1.
    case: args hargs => // -[] // eb [] // emsf [] // hargs.
    t_xrbindP => /andP []; rewrite negb_or => /andP [] haux1 haux2 /eqP haux <- /=.
    t_xrbindP => -[op oargs] hass _ [op' oargs'] hasscmov <- <- hlo /=.
    have [s1 {hass hlo}] := assemble_mov hlo hw1 hass.
    t_xrbindP => _ -> -> hlo /=.
    assert (h := assemble_asm_opI hasscmov); case: h => hca hcd hidc -> /= {hasscmov}.
    move: hw1 => /=; t_xrbindP => vm hset ?; subst m1.
    have hes : sem_rexprs (with_vm m vm) [:: Rexpr (Fapp1 Onot eb); Rexpr (Fvar vaux); emsf] =
                 ok [:: Vbool (~~b); Vword (wrepr U64 (-1)); vw].
    + move: hargs => /=; t_xrbindP.
      rewrite (free_varsP (vm2:= vm)); last by apply: set_var_disjoint_eq_on haux1 hset.
      rewrite (free_vars_rP (vm2:= vm) (vm1:=evm m) (r:=emsf) (emem m));
        last by apply: set_var_disjoint_eq_on haux2 hset.
      move=> _ -> _ _ -> <- -> [->] /=.
      by rewrite (get_var_set_var vaux hset) eqxx /sem_sop1 /= hb haux.
    have hws : write_lexprs [:: x] [:: Vword (if ~~ b then wrepr U64 (-1) else w)] (with_vm m vm) = ok m2.
    + by rewrite /= hw2.
    have []:= compile_asm_opn_aux eval_assemble_cond hes _ hws hca hcd hidc hlo.
    + by rewrite /exec_sopn /= hw /sopn_sem /= /x86_CMOVcc /= truncate_word_u; case: ifP.
    by rewrite /eval_op => s' -> ?; exists s'.

  (* SLHmove *)
  + move=> hes hex hw [] <- hmap hlo.
    apply: (assemble_opsP eval_assemble_cond hmap erefl _ hlo).
    move: hex; rewrite /= hes /exec_sopn /= /sopn_sem /= /se_move_sem.
    by case: (xs) => //; t_xrbindP => vx [] // _ _ -> [->] /= ->; rewrite hw.

  (* SLHprotect *)

Opaque cat.
  rewrite /exec_sopn /= /sopn_sem /= /Ox86SLHprotect_instr /Uptr /assemble_slh_protect /= => ws.
  case: ifP => /= Hws; t_xrbindP.
    (* ws <= U64 *)
  + case: xs => // vw; t_xrbindP => -[] // vmsf; t_xrbindP => // -[] // hes tr w hw wmsf hmsf.
    rewrite /se_protect_small_sem /x86_OR /check_size_8_64 Hws => -[?]? hws ? hmap hlo; subst tr ys ops.
    apply: (assemble_opsP eval_assemble_cond hmap erefl _ hlo).
    by rewrite /= hes /exec_sopn /= hw hmsf /= /sopn_sem /= /x86_OR /check_size_8_64 Hws /= hws.
  (* ws >= U64 *)
  have {Hws} Hws : (U64 < ws)%CMP by rewrite -cmp_nle_lt Hws.
  have Hws' : (U128 <= ws)%CMP by case: (ws) Hws.
  case: xs => // vw; t_xrbindP => -[] // vmsf; t_xrbindP => // -[] // hes tr w hw wmsf hmsf.
  rewrite /se_protect_large_sem Hws /= => -[?]?; subst tr ys.
  case: lvs => // -[] // [aux iaux] [] // y [] // hws.
  case: args hes => // ew [] // emsf [] // hes1.
  t_xrbindP; rewrite negb_or => /andP [] haux1 haux2 hops /dup[] + hmap hlo.
Transparent cat.
  rewrite -hops /=; t_xrbindP => -[op1 oargs1] hass1 z0 z1 _ z2.
  rewrite mapM_cat /=; t_xrbindP => _ _ _ -[op2 oargs2] hass2 _ _ _ _ {z0 z1 z2}.
Opaque cat.
  assert (h := assemble_asm_opI hass1); case: h => hca hcd hidc _ /= {hass1}.
  have [xr [vi /= [??] _]] := check_sopn_args_xmm (n:= 0) hca hidc erefl erefl erefl.
  subst vi aux => {op1 oargs1 hidc hcd hca}.
  set aux := {| v_var := to_var xr; v_info := iaux |}.
  assert (h := assemble_asm_opI hass2); case: h => hca hcd hidc _ /= {hass2}.
  have [yr [vi /= hy _ ]] := check_sopn_dests_xmm (n:= 0) hcd hidc erefl erefl erefl.

  pose v0 := (s.(asm_xreg) xr).
  pose (pv0 := @Build_pword U256 U256 v0 erefl).
  pose (vm0 := ((evm m).[to_var xr <- ok pv0])%vmap).
  pose (m0 := with_vm m vm0).
  have hlo0: lom_eqv rip m0 s by apply lom_eqv_set_xreg.

  move: hes1 => /=; t_xrbindP => z hew _ z1 hemsf <- ? [?]; subst z z1.
  have heqvm0 : vm0 =[free_vars_r emsf] evm m.
  + by apply/eq_onS/(set_var_disjoint_eq_on (x:= to_var xr) (v:= Vword (s.(asm_xreg) xr))).
  move: hmap; rewrite -hops !mapM_cat; t_xrbindP.
  move=> ops1' hmap1 _ ops2' hmap2 ops3' hmap3 <- <-.
  rewrite foldM_cat.
  (* first instruction *)
  pose v1 := wpinsr (zero_extend U128 (s.(asm_xreg) xr)) wmsf (wrepr U8 0).
  pose (pv1 := (@Build_pword U256 U128 v1 erefl)).
  pose (vm1 := ((evm m0).[to_var xr <- ok pv1])%vmap).
  pose (m1 := with_vm m vm1).
  (* second instruction *)
  pose v2 := wpbroadcast U128 wmsf.
  pose (pv2 := (@Build_pword U256 U128 v2 erefl)).
  pose (vm2 := ((evm m1).[to_var xr <- ok pv2])%vmap).
  pose (m2 := with_vm m vm2).

  have /(_ m2) [|s2 -> hlo2] /= :=
    assemble_opsP eval_assemble_cond hmap1 erefl _ hlo0.
  + have -> /=: get_var vm0 (to_var xr) = ok (Vword (s.(asm_xreg) xr)).
    + by rewrite /get_var /vm0 Fv.setP_eq /=.
    have -> /= : sem_rexpr (emem m) vm0 emsf = ok vmsf.
    + by rewrite -hemsf; apply: free_vars_rP.
    rewrite /exec_sopn /= hmsf /= !truncate_word_le // /=.
    have -> : wand (wrepr U8 0) (x86_nelem_mask U64 U128) = wrepr U8 0.
    + by apply/wunsigned_inj/(wand_modulo _ 1).
    have -> /=: get_var vm1 (to_var xr) = ok (Vword v1).
    + by rewrite /get_var /vm0 Fv.setP_eq /=.
    have -> /= : sem_rexpr (emem m) vm1 emsf = ok vmsf.
    + rewrite -hemsf; apply: free_vars_rP.
      apply/(eq_onT (vm2:= vm0)) => //.
      by apply/eq_onS/(set_var_disjoint_eq_on (x:= to_var xr) (v:= Vword v1)).
    rewrite /exec_sopn /= hmsf /= !truncate_word_u /=.
    have -> : wand (wrepr U8 1) (x86_nelem_mask U64 U128) = wrepr U8 1.
    + by apply/wunsigned_inj/(wand_modulo _ 1).
    rewrite /m2 /= /vm2 /pv2 /v2 /with_vm /=.
    do 5! f_equal.
    rewrite /wpinsr /v2 /wpbroadcast /= /v1 /wpinsr /=.
    by rewrite subword_make_vec_bits_low.
  rewrite foldM_cat => {hmap1 hops}.
  (* third write *)
  pose v3 := wpbroadcast ws wmsf.
  pose (pv3 := (@Build_pword U256 ws v3 (wsize_ge_U256 ws))).
  pose (vm3 := ((evm m2).[to_var xr <- ok pv3])%vmap).
  pose (m3 := with_vm m2 vm3).
  have : exists2 s3,
      foldM (fun '(op'', asm_args) => [eta eval_op op'' asm_args]) s2 ops2' = ok s3 &
      lom_eqv rip m3 s3.
  + move: hmap2; case: eqP => [? | ]; last first.
    + move=> /= hws1 [?]; subst ops2' => /=.
      eexists; first reflexivity.
      apply: (lom_eqv_ext _ hlo2).
      move=> z; rewrite /vm3.
      case: (to_var xr =P z) => [<- | /eqP ?]; last by rewrite Fv.setP_neq.
      rewrite /m2 /vm2 /= !Fv.setP_eq /pv2 /pv3.
      have ? : ws = U128 by case: (ws) hws1 Hws.
      by subst ws; rewrite -(Eqdep_dec.UIP_refl_bool _ (wsize_ge_U256 U128)).
    subst ws => hmap2.
    apply: (@assemble_extra_concat128 rip ii [:: LLvar aux] [:: Rexpr (Fvar aux); Rexpr (Fvar aux)]
            m2 [:: Vword v2; Vword v2] [:: Vword (wpbroadcast U256 wmsf)] m3 s2 _ ops2') hmap2 hlo2 => //=.
    + by rewrite /get_var /vm2 Fv.setP_eq.
    + rewrite /exec_sopn /= truncate_word_u /=; do 3!f_equal.
      rewrite /v2 /wpbroadcast /=.
      exact: make_vec_4x64.
    by rewrite -(Eqdep_dec.UIP_refl_bool _ (wsize_ge_U256 U256)).
Transparent cat.
  move=> [s3 -> hlo3] /= {hmap2}.
  (* fourth instruction *)
  move: hws; subst y => /=.
  rewrite (sumbool_of_boolET (wsize_ge_U256 ws)) /with_vm /=.
  set v4 := wor _ _; set pv4 := {| pw_word := v4 |}.
  set vm1' := ((evm m).[ _ <- _])%vmap => -[<-].
  pose (vm4 := (vm3 .[ to_var yr <- ok pv4])%vmap).
  have /(_ (with_vm m vm4)) [|s' -> hlo4] /= :=
    assemble_opsP eval_assemble_cond hmap3 erefl _ hlo3.
  + have -> /=: get_var vm3 (to_var xr) = ok (Vword v3).
    + by rewrite /get_var /vm3 Fv.setP_eq /=.
    have -> /= : sem_rexpr (emem m) vm3 ew = ok vw.
    + rewrite -hew; apply: free_vars_rP.
      apply/eq_onS/(eq_onT (vm2:= vm2)); [ apply/(eq_onT (vm2:= vm1)); [ apply/(eq_onT (vm2:= vm0)) | ] | ].
      + by apply(set_var_disjoint_eq_on (x:= to_var xr) (v:= Vword v0)).
      + by apply/(set_var_disjoint_eq_on (x:= to_var xr) (v:= Vword v1)).
      + by apply/(set_var_disjoint_eq_on (x:= to_var xr) (v:= Vword v2)).
      apply/(set_var_disjoint_eq_on (x:= to_var xr) (v:= Vword v3)) => //.
      by rewrite /set_var /= (sumbool_of_boolET (wsize_ge_U256 ws)).
    by rewrite /exec_sopn /= truncate_word_u hw /= /sopn_sem /= /x86_VPOR /x86_u128_binop
         /check_size_128_256 Hws' /= (wsize_ge_U256 ws) /=
         (sumbool_of_boolET (wsize_ge_U256 ws)).
  exists s' => //; apply: lom_eqv_ext hlo4 => z /=.
  rewrite /vm4; case: (to_var yr =P z) => [ | /eqP] ?;first by subst z; rewrite !Fv.setP_eq.
  rewrite Fv.setP_neq // Fv.setP_neq // /vm3 /m2 /vm2 /m1 /vm1 /m0 /vm0 /vm1' /=.
  case: (to_var xr =P z) => [<- | /eqP ?]; first by rewrite !Fv.setP_eq.
  by rewrite !Fv.setP_neq.
Qed.

Definition x86_hagparams : h_asm_gen_params (ap_agp x86_params) :=
  {|
    hagp_eval_assemble_cond := eval_assemble_cond;
    hagp_assemble_extra_op := assemble_extra_op;
  |}.


(* ------------------------------------------------------------------------ *)
(* Register zeroization hypotheses. *)

Section REGISTER_ZEROIZATION.

Import
  linear_sem.
Import
  register_zeroization
  register_zeroization_proof
  register_zeroization_proof_utils.

Definition x86_h_rz_zeroized (x : var) : option value :=
  match vtype x with
  | sword ws => Some (@Vword ws 0%R)
  | sbool => Some (Vbool (x \in [:: to_var ZF; to_var PF ]))
  | _ => None
  end.

Notation invariant := (invariant x86_h_rz_zeroized).

(* All lemmas are generalized to code rather than a single instruction. *)
Notation zeroize_var_cmd err :=
  (fun x => Let args := x86_zeroize_var err x in ok [:: args ])
  (only parsing).

Lemma x86_zeroize_varP err_register x :
  get_lopn_invariant (zeroize_var_cmd err_register) invariant x.
Proof.
  move=> lp scs vm m fn pre pos args ii h hbody.

  move: h.
  move: x => [[|||ws] xname] //=.
  set x := {| vname := xname; |}.
  rewrite /x86_zeroize_var /=.

  case hws : (ws <= U64)%CMP;
    move=> [?]; subst args.

  - eexists; eexists; eexists; split.
    + apply: LSem_step.
      rewrite /lsem1 /step -{1}(addn0 (size pre)).
      rewrite (find_instr_skip hbody) /=.

      (* TODO: Abstract. *)
      rewrite /eval_instr /=.
      rewrite /of_estate /=.
      subst x.
      {
        all: case: ws hws hbody => // _ _.
        all: rewrite /= pword_of_wordE zero_extend_u addn1.
        all: reflexivity.
      }

    (* TODO: This is the same as the wide register case. *)
    split; first done; first done.
    split=> y hy.

    + move: hy => /sv_of_listP.
      rewrite notin_cons.
      move=> /andP [] /eqP hyx _.
      rewrite /=.
      by t_vm_get.

    move: hy => /Sv_memP /sv_of_listP.
    rewrite in_cons.
    move=> /orP []; last done.
    move=> /eqP ?; subst y.
    rewrite /zeroized_on.
    by rewrite get_var_eq /= wrepr0.

  eexists; eexists; eexists; split.
  - apply: LSem_step.
    rewrite /lsem1 /step -{1}(addn0 (size pre)).
    rewrite (find_instr_skip hbody) /=.

    (* TODO: Abstract. *)
    rewrite /eval_instr /=.
    rewrite /of_estate /=.
    subst x.
    {
      all: case: ws hws hbody => // _ _.
      all: rewrite /= pword_of_wordE addn1.
      all: reflexivity.
    }

  split; first done; first done.
  split=> y hy.

  - move: hy => /sv_of_listP.
    rewrite notin_cons.
    move=> /andP [] /eqP hyx _.
    rewrite /=.
    by t_vm_get.

  move: hy => /Sv_memP /sv_of_listP.
  rewrite in_cons.
  move=> /orP []; last done.
  move=> /eqP ?; subst y.
  rewrite /zeroized_on.
  by rewrite get_var_eq /=.
Qed.

Lemma x86_zeroize_flagsP :
  zeroize_flags_spec x86_zeroize_flags x86_h_rz_zeroized.
Proof.
  move=> lp scs vm m err_flags fn ii xname P Q args.
  move=> [?]; subst args.
  set lflags := LLvar _ :: _.
  move=> hx hbody.

  eexists.

  - apply: LSem_step.
    rewrite /lsem1 /step -{1}(addn0 (size P)).
    rewrite (find_instr_skip hbody) /=.
    rewrite /eval_instr /=.
    rewrite /sem_sopn /=.
    rewrite /get_gvar /=.
    move: hx.
    rewrite /zeroized_on.
    case: get_var => //= v.
    move: v => [|||[]|] // w [?]; subst w.
    rewrite /exec_sopn /=.
    rewrite /of_estate /with_vm addn1 /=.
    reflexivity.

  split=> y; first last.

  - move=> /Sv_memP /sv_of_listP.
    rewrite /= /zeroized_on !in_cons.
    repeat (move=> /orP [/eqP -> |]; first by t_get_var).
    done.

  move=> /sv_of_listP.
  rewrite !notin_cons.
  repeat (move=> /andP [] /eqP ?).
  move=> _.
  by t_vm_get.
Qed.

Lemma x86_h_rz_cmd_args :
  h_rz_cmd_args_spec (rz_cmd_args x86_rzparams) x86_h_rz_zeroized.
Proof.
  exact: (naive_rz_cmd_argsP _ _ _ x86_zeroize_varP x86_zeroize_flagsP).
Qed.

Definition x86_hrzparams : h_register_zeroization_params x86_rzparams :=
  {|
    h_rz_cmd_args := x86_h_rz_cmd_args;
  |}.

End REGISTER_ZEROIZATION.


(* ------------------------------------------------------------------------ *)
(* Speculative execution. *)

Lemma x86_spec_shp_lower :
  spec_shp_lower (shp_lower x86_shparams).
Proof.
  move=> s s' gd lvs slho es args res lvs' op' es'.
  case: slho => [|||[]||] //= [???] hargs;
     subst lvs' op' es'; rewrite /sem_sopn /exec_sopn /= => ->;
     move: args hargs; destruct_opn_args=> /=.
  - by move=> _ _ [<-] <-.
  - by move=> [->] _ _ [<-] ? -> [<-] <-.
  - by move=> _ _ ? -> [<-] <-.
  all: move=> [v [] ? hv]; subst v; rewrite hv.
  all: move=>  _ ? -> _ [<-] [<-] <- /=.
  1,2,3:
   move/to_wordI: hv => [sz [w] [? /truncate_wordP [hle hze]]]; subst => /=;
   rewrite truncate_word_le ?(cmp_le_trans _ hle) //
      -(zero_extend_idem (s2:= U64)) // -hze zero_extend0 /=.
  all: by rewrite ?wpbroadcast0 worC wor0.
Qed.

Definition x86_hshparams : h_sh_params (ap_shp x86_params) :=
  {|
    hshp_spec_lower := x86_spec_shp_lower;
  |}.


(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Definition x86_is_move_opP op vx v :
  ap_is_move_op x86_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> List.Forall2 value_uincl v [:: vx ].
Proof.
  case: op => [[[|] [] ws] | []] // _.

  all: rewrite /exec_sopn /=.
  all: t_xrbindP=> w w0 /to_wordI' [ws' [wx [hle ??]]];
         subst vx w0.

  all: rewrite /sopn_sem /=.
  all: match goal with
       | [ |- ?f (zero_extend _ _) = _ -> _ ] => rewrite /f
       end.
  all: t_xrbindP=> *.
  all: t_simpl_rewrites; subst.

  all: constructor; last by constructor.
  all: exact: word_uincl_zero_ext.
Qed.


(* ------------------------------------------------------------------------ *)

Definition x86_h_params : h_architecture_params x86_params :=
  {|
    hap_hpip := x86_hpiparams;
    hap_hsap := x86_hsaparams;
    hap_hlip := x86_hliparams;
    ok_lip_tmp := x86_ok_lip_tmp;
    hap_hlop := x86_hloparams;
    hap_hagp := x86_hagparams;
    hap_hrzp := x86_hrzparams;
    hap_hshp := x86_hshparams;
    hap_is_move_opP := x86_is_move_opP;
  |}.

End Section.
